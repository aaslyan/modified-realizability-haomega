/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.RealCalculusBridge

/-!
# Validated Numerics: Dyadic Ball Arithmetic, Krawczyk Root/Fixed-Point Operators (1D & ND), and True Fourier Integral Reconstruction

This module addresses three foundational capabilities of modern numerical analysis and validated
scientific computing on top of [`HAomega/RealCalculusBridge.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean):

## 1. Fixed-Denominator Dyadic Ball Arithmetic (`roundDyadic`, `DyadicBall`, `approxDyadic`)
- Eliminates exact-rational denominator swell in polynomial evaluation by rounding each power-series
  term $c_n x^n$ to a fixed binary precision $2^{-p}$ via `roundDyadic q p = ⌊q · 2^p⌋ / 2^p`.
- Proves the single-term rounding bound `|(roundDyadic q p : ℝ) - (q : ℝ)| ≤ 1 / 2^p` (`roundDyadic_error_le`)
  and the $N$-term roundoff accumulation bound
  `|(S.evalDyadic N p x : ℝ) - S.realEvalPoly N (x.val : ℝ)| ≤ N / 2^p` (`evalDyadic_sub_realEvalPoly_le`).
- Proves that `S.evalDyadic N p x` is a single dyadic fraction `(S.evalDyadicNum N p x : Rat) / 2^p`
  with fixed denominator $2^p$ (`evalDyadic_eq_num_div_pow2`).
- Establishes the **Certified Dyadic Series Evaluator Theorem (`CertifiedAnalyticRep.approxDyadic_spec`)**:
  at truncation degree $N(k) = k + S.M + 2$ and dyadic bit-precision $p(k) = 2k + S.M + 3$,
  `S.approxDyadic k x` approximates the true infinite real power series `S.realAnalyticValue (x.val : ℝ)`
  within $2^{-k}$, packaged as a verified `DyadicBall` enclosure.

## 2. The Certified Krawczyk / Interval-Newton Operator in 1D and $N$ Dimensions
- **1D Krawczyk Operator on `PolyODEProof` (`krawczykMap`, `krawczykFast`)**:
  - Defines the preconditioned Newton–Krawczyk operator $T_c(x) = x - c \cdot f_P(x)$ ($c \neq 0$),
    avoiding any manual sign-change bracket $f(a) < 0 < f(b)$.
  - Proves `krawczykMap_contractive_of_deriv_approx`: using the quadratic Taylor remainder
    `realAnalyticValue_quad_rem_disk` and derivative Lipschitz bound, whenever
    $|1 - c \cdot f_{P'}(x_0)| \le 1/4$ and the ball radius $\rho$ satisfies the explicit curvature bound,
    $T_c$ is automatically $(1/2)$-contractive on $[x_0 - \rho, x_0 + \rho]$ and maps the ball into itself
    whenever $|c \cdot f_P(x_0)| \le \rho / 2$.
  - Proves **Existence, Uniqueness, and $O(2^{-n})$ Convergence (`PolyODEProof.krawczykFast_exists_unique_real_zero`)**:
    the fast constructive rational iterates `P.krawczykFast c x₀ n` converge in $\mathbb{R}$ to the
    **unique** real zero $z_* \in [x_0 - \rho, x_0 + \rho]$ of `P.toCertifiedAnalyticRep.realAnalyticValue`.
- **$N$-Dimensional Krawczyk Operator on $\mathbb{R}^d = \mathrm{Fin}\;d \to \mathbb{R}$ (`krawczykOpND`, `krawczykND_exists_unique_zero`)**:
  - For any dimension $d \in \mathbb{N}$, nonlinear system $F : (\mathrm{Fin}\;d \to \mathbb{R}) \to (\mathrm{Fin}\;d \to \mathbb{R})$,
    and injective preconditioner $C$, if $K_{F,C}(x) = x - C(F(x))$ is $(1/2)$-contractive on the
    $\ell_\infty$ box $\mathrm{Metric.closedBall}\;x_0\;\rho$ and $\|C(F(x_0))\|_\infty \le \rho / 2$,
    then all iterates $x_n = \operatorname{krawczykIterND}\;F\;C\;x_0\;n$ remain inside the box and
    converge at geometric rate $\|x_n - z_*\|_\infty \le \rho / 2^n$ to the **unique** zero $F(z_*) = 0$ in the box.

## 3. Classical Mathlib Fourier Integral Orthogonality & True Fourier Series Reconstruction
- Proves classical Mathlib `intervalIntegral` orthogonality of $\cos(m x)$ and $\sin(m x)$ over $0..2\pi$
  (`integral_cos_nat_mul_two_pi`, `integral_sin_nat_mul_two_pi`, `integral_cos_mul_cos_two_pi`,
  `integral_sin_mul_sin_two_pi`, `integral_cos_mul_sin_two_pi`).
- Defines the real periodic function `F.realWave : ℝ → ℝ` and its $N$-mode trigonometric partial sum
  `F.realWaveTrunc N : ℝ → ℝ`, together with the classical Mathlib Fourier coefficient functionals
  `realFourierA0`, `realFourierA`, and `realFourierB` defined via $\int_0^{2\pi} \cdots dx$.
- Proves that the classical Mathlib Fourier integrals of the infinite series `F.realWave` equal the exact
  stored shell coefficients (`realFourierA0_realWave`, `realFourierA_realWave`, `realFourierB_realWave`).
- Establishes the **True Fourier Integral Reconstruction Theorem (`StripFourierRep.certified_fourier_reconstruction`)**:
  $$F.\operatorname{realWave}(x) = \operatorname{realFourierA0}(F.\operatorname{realWave})
    + \sum_{m=1}^{\infty} \Bigl(\operatorname{realFourierA}(F.\operatorname{realWave}, m)\cos(m x)
      + \operatorname{realFourierB}(F.\operatorname{realWave}, m)\sin(m x)\Bigr)$$
  with certified $2^{-k}$ truncation error across all $x \in \mathbb{R}$ at $N(k) = k + F.M + 1$.
-/

noncomputable section

namespace HAomega

open Classical

/-! ## Section 1: Fixed-Denominator Dyadic Ball Arithmetic (`roundDyadic`, `DyadicBall`, `approxDyadic`) -/

/-- Integer numerator $\lfloor q \cdot 2^p \rfloor \in \mathbb{Z}$ of the $p$-bit dyadic floor rounding of `q : Rat`. -/
def roundDyadicNum (q : Rat) (p : Nat) : Int :=
  ⌊q * (2 : Rat) ^ p⌋

/-- Rounded dyadic rational $\lfloor q \cdot 2^p \rfloor / 2^p \in \mathbb{Q}$ with fixed denominator $2^p$. -/
def roundDyadic (q : Rat) (p : Nat) : Rat :=
  (roundDyadicNum q p : Rat) / (2 : Rat) ^ p

/-- Rational rounding error bound: `roundDyadic q p ≤ q` and `q - roundDyadic q p ≤ 1 / 2^p`. -/
theorem roundDyadic_bounds_rat (q : Rat) (p : Nat) :
    roundDyadic q p ≤ q ∧ q - roundDyadic q p ≤ 1 / (2 : Rat) ^ p := by
  unfold roundDyadic roundDyadicNum
  have h2p : (0 : Rat) < (2 : Rat) ^ p := by positivity
  have hle : (⌊q * (2 : Rat) ^ p⌋ : Rat) ≤ q * (2 : Rat) ^ p := Int.floor_le _
  have hlt : q * (2 : Rat) ^ p < (⌊q * (2 : Rat) ^ p⌋ : Rat) + 1 := Int.lt_floor_add_one _
  constructor
  · exact (div_le_iff₀ h2p).mpr hle
  · have h1 : (q * (2 : Rat) ^ p - (⌊q * (2 : Rat) ^ p⌋ : Rat)) / (2 : Rat) ^ p ≤
        1 / (2 : Rat) ^ p := by
      refine div_le_div_of_nonneg_right ?_ (le_of_lt h2p)
      linarith
    have h2 : (q * (2 : Rat) ^ p - (⌊q * (2 : Rat) ^ p⌋ : Rat)) / (2 : Rat) ^ p =
        q - (⌊q * (2 : Rat) ^ p⌋ : Rat) / (2 : Rat) ^ p := by
      rw [sub_div, mul_div_cancel_right₀ q (ne_of_gt h2p)]
    linarith

/-- Rational absolute rounding error bound: `|roundDyadic q p - q| ≤ 1 / 2^p`. -/
theorem roundDyadic_error_rat_le (q : Rat) (p : Nat) :
    |roundDyadic q p - q| ≤ 1 / (2 : Rat) ^ p := by
  have hb := roundDyadic_bounds_rat q p
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- **Single-Term Dyadic Rounding Bound in $\mathbb{R}$ (`roundDyadic_error_le`)**:
    For every rational $q \in \mathbb{Q}$ and bit-precision $p \in \mathbb{N}$:
    $$\big|(\operatorname{roundDyadic}\;q\;p : \mathbb{R}) - (q : \mathbb{R})\big| \le \frac{1}{(2 : \mathbb{R})^p}.$$ -/
theorem roundDyadic_error_le (q : Rat) (p : Nat) :
    |(roundDyadic q p : ℝ) - (q : ℝ)| ≤ 1 / (2 : ℝ) ^ p := by
  have h := rat_abs_le_pow2_to_real (roundDyadic_error_rat_le q p)
  simpa only [Rat.cast_sub] using h

/-- Certified dyadic interval enclosure `[center - radius, center + radius]` with fixed denominator $2^p$. -/
structure DyadicBall where
  num    : Int
  prec   : Nat
  radius : Rat

/-- Rational center `num / 2^prec` of a `DyadicBall`. -/
def DyadicBall.center (B : DyadicBall) : Rat :=
  (B.num : Rat) / (2 : Rat) ^ B.prec

/-- Membership of a real number `v : ℝ` in a `DyadicBall` (`|(B.center : ℝ) - v| ≤ (B.radius : ℝ)`). -/
def DyadicBall.Contains (B : DyadicBall) (v : ℝ) : Prop :=
  |(B.center : ℝ) - v| ≤ (B.radius : ℝ)

namespace CertifiedAnalyticRep

/-- Combined integer numerator $\sum_{n < N} \lfloor c_n x^n \cdot 2^p \rfloor \in \mathbb{Z}$
    for fixed-denominator dyadic power-series evaluation. -/
def evalDyadicNum (S : CertifiedAnalyticRep) (N p : Nat) (x : Q) : Int :=
  ∑ n ∈ Finset.range N, roundDyadicNum (S.coeff n * x.val ^ n) p

/-- Term-by-term dyadic-rounded degree-$N$ polynomial evaluator at binary precision $p$. -/
def evalDyadic (S : CertifiedAnalyticRep) (N p : Nat) (x : Q) : Rat :=
  ∑ n ∈ Finset.range N, roundDyadic (S.coeff n * x.val ^ n) p

/-- **Fixed-Denominator Identity (`evalDyadic_eq_num_div_pow2`)**:
    `S.evalDyadic N p x` is a single dyadic fraction `(S.evalDyadicNum N p x : Rat) / 2^p`
    with integer numerator and fixed power-of-two denominator $2^p$ (zero denominator swell). -/
theorem evalDyadic_eq_num_div_pow2 (S : CertifiedAnalyticRep) (N p : Nat) (x : Q) :
    S.evalDyadic N p x = (S.evalDyadicNum N p x : Rat) / (2 : Rat) ^ p := by
  unfold evalDyadic evalDyadicNum roundDyadic
  rw [← Finset.sum_div, Int.cast_sum]

/-- **$N$-Term Roundoff Error Accumulation Bound (`evalDyadic_sub_realEvalPoly_le`)**:
    Rounding each of the $N$ terms $c_n x^n$ to binary precision $2^{-p}$ accumulates
    at most $N / 2^p$ total roundoff error against the exact polynomial evaluation:
    $$\big|(S.\operatorname{evalDyadic}\;N\;p\;x : \mathbb{R}) - S.\operatorname{realEvalPoly}\;N\;(x.\mathrm{val} : \mathbb{R})\big|
      \le \frac{(N : \mathbb{R})}{(2 : \mathbb{R})^p}.$$ -/
theorem evalDyadic_sub_realEvalPoly_le (S : CertifiedAnalyticRep) (N p : Nat) (x : Q) :
    |(S.evalDyadic N p x : ℝ) - S.realEvalPoly N (x.val : ℝ)| ≤
      (N : ℝ) / (2 : ℝ) ^ p := by
  unfold evalDyadic realEvalPoly realSeriesTerm
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ n ∈ Finset.range N,
      |(roundDyadic (S.coeff n * x.val ^ n) p : ℝ) - (S.coeff n : ℝ) * (x.val : ℝ) ^ n| ≤
        1 / (2 : ℝ) ^ p := by
    intro n _
    have h := roundDyadic_error_le (S.coeff n * x.val ^ n) p
    simpa only [Rat.cast_mul, Rat.cast_pow] using h
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- Truncation degree schedule $N(k) = k + S.M + 2$ for dyadic series evaluation. -/
def dyadicDeg (S : CertifiedAnalyticRep) (k : Nat) : Nat :=
  k + S.M + 2

/-- Binary rounding precision schedule $p(k) = k + N(k) + 1 = 2k + S.M + 3$ for dyadic series evaluation. -/
def dyadicPrec (S : CertifiedAnalyticRep) (k : Nat) : Nat :=
  k + S.dyadicDeg k + 1

/-- **Fixed-Denominator Dyadic Series Evaluator (`CertifiedAnalyticRep.approxDyadic`)**:
    Evaluates $S$ to accuracy $2^{-k}$ using purely dyadic rationals of fixed denominator $2^{p(k)}$. -/
def approxDyadic (S : CertifiedAnalyticRep) (k : Nat) (x : Q) : Rat :=
  S.evalDyadic (S.dyadicDeg k) (S.dyadicPrec k) x

/-- Certified `DyadicBall` enclosure produced by `approxDyadic`. -/
def approxDyadicBall (S : CertifiedAnalyticRep) (k : Nat) (x : Q) : DyadicBall where
  num    := S.evalDyadicNum (S.dyadicDeg k) (S.dyadicPrec k) x
  prec   := S.dyadicPrec k
  radius := 1 / (2 : Rat) ^ k

/-- **Certified Fixed-Denominator Dyadic Evaluation Theorem (`approxDyadic_spec`)**:
    For every $x : Q$ in the certified disk $|x.\mathrm{val}| \le 2^{-(S.R + 1)}$ and every target precision $k \in \mathbb{N}$:
    1. `S.approxDyadic k x` has fixed power-of-two denominator $2^{2k + S.M + 3}$:
       `S.approxDyadic k x = (S.approxDyadicBall k x).center`.
    2. Combined roundoff + series-truncation error is at most $2^{-k}$:
       $$\big|(S.\operatorname{approxDyadic}\;k\;x : \mathbb{R}) - S.\operatorname{realAnalyticValue}(x.\mathrm{val} : \mathbb{R})\big|
         \le \frac{1}{(2 : \mathbb{R})^k},$$
       i.e. `(S.approxDyadicBall k x).Contains (S.realAnalyticValue (x.val : ℝ))`. -/
theorem approxDyadic_spec (S : CertifiedAnalyticRep) (k : Nat) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (S.R + 1)) :
    S.approxDyadic k x = (S.approxDyadicBall k x).center ∧
    |(S.approxDyadic k x : ℝ) - S.realAnalyticValue (x.val : ℝ)| ≤ 1 / (2 : ℝ) ^ k ∧
    (S.approxDyadicBall k x).Contains (S.realAnalyticValue (x.val : ℝ)) := by
  have hcenter : S.approxDyadic k x = (S.approxDyadicBall k x).center :=
    S.evalDyadic_eq_num_div_pow2 (S.dyadicDeg k) (S.dyadicPrec k) x
  have hx_real : |(x.val : ℝ)| ≤ 1 / (2 : ℝ) ^ (S.R + 1) := rat_abs_le_pow2_to_real hx
  set N := S.dyadicDeg k
  set p := S.dyadicPrec k
  have hround := S.evalDyadic_sub_realEvalPoly_le N p x
  have hround_half : (N : ℝ) / (2 : ℝ) ^ p ≤ 1 / (2 : ℝ) ^ (k + 1) := by
    have hN_pow : (N : ℝ) ≤ (2 : ℝ) ^ N := real_nat_le_two_pow N
    have h1 : (N : ℝ) / (2 : ℝ) ^ p ≤ (2 : ℝ) ^ N / (2 : ℝ) ^ p :=
      div_le_div_of_nonneg_right hN_pow (by positivity)
    have h2 : (2 : ℝ) ^ N / (2 : ℝ) ^ p = 1 / (2 : ℝ) ^ (k + 1) := by
      dsimp [p, dyadicPrec]
      rw [show k + N + 1 = N + (k + 1) by omega, pow_add (2 : ℝ) N (k + 1)]
      field_simp
    linarith
  have htrunc := S.realAnalyticValue_sub_realEvalPoly_le (x.val : ℝ) hx_real N
  have htrunc_half : (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N = 1 / (2 : ℝ) ^ (k + 1) := by
    dsimp [N, dyadicDeg]
    rw [show k + S.M + 2 = (S.M + 1) + (k + 1) by omega, pow_add (2 : ℝ) (S.M + 1) (k + 1)]
    field_simp
  rw [htrunc_half] at htrunc
  have htri : |(S.approxDyadic k x : ℝ) - S.realAnalyticValue (x.val : ℝ)| ≤
      |(S.approxDyadic k x : ℝ) - S.realEvalPoly N (x.val : ℝ)| +
      |S.realEvalPoly N (x.val : ℝ) - S.realAnalyticValue (x.val : ℝ)| := by
    have := abs_add_le ((S.approxDyadic k x : ℝ) - S.realEvalPoly N (x.val : ℝ))
      (S.realEvalPoly N (x.val : ℝ) - S.realAnalyticValue (x.val : ℝ))
    simpa using this
  have hdef : S.approxDyadic k x = S.evalDyadic N p x := rfl
  rw [← hdef] at hround
  have hsum : 1 / (2 : ℝ) ^ (k + 1) + 1 / (2 : ℝ) ^ (k + 1) = 1 / (2 : ℝ) ^ k := by
    rw [pow_succ (2 : ℝ) k]; field_simp; ring
  have herr : |(S.approxDyadic k x : ℝ) - S.realAnalyticValue (x.val : ℝ)| ≤ 1 / (2 : ℝ) ^ k := by
    linarith
  refine ⟨hcenter, herr, ?_⟩
  unfold DyadicBall.Contains
  rw [← hcenter]
  have hrad : ((S.approxDyadicBall k x).radius : ℝ) = 1 / (2 : ℝ) ^ k := by
    unfold approxDyadicBall; push_cast; rfl
  rwa [hrad]

end CertifiedAnalyticRep

/-! ## Section 2: The Certified Krawczyk / Interval-Newton Operator in 1D and $N$ Dimensions -/

/-- **1D Preconditioned Newton–Krawczyk Map (`PolyODEProof.krawczykMap`)**:
    $$T_c(x) := x - c \cdot P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}(x).$$ -/
noncomputable def PolyODEProof.krawczykMap (P : PolyODEProof) (c : Rat) (x : ℝ) : ℝ :=
  x - (c : ℝ) * P.toCertifiedAnalyticRep.realAnalyticValue x

/-- For any non-zero preconditioner $c \neq 0$, fixed points of `P.krawczykMap c` are
    **identical** to real zeros of `P.toCertifiedAnalyticRep.realAnalyticValue`. -/
theorem PolyODEProof.krawczykMap_fixedPoint_iff_zero (P : PolyODEProof) (c : Rat) (hc : c ≠ 0) (x : ℝ) :
    P.krawczykMap c x = x ↔ P.toCertifiedAnalyticRep.realAnalyticValue x = 0 := by
  unfold PolyODEProof.krawczykMap
  have hc_real : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  constructor
  · intro h
    have hmul : (c : ℝ) * P.toCertifiedAnalyticRep.realAnalyticValue x = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hc_real
  · intro h
    rw [h, mul_zero, sub_zero]

/-- **Krawczyk Ball Self-Mapping Theorem (`PolyODEProof.krawczykMap_maps_ball_to_ball`)**:
    If `P.krawczykMap c` is $(1/2)$-contractive on $[x_0 - \rho, x_0 + \rho]$ and the center residual
    satisfies $|c \cdot f_P(x_0)| \le \rho / 2$, then `P.krawczykMap c` maps $[x_0 - \rho, x_0 + \rho]$
    into itself. -/
theorem PolyODEProof.krawczykMap_maps_ball_to_ball (P : PolyODEProof) (c : Rat) (x₀ ρ : ℝ)
    (hcontract : ∀ u v : ℝ, |u - x₀| ≤ ρ → |v - x₀| ≤ ρ →
      |P.krawczykMap c u - P.krawczykMap c v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hcenter : |(c : ℝ) * P.toCertifiedAnalyticRep.realAnalyticValue x₀| ≤ (1 / 2 : ℝ) * ρ)
    {x : ℝ} (hx : |x - x₀| ≤ ρ) :
    |P.krawczykMap c x - x₀| ≤ ρ := by
  have hx0 : |x₀ - x₀| ≤ ρ := by
    rw [sub_self, abs_zero]
    exact le_trans (abs_nonneg _) hx
  have hc := hcontract x x₀ hx hx0
  have hid : P.krawczykMap c x - x₀ =
      (P.krawczykMap c x - P.krawczykMap c x₀) -
      (c : ℝ) * P.toCertifiedAnalyticRep.realAnalyticValue x₀ := by
    unfold PolyODEProof.krawczykMap; ring
  rw [hid]
  have htri : |(P.krawczykMap c x - P.krawczykMap c x₀) -
      (c : ℝ) * P.toCertifiedAnalyticRep.realAnalyticValue x₀| ≤
      |P.krawczykMap c x - P.krawczykMap c x₀| +
      |(c : ℝ) * P.toCertifiedAnalyticRep.realAnalyticValue x₀| := by
    simpa [sub_eq_add_neg] using
      abs_add_le (P.krawczykMap c x - P.krawczykMap c x₀)
        (-((c : ℝ) * P.toCertifiedAnalyticRep.realAnalyticValue x₀))
  linarith

/-- **Automatic Krawczyk Contractivity from Quadratic Taylor Remainder (`krawczykMap_contractive_of_deriv_approx`)**:
    Suppose the ball $B(x_0, \rho) = \{u \in \mathbb{R} : |u - x_0| \le \rho\}$ lies in the quarter-radius disks
    of both `P` and `P.derivOp`, the preconditioner $c$ satisfies $|1 - c \cdot f_{P'}(x_0)| \le 1/4$,
    and the radius $\rho$ satisfies
    $$|c| \cdot \bigl(2^{M_{P'} + R_{P'} + 2} + 2 \cdot 2^{M_P + 2 R_P + 5}\bigr) \cdot \rho \le \frac{1}{4}.$$
    Then `P.krawczykMap c` is automatically $(1/2)$-contractive across all $u, v \in B(x_0, \rho)$! -/
theorem PolyODEProof.krawczykMap_contractive_of_deriv_approx (P : PolyODEProof)
    (c : Rat) (x₀ ρ : ℝ)
    (hdisk : ∀ u : ℝ, |u - x₀| ≤ ρ → |u| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2))
    (hdisk_d : ∀ u : ℝ, |u - x₀| ≤ ρ → |u| ≤ 1 / (2 : ℝ) ^ ((sysParams P.derivOp.sys).2 + 2))
    (hpre : |1 - (c : ℝ) * P.derivOp.toCertifiedAnalyticRep.realAnalyticValue x₀| ≤ 1 / 4)
    (hrho : |(c : ℝ)| *
      ((2 : ℝ) ^ ((sysParams P.derivOp.sys).1 + (sysParams P.derivOp.sys).2 + 2) +
       2 * (2 : ℝ) ^ ((sysParams P.sys).1 + 2 * (sysParams P.sys).2 + 5)) * ρ ≤ 1 / 4)
    {u v : ℝ} (hu : |u - x₀| ≤ ρ) (hv : |v - x₀| ≤ ρ) :
    |P.krawczykMap c u - P.krawczykMap c v| ≤ (1 / 2 : ℝ) * |u - v| := by
  let S := P.toCertifiedAnalyticRep
  let S' := P.derivOp.toCertifiedAnalyticRep
  set K := (2 : ℝ) ^ ((sysParams P.sys).1 + 2 * (sysParams P.sys).2 + 5)
  set L' := (2 : ℝ) ^ ((sysParams P.derivOp.sys).1 + (sysParams P.derivOp.sys).2 + 2)
  have hrho_nonneg : 0 ≤ ρ := le_trans (abs_nonneg _) hu
  have hx0_ball : |x₀ - x₀| ≤ ρ := by rw [sub_self, abs_zero]; exact hrho_nonneg
  have hquad := P.realAnalyticValue_quad_rem_disk v u (hdisk v hv) (hdisk u hu)
  have hlip_d := S'.realAnalyticValue_lipschitz_disk v x₀ (hdisk_d v hv) (hdisk_d x₀ hx0_ball)
  set Qrem := S.realAnalyticValue u - S.realAnalyticValue v - S'.realAnalyticValue v * (u - v)
  set Drem := S'.realAnalyticValue v - S'.realAnalyticValue x₀
  have hid : P.krawczykMap c u - P.krawczykMap c v =
      (1 - (c : ℝ) * S'.realAnalyticValue x₀) * (u - v) -
      (c : ℝ) * (Drem * (u - v) + Qrem) := by
    unfold PolyODEProof.krawczykMap
    dsimp [Qrem, Drem]
    ring
  rw [hid]
  have huv_le : |u - v| ≤ 2 * ρ := by
    have h1 : u - v = (u - x₀) + (x₀ - v) := by ring
    have h2 := abs_add_le (u - x₀) (x₀ - v)
    rw [← h1, abs_sub_comm x₀ v] at h2
    linarith
  have hQ_bound : |Qrem| ≤ 2 * K * ρ * |u - v| := by
    have hsq : (u - v) ^ 2 = |u - v| * |u - v| := by rw [← sq_abs, sq]
    rw [hsq] at hquad
    have h2 := mul_le_mul_of_nonneg_right huv_le (abs_nonneg (u - v))
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ K)
    linarith
  have hD_bound : |Drem * (u - v)| ≤ L' * ρ * |u - v| := by
    rw [abs_mul]
    have h1 : |Drem| ≤ L' * ρ := le_trans hlip_d (mul_le_mul_of_nonneg_left hv (by positivity))
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hcomb : |(c : ℝ) * (Drem * (u - v) + Qrem)| ≤
      (|(c : ℝ)| * (L' + 2 * K) * ρ) * |u - v| := by
    rw [abs_mul]
    have htri := abs_add_le (Drem * (u - v)) Qrem
    have hcomb1 : |Drem * (u - v) + Qrem| ≤ (L' + 2 * K) * ρ * |u - v| := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcomb1 (abs_nonneg (c : ℝ))
    have halg : |(c : ℝ)| * ((L' + 2 * K) * ρ * |u - v|) =
        (|(c : ℝ)| * (L' + 2 * K) * ρ) * |u - v| := by ring
    linarith
  have hcomb_quarter : |(c : ℝ) * (Drem * (u - v) + Qrem)| ≤ (1 / 4 : ℝ) * |u - v| := by
    refine le_trans hcomb ?_
    exact mul_le_mul_of_nonneg_right hrho (abs_nonneg _)
  have hfirst_quarter : |(1 - (c : ℝ) * S'.realAnalyticValue x₀) * (u - v)| ≤ (1 / 4 : ℝ) * |u - v| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hpre (abs_nonneg _)
  have htri_main : |(1 - (c : ℝ) * S'.realAnalyticValue x₀) * (u - v) -
      (c : ℝ) * (Drem * (u - v) + Qrem)| ≤
      |(1 - (c : ℝ) * S'.realAnalyticValue x₀) * (u - v)| +
      |(c : ℝ) * (Drem * (u - v) + Qrem)| := by
    simpa [sub_eq_add_neg] using
      abs_add_le ((1 - (c : ℝ) * S'.realAnalyticValue x₀) * (u - v))
        (-((c : ℝ) * (Drem * (u - v) + Qrem)))
  linarith

/-- **Constructive 1D Krawczyk / Simplified-Newton Iterator (`PolyODEProof.krawczykFast`)**:
    Iterates $x_{n+1} = x_n - c \cdot \operatorname{GPACSys.approxFast}\;P.\mathrm{sys}\;P.v\;x_n\;(2n + 2)$. -/
def PolyODEProof.krawczykFast (P : PolyODEProof) (c x₀ : Q) : Nat → Q
  | 0 => x₀
  | n + 1 =>
    let xn := P.krawczykFast c x₀ n
    Q.sub xn (Q.mul c (GPACSys.approxFast P.sys P.v xn (2 * n + 2)))

@[simp]
theorem PolyODEProof.krawczykFast_zero (P : PolyODEProof) (c x₀ : Q) :
    P.krawczykFast c x₀ 0 = x₀ := rfl

/-- Value of the $(n+1)$-th Krawczyk iterate in $\mathbb{Q}$. -/
theorem PolyODEProof.krawczykFast_succ_val (P : PolyODEProof) (c x₀ : Q) (n : Nat) :
    (P.krawczykFast c x₀ (n + 1)).val =
      (P.krawczykFast c x₀ n).val -
        c.val * (GPACSys.approxFast P.sys P.v (P.krawczykFast c x₀ n) (2 * n + 2)).val := by
  change (Q.sub (P.krawczykFast c x₀ n)
    (Q.mul c (GPACSys.approxFast P.sys P.v (P.krawczykFast c x₀ n) (2 * n + 2)))).val = _
  rw [Q.val_sub, Q.val_mul]

/-- One-step approximation error between `P.krawczykFast c x₀ (n + 1)` and the true Krawczyk map
    `P.krawczykMap c.val (P.krawczykFast c x₀ n).val`. -/
theorem PolyODEProof.krawczykFast_step_approx (P : PolyODEProof) (c x₀ : Q) (n : Nat)
    (hdisk : |(P.krawczykFast c x₀ n).val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1)) :
    |((P.krawczykFast c x₀ (n + 1)).val : ℝ) -
      P.krawczykMap c.val ((P.krawczykFast c x₀ n).val : ℝ)| ≤
      |(c.val : ℝ)| * (1 / 4 : ℝ) ^ (n + 1) := by
  set xn := P.krawczykFast c x₀ n
  have hval := P.krawczykFast_succ_val c x₀ n
  have hval_r : ((P.krawczykFast c x₀ (n + 1)).val : ℝ) =
      (xn.val : ℝ) - (c.val : ℝ) * ((GPACSys.approxFast P.sys P.v xn (2 * n + 2)).val : ℝ) := by
    exact_mod_cast hval
  rw [hval_r]
  unfold PolyODEProof.krawczykMap
  rw [P.toCertifiedAnalyticRep.realAnalyticValue_coe xn]
  have hid : ((xn.val : ℝ) - (c.val : ℝ) * ((GPACSys.approxFast P.sys P.v xn (2 * n + 2)).val : ℝ)) -
      ((xn.val : ℝ) - (c.val : ℝ) * P.toCertifiedAnalyticRep.analyticValue xn) =
      -(c.val : ℝ) * (((GPACSys.approxFast P.sys P.v xn (2 * n + 2)).val : ℝ) -
        P.toCertifiedAnalyticRep.analyticValue xn) := by ring
  rw [hid, abs_mul, abs_neg]
  have hcert := certified_evaluation P xn (2 * n + 2) hdisk
  have hpow4 : 1 / (2 : ℝ) ^ (2 * n + 2) = (1 / 4 : ℝ) ^ (n + 1) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul (2 : ℝ) 2 (n + 1), one_div_pow]
    norm_num
  rw [hpow4] at hcert
  exact mul_le_mul_of_nonneg_left hcert (abs_nonneg _)

/-- One-step contraction of the Krawczyk residual $|T_c(x_n) - x_n|$. -/
theorem PolyODEProof.krawczykFast_residual_step (P : PolyODEProof) (c x₀ : Q) (ρ : ℝ)
    (hcontract : ∀ u v : ℝ, |u - (x₀.val : ℝ)| ≤ ρ → |v - (x₀.val : ℝ)| ≤ ρ →
      |P.krawczykMap c.val u - P.krawczykMap c.val v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hball : ∀ n : Nat, |((P.krawczykFast c x₀ n).val : ℝ) - (x₀.val : ℝ)| ≤ ρ)
    (hdisk : ∀ n : Nat, |(P.krawczykFast c x₀ n).val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (n : Nat) :
    |P.krawczykMap c.val ((P.krawczykFast c x₀ (n + 1)).val : ℝ) -
        ((P.krawczykFast c x₀ (n + 1)).val : ℝ)| ≤
      (1 / 2 : ℝ) *
        |P.krawczykMap c.val ((P.krawczykFast c x₀ n).val : ℝ) -
          ((P.krawczykFast c x₀ n).val : ℝ)| +
      2 * |(c.val : ℝ)| * (1 / 4 : ℝ) ^ (n + 1) := by
  set xn : ℝ := ((P.krawczykFast c x₀ n).val : ℝ)
  set xn1 : ℝ := ((P.krawczykFast c x₀ (n + 1)).val : ℝ)
  have hstep := P.krawczykFast_step_approx c x₀ n (hdisk n)
  have hstep' : |P.krawczykMap c.val xn - xn1| ≤ |(c.val : ℝ)| * (1 / 4 : ℝ) ^ (n + 1) := by
    rw [abs_sub_comm]; exact hstep
  have hl := hcontract xn1 xn (hball (n + 1)) (hball n)
  have htri1 : |P.krawczykMap c.val xn1 - xn1| ≤
      |P.krawczykMap c.val xn1 - P.krawczykMap c.val xn| + |P.krawczykMap c.val xn - xn1| := by
    have := abs_add_le (P.krawczykMap c.val xn1 - P.krawczykMap c.val xn)
      (P.krawczykMap c.val xn - xn1)
    simpa using this
  have htri2 : |xn1 - xn| ≤
      |xn1 - P.krawczykMap c.val xn| + |P.krawczykMap c.val xn - xn| := by
    have := abs_add_le (xn1 - P.krawczykMap c.val xn) (P.krawczykMap c.val xn - xn)
    simpa using this
  have htri2_half : (1 / 2 : ℝ) * |xn1 - xn| ≤
      (1 / 2 : ℝ) * |xn1 - P.krawczykMap c.val xn| +
      (1 / 2 : ℝ) * |P.krawczykMap c.val xn - xn| := by linarith
  have hnonneg : (0 : ℝ) ≤ |(c.val : ℝ)| * (1 / 4 : ℝ) ^ (n + 1) := by positivity
  change |P.krawczykMap c.val xn1 - xn1| ≤
    (1 / 2 : ℝ) * |P.krawczykMap c.val xn - xn| + 2 * |(c.val : ℝ)| * (1 / 4 : ℝ) ^ (n + 1)
  linarith

/-- Telescoping bound on the Krawczyk residual $|T_c(x_n) - x_n|$. -/
theorem PolyODEProof.krawczykFast_residual_telescoping (P : PolyODEProof) (c x₀ : Q) (ρ : ℝ)
    (hcontract : ∀ u v : ℝ, |u - (x₀.val : ℝ)| ≤ ρ → |v - (x₀.val : ℝ)| ≤ ρ →
      |P.krawczykMap c.val u - P.krawczykMap c.val v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hball : ∀ n : Nat, |((P.krawczykFast c x₀ n).val : ℝ) - (x₀.val : ℝ)| ≤ ρ)
    (hdisk : ∀ n : Nat, |(P.krawczykFast c x₀ n).val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1)) :
    ∀ n : Nat,
      |P.krawczykMap c.val ((P.krawczykFast c x₀ n).val : ℝ) -
          ((P.krawczykFast c x₀ n).val : ℝ)| ≤
        (|P.krawczykMap c.val (x₀.val : ℝ) - (x₀.val : ℝ)| + 2 * |(c.val : ℝ)|) * (1 / 2 : ℝ) ^ n -
          2 * |(c.val : ℝ)| * (1 / 4 : ℝ) ^ n
  | 0 => by
    simp [PolyODEProof.krawczykFast_zero]
  | n + 1 => by
    have ih := P.krawczykFast_residual_telescoping c x₀ ρ hcontract hball hdisk n
    have hstep := P.krawczykFast_residual_step c x₀ ρ hcontract hball hdisk n
    have halg :
        (1 / 2 : ℝ) *
          ((|P.krawczykMap c.val (x₀.val : ℝ) - (x₀.val : ℝ)| + 2 * |(c.val : ℝ)|) * (1 / 2 : ℝ) ^ n -
            2 * |(c.val : ℝ)| * (1 / 4 : ℝ) ^ n) +
        2 * |(c.val : ℝ)| * (1 / 4 : ℝ) ^ (n + 1) =
        (|P.krawczykMap c.val (x₀.val : ℝ) - (x₀.val : ℝ)| + 2 * |(c.val : ℝ)|) * (1 / 2 : ℝ) ^ (n + 1) -
          2 * |(c.val : ℝ)| * (1 / 4 : ℝ) ^ (n + 1) := by
      rw [pow_succ (1 / 2 : ℝ) n, pow_succ (1 / 4 : ℝ) n]
      ring
    linarith

/-- Explicit $O(2^{-n})$ Krawczyk residual bound. -/
theorem PolyODEProof.krawczykFast_residual_le (P : PolyODEProof) (c x₀ : Q) (ρ : ℝ)
    (hcontract : ∀ u v : ℝ, |u - (x₀.val : ℝ)| ≤ ρ → |v - (x₀.val : ℝ)| ≤ ρ →
      |P.krawczykMap c.val u - P.krawczykMap c.val v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hball : ∀ n : Nat, |((P.krawczykFast c x₀ n).val : ℝ) - (x₀.val : ℝ)| ≤ ρ)
    (hdisk : ∀ n : Nat, |(P.krawczykFast c x₀ n).val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (n : Nat) :
    |P.krawczykMap c.val ((P.krawczykFast c x₀ n).val : ℝ) -
        ((P.krawczykFast c x₀ n).val : ℝ)| ≤
      (|P.krawczykMap c.val (x₀.val : ℝ) - (x₀.val : ℝ)| + 2 * |(c.val : ℝ)|) / (2 : ℝ) ^ n := by
  have htel := P.krawczykFast_residual_telescoping c x₀ ρ hcontract hball hdisk n
  have hpos : (0 : ℝ) ≤ 2 * |(c.val : ℝ)| * (1 / 4 : ℝ) ^ n := by positivity
  have hpow : (|P.krawczykMap c.val (x₀.val : ℝ) - (x₀.val : ℝ)| + 2 * |(c.val : ℝ)|) * (1 / 2 : ℝ) ^ n =
      (|P.krawczykMap c.val (x₀.val : ℝ) - (x₀.val : ℝ)| + 2 * |(c.val : ℝ)|) / (2 : ℝ) ^ n := by
    rw [one_div_pow]; ring
  linarith

/-- **1D Krawczyk Real Zero Existence, Uniqueness, & Convergence Theorem (`krawczykFast_exists_unique_real_zero`)**:
    When $c.\mathrm{val} \neq 0$, `P.krawczykMap c.val` is $(1/2)$-contractive on $B(x_0, \rho)$,
    and the iterates `P.krawczykFast c x₀ n` lie in $B(x_0, \rho)$ and the certified disk:
    1. `P.krawczykFast c x₀ n` converges in $\mathbb{R}$ to a genuine real zero $z_* \in B(x_0, \rho)$,
    2. **Exact Real Zero**: $P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}\;z_* = 0$,
    3. **Certified $O(2^{-n})$ Convergence Rate**:
       $$\big|((P.\operatorname{krawczykFast}\;c\;x_0\;n).\mathrm{val} : \mathbb{R}) - z_*\big|
         \le 2 \cdot \frac{|P.\operatorname{krawczykMap}\;c.\mathrm{val}\;(x_0.\mathrm{val} : \mathbb{R}) - (x_0.\mathrm{val} : \mathbb{R})| + 2 |c.\mathrm{val}| + 1}{(2 : \mathbb{R})^n},$$
    4. **Uniqueness in the Ball $B(x_0, \rho)$**:
       Every $z \in \mathbb{R}$ with $|z - (x_0.\mathrm{val} : \mathbb{R})| \le \rho$ and
       $P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}\;z = 0$ satisfies $z = z_*$. -/
theorem PolyODEProof.krawczykFast_exists_unique_real_zero (P : PolyODEProof) (c x₀ : Q) (ρ : ℝ)
    (hc : c.val ≠ 0)
    (hcontract : ∀ u v : ℝ, |u - (x₀.val : ℝ)| ≤ ρ → |v - (x₀.val : ℝ)| ≤ ρ →
      |P.krawczykMap c.val u - P.krawczykMap c.val v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hball : ∀ n : Nat, |((P.krawczykFast c x₀ n).val : ℝ) - (x₀.val : ℝ)| ≤ ρ)
    (hdisk : ∀ n : Nat, |(P.krawczykFast c x₀ n).val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1)) :
    ∃ zstar : ℝ,
      Filter.Tendsto (fun n ↦ ((P.krawczykFast c x₀ n).val : ℝ)) Filter.atTop (nhds zstar) ∧
      |zstar - (x₀.val : ℝ)| ≤ ρ ∧
      P.toCertifiedAnalyticRep.realAnalyticValue zstar = 0 ∧
      (∀ n : Nat,
        |((P.krawczykFast c x₀ n).val : ℝ) - zstar| ≤
          2 * (|P.krawczykMap c.val (x₀.val : ℝ) - (x₀.val : ℝ)| + 2 * |(c.val : ℝ)| + 1) / (2 : ℝ) ^ n) ∧
      (∀ z : ℝ, |z - (x₀.val : ℝ)| ≤ ρ →
        P.toCertifiedAnalyticRep.realAnalyticValue z = 0 → z = zstar) := by
  set R₀ : ℝ := |P.krawczykMap c.val (x₀.val : ℝ) - (x₀.val : ℝ)| + 2 * |(c.val : ℝ)|
  set K : ℝ := 2 * (R₀ + 1)
  have hR0_nonneg : 0 ≤ R₀ := by dsimp [R₀]; positivity
  have hK_pos : 0 < K := by dsimp [K]; positivity
  let u : Nat → ℝ := fun n ↦ ((P.krawczykFast c x₀ n).val : ℝ)
  have hdist : ∀ n₁ n₂ : Nat,
      |u n₁ - u n₂| ≤ K * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) := by
    intro n₁ n₂
    have hid : u n₁ - u n₂ =
        (u n₁ - P.krawczykMap c.val (u n₁)) +
        ((P.krawczykMap c.val (u n₂) - u n₂) +
         (P.krawczykMap c.val (u n₁) - P.krawczykMap c.val (u n₂))) := by ring
    have htri1 := abs_add_le (u n₁ - P.krawczykMap c.val (u n₁))
      ((P.krawczykMap c.val (u n₂) - u n₂) +
       (P.krawczykMap c.val (u n₁) - P.krawczykMap c.val (u n₂)))
    have htri2 := abs_add_le (P.krawczykMap c.val (u n₂) - u n₂)
      (P.krawczykMap c.val (u n₁) - P.krawczykMap c.val (u n₂))
    rw [← hid, abs_sub_comm (u n₁) (P.krawczykMap c.val (u n₁))] at htri1
    have hl := hcontract (u n₁) (u n₂) (hball n₁) (hball n₂)
    have hr₁ := P.krawczykFast_residual_le c x₀ ρ hcontract hball hdisk n₁
    have hr₂ := P.krawczykFast_residual_le c x₀ ρ hcontract hball hdisk n₂
    change |P.krawczykMap c.val (u n₁) - u n₁| ≤ R₀ / (2 : ℝ) ^ n₁ at hr₁
    change |P.krawczykMap c.val (u n₂) - u n₂| ≤ R₀ / (2 : ℝ) ^ n₂ at hr₂
    have hle1 : R₀ / (2 : ℝ) ^ n₁ ≤ (R₀ + 1) / (2 : ℝ) ^ n₁ :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hle2 : R₀ / (2 : ℝ) ^ n₂ ≤ (R₀ + 1) / (2 : ℝ) ^ n₂ :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have halg : 2 * ((R₀ + 1) / (2 : ℝ) ^ n₁ + (R₀ + 1) / (2 : ℝ) ^ n₂) =
        K * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) := by dsimp [K]; ring
    linarith
  have hcauchy : CauchySeq u := cauchySeq_of_pow2_dist_bound u K hK_pos hdist
  obtain ⟨zstar, hz_lim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hz_mem : zstar ∈ Set.Icc ((x₀.val : ℝ) - ρ) ((x₀.val : ℝ) + ρ) := by
    refine isClosed_Icc.mem_of_tendsto hz_lim (Filter.Eventually.of_forall fun n ↦ ?_)
    have hb := abs_le.mp (hball n)
    constructor <;> linarith [hb.1, hb.2]
  have hz_ball : |zstar - (x₀.val : ℝ)| ≤ ρ := by
    rw [abs_le]
    constructor <;> linarith [hz_mem.1, hz_mem.2]
  have h_rate : ∀ n : Nat, |u n - zstar| ≤ K / (2 : ℝ) ^ n :=
    dist_limit_le_of_pow2_dist_bound u zstar K (le_of_lt hK_pos) hz_lim hdist
  have hz_fix : P.krawczykMap c.val zstar = zstar := by
    have hle0 : |P.krawczykMap c.val zstar - zstar| ≤ 0 := by
      refine real_le_of_forall_sub_pow2_le |P.krawczykMap c.val zstar - zstar| 0
        (2 * K) (by positivity) (fun n ↦ ?_)
      have hl := hcontract zstar (u n) hz_ball (hball n)
      rw [abs_sub_comm zstar (u n)] at hl
      have hres := P.krawczykFast_residual_le c x₀ ρ hcontract hball hdisk n
      change |P.krawczykMap c.val (u n) - u n| ≤ R₀ / (2 : ℝ) ^ n at hres
      have hres' : |P.krawczykMap c.val (u n) - u n| ≤ (1 / 2 : ℝ) * (K / (2 : ℝ) ^ n) := by
        have h1 : R₀ / (2 : ℝ) ^ n ≤ (R₀ + 1) / (2 : ℝ) ^ n :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        have h2 : (R₀ + 1) / (2 : ℝ) ^ n = (1 / 2 : ℝ) * (K / (2 : ℝ) ^ n) := by
          dsimp [K]; ring
        linarith
      have hrate_n := h_rate n
      have htri : |P.krawczykMap c.val zstar - zstar| ≤
          |P.krawczykMap c.val zstar - P.krawczykMap c.val (u n)| +
          (|P.krawczykMap c.val (u n) - u n| + |u n - zstar|) := by
        have h1 := abs_add_le (P.krawczykMap c.val zstar - P.krawczykMap c.val (u n))
          (P.krawczykMap c.val (u n) - zstar)
        have h2 := abs_add_le (P.krawczykMap c.val (u n) - u n) (u n - zstar)
        have hid1 : (P.krawczykMap c.val zstar - P.krawczykMap c.val (u n)) +
            (P.krawczykMap c.val (u n) - zstar) = P.krawczykMap c.val zstar - zstar := by ring
        have hid2 : (P.krawczykMap c.val (u n) - u n) + (u n - zstar) =
            P.krawczykMap c.val (u n) - zstar := by ring
        rw [hid1] at h1
        rw [hid2] at h2
        linarith
      have h2K : (1 / 2 : ℝ) * (K / (2 : ℝ) ^ n) +
          ((1 / 2 : ℝ) * (K / (2 : ℝ) ^ n) + K / (2 : ℝ) ^ n) =
          2 * K / (2 : ℝ) ^ n := by ring
      linarith
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hle0)
  have hz_zero : P.toCertifiedAnalyticRep.realAnalyticValue zstar = 0 :=
    (P.krawczykMap_fixedPoint_iff_zero c.val hc zstar).mp hz_fix
  have h_unique : ∀ z : ℝ, |z - (x₀.val : ℝ)| ≤ ρ →
      P.toCertifiedAnalyticRep.realAnalyticValue z = 0 → z = zstar := by
    intro z hz_b hz_z
    have hz_f : P.krawczykMap c.val z = z :=
      (P.krawczykMap_fixedPoint_iff_zero c.val hc z).mpr hz_z
    have hcontr := hcontract z zstar hz_b hz_ball
    rw [hz_f, hz_fix] at hcontr
    have hnonneg : 0 ≤ |z - zstar| := abs_nonneg _
    have h0 : |z - zstar| ≤ 0 := by linarith
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
  exact ⟨zstar, hz_lim, hz_ball, hz_zero, h_rate, h_unique⟩

/-! ### $N$-Dimensional Krawczyk Operator on $\mathbb{R}^d = \mathrm{Fin}\;d \to \mathbb{R}$ -/

/-- **$N$-Dimensional Preconditioned Krawczyk Operator (`krawczykOpND`)**:
    For $F : \mathbb{R}^d \to \mathbb{R}^d$ and linear preconditioner $C : \mathbb{R}^d \to \mathbb{R}^d$,
    $$K_{F,C}(x) := x - C(F(x)).$$ -/
def krawczykOpND {d : Nat} (F C : (Fin d → ℝ) → (Fin d → ℝ)) (x : Fin d → ℝ) : Fin d → ℝ :=
  x - C (F x)

/-- **$N$-Dimensional Krawczyk Iteration (`krawczykIterND`)**:
    $$x_0,\qquad x_{n+1} = K_{F,C}(x_n) = x_n - C(F(x_n)).$$ -/
def krawczykIterND {d : Nat} (F C : (Fin d → ℝ) → (Fin d → ℝ)) (x₀ : Fin d → ℝ) :
    Nat → (Fin d → ℝ)
  | 0 => x₀
  | n + 1 => krawczykOpND F C (krawczykIterND F C x₀ n)

/-- When $C$ has trivial kernel (`∀ v, C v = 0 → v = 0`) and $C(0) = 0$, fixed points of
    `krawczykOpND F C` coincide with zeros of $F$ in $\mathbb{R}^d$. -/
theorem krawczykOpND_fixedPoint_iff_zero {d : Nat} (F C : (Fin d → ℝ) → (Fin d → ℝ))
    (hC0 : C 0 = 0) (hC_inj : ∀ v : Fin d → ℝ, C v = 0 → v = 0) (x : Fin d → ℝ) :
    krawczykOpND F C x = x ↔ F x = 0 := by
  unfold krawczykOpND
  constructor
  · intro h
    have hsub : C (F x) = 0 := by
      ext i
      have hi : x i - C (F x) i = x i := congr_fun h i
      change C (F x) i = (0 : ℝ)
      linarith
    exact hC_inj (F x) hsub
  · intro h
    rw [h, hC0, sub_zero]

/-- **Automatic $\ell_\infty$-Box Invariance of $N$-Dimensional Krawczyk Iterates (`krawczykIterND_mem_closedBall`)**:
    If `krawczykOpND F C` is $(1/2)$-contractive on `Metric.closedBall x₀ ρ` and
    `‖C (F x₀)‖ ≤ (1 / 2) * ρ`, then every iterate `krawczykIterND F C x₀ n` remains inside
    `Metric.closedBall x₀ ρ`. -/
theorem krawczykIterND_mem_closedBall {d : Nat} (F C : (Fin d → ℝ) → (Fin d → ℝ))
    (x₀ : Fin d → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hcontract : ∀ u v : Fin d → ℝ,
      u ∈ Metric.closedBall x₀ ρ → v ∈ Metric.closedBall x₀ ρ →
      ‖krawczykOpND F C u - krawczykOpND F C v‖ ≤ (1 / 2 : ℝ) * ‖u - v‖)
    (hcenter : ‖C (F x₀)‖ ≤ (1 / 2 : ℝ) * ρ) :
    ∀ n : Nat, krawczykIterND F C x₀ n ∈ Metric.closedBall x₀ ρ
  | 0 => Metric.mem_closedBall_self hρ
  | n + 1 => by
    have ih := krawczykIterND_mem_closedBall F C x₀ ρ hρ hcontract hcenter n
    have hx0 : x₀ ∈ Metric.closedBall x₀ ρ := Metric.mem_closedBall_self hρ
    rw [Metric.mem_closedBall, dist_eq_norm] at ih ⊢
    change ‖krawczykOpND F C (krawczykIterND F C x₀ n) - x₀‖ ≤ ρ
    have hc := hcontract (krawczykIterND F C x₀ n) x₀ (by rwa [Metric.mem_closedBall, dist_eq_norm]) hx0
    have hid : krawczykOpND F C (krawczykIterND F C x₀ n) - x₀ =
        (krawczykOpND F C (krawczykIterND F C x₀ n) - krawczykOpND F C x₀) - C (F x₀) := by
      unfold krawczykOpND; abel
    rw [hid]
    have htri := norm_sub_le (krawczykOpND F C (krawczykIterND F C x₀ n) - krawczykOpND F C x₀) (C (F x₀))
    linarith

/-- **$N$-Dimensional Krawczyk Step Contraction (`krawczykIterND_succ_sub_norm_le`)**:
    Under the Krawczyk box conditions, `‖x_{n+1} - x_n‖ ≤ (1/2) * ρ * (1/2)^n`. -/
theorem krawczykIterND_succ_sub_norm_le {d : Nat} (F C : (Fin d → ℝ) → (Fin d → ℝ))
    (x₀ : Fin d → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hcontract : ∀ u v : Fin d → ℝ,
      u ∈ Metric.closedBall x₀ ρ → v ∈ Metric.closedBall x₀ ρ →
      ‖krawczykOpND F C u - krawczykOpND F C v‖ ≤ (1 / 2 : ℝ) * ‖u - v‖)
    (hcenter : ‖C (F x₀)‖ ≤ (1 / 2 : ℝ) * ρ) :
    ∀ n : Nat,
      ‖krawczykIterND F C x₀ (n + 1) - krawczykIterND F C x₀ n‖ ≤
        ((1 / 2 : ℝ) * ρ) * (1 / 2 : ℝ) ^ n
  | 0 => by
    change ‖(x₀ - C (F x₀)) - x₀‖ ≤ ((1 / 2 : ℝ) * ρ) * 1
    rw [sub_sub_cancel_left, norm_neg, mul_one]
    exact hcenter
  | n + 1 => by
    have ih := krawczykIterND_succ_sub_norm_le F C x₀ ρ hρ hcontract hcenter n
    have hmem1 := krawczykIterND_mem_closedBall F C x₀ ρ hρ hcontract hcenter (n + 1)
    have hmem0 := krawczykIterND_mem_closedBall F C x₀ ρ hρ hcontract hcenter n
    have hc := hcontract (krawczykIterND F C x₀ (n + 1)) (krawczykIterND F C x₀ n) hmem1 hmem0
    have hpow : (1 / 2 : ℝ) * (((1 / 2 : ℝ) * ρ) * (1 / 2 : ℝ) ^ n) =
        ((1 / 2 : ℝ) * ρ) * (1 / 2 : ℝ) ^ (n + 1) := by
      rw [pow_succ (1 / 2 : ℝ) n]; ring
    change ‖krawczykOpND F C (krawczykIterND F C x₀ (n + 1)) -
        krawczykOpND F C (krawczykIterND F C x₀ n)‖ ≤
      ((1 / 2 : ℝ) * ρ) * (1 / 2 : ℝ) ^ (n + 1)
    linarith

/-- **$N$-Dimensional Krawczyk Secant Bound**:
    For any $u, v \in \mathrm{Metric.closedBall}\;x_0\;\rho$:
    $$\|u - v\| \le 2 \cdot \bigl(\|K_{F,C}(u) - u\| + \|K_{F,C}(v) - v\|\bigr).$$ -/
theorem krawczykOpND_secant_bound {d : Nat} (F C : (Fin d → ℝ) → (Fin d → ℝ))
    (x₀ : Fin d → ℝ) (ρ : ℝ)
    (hcontract : ∀ u v : Fin d → ℝ,
      u ∈ Metric.closedBall x₀ ρ → v ∈ Metric.closedBall x₀ ρ →
      ‖krawczykOpND F C u - krawczykOpND F C v‖ ≤ (1 / 2 : ℝ) * ‖u - v‖)
    {u v : Fin d → ℝ}
    (hu : u ∈ Metric.closedBall x₀ ρ) (hv : v ∈ Metric.closedBall x₀ ρ) :
    ‖u - v‖ ≤ 2 * (‖krawczykOpND F C u - u‖ + ‖krawczykOpND F C v - v‖) := by
  have hid : u - v = (u - krawczykOpND F C u) +
      ((krawczykOpND F C v - v) + (krawczykOpND F C u - krawczykOpND F C v)) := by abel
  have htri1 := norm_add_le (u - krawczykOpND F C u)
    ((krawczykOpND F C v - v) + (krawczykOpND F C u - krawczykOpND F C v))
  have htri2 := norm_add_le (krawczykOpND F C v - v)
    (krawczykOpND F C u - krawczykOpND F C v)
  rw [← hid, norm_sub_rev u (krawczykOpND F C u)] at htri1
  have hc := hcontract u v hu hv
  linarith

/-- **$N$-Dimensional Krawczyk Existence, Uniqueness, & Convergence Theorem (`krawczykND_exists_unique_zero`)**:
    For any dimension $d \in \mathbb{N}$, nonlinear system $F : (\mathrm{Fin}\;d \to \mathbb{R}) \to (\mathrm{Fin}\;d \to \mathbb{R})$,
    and injective preconditioner $C$ (`C 0 = 0`, `∀ v, C v = 0 → v = 0`), if `krawczykOpND F C`
    is $(1/2)$-contractive on the $\ell_\infty$ box `Metric.closedBall x₀ ρ` ($\rho \ge 0$) and
    `‖C (F x₀)‖ ≤ (1 / 2) * ρ`, then there exists a **unique** zero $z_* \in \mathrm{Metric.closedBall}\;x_0\;\rho$
    of $F$ in the box:
    1. `Filter.Tendsto (krawczykIterND F C x₀) Filter.atTop (nhds zstar)`,
    2. $z_* \in \mathrm{Metric.closedBall}\;x_0\;\rho$,
    3. **Exact $N$-Dimensional Zero**: $F(z_*) = 0$,
    4. **Geometric Convergence Rate**: $\forall n \in \mathbb{N},\; \|\operatorname{krawczykIterND}\;F\;C\;x_0\;n - z_*\| \le \rho / 2^n$,
    5. **Uniqueness in the Box**: $\forall z \in \mathrm{Metric.closedBall}\;x_0\;\rho,\; F(z) = 0 \implies z = z_*$. -/
theorem krawczykND_exists_unique_zero {d : Nat} (F C : (Fin d → ℝ) → (Fin d → ℝ))
    (x₀ : Fin d → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hC0 : C 0 = 0) (hC_inj : ∀ v : Fin d → ℝ, C v = 0 → v = 0)
    (hcontract : ∀ u v : Fin d → ℝ,
      u ∈ Metric.closedBall x₀ ρ → v ∈ Metric.closedBall x₀ ρ →
      ‖krawczykOpND F C u - krawczykOpND F C v‖ ≤ (1 / 2 : ℝ) * ‖u - v‖)
    (hcenter : ‖C (F x₀)‖ ≤ (1 / 2 : ℝ) * ρ) :
    ∃ zstar : Fin d → ℝ,
      Filter.Tendsto (krawczykIterND F C x₀) Filter.atTop (nhds zstar) ∧
      zstar ∈ Metric.closedBall x₀ ρ ∧
      F zstar = 0 ∧
      (∀ n : Nat, ‖krawczykIterND F C x₀ n - zstar‖ ≤ ρ / (2 : ℝ) ^ n) ∧
      (∀ z ∈ Metric.closedBall x₀ ρ, F z = 0 → z = zstar) := by
  let x := krawczykIterND F C x₀
  have hmem : ∀ n : Nat, x n ∈ Metric.closedBall x₀ ρ :=
    krawczykIterND_mem_closedBall F C x₀ ρ hρ hcontract hcenter
  have hstep : ∀ n : Nat, ‖krawczykOpND F C (x n) - x n‖ ≤ ((1 / 2 : ℝ) * ρ) / (2 : ℝ) ^ n := by
    intro n
    have hs := krawczykIterND_succ_sub_norm_le F C x₀ ρ hρ hcontract hcenter n
    have hpow : ((1 / 2 : ℝ) * ρ) * (1 / 2 : ℝ) ^ n = ((1 / 2 : ℝ) * ρ) / (2 : ℝ) ^ n := by
      rw [one_div_pow]; ring
    rwa [hpow] at hs
  have hdist : ∀ n₁ n₂ : Nat,
      ‖x n₁ - x n₂‖ ≤ ρ * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) := by
    intro n₁ n₂
    have hsec := krawczykOpND_secant_bound F C x₀ ρ hcontract (hmem n₁) (hmem n₂)
    have hs₁ := hstep n₁
    have hs₂ := hstep n₂
    have halg : 2 * (((1 / 2 : ℝ) * ρ) / (2 : ℝ) ^ n₁ + ((1 / 2 : ℝ) * ρ) / (2 : ℝ) ^ n₂) =
        ρ * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) := by ring
    linarith
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * (ρ + 1) / ε)
    refine ⟨N, fun n₁ hn₁ n₂ hn₂ ↦ ?_⟩
    rw [dist_eq_norm]
    have hd := hdist n₁ n₂
    have hpow₁ : 1 / (2 : ℝ) ^ n₁ ≤ 1 / (2 : ℝ) ^ N :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hn₁)
    have hpow₂ : 1 / (2 : ℝ) ^ n₂ ≤ 1 / (2 : ℝ) ^ N :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hn₂)
    have hle : ρ * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) ≤ 2 * (ρ + 1) / (2 : ℝ) ^ N := by
      have h1 : 1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂ ≤ 2 * (1 / (2 : ℝ) ^ N) := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hρ
      have h3 : ρ * (2 * (1 / (2 : ℝ) ^ N)) ≤ 2 * (ρ + 1) / (2 : ℝ) ^ N := by
        have hpos : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ N := by positivity
        have halg : 2 * (ρ + 1) / (2 : ℝ) ^ N - ρ * (2 * (1 / (2 : ℝ) ^ N)) =
            2 * (1 / (2 : ℝ) ^ N) := by ring
        linarith
      linarith
    have hN_pow : (N : ℝ) ≤ (2 : ℝ) ^ N := real_nat_le_two_pow N
    have h2N_gt : 2 * (ρ + 1) / ε < (2 : ℝ) ^ N := lt_of_lt_of_le hN hN_pow
    have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have h1 : 2 * (ρ + 1) < (2 : ℝ) ^ N * ε := (div_lt_iff₀ hε).mp h2N_gt
    have h2 : 2 * (ρ + 1) / (2 : ℝ) ^ N < ε := (div_lt_iff₀ h2N_pos).mpr (by linarith)
    linarith
  obtain ⟨zstar, hz_lim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hz_ball : zstar ∈ Metric.closedBall x₀ ρ :=
    Metric.isClosed_closedBall.mem_of_tendsto hz_lim (Filter.Eventually.of_forall hmem)
  have h_rate : ∀ n : Nat, ‖x n - zstar‖ ≤ ρ / (2 : ℝ) ^ n := by
    intro n
    have hcoord : ∀ i : Fin d, |x n i - zstar i| ≤ ρ / (2 : ℝ) ^ n := by
      intro i
      have hlim_i : Filter.Tendsto (fun m ↦ x m i) Filter.atTop (nhds (zstar i)) :=
        (continuous_apply i).tendsto zstar |>.comp hz_lim
      have hdist_i : ∀ n₁ n₂ : Nat,
          |x n₁ i - x n₂ i| ≤ ρ * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) := by
        intro n₁ n₂
        exact le_trans (norm_le_pi_norm (x n₁ - x n₂) i) (hdist n₁ n₂)
      exact dist_limit_le_of_pow2_dist_bound (fun m ↦ x m i) (zstar i) ρ hρ hlim_i hdist_i n
    exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr hcoord
  have hz_fix : krawczykOpND F C zstar = zstar := by
    have hle0 : ‖krawczykOpND F C zstar - zstar‖ ≤ 0 := by
      refine real_le_of_forall_sub_pow2_le ‖krawczykOpND F C zstar - zstar‖ 0
        (2 * ρ + 1) (by positivity) (fun n ↦ ?_)
      have hc := hcontract zstar (x n) hz_ball (hmem n)
      rw [norm_sub_rev zstar (x n)] at hc
      have hs := hstep n
      have hr := h_rate n
      have htri1 := norm_add_le (krawczykOpND F C zstar - krawczykOpND F C (x n))
        (krawczykOpND F C (x n) - zstar)
      have htri2 := norm_add_le (krawczykOpND F C (x n) - x n) (x n - zstar)
      have hid : (krawczykOpND F C zstar - krawczykOpND F C (x n)) +
          (krawczykOpND F C (x n) - zstar) = krawczykOpND F C zstar - zstar := by abel
      have hid2 : (krawczykOpND F C (x n) - x n) + (x n - zstar) =
          krawczykOpND F C (x n) - zstar := by abel
      rw [hid] at htri1
      rw [hid2] at htri2
      have hpos : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ n := by positivity
      have halg : (1 / 2 : ℝ) * (ρ / (2 : ℝ) ^ n) + ((1 / 2 : ℝ) * ρ) / (2 : ℝ) ^ n +
          ρ / (2 : ℝ) ^ n = 2 * ρ / (2 : ℝ) ^ n := by ring
      have halg2 : (2 * ρ + 1) / (2 : ℝ) ^ n = 2 * ρ / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ n := by ring
      linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hle0)
  have hz_zero : F zstar = 0 :=
    (krawczykOpND_fixedPoint_iff_zero F C hC0 hC_inj zstar).mp hz_fix
  have h_unique : ∀ z ∈ Metric.closedBall x₀ ρ, F z = 0 → z = zstar := by
    intro z hz_b hz_z
    have hz_f : krawczykOpND F C z = z :=
      (krawczykOpND_fixedPoint_iff_zero F C hC0 hC_inj z).mpr hz_z
    have hcontr := hcontract z zstar hz_b hz_ball
    rw [hz_f, hz_fix] at hcontr
    have hnonneg : 0 ≤ ‖z - zstar‖ := norm_nonneg _
    have h0 : ‖z - zstar‖ ≤ 0 := by linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  exact ⟨zstar, hz_lim, hz_ball, hz_zero, h_rate, h_unique⟩

/-! ## Section 3: Classical Mathlib Fourier Integral Orthogonality & True Fourier Series Reconstruction -/

/-- Exact periodicity $\sin(k \cdot 2\pi) = 0$ and $\cos(k \cdot 2\pi) = 1$ for all $k \in \mathbb{N}$. -/
theorem sin_and_cos_nat_mul_two_pi : ∀ k : Nat,
    Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 ∧ Real.cos ((k : ℝ) * (2 * Real.pi)) = 1
  | 0 => by simp
  | k + 1 => by
    obtain ⟨hsin, hcos⟩ := sin_and_cos_nat_mul_two_pi k
    have hexp : ((k + 1 : Nat) : ℝ) * (2 * Real.pi) =
        (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by push_cast; ring
    rw [hexp, Real.sin_add, Real.cos_add, hsin, hcos, Real.sin_two_pi, Real.cos_two_pi]
    constructor <;> ring

/-- Exact periodicity $\sin(k \cdot 2\pi) = 0$ and $\cos(k \cdot 2\pi) = 1$ for all $k \in \mathbb{Z}$. -/
theorem sin_and_cos_int_mul_two_pi (k : Int) :
    Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 ∧ Real.cos ((k : ℝ) * (2 * Real.pi)) = 1 := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · simpa using sin_and_cos_nat_mul_two_pi m
  · obtain ⟨hsin, hcos⟩ := sin_and_cos_nat_mul_two_pi m
    have hexp : ((- (m : Int) : Int) : ℝ) * (2 * Real.pi) = -((m : ℝ) * (2 * Real.pi)) := by
      push_cast; ring
    rw [hexp, Real.sin_neg, Real.cos_neg, hsin, hcos, neg_zero]
    exact ⟨rfl, rfl⟩

/-- Classical Mathlib `HasDerivAt` for $x \mapsto \sin(c x) / c$ ($c \neq 0$). -/
theorem hasDerivAt_sin_mul_div (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.sin (c * t) / c) (Real.cos (c * x)) x := by
  have hlin : HasDerivAt (fun t : ℝ ↦ c * t) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hsin := (Real.hasDerivAt_sin (c * x)).comp x hlin
  have hdiv := hsin.div_const c
  have hcancel : Real.cos (c * x) * c / c = Real.cos (c * x) := mul_div_cancel_right₀ _ hc
  rwa [hcancel] at hdiv

/-- Classical Mathlib `HasDerivAt` for $x \mapsto -\cos(c x) / c$ ($c \neq 0$). -/
theorem hasDerivAt_neg_cos_mul_div (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ -Real.cos (c * t) / c) (Real.sin (c * x)) x := by
  have hlin : HasDerivAt (fun t : ℝ ↦ c * t) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hcos := ((Real.hasDerivAt_cos (c * x)).comp x hlin).neg
  have hdiv := hcos.div_const c
  have hcancel : -(-Real.sin (c * x) * c) / c = Real.sin (c * x) := by
    field_simp
  rwa [hcancel] at hdiv

/-- **Classical Mathlib Integral of $\cos(k x)$ over $0..2\pi$ (`integral_cos_int_mul_two_pi`)**:
    For every non-zero integer $k \in \mathbb{Z}$ ($k \neq 0$),
    $$\int_0^{2\pi} \cos(k x)\,dx = 0.$$ -/
theorem integral_cos_int_mul_two_pi (k : Int) (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * x) = 0 := by
  have hk_real : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hcont : Continuous (fun x : ℝ ↦ Real.cos ((k : ℝ) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hasDerivAt_sin_mul_div (k : ℝ) hk_real x)
    (hcont.intervalIntegrable _ _)]
  have h2pi := (sin_and_cos_int_mul_two_pi k).1
  rw [mul_zero, Real.sin_zero, h2pi, zero_div, sub_self]

/-- **Classical Mathlib Integral of $\sin(k x)$ over $0..2\pi$ (`integral_sin_int_mul_two_pi`)**:
    For every integer $k \in \mathbb{Z}$,
    $$\int_0^{2\pi} \sin(k x)\,dx = 0.$$ -/
theorem integral_sin_int_mul_two_pi (k : Int) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * x) = 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  · have hk_real : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hcont : Continuous (fun x : ℝ ↦ Real.sin ((k : ℝ) * x)) :=
      Real.continuous_sin.comp (continuous_const.mul continuous_id)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ hasDerivAt_neg_cos_mul_div (k : ℝ) hk_real x)
      (hcont.intervalIntegrable _ _)]
    have h2pi := (sin_and_cos_int_mul_two_pi k).2
    rw [mul_zero, Real.cos_zero, h2pi, sub_self]

/-- Product-to-sum identity for $\cos(a)\cos(b)$. -/
theorem cos_mul_cos_eq (a b : ℝ) :
    Real.cos a * Real.cos b = (1 / 2 : ℝ) * (Real.cos (a - b) + Real.cos (a + b)) := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- Product-to-sum identity for $\sin(a)\sin(b)$. -/
theorem sin_mul_sin_eq (a b : ℝ) :
    Real.sin a * Real.sin b = (1 / 2 : ℝ) * (Real.cos (a - b) - Real.cos (a + b)) := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- Product-to-sum identity for $\sin(a)\cos(b)$. -/
theorem sin_mul_cos_eq (a b : ℝ) :
    Real.sin a * Real.cos b = (1 / 2 : ℝ) * (Real.sin (a - b) + Real.sin (a + b)) := by
  rw [Real.sin_sub, Real.sin_add]; ring

/-- **Classical Mathlib Cosine Orthogonality over $0..2\pi$ (`integral_cos_mul_cos_two_pi`)**:
    For all positive frequencies $m + 1, k + 1 \ge 1$:
    $$\frac{1}{\pi} \int_0^{2\pi} \cos((m+1)x)\cos((k+1)x)\,dx = \begin{cases} 1 & m = k \\ 0 & m \neq k. \end{cases}$$ -/
theorem integral_cos_mul_cos_two_pi (m k : Nat) :
    (1 / Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi),
      Real.cos (((m + 1 : Nat) : ℝ) * x) * Real.cos (((k + 1 : Nat) : ℝ) * x)) =
      if m = k then 1 else 0 := by
  set jm : Int := ((m + 1 : Nat) : Int)
  set jk : Int := ((k + 1 : Nat) : Int)
  have hrew : (fun x : ℝ ↦ Real.cos (((m + 1 : Nat) : ℝ) * x) * Real.cos (((k + 1 : Nat) : ℝ) * x)) =
      fun x : ℝ ↦ (1 / 2 : ℝ) * (Real.cos (((jm - jk : Int) : ℝ) * x) +
        Real.cos (((jm + jk : Int) : ℝ) * x)) := by
    ext x
    rw [cos_mul_cos_eq]
    congr 2
    · congr 1; dsimp [jm, jk]; push_cast; ring
    · congr 1; dsimp [jm, jk]; push_cast; ring
  have hcont1 : Continuous (fun x : ℝ ↦ Real.cos (((jm - jk : Int) : ℝ) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcont2 : Continuous (fun x : ℝ ↦ Real.cos (((jm + jk : Int) : ℝ) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  rw [hrew, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)]
  have hsum_ne : jm + jk ≠ 0 := by dsimp [jm, jk]; omega
  rw [integral_cos_int_mul_two_pi (jm + jk) hsum_ne, add_zero]
  by_cases hmk : m = k
  · subst hmk
    rw [if_pos rfl]
    have hdiff_zero : jm - jk = 0 := sub_self jm
    rw [hdiff_zero]
    simp [Real.pi_ne_zero]
  · rw [if_neg hmk]
    have hdiff_ne : jm - jk ≠ 0 := by dsimp [jm, jk]; omega
    rw [integral_cos_int_mul_two_pi (jm - jk) hdiff_ne]
    ring

/-- **Classical Mathlib Sine Orthogonality over $0..2\pi$ (`integral_sin_mul_sin_two_pi`)**:
    For all positive frequencies $m + 1, k + 1 \ge 1$:
    $$\frac{1}{\pi} \int_0^{2\pi} \sin((m+1)x)\sin((k+1)x)\,dx = \begin{cases} 1 & m = k \\ 0 & m \neq k. \end{cases}$$ -/
theorem integral_sin_mul_sin_two_pi (m k : Nat) :
    (1 / Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi),
      Real.sin (((m + 1 : Nat) : ℝ) * x) * Real.sin (((k + 1 : Nat) : ℝ) * x)) =
      if m = k then 1 else 0 := by
  set jm : Int := ((m + 1 : Nat) : Int)
  set jk : Int := ((k + 1 : Nat) : Int)
  have hrew : (fun x : ℝ ↦ Real.sin (((m + 1 : Nat) : ℝ) * x) * Real.sin (((k + 1 : Nat) : ℝ) * x)) =
      fun x : ℝ ↦ (1 / 2 : ℝ) * (Real.cos (((jm - jk : Int) : ℝ) * x) -
        Real.cos (((jm + jk : Int) : ℝ) * x)) := by
    ext x
    rw [sin_mul_sin_eq]
    congr 2
    · congr 1; dsimp [jm, jk]; push_cast; ring
    · congr 1; dsimp [jm, jk]; push_cast; ring
  have hcont1 : Continuous (fun x : ℝ ↦ Real.cos (((jm - jk : Int) : ℝ) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcont2 : Continuous (fun x : ℝ ↦ Real.cos (((jm + jk : Int) : ℝ) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  rw [hrew, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)]
  have hsum_ne : jm + jk ≠ 0 := by dsimp [jm, jk]; omega
  rw [integral_cos_int_mul_two_pi (jm + jk) hsum_ne, sub_zero]
  by_cases hmk : m = k
  · subst hmk
    rw [if_pos rfl]
    have hdiff_zero : jm - jk = 0 := sub_self jm
    rw [hdiff_zero]
    simp [Real.pi_ne_zero]
  · rw [if_neg hmk]
    have hdiff_ne : jm - jk ≠ 0 := by dsimp [jm, jk]; omega
    rw [integral_cos_int_mul_two_pi (jm - jk) hdiff_ne]
    ring

/-- **Classical Mathlib Sine–Cosine Orthogonality over $0..2\pi$ (`integral_sin_mul_cos_two_pi`)**:
    For all frequencies $m, k \in \mathbb{Z}$:
    $$\int_0^{2\pi} \sin(m x)\cos(k x)\,dx = 0.$$ -/
theorem integral_sin_mul_cos_two_pi (m k : Int) :
    ∫ x in (0 : ℝ)..(2 * Real.pi),
      Real.sin ((m : ℝ) * x) * Real.cos ((k : ℝ) * x) = 0 := by
  have hrew : (fun x : ℝ ↦ Real.sin ((m : ℝ) * x) * Real.cos ((k : ℝ) * x)) =
      fun x : ℝ ↦ (1 / 2 : ℝ) * (Real.sin (((m - k : Int) : ℝ) * x) +
        Real.sin (((m + k : Int) : ℝ) * x)) := by
    ext x
    rw [sin_mul_cos_eq]
    congr 2
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  have hcont1 : Continuous (fun x : ℝ ↦ Real.sin (((m - k : Int) : ℝ) * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hcont2 : Continuous (fun x : ℝ ↦ Real.sin (((m + k : Int) : ℝ) * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  rw [hrew, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _),
      integral_sin_int_mul_two_pi (m - k), integral_sin_int_mul_two_pi (m + k)]
  ring

/-- Classical Mathlib Fourier integral functionals on $f : \mathbb{R} \to \mathbb{R}$ over $[0, 2\pi]$. -/
noncomputable def realFourierA0 (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi), f x

noncomputable def realFourierA (f : ℝ → ℝ) (m : Nat) : ℝ :=
  (1 / Real.pi) * ∫ x in (0 : ℝ)..(2 * Real.pi), f x * Real.cos (((m + 1 : Nat) : ℝ) * x)

noncomputable def realFourierB (f : ℝ → ℝ) (m : Nat) : ℝ :=
  (1 / Real.pi) * ∫ x in (0 : ℝ)..(2 * Real.pi), f x * Real.sin (((m + 1 : Nat) : ℝ) * x)

namespace StripFourierRep

/-- Real cosine basis at $x \in \mathbb{R}$: $n \mapsto \cos(n x)$. -/
noncomputable def realCosBasis (x : ℝ) (n : Int) : ℝ :=
  Real.cos ((n : ℝ) * x)

/-- Real sine basis at $x \in \mathbb{R}$: $n \mapsto \sin(n x)$. -/
noncomputable def realSinBasis (x : ℝ) (n : Int) : ℝ :=
  Real.sin ((n : ℝ) * x)

theorem abs_realCosBasis_le_one (x : ℝ) (n : Int) : |realCosBasis x n| ≤ 1 :=
  Real.abs_cos_le_one _

theorem abs_realSinBasis_le_one (x : ℝ) (n : Int) : |realSinBasis x n| ≤ 1 :=
  Real.abs_sin_le_one _

/-- **Real Periodic Analytic Wave (`StripFourierRep.realWave`)**:
    Evaluates the infinite two-sided Fourier series of `F` at any real point $x \in \mathbb{R}$. -/
noncomputable def realWave (F : StripFourierRep) (x : ℝ) : ℝ :=
  F.fourierValue (realCosBasis x) (realSinBasis x)

/-- **Degree-$N$ Real Trigonometric Partial Sum (`StripFourierRep.realWaveTrunc`)**:
    Evaluates the truncated Fourier sum of `F` up to frequency shell $N$ at $x \in \mathbb{R}$. -/
noncomputable def realWaveTrunc (F : StripFourierRep) (N : Nat) (x : ℝ) : ℝ :=
  F.evalTrunc (realCosBasis x) (realSinBasis x) N

/-- Real cosine shell amplitude $A_{m+1} = \mathrm{Re}(c_{m+1}) + \mathrm{Re}(c_{-(m+1)})$. -/
def shellCosCoeff (F : StripFourierRep) (m : Nat) : ℝ :=
  ((F.c ((m + 1 : Nat) : Int)).re.val : ℝ) + ((F.c (-((m + 1 : Nat) : Int))).re.val : ℝ)

/-- Real sine shell amplitude $B_{m+1} = \mathrm{Im}(c_{-(m+1)}) - \mathrm{Im}(c_{m+1})$. -/
def shellSinCoeff (F : StripFourierRep) (m : Nat) : ℝ :=
  ((F.c (-((m + 1 : Nat) : Int))).im.val : ℝ) - ((F.c ((m + 1 : Nat) : Int)).im.val : ℝ)

/-- Zero-frequency shell of `F` at `realCosBasis x`, `realSinBasis x` is constant `(F.c 0).re.val`. -/
theorem shellTerm_realBasis_zero (F : StripFourierRep) (x : ℝ) :
    F.shellTerm (realCosBasis x) (realSinBasis x) 0 = ((F.c 0).re.val : ℝ) := by
  unfold shellTerm modeEvalRe realCosBasis realSinBasis
  simp

/-- Positive-frequency shell `m + 1` of `F` at `realCosBasis x`, `realSinBasis x` equals
    `F.shellCosCoeff m * cos((m+1)x) + F.shellSinCoeff m * sin((m+1)x)`. -/
theorem shellTerm_realBasis_succ (F : StripFourierRep) (m : Nat) (x : ℝ) :
    F.shellTerm (realCosBasis x) (realSinBasis x) (m + 1) =
      F.shellCosCoeff m * Real.cos (((m + 1 : Nat) : ℝ) * x) +
      F.shellSinCoeff m * Real.sin (((m + 1 : Nat) : ℝ) * x) := by
  change F.modeEvalRe (realCosBasis x) (realSinBasis x) ((m + 1 : Nat) : Int) +
      F.modeEvalRe (realCosBasis x) (realSinBasis x) (-((m + 1 : Nat) : Int)) = _
  unfold modeEvalRe realCosBasis realSinBasis shellCosCoeff shellSinCoeff
  push_cast
  rw [neg_mul, Real.cos_neg, Real.sin_neg]
  ring

/-- Continuity of each frequency shell $x \mapsto F.\operatorname{shellTerm}(\cos_x, \sin_x, m)$ on $\mathbb{R}$. -/
theorem continuous_shellTerm_realBasis (F : StripFourierRep) :
    ∀ m : Nat, Continuous (fun x : ℝ ↦ F.shellTerm (realCosBasis x) (realSinBasis x) m)
  | 0 => by
    simp only [shellTerm_realBasis_zero]
    exact continuous_const
  | m + 1 => by
    simp only [shellTerm_realBasis_succ]
    refine Continuous.add ?_ ?_
    · exact continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    · exact continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))

/-- Continuity of `F.realWaveTrunc N` on $\mathbb{R}$. -/
theorem continuous_realWaveTrunc (F : StripFourierRep) (N : Nat) :
    Continuous (F.realWaveTrunc N) := by
  unfold realWaveTrunc evalTrunc
  exact continuous_finset_sum _ fun m _ ↦ F.continuous_shellTerm_realBasis m

/-- **Global Continuity of `F.realWave` on $\mathbb{R}$ (`continuous_realWave`)**:
    Because the frequency shells are bounded by the geometric series $2^{F.M+1}(1/2)^m$,
    `F.realWave` is continuous on all of $\mathbb{R}$ by the Weierstrass M-test. -/
theorem continuous_realWave (F : StripFourierRep) :
    Continuous F.realWave := by
  unfold realWave fourierValue
  refine continuous_tsum (fun m ↦ F.continuous_shellTerm_realBasis m)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left ((2 : ℝ) ^ (F.M + 1))) ?_
  intro m x
  exact F.shellTerm_abs_le (realCosBasis x) (realSinBasis x)
    (abs_realCosBasis_le_one x) (abs_realSinBasis_le_one x) m

/-- **Uniform Approximation of `F.realWave` by `F.realWaveTrunc N` on all of $\mathbb{R}$**:
    $$\forall x \in \mathbb{R},\quad \big|F.\operatorname{realWaveTrunc}(N, x) - F.\operatorname{realWave}(x)\big|
      \le \frac{(2 : \mathbb{R})^{F.M + 1}}{(2 : \mathbb{R})^N}.$$ -/
theorem realWaveTrunc_sub_realWave_le (F : StripFourierRep) (N : Nat) (x : ℝ) :
    |F.realWaveTrunc N x - F.realWave x| ≤ (2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N :=
  F.fourierValue_sub_evalTrunc_le (realCosBasis x) (realSinBasis x)
    (abs_realCosBasis_le_one x) (abs_realSinBasis_le_one x) N

/-- Zero-frequency classical Mathlib integral of a single frequency shell `m`. -/
theorem integral_shellTerm_two_pi (F : StripFourierRep) :
    ∀ m : Nat,
      (1 / (2 * Real.pi)) * (∫ x in (0 : ℝ)..(2 * Real.pi),
        F.shellTerm (realCosBasis x) (realSinBasis x) m) =
      if m = 0 then ((F.c 0).re.val : ℝ) else 0
  | 0 => by
    simp only [shellTerm_realBasis_zero, if_true]
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    field_simp
  | m + 1 => by
    simp only [shellTerm_realBasis_succ, Nat.succ_ne_zero, if_false]
    set jm : Int := ((m + 1 : Nat) : Int)
    have hcont1 : Continuous (fun x : ℝ ↦ F.shellCosCoeff m * Real.cos (((m + 1 : Nat) : ℝ) * x)) :=
      continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    have hcont2 : Continuous (fun x : ℝ ↦ F.shellSinCoeff m * Real.sin (((m + 1 : Nat) : ℝ) * x)) :=
      continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    rw [intervalIntegral.integral_add (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hc : ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (((m + 1 : Nat) : ℝ) * x) = 0 := by
      simpa [jm] using integral_cos_int_mul_two_pi jm (by dsimp [jm]; omega)
    have hs : ∫ x in (0 : ℝ)..(2 * Real.pi), Real.sin (((m + 1 : Nat) : ℝ) * x) = 0 := by
      simpa [jm] using integral_sin_int_mul_two_pi jm
    rw [hc, hs]; ring

/-- Cosine classical Mathlib integral of a single frequency shell `j` against $\cos((m+1)x)$. -/
theorem integral_shellTerm_mul_cos_two_pi (F : StripFourierRep) (m : Nat) :
    ∀ j : Nat,
      (1 / Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi),
        F.shellTerm (realCosBasis x) (realSinBasis x) j *
          Real.cos (((m + 1 : Nat) : ℝ) * x)) =
      if j = m + 1 then F.shellCosCoeff m else 0
  | 0 => by
    simp only [shellTerm_realBasis_zero, Nat.zero_ne_add_one, if_false]
    rw [intervalIntegral.integral_const_mul]
    set jm : Int := ((m + 1 : Nat) : Int)
    have hc : ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (((m + 1 : Nat) : ℝ) * x) = 0 := by
      simpa [jm] using integral_cos_int_mul_two_pi jm (by dsimp [jm]; omega)
    rw [hc]; ring
  | k + 1 => by
    have hrew : (fun x : ℝ ↦ F.shellTerm (realCosBasis x) (realSinBasis x) (k + 1) *
        Real.cos (((m + 1 : Nat) : ℝ) * x)) =
      fun x : ℝ ↦ F.shellCosCoeff k *
          (Real.cos (((k + 1 : Nat) : ℝ) * x) * Real.cos (((m + 1 : Nat) : ℝ) * x)) +
        F.shellSinCoeff k *
          (Real.sin (((k + 1 : Nat) : ℝ) * x) * Real.cos (((m + 1 : Nat) : ℝ) * x)) := by
      ext x; rw [shellTerm_realBasis_succ]; ring
    have hcont1 : Continuous (fun x : ℝ ↦ F.shellCosCoeff k *
        (Real.cos (((k + 1 : Nat) : ℝ) * x) * Real.cos (((m + 1 : Nat) : ℝ) * x))) :=
      continuous_const.mul ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    have hcont2 : Continuous (fun x : ℝ ↦ F.shellSinCoeff k *
        (Real.sin (((k + 1 : Nat) : ℝ) * x) * Real.cos (((m + 1 : Nat) : ℝ) * x))) :=
      continuous_const.mul ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    rw [hrew, intervalIntegral.integral_add (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hsc : ∫ x in (0 : ℝ)..(2 * Real.pi),
        Real.sin (((k + 1 : Nat) : ℝ) * x) * Real.cos (((m + 1 : Nat) : ℝ) * x) = 0 := by
      simpa using integral_sin_mul_cos_two_pi (k + 1 : Nat) (m + 1 : Nat)
    rw [hsc, mul_zero, add_zero]
    have hcc := integral_cos_mul_cos_two_pi k m
    have hfactor : (1 / Real.pi) * (F.shellCosCoeff k *
        ∫ x in (0 : ℝ)..(2 * Real.pi),
          Real.cos (((k + 1 : Nat) : ℝ) * x) * Real.cos (((m + 1 : Nat) : ℝ) * x)) =
      F.shellCosCoeff k * ((1 / Real.pi) *
        ∫ x in (0 : ℝ)..(2 * Real.pi),
          Real.cos (((k + 1 : Nat) : ℝ) * x) * Real.cos (((m + 1 : Nat) : ℝ) * x)) := by ring
    rw [hfactor, hcc]
    by_cases hkm : k = m
    · subst hkm; simp
    · have hsucc : k + 1 ≠ m + 1 := by omega
      rw [if_neg hkm, if_neg hsucc, mul_zero]

/-- Sine classical Mathlib integral of a single frequency shell `j` against $\sin((m+1)x)$. -/
theorem integral_shellTerm_mul_sin_two_pi (F : StripFourierRep) (m : Nat) :
    ∀ j : Nat,
      (1 / Real.pi) * (∫ x in (0 : ℝ)..(2 * Real.pi),
        F.shellTerm (realCosBasis x) (realSinBasis x) j *
          Real.sin (((m + 1 : Nat) : ℝ) * x)) =
      if j = m + 1 then F.shellSinCoeff m else 0
  | 0 => by
    simp only [shellTerm_realBasis_zero, Nat.zero_ne_add_one, if_false]
    rw [intervalIntegral.integral_const_mul]
    set jm : Int := ((m + 1 : Nat) : Int)
    have hs : ∫ x in (0 : ℝ)..(2 * Real.pi), Real.sin (((m + 1 : Nat) : ℝ) * x) = 0 := by
      simpa [jm] using integral_sin_int_mul_two_pi jm
    rw [hs]; ring
  | k + 1 => by
    have hrew : (fun x : ℝ ↦ F.shellTerm (realCosBasis x) (realSinBasis x) (k + 1) *
        Real.sin (((m + 1 : Nat) : ℝ) * x)) =
      fun x : ℝ ↦ F.shellCosCoeff k *
          (Real.sin (((m + 1 : Nat) : ℝ) * x) * Real.cos (((k + 1 : Nat) : ℝ) * x)) +
        F.shellSinCoeff k *
          (Real.sin (((k + 1 : Nat) : ℝ) * x) * Real.sin (((m + 1 : Nat) : ℝ) * x)) := by
      ext x; rw [shellTerm_realBasis_succ]; ring
    have hcont1 : Continuous (fun x : ℝ ↦ F.shellCosCoeff k *
        (Real.sin (((m + 1 : Nat) : ℝ) * x) * Real.cos (((k + 1 : Nat) : ℝ) * x))) :=
      continuous_const.mul ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    have hcont2 : Continuous (fun x : ℝ ↦ F.shellSinCoeff k *
        (Real.sin (((k + 1 : Nat) : ℝ) * x) * Real.sin (((m + 1 : Nat) : ℝ) * x))) :=
      continuous_const.mul ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
    rw [hrew, intervalIntegral.integral_add (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hsc : ∫ x in (0 : ℝ)..(2 * Real.pi),
        Real.sin (((m + 1 : Nat) : ℝ) * x) * Real.cos (((k + 1 : Nat) : ℝ) * x) = 0 := by
      simpa using integral_sin_mul_cos_two_pi (m + 1 : Nat) (k + 1 : Nat)
    rw [hsc, mul_zero, zero_add]
    have hss := integral_sin_mul_sin_two_pi k m
    have hfactor : (1 / Real.pi) * (F.shellSinCoeff k *
        ∫ x in (0 : ℝ)..(2 * Real.pi),
          Real.sin (((k + 1 : Nat) : ℝ) * x) * Real.sin (((m + 1 : Nat) : ℝ) * x)) =
      F.shellSinCoeff k * ((1 / Real.pi) *
        ∫ x in (0 : ℝ)..(2 * Real.pi),
          Real.sin (((k + 1 : Nat) : ℝ) * x) * Real.sin (((m + 1 : Nat) : ℝ) * x)) := by ring
    rw [hfactor, hss]
    by_cases hkm : k = m
    · subst hkm; simp
    · have hsucc : k + 1 ≠ m + 1 := by omega
      rw [if_neg hkm, if_neg hsucc, mul_zero]

/-- On `F.realWaveTrunc N`, the classical Mathlib integral `realFourierA0` equals `(F.c 0).re.val`. -/
theorem realFourierA0_realWaveTrunc (F : StripFourierRep) (N : Nat) :
    realFourierA0 (F.realWaveTrunc N) = ((F.c 0).re.val : ℝ) := by
  unfold realFourierA0 realWaveTrunc evalTrunc
  rw [intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    have hsum : (∑ j ∈ Finset.range (N + 1),
        (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi),
          F.shellTerm (realCosBasis x) (realSinBasis x) j) =
      ∑ j ∈ Finset.range (N + 1), if j = 0 then ((F.c 0).re.val : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun j _ ↦ F.integral_shellTerm_two_pi j
    rw [hsum, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (Nat.zero_lt_succ N))]
  · intro j _
    exact (F.continuous_shellTerm_realBasis j).intervalIntegrable _ _

/-- On `F.realWaveTrunc N` ($N \ge m + 1$), `realFourierA (F.realWaveTrunc N) m = F.shellCosCoeff m`. -/
theorem realFourierA_realWaveTrunc (F : StripFourierRep) (N m : Nat) (hm : m + 1 ≤ N) :
    realFourierA (F.realWaveTrunc N) m = F.shellCosCoeff m := by
  unfold realFourierA realWaveTrunc evalTrunc
  have hrew : (fun x : ℝ ↦ (∑ j ∈ Finset.range (N + 1),
      F.shellTerm (realCosBasis x) (realSinBasis x) j) * Real.cos (((m + 1 : Nat) : ℝ) * x)) =
    fun x : ℝ ↦ ∑ j ∈ Finset.range (N + 1),
      F.shellTerm (realCosBasis x) (realSinBasis x) j * Real.cos (((m + 1 : Nat) : ℝ) * x) := by
    ext x; exact Finset.sum_mul _ _ _
  rw [hrew, intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    have hsum : (∑ j ∈ Finset.range (N + 1),
        (1 / Real.pi) * ∫ x in (0 : ℝ)..(2 * Real.pi),
          F.shellTerm (realCosBasis x) (realSinBasis x) j * Real.cos (((m + 1 : Nat) : ℝ) * x)) =
      ∑ j ∈ Finset.range (N + 1), if j = m + 1 then F.shellCosCoeff m else 0 := by
      refine Finset.sum_congr rfl fun j _ ↦ F.integral_shellTerm_mul_cos_two_pi m j
    rw [hsum, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  · intro j _
    exact ((F.continuous_shellTerm_realBasis j).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- On `F.realWaveTrunc N` ($N \ge m + 1$), `realFourierB (F.realWaveTrunc N) m = F.shellSinCoeff m`. -/
theorem realFourierB_realWaveTrunc (F : StripFourierRep) (N m : Nat) (hm : m + 1 ≤ N) :
    realFourierB (F.realWaveTrunc N) m = F.shellSinCoeff m := by
  unfold realFourierB realWaveTrunc evalTrunc
  have hrew : (fun x : ℝ ↦ (∑ j ∈ Finset.range (N + 1),
      F.shellTerm (realCosBasis x) (realSinBasis x) j) * Real.sin (((m + 1 : Nat) : ℝ) * x)) =
    fun x : ℝ ↦ ∑ j ∈ Finset.range (N + 1),
      F.shellTerm (realCosBasis x) (realSinBasis x) j * Real.sin (((m + 1 : Nat) : ℝ) * x) := by
    ext x; exact Finset.sum_mul _ _ _
  rw [hrew, intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    have hsum : (∑ j ∈ Finset.range (N + 1),
        (1 / Real.pi) * ∫ x in (0 : ℝ)..(2 * Real.pi),
          F.shellTerm (realCosBasis x) (realSinBasis x) j * Real.sin (((m + 1 : Nat) : ℝ) * x)) =
      ∑ j ∈ Finset.range (N + 1), if j = m + 1 then F.shellSinCoeff m else 0 := by
      refine Finset.sum_congr rfl fun j _ ↦ F.integral_shellTerm_mul_sin_two_pi m j
    rw [hsum, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  · intro j _
    exact ((F.continuous_shellTerm_realBasis j).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- Helper: if two continuous functions $f, g : \mathbb{R} \to \mathbb{R}$ satisfy $|f(x) - g(x)| \le \varepsilon$
    on $[0, 2\pi]$ and $|w(x)| \le 1$, then
    $$\left|\int_0^{2\pi} f(x)w(x)\,dx - \int_0^{2\pi} g(x)w(x)\,dx\right| \le 2\pi\varepsilon.$$ -/
theorem intervalIntegral_weighted_diff_le_two_pi (f g w : ℝ → ℝ) (ε : ℝ)
    (hf : Continuous f) (hg : Continuous g) (hw : Continuous w)
    (hdiff : ∀ x : ℝ, |f x - g x| ≤ ε)
    (hw_le : ∀ x : ℝ, |w x| ≤ 1) :
    |(∫ x in (0 : ℝ)..(2 * Real.pi), f x * w x) -
     (∫ x in (0 : ℝ)..(2 * Real.pi), g x * w x)| ≤ 2 * Real.pi * ε := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [← intervalIntegral.integral_sub ((hf.mul hw).intervalIntegrable _ _)
        ((hg.mul hw).intervalIntegrable _ _)]
  have hrew : (fun x : ℝ ↦ f x * w x - g x * w x) = fun x : ℝ ↦ (f x - g x) * w x := by
    ext x; ring
  rw [hrew, ← Real.norm_eq_abs]
  have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) (2 * Real.pi), ‖(f x - g x) * w x‖ ≤ ε := by
    intro x _
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := mul_le_mul (hdiff x) (hw_le x) (abs_nonneg _) (le_trans (abs_nonneg _) (hdiff x))
    linarith
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_of_nonneg hpi] at hle
  linarith

/-- **Classical Mathlib Zero-Mode Fourier Integral of `F.realWave` (`realFourierA0_realWave`)**:
    $$\frac{1}{2\pi} \int_0^{2\pi} F.\operatorname{realWave}(x)\,dx = ((F.c\;0).\mathrm{re}.\mathrm{val} : \mathbb{R}).$$ -/
theorem realFourierA0_realWave (F : StripFourierRep) :
    realFourierA0 F.realWave = ((F.c 0).re.val : ℝ) := by
  have hle0 : |realFourierA0 F.realWave - ((F.c 0).re.val : ℝ)| ≤ 0 := by
    refine real_le_of_forall_sub_pow2_le |realFourierA0 F.realWave - ((F.c 0).re.val : ℝ)| 0
      ((2 : ℝ) ^ (F.M + 1)) (by positivity) (fun N ↦ ?_)
    rw [← F.realFourierA0_realWaveTrunc N]
    unfold realFourierA0
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    have h1 : (fun x : ℝ ↦ F.realWave x * 1) = F.realWave := by ext x; ring
    have h2 : (fun x : ℝ ↦ F.realWaveTrunc N x * 1) = F.realWaveTrunc N := by ext x; ring
    have hdiff := intervalIntegral_weighted_diff_le_two_pi F.realWave (F.realWaveTrunc N) (fun _ ↦ 1)
      ((2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N) F.continuous_realWave (F.continuous_realWaveTrunc N)
      continuous_const (fun x ↦ by rw [abs_sub_comm]; exact F.realWaveTrunc_sub_realWave_le N x)
      (fun _ ↦ by norm_num)
    rw [h1, h2] at hdiff
    have hmul := mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    have hcancel : (1 / (2 * Real.pi)) * (2 * Real.pi * ((2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N)) =
        (2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N := by
      have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
      field_simp
    linarith
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hle0)

/-- **Classical Mathlib Cosine Fourier Integral of `F.realWave` (`realFourierA_realWave`)**:
    For every frequency $m + 1 \ge 1$:
    $$\frac{1}{\pi} \int_0^{2\pi} F.\operatorname{realWave}(x)\cos((m+1)x)\,dx = F.\operatorname{shellCosCoeff}\;m.$$ -/
theorem realFourierA_realWave (F : StripFourierRep) (m : Nat) :
    realFourierA F.realWave m = F.shellCosCoeff m := by
  set C : ℝ := (2 : ℝ) ^ (F.M + 2)
  have hle0 : |realFourierA F.realWave m - F.shellCosCoeff m| ≤ 0 := by
    refine real_le_of_forall_sub_pow2_le |realFourierA F.realWave m - F.shellCosCoeff m| 0
      C (by positivity) (fun N ↦ ?_)
    let N' := N + m + 1
    rw [← F.realFourierA_realWaveTrunc N' m (by omega)]
    unfold realFourierA
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    have hdiff := intervalIntegral_weighted_diff_le_two_pi F.realWave (F.realWaveTrunc N')
      (fun x ↦ Real.cos (((m + 1 : Nat) : ℝ) * x))
      ((2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N') F.continuous_realWave (F.continuous_realWaveTrunc N')
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      (fun x ↦ by rw [abs_sub_comm]; exact F.realWaveTrunc_sub_realWave_le N' x)
      (fun x ↦ Real.abs_cos_le_one _)
    have hmul := mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
    have hcancel : (1 / Real.pi) * (2 * Real.pi * ((2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N')) =
        C / (2 : ℝ) ^ N' := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      dsimp [C]
      rw [pow_succ (2 : ℝ) (F.M + 1)]
      field_simp
    have hle_N : C / (2 : ℝ) ^ N' ≤ C / (2 : ℝ) ^ N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega))
    linarith
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hle0)

/-- **Classical Mathlib Sine Fourier Integral of `F.realWave` (`realFourierB_realWave`)**:
    For every frequency $m + 1 \ge 1$:
    $$\frac{1}{\pi} \int_0^{2\pi} F.\operatorname{realWave}(x)\sin((m+1)x)\,dx = F.\operatorname{shellSinCoeff}\;m.$$ -/
theorem realFourierB_realWave (F : StripFourierRep) (m : Nat) :
    realFourierB F.realWave m = F.shellSinCoeff m := by
  set C : ℝ := (2 : ℝ) ^ (F.M + 2)
  have hle0 : |realFourierB F.realWave m - F.shellSinCoeff m| ≤ 0 := by
    refine real_le_of_forall_sub_pow2_le |realFourierB F.realWave m - F.shellSinCoeff m| 0
      C (by positivity) (fun N ↦ ?_)
    let N' := N + m + 1
    rw [← F.realFourierB_realWaveTrunc N' m (by omega)]
    unfold realFourierB
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    have hdiff := intervalIntegral_weighted_diff_le_two_pi F.realWave (F.realWaveTrunc N')
      (fun x ↦ Real.sin (((m + 1 : Nat) : ℝ) * x))
      ((2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N') F.continuous_realWave (F.continuous_realWaveTrunc N')
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
      (fun x ↦ by rw [abs_sub_comm]; exact F.realWaveTrunc_sub_realWave_le N' x)
      (fun x ↦ Real.abs_sin_le_one _)
    have hmul := mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
    have hcancel : (1 / Real.pi) * (2 * Real.pi * ((2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N')) =
        C / (2 : ℝ) ^ N' := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      dsimp [C]
      rw [pow_succ (2 : ℝ) (F.M + 1)]
      field_simp
    have hle_N : C / (2 : ℝ) ^ N' ≤ C / (2 : ℝ) ^ N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega))
    linarith
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hle0)

/-- The $m$-th Fourier integral shell of any function $f : \mathbb{R} \to \mathbb{R}$,
    defined purely from the classical Mathlib integrals `realFourierA0 f`, `realFourierA f`, `realFourierB f`. -/
noncomputable def realFourierIntegralShell (f : ℝ → ℝ) (x : ℝ) : Nat → ℝ
  | 0 => realFourierA0 f
  | m + 1 =>
    realFourierA f m * Real.cos (((m + 1 : Nat) : ℝ) * x) +
    realFourierB f m * Real.sin (((m + 1 : Nat) : ℝ) * x)

/-- Every frequency shell of `F.realWave` equals the classical Mathlib Fourier integral shell
    `realFourierIntegralShell F.realWave x m`. -/
theorem shellTerm_eq_realFourierIntegralShell (F : StripFourierRep) (x : ℝ) :
    ∀ m : Nat,
      F.shellTerm (realCosBasis x) (realSinBasis x) m =
        realFourierIntegralShell F.realWave x m
  | 0 => by
    rw [shellTerm_realBasis_zero, realFourierIntegralShell, F.realFourierA0_realWave]
  | m + 1 => by
    rw [shellTerm_realBasis_succ, realFourierIntegralShell,
        F.realFourierA_realWave m, F.realFourierB_realWave m]

/-- **True Classical Fourier Integral Reconstruction Theorem (`certified_fourier_reconstruction`)**:
    For every strip-analytic Fourier representation `F : StripFourierRep` and every $x \in \mathbb{R}$:
    1. **Exact Classical Fourier Integral Identity**:
       $$F.\operatorname{realWave}(x) = \sum_{m=0}^{\infty} \operatorname{realFourierIntegralShell}\;F.\operatorname{realWave}\;x\;m$$
       where $\operatorname{realFourierIntegralShell}$ is defined by the classical Mathlib integrals
       $\frac{1}{2\pi}\int_0^{2\pi} F.\operatorname{realWave}(t)\,dt$,
       $\frac{1}{\pi}\int_0^{2\pi} F.\operatorname{realWave}(t)\cos(mt)\,dt$, and
       $\frac{1}{\pi}\int_0^{2\pi} F.\operatorname{realWave}(t)\sin(mt)\,dt$.
    2. **Certified $2^{-k}$ Truncated Fourier Integral Reconstruction**:
       At the linear truncation modulus $N(k) = k + F.M + 1$:
       $$\left|\left(\sum_{m=0}^{k + F.M + 1} \operatorname{realFourierIntegralShell}\;F.\operatorname{realWave}\;x\;m\right)
         - F.\operatorname{realWave}(x)\right| \le \frac{1}{(2 : \mathbb{R})^k}.$$ -/
theorem certified_fourier_reconstruction (F : StripFourierRep) (x : ℝ) (k : Nat) :
    F.realWave x = (∑' m : Nat, realFourierIntegralShell F.realWave x m) ∧
    |(∑ m ∈ Finset.range (k + F.M + 1 + 1), realFourierIntegralShell F.realWave x m) -
      F.realWave x| ≤ 1 / (2 : ℝ) ^ k := by
  have hcongr : (fun m : Nat ↦ F.shellTerm (realCosBasis x) (realSinBasis x) m) =
      fun m : Nat ↦ realFourierIntegralShell F.realWave x m := by
    ext m; exact F.shellTerm_eq_realFourierIntegralShell x m
  constructor
  · change (∑' m : Nat, F.shellTerm (realCosBasis x) (realSinBasis x) m) =
      ∑' m : Nat, realFourierIntegralShell F.realWave x m
    rw [hcongr]
  · have hsum_eq : (∑ m ∈ Finset.range (k + F.M + 1 + 1), realFourierIntegralShell F.realWave x m) =
        F.realWaveTrunc (k + F.M + 1) x := by
      unfold realWaveTrunc evalTrunc
      exact Finset.sum_congr rfl fun m _ ↦ (F.shellTerm_eq_realFourierIntegralShell x m).symm
    rw [hsum_eq]
    exact (F.certified_fourier_series_evaluation (realCosBasis x) (realSinBasis x)
      (abs_realCosBasis_le_one x) (abs_realSinBasis_le_one x) k).2

end StripFourierRep

#print axioms roundDyadic_error_le
#print axioms CertifiedAnalyticRep.evalDyadic_eq_num_div_pow2
#print axioms CertifiedAnalyticRep.evalDyadic_sub_realEvalPoly_le
#print axioms CertifiedAnalyticRep.approxDyadic_spec
#print axioms PolyODEProof.krawczykMap_fixedPoint_iff_zero
#print axioms PolyODEProof.krawczykMap_maps_ball_to_ball
#print axioms PolyODEProof.krawczykMap_contractive_of_deriv_approx
#print axioms PolyODEProof.krawczykFast_exists_unique_real_zero
#print axioms krawczykIterND_mem_closedBall
#print axioms krawczykND_exists_unique_zero
#print axioms integral_cos_mul_cos_two_pi
#print axioms integral_sin_mul_sin_two_pi
#print axioms integral_sin_mul_cos_two_pi
#print axioms StripFourierRep.continuous_realWave
#print axioms StripFourierRep.realFourierA0_realWave
#print axioms StripFourierRep.realFourierA_realWave
#print axioms StripFourierRep.realFourierB_realWave
#print axioms StripFourierRep.certified_fourier_reconstruction

end HAomega
