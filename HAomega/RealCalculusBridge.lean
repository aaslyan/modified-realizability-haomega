/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.CertifiedOptimization

/-!
# The Classical Real-Analysis Semantic Bridge & Certified Fixed-Point Operators

This module completes the semantic bridge between constructive $\mathsf{HA}^\omega$ representations
(`PolyODEProof`, `CertifiedAnalyticRep`) and classical real analysis in Mathlib (`HasDerivAt`,
`HasDerivWithinAt`, `ContinuousOn`, `intervalIntegral`, `CauchySeq`, and real fixed points):

## 1. Real Power-Series Extension (`CertifiedAnalyticRep.realAnalyticValue : ℝ → ℝ`)
- Extends `S.analyticValue : Q → ℝ` from rational arguments to all real numbers $x \in \mathbb{R}$:
  $$\operatorname{S.realAnalyticValue}(x) = \sum_{n=0}^{\infty} (S.\mathrm{coeff}\;n : \mathbb{R})\,x^n.$$
- Proves exact agreement at coerced rationals (`S.realAnalyticValue (x.val : ℝ) = S.analyticValue x`),
  absolute convergence (`summable_realSeriesTerm`), and the uniform truncation bound
  $|S.\operatorname{realEvalPoly}\;N\;x - S.\operatorname{realAnalyticValue}\;x| \le 2^{S.M + 1} / 2^N$
  for all $x \in \mathbb{R}$ with $|x| \le 2^{-(S.R + 1)}$.
- Proves the global real Lipschitz bound and `ContinuousOn` on the closed quarter-radius disk
  $[-2^{-(S.R + 2)}, 2^{-(S.R + 2)}] \subseteq \mathbb{R}$.

## 2. Quadratic Taylor Remainder, Mathlib `HasDerivAt`, and Classical `intervalIntegral`
- Establishes the explicit quadratic first-order Taylor remainder bound on $[-2^{-(S.R + 2)}, 2^{-(S.R + 2)}]$:
  $$\big|S.\operatorname{realAnalyticValue}(y) - S.\operatorname{realAnalyticValue}(x)
    - S'.\operatorname{realAnalyticValue}(x)\cdot (y - x)\big|
    \le 2^{S.M + 2 S.R + 5}\,(y - x)^2.$$
- Deduces Mathlib's `HasDerivWithinAt` on the closed disk $|x| \le 2^{-(S.R + 2)}$ and
  `HasDerivAt` at every interior point $|x| < 2^{-(S.R + 2)}$ (`PolyODEProof.hasDerivAt_realAnalyticValue`).
- Deduces `HasDerivAt` for the antiderivative representation `P.integ` (`PolyODEProof.hasDerivAt_integ_realAnalyticValue`)
  and applies Mathlib's Fundamental Theorem of Calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`)
  to prove that `P.defIntegralFast a b k` approximates the genuine Mathlib `intervalIntegral`
  $\int_{a.\mathrm{val}}^{b.\mathrm{val}} P.\operatorname{realAnalyticValue}(t)\,dt$ within $2^{-k}$
  (`PolyODEProof.defIntegralFast_intervalIntegral_spec`).

## 3. Unconditional Constructive Root Sequence (`PolyODEProof.rootSeq`) & Real Zero Existence
- Proves `PolyODEProof.rootColor_endpoints_ne_of_sign_margin`: a strict sign change with margin
  $2^{-k_0}$ at the endpoints $a, b$ automatically guarantees opposite sign colors
  `P.rootColor a b j p 0 ≠ P.rootColor a b j p (2 ^ j)` for all $j \in \mathbb{N}$ and $p \ge k_0 + 1$.
- Defines the explicit 1-parameter constructive root sequence `P.rootSeq a b k₀ n : Q` and proves:
  1. $|S.\operatorname{analyticValue}(P.\operatorname{rootSeq}\;a\;b\;k_0\;n)| \le 2^{-n}$,
  2. $|(r_{n_1}.\mathrm{val} : \mathbb{R}) - (r_{n_2}.\mathrm{val} : \mathbb{R})| \le (2^{-n_1} + 2^{-n_2}) / m$,
  3. Convergence in $\mathbb{R}$ to a genuine real zero $z_* \in [a.\mathrm{val}, b.\mathrm{val}]$
     satisfying $S.\operatorname{realAnalyticValue}(z_*) = 0$ and $|(r_n.\mathrm{val} : \mathbb{R}) - z_*| \le 2^{-n} / m$.

## 4. Certified Fixed-Point Operators (`PolyODEProof.fixFast` and `PolyODEProof.fixRootSeq`)
- **Contractive Picard/Banach Fixed-Point Operator (`PolyODEProof.fixFast`)**:
  Iterates `GPACSys.approxFast` with precision schedule $2n + 2$:
  $$x_0,\qquad x_{n+1} = \operatorname{GPACSys.approxFast}\;P.\mathrm{sys}\;P.v\;x_n\;(2n + 2).$$
  When $S.\operatorname{realAnalyticValue}$ is $(1/2)$-contractive on $[-r, r]$, proves the explicit
  residual bound $|S.\operatorname{analyticValue}(x_n) - x_n.\mathrm{val}| \le (R_0 + 2) / 2^n$,
  mutual Cauchy bound, and convergence to a genuine real fixed point $S.\operatorname{realAnalyticValue}(z_*) = z_*$.
- **General Non-Contractive Fixed-Point Reduction (`PolyODEProof.fixPointEq`, `PolyODEProof.fixRootSeq`)**:
  Defines `P.fixPointEq := P.sub PolyODEProof.varX`, proves that its zeros are exact fixed points
  $S.\operatorname{realAnalyticValue}(x) = x$, and constructs `P.fixRootSeq` via `rootSeq`.
-/

namespace HAomega

open Rat

/-! ## Section 1: Real Power-Series Extension (`CertifiedAnalyticRep.realAnalyticValue`) -/

/-- The $n$-th real power-series term $(S.\mathrm{coeff}\;n : \mathbb{R}) \cdot x^n$ at a real point $x \in \mathbb{R}$. -/
noncomputable def CertifiedAnalyticRep.realSeriesTerm (S : CertifiedAnalyticRep) (x : ℝ) (n : Nat) : ℝ :=
  (S.coeff n : ℝ) * x ^ n

/-- **Real Analytic Function Extension (`CertifiedAnalyticRep.realAnalyticValue : ℝ → ℝ`)**:
    Evaluates the infinite power series $\sum_{n=0}^{\infty} (S.\mathrm{coeff}\;n : \mathbb{R})\,x^n$
    at any real argument $x \in \mathbb{R}$. -/
noncomputable def CertifiedAnalyticRep.realAnalyticValue (S : CertifiedAnalyticRep) (x : ℝ) : ℝ :=
  ∑' n : Nat, S.realSeriesTerm x n

/-- Degree-$N$ Taylor polynomial $\sum_{n < N} (S.\mathrm{coeff}\;n : \mathbb{R})\,x^n$ evaluated at $x \in \mathbb{R}$. -/
noncomputable def CertifiedAnalyticRep.realEvalPoly (S : CertifiedAnalyticRep) (N : Nat) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, S.realSeriesTerm x n

/-- At any rational point `x : Q`, `realSeriesTerm` agrees definitionally with `seriesTerm`. -/
@[simp]
theorem CertifiedAnalyticRep.realSeriesTerm_coe (S : CertifiedAnalyticRep) (x : Q) (n : Nat) :
    S.realSeriesTerm (x.val : ℝ) n = S.seriesTerm x n := rfl

/-- **Rational–Real Agreement (`CertifiedAnalyticRep.realAnalyticValue_coe`)**:
    At every rational point `x : Q`, `S.realAnalyticValue (x.val : ℝ)` equals `S.analyticValue x`. -/
@[simp]
theorem CertifiedAnalyticRep.realAnalyticValue_coe (S : CertifiedAnalyticRep) (x : Q) :
    S.realAnalyticValue (x.val : ℝ) = S.analyticValue x := rfl

/-- At every rational point `x : Q`, `S.realEvalPoly N (x.val : ℝ)` equals the coerced rational
    polynomial evaluation `((Jet.mk (solFast S.sys S.v)).evalPoly N x).val`. -/
theorem CertifiedAnalyticRep.realEvalPoly_coe (S : CertifiedAnalyticRep) (N : Nat) (x : Q) :
    S.realEvalPoly N (x.val : ℝ) =
      (((Jet.mk (solFast S.sys S.v)).evalPoly N x).val : ℝ) := by
  rw [S.evalPoly_solFast_eq_sum x N, Rat.cast_sum]
  unfold realEvalPoly realSeriesTerm
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp [Rat.cast_mul, Rat.cast_pow]

@[simp]
theorem CertifiedAnalyticRep.realEvalPoly_zero (S : CertifiedAnalyticRep) (x : ℝ) :
    S.realEvalPoly 0 x = 0 := by
  simp [realEvalPoly]

theorem CertifiedAnalyticRep.realEvalPoly_succ (S : CertifiedAnalyticRep) (N : Nat) (x : ℝ) :
    S.realEvalPoly (N + 1) x = S.realEvalPoly N x + (S.coeff N : ℝ) * x ^ N := by
  unfold realEvalPoly realSeriesTerm
  rw [Finset.sum_range_succ]

@[simp]
theorem CertifiedAnalyticRep.realEvalPoly_one (S : CertifiedAnalyticRep) (x : ℝ) :
    S.realEvalPoly 1 x = (S.coeff 0 : ℝ) := by
  rw [S.realEvalPoly_succ 0 x, S.realEvalPoly_zero, zero_add, pow_zero, mul_one]

/-- On the real disk $|x| \le 1 / (2 : \mathbb{R})^{S.R + 1}$, we have $2^{S.R} \cdot |x| \le 1 / 2$. -/
theorem CertifiedAnalyticRep.real_scaled_abs_le_half (S : CertifiedAnalyticRep) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 1)) :
    (2 : ℝ) ^ S.R * |x| ≤ (1 / 2 : ℝ) := by
  have hmul := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ S.R)
  have hpow : (2 : ℝ) ^ S.R * (1 / (2 : ℝ) ^ (S.R + 1)) = (1 / 2 : ℝ) := by
    rw [pow_succ (2 : ℝ) S.R]
    field_simp
  linarith

/-- Termwise geometric bound `‖S.realSeriesTerm x n‖ ≤ 2^M · (1/2)^n` on $|x| \le 2^{-(S.R + 1)}$. -/
theorem CertifiedAnalyticRep.realSeriesTerm_abs_le (S : CertifiedAnalyticRep) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 1)) (n : Nat) :
    ‖S.realSeriesTerm x n‖ ≤ (2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ n := by
  rw [Real.norm_eq_abs]
  unfold realSeriesTerm
  rw [abs_mul, abs_pow]
  have hmaj := S.majorant_real n
  have h1 := mul_le_mul_of_nonneg_right hmaj (by positivity : (0 : ℝ) ≤ |x| ^ n)
  have hcomb : (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ n * |x| ^ n =
      (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R * |x|) ^ n := by
    rw [mul_assoc, ← mul_pow]
  rw [hcomb] at h1
  have hhalf := S.real_scaled_abs_le_half x hx
  have hpow : ((2 : ℝ) ^ S.R * |x|) ^ n ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_left₀ (by positivity) hhalf n
  have h2 := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ S.M)
  linarith

/-- Absolute convergence of `S.realSeriesTerm x` for all $x \in \mathbb{R}$ with $|x| \le 2^{-(S.R + 1)}$. -/
theorem CertifiedAnalyticRep.summable_realSeriesTerm (S : CertifiedAnalyticRep) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 1)) :
    Summable (S.realSeriesTerm x) := by
  have hgeom : Summable (fun n : Nat ↦ (2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left ((2 : ℝ) ^ S.M)
  exact Summable.of_norm_bounded hgeom (S.realSeriesTerm_abs_le x hx)

/-- **Uniform Real Power-Series Tail Remainder Bound (`realAnalyticValue_sub_realEvalPoly_le`)**:
    For every real point $x \in \mathbb{R}$ with $|x| \le 1 / (2 : \mathbb{R})^{S.R + 1}$ and degree $N \in \mathbb{N}$:
    $$\big|S.\operatorname{realEvalPoly}\;N\;x - S.\operatorname{realAnalyticValue}\;x\big|
      \le \frac{(2 : \mathbb{R})^{S.M + 1}}{(2 : \mathbb{R})^N}.$$ -/
theorem CertifiedAnalyticRep.realAnalyticValue_sub_realEvalPoly_le (S : CertifiedAnalyticRep) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 1)) (N : Nat) :
    |S.realEvalPoly N x - S.realAnalyticValue x| ≤ (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N := by
  have hsummable := S.summable_realSeriesTerm x hx
  have hsplit := hsummable.sum_add_tsum_nat_add N
  have hdiff : S.realEvalPoly N x - S.realAnalyticValue x =
      - (∑' k : Nat, S.realSeriesTerm x (k + N)) := by
    unfold realEvalPoly realAnalyticValue
    linarith
  rw [hdiff, abs_neg, ← Real.norm_eq_abs]
  have hshift_summable : Summable (fun k : Nat ↦ S.realSeriesTerm x (k + N)) :=
    hsummable.comp_injective (add_left_injective N)
  have hgeom_shift : Summable (fun k : Nat ↦ ((2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hterm_le : ∀ k : Nat,
      ‖S.realSeriesTerm x (k + N)‖ ≤ ((2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k := by
    intro k
    have hb := S.realSeriesTerm_abs_le x hx (k + N)
    have hpow : (2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ (k + N) =
        ((2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k := by
      rw [pow_add]
      ring
    linarith
  have htsum_le := norm_tsum_le_tsum_norm hshift_summable.norm
  have hbound := Summable.tsum_le_tsum hterm_le hshift_summable.norm hgeom_shift
  have hgeom_val : (∑' k : Nat, ((2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k) =
      (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    rw [pow_succ (2 : ℝ) S.M, one_div_pow]
    ring
  linarith

/-- Two `CertifiedAnalyticRep`s with identical rational coefficients have the exact
    same real power series `realAnalyticValue` at every real point $x \in \mathbb{R}$. -/
theorem CertifiedAnalyticRep.realAnalyticValue_congr (S₁ S₂ : CertifiedAnalyticRep)
    (h : ∀ n : Nat, S₁.coeff n = S₂.coeff n) (x : ℝ) :
    S₁.realAnalyticValue x = S₂.realAnalyticValue x := by
  unfold realAnalyticValue realSeriesTerm
  congr 1; ext n; rw [h n]

/-- Semantically equivalent `PolyODEProof`s have identical `realAnalyticValue` on all of $\mathbb{R}$. -/
theorem PolyODEProof.SemEq.realAnalyticValue_eq {P₁ P₂ : PolyODEProof}
    (h : P₁.SemEq P₂) (x : ℝ) :
    P₁.toCertifiedAnalyticRep.realAnalyticValue x =
      P₂.toCertifiedAnalyticRep.realAnalyticValue x :=
  CertifiedAnalyticRep.realAnalyticValue_congr _ _ h x

/-! ### Real Polynomial & Power-Series Lipschitz Continuity on $[-2^{-(R+2)}, 2^{-(R+2)}]$ -/

/-- Helper: cast rational bound `|q| ≤ 1 / 2^m` to `ℝ`. -/
theorem rat_abs_le_pow2_to_real {q : Rat} {m : Nat} (h : |q| ≤ 1 / (2 : Rat) ^ m) :
    |(q : ℝ)| ≤ 1 / (2 : ℝ) ^ m := by
  have hcast : ((|q| : Rat) : ℝ) ≤ ((1 / (2 : Rat) ^ m : Rat) : ℝ) := by exact_mod_cast h
  simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hcast

/-- Helper: cast strict rational bound `|q| < 1 / 2^m` to `ℝ`. -/
theorem rat_abs_lt_pow2_to_real {q : Rat} {m : Nat} (h : |q| < 1 / (2 : Rat) ^ m) :
    |(q : ℝ)| < 1 / (2 : ℝ) ^ m := by
  have hcast : ((|q| : Rat) : ℝ) < ((1 / (2 : Rat) ^ m : Rat) : ℝ) := by exact_mod_cast h
  simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hcast

/-- Elementary real dominance `((j + 1 : Nat) : ℝ) ≤ 2 * (2 : ℝ) ^ j`. -/
theorem real_nat_succ_le_two_mul_pow2 : ∀ j : Nat, ((j + 1 : Nat) : ℝ) ≤ 2 * (2 : ℝ) ^ j
  | 0 => by norm_num
  | j + 1 => by
    have ih := real_nat_succ_le_two_mul_pow2 j
    have h1 : (1 : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      linarith
    rw [pow_succ (2 : ℝ) j]
    push_cast at ih ⊢
    linarith

/-- Elementary real quadratic dominance `((j + 1 : Nat) : ℝ) ^ 2 ≤ 4 * (2 : ℝ) ^ j`. -/
theorem real_nat_succ_sq_le_four_mul_pow2 : ∀ j : Nat, ((j + 1 : Nat) : ℝ) ^ 2 ≤ 4 * (2 : ℝ) ^ j
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | j + 3 => by
    have ih := real_nat_succ_sq_le_four_mul_pow2 (j + 2)
    set u : ℝ := ((j + 2 + 1 : Nat) : ℝ)
    have hu_ge : (3 : ℝ) ≤ u := by
      dsimp [u]; push_cast
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hu_succ : ((j + 3 + 1 : Nat) : ℝ) = u + 1 := by
      dsimp [u]; push_cast; ring
    have h_diff : ((j + 3 + 1 : Nat) : ℝ) ^ 2 ≤ 2 * u ^ 2 := by
      rw [hu_succ]
      have hprod : 0 ≤ (u - 3) * u := mul_nonneg (by linarith) (by linarith)
      have hid : 2 * u ^ 2 - (u + 1) ^ 2 = (u - 3) * u + (u - 1) := by ring
      linarith
    have h_pow : 2 * (4 * (2 : ℝ) ^ (j + 2)) = 4 * (2 : ℝ) ^ (j + 3) := by
      rw [pow_succ (2 : ℝ) (j + 2)]
      ring
    linarith

/-- Finite geometric series bound $\sum_{j < N} (1 / 2)^j \le 2$ in $\mathbb{R}$. -/
theorem real_sum_half_pow_le_two : ∀ N : Nat,
    (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) = 2 - 2 * (1 / 2 : ℝ) ^ N
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, real_sum_half_pow_le_two N, pow_succ (1 / 2 : ℝ) N]
    ring

theorem real_sum_half_pow_le (N : Nat) :
    (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) ≤ 2 := by
  rw [real_sum_half_pow_le_two N]
  have : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ N := by positivity
  linarith

/-- Monomial Lipschitz bound $|x^{j+1} - y^{j+1}| \le (j + 1) \cdot r^j \cdot |x - y|$ in $\mathbb{R}$
    for $|x|, |y| \le r$. -/
theorem real_pow_succ_sub_pow_succ_le_disk (x y r : ℝ) (hr : 0 ≤ r) (hx : |x| ≤ r) (hy : |y| ≤ r) :
    ∀ j : Nat, |x ^ (j + 1) - y ^ (j + 1)| ≤ ((j + 1 : Nat) : ℝ) * r ^ j * |x - y|
  | 0 => by simp
  | j + 1 => by
    have ih := real_pow_succ_sub_pow_succ_le_disk x y r hr hx hy j
    have h_id : x ^ (j + 2) - y ^ (j + 2) =
        (x - y) * x ^ (j + 1) + y * (x ^ (j + 1) - y ^ (j + 1)) := by ring
    rw [h_id]
    have h_tri := abs_add_le ((x - y) * x ^ (j + 1)) (y * (x ^ (j + 1) - y ^ (j + 1)))
    rw [abs_mul, abs_mul, abs_pow] at h_tri
    have hx_pow : |x| ^ (j + 1) ≤ r ^ (j + 1) := pow_le_pow_left₀ (abs_nonneg _) hx (j + 1)
    have h1 : |x - y| * |x| ^ (j + 1) ≤ r ^ (j + 1) * |x - y| := by
      have := mul_le_mul_of_nonneg_left hx_pow (abs_nonneg (x - y))
      linarith
    have h2 : |y| * |x ^ (j + 1) - y ^ (j + 1)| ≤
        r * (((j + 1 : Nat) : ℝ) * r ^ j * |x - y|) :=
      mul_le_mul hy ih (abs_nonneg _) (by positivity)
    have h2_eq : r * (((j + 1 : Nat) : ℝ) * r ^ j * |x - y|) =
        ((j + 1 : Nat) : ℝ) * r ^ (j + 1) * |x - y| := by
      rw [pow_succ r j]; ring
    have h_sum : r ^ (j + 1) * |x - y| + ((j + 1 : Nat) : ℝ) * r ^ (j + 1) * |x - y| =
        ((j + 1 + 1 : Nat) : ℝ) * r ^ (j + 1) * |x - y| := by
      push_cast; ring
    linarith

/-- Single-term Lipschitz bound on the quarter-radius disk $r = 1 / (2 : \mathbb{R})^{S.R + 2}$. -/
theorem CertifiedAnalyticRep.realSeriesTerm_sub_le_disk (S : CertifiedAnalyticRep) (x y : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 2))
    (hy : |y| ≤ 1 / (2 : ℝ) ^ (S.R + 2)) (j : Nat) :
    |(S.coeff (j + 1) : ℝ) * (x ^ (j + 1) - y ^ (j + 1))| ≤
      (2 : ℝ) ^ (S.M + S.R + 1) * (1 / 2 : ℝ) ^ j * |x - y| := by
  set r : ℝ := 1 / (2 : ℝ) ^ (S.R + 2)
  have hr : 0 ≤ r := by positivity
  rw [abs_mul]
  have hmaj := S.majorant_real (j + 1)
  have hpow := real_pow_succ_sub_pow_succ_le_disk x y r hr hx hy j
  have hmul := mul_le_mul hmaj hpow (abs_nonneg _) (by positivity)
  have hj_pow := real_nat_succ_le_two_mul_pow2 j
  have hmul2 : (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ (j + 1) * (((j + 1 : Nat) : ℝ) * r ^ j * |x - y|) ≤
      (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ (j + 1) * ((2 * (2 : ℝ) ^ j) * r ^ j * |x - y|) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right hj_pow (by positivity)
  have h_id : (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ (j + 1) * ((2 * (2 : ℝ) ^ j) * r ^ j * |x - y|) =
      (2 : ℝ) ^ (S.M + S.R + 1) * ((2 : ℝ) ^ S.R * 2 * r) ^ j * |x - y| := by
    rw [show S.M + S.R + 1 = (S.M + S.R) + 1 from rfl,
        pow_succ (2 : ℝ) (S.M + S.R), pow_add (2 : ℝ) S.M S.R,
        pow_succ ((2 : ℝ) ^ S.R) j, mul_pow, mul_pow]
    ring
  have hr_half : (2 : ℝ) ^ S.R * 2 * r = 1 / 2 := by
    dsimp [r]
    rw [show S.R + 2 = S.R + 1 + 1 by omega, pow_succ (2 : ℝ) (S.R + 1), pow_succ (2 : ℝ) S.R]
    field_simp
  rw [hr_half] at h_id
  linarith

/-- Uniform Lipschitz bound for `S.realEvalPoly N` on $|x|, |y| \le 1 / (2 : \mathbb{R})^{S.R + 2}$. -/
theorem CertifiedAnalyticRep.realEvalPoly_lipschitz_disk (S : CertifiedAnalyticRep) (x y : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 2))
    (hy : |y| ≤ 1 / (2 : ℝ) ^ (S.R + 2)) :
    ∀ N : Nat,
      |S.realEvalPoly N x - S.realEvalPoly N y| ≤
        (2 : ℝ) ^ (S.M + S.R + 2) * |x - y|
  | 0 => by
    rw [S.realEvalPoly_zero, S.realEvalPoly_zero, sub_self, abs_zero]
    positivity
  | N + 1 => by
    have h_sum_eq : S.realEvalPoly (N + 1) x - S.realEvalPoly (N + 1) y =
        ∑ j ∈ Finset.range N, (S.coeff (j + 1) : ℝ) * (x ^ (j + 1) - y ^ (j + 1)) := by
      induction N with
      | zero =>
        rw [S.realEvalPoly_one, S.realEvalPoly_one, sub_self, Finset.range_zero, Finset.sum_empty]
      | succ m ih =>
        rw [S.realEvalPoly_succ (m + 1) x, S.realEvalPoly_succ (m + 1) y,
            Finset.sum_range_succ, ← ih]
        ring
    rw [h_sum_eq]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h_le : ∑ j ∈ Finset.range N, |(S.coeff (j + 1) : ℝ) * (x ^ (j + 1) - y ^ (j + 1))| ≤
        ∑ j ∈ Finset.range N, ((2 : ℝ) ^ (S.M + S.R + 1) * |x - y|) * (1 / 2 : ℝ) ^ j := by
      refine Finset.sum_le_sum fun j _ ↦ ?_
      have hterm := S.realSeriesTerm_sub_le_disk x y hx hy j
      linarith
    rw [← Finset.mul_sum] at h_le
    have h_geom := mul_le_mul_of_nonneg_left (real_sum_half_pow_le N)
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (S.M + S.R + 1) * |x - y|)
    have h_rhs : ((2 : ℝ) ^ (S.M + S.R + 1) * |x - y|) * 2 =
        (2 : ℝ) ^ (S.M + S.R + 2) * |x - y| := by
      rw [show S.M + S.R + 2 = (S.M + S.R + 1) + 1 by omega, pow_succ (2 : ℝ) (S.M + S.R + 1)]
      ring
    linarith

/-- **Real Power-Series Lipschitz Bound on the Quarter-Radius Disk (`realAnalyticValue_lipschitz_disk`)**:
    For every `S : CertifiedAnalyticRep` and all real points $x, y \in \mathbb{R}$ with
    $|x|, |y| \le 1 / (2 : \mathbb{R})^{S.R + 2}$:
    $$\big|S.\operatorname{realAnalyticValue}\;x - S.\operatorname{realAnalyticValue}\;y\big|
      \le (2 : \mathbb{R})^{S.M + S.R + 2} \cdot |x - y|.$$ -/
theorem CertifiedAnalyticRep.realAnalyticValue_lipschitz_disk (S : CertifiedAnalyticRep) (x y : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 2))
    (hy : |y| ≤ 1 / (2 : ℝ) ^ (S.R + 2)) :
    |S.realAnalyticValue x - S.realAnalyticValue y| ≤
      (2 : ℝ) ^ (S.M + S.R + 2) * |x - y| := by
  have hx1 : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 1) :=
    le_trans hx (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hy1 : |y| ≤ 1 / (2 : ℝ) ^ (S.R + 1) :=
    le_trans hy (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  let C : ℝ := 2 * (2 : ℝ) ^ (S.M + 1)
  refine real_le_of_forall_sub_pow2_le _ _ C (by positivity) (fun N ↦ ?_)
  have hlip := S.realEvalPoly_lipschitz_disk x y hx hy N
  have hrem_x := S.realAnalyticValue_sub_realEvalPoly_le x hx1 N
  have hrem_y := S.realAnalyticValue_sub_realEvalPoly_le y hy1 N
  have hrem_x' : |S.realAnalyticValue x - S.realEvalPoly N x| ≤ (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N := by
    rw [abs_sub_comm]; exact hrem_x
  have htri1 : |S.realAnalyticValue x - S.realAnalyticValue y| =
      |(S.realAnalyticValue x - S.realEvalPoly N x) +
       ((S.realEvalPoly N x - S.realEvalPoly N y) +
        (S.realEvalPoly N y - S.realAnalyticValue y))| := by
    congr 1; ring
  have htri2 := abs_add_le (S.realAnalyticValue x - S.realEvalPoly N x)
    ((S.realEvalPoly N x - S.realEvalPoly N y) + (S.realEvalPoly N y - S.realAnalyticValue y))
  have htri3 := abs_add_le (S.realEvalPoly N x - S.realEvalPoly N y)
    (S.realEvalPoly N y - S.realAnalyticValue y)
  have hC : 2 * ((2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N) = C / (2 : ℝ) ^ N := by
    dsimp [C]; ring
  linarith

/-- **Continuity of `S.realAnalyticValue` on the Closed Quarter-Radius Disk (`continuousOn_realAnalyticValue_disk`)**. -/
theorem CertifiedAnalyticRep.continuousOn_realAnalyticValue_disk (S : CertifiedAnalyticRep) :
    ContinuousOn S.realAnalyticValue
      (Set.Icc (-(1 / (2 : ℝ) ^ (S.R + 2))) (1 / (2 : ℝ) ^ (S.R + 2))) := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  set L : ℝ := (2 : ℝ) ^ (S.M + S.R + 2)
  have hL_pos : 0 < L := by positivity
  refine ⟨ε / L, div_pos hε hL_pos, fun y hy hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hx_abs : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 2) := abs_le.mpr hx
  have hy_abs : |y| ≤ 1 / (2 : ℝ) ^ (S.R + 2) := abs_le.mpr hy
  have hlip := S.realAnalyticValue_lipschitz_disk y x hy_abs hx_abs
  have hlt : L * |y - x| < L * (ε / L) := mul_lt_mul_of_pos_left hdist hL_pos
  have hcancel : L * (ε / L) = ε := mul_div_cancel₀ ε (ne_of_gt hL_pos)
  linarith

/-! ## Section 2: Quadratic Taylor Remainder, Mathlib `HasDerivAt`, and Classical `intervalIntegral` -/

/-- Radius-weighted second-order monomial Taylor remainder in $\mathbb{R}$ on $|x|, |x + h| \le r$:
    $$r \cdot \big|(x + h)^{j+1} - x^{j+1} - (j + 1)\,h\,x^j\big|
      \le ((j + 1 : \mathrm{Nat}) : \mathbb{R})^2 \cdot r^j \cdot h^2.$$ -/
theorem real_mul_radius_pow_lin_rem_le_disk (x h r : ℝ) (hr : 0 ≤ r)
    (hx : |x| ≤ r) (hxh : |x + h| ≤ r) :
    ∀ j : Nat,
      r * |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * h * x ^ j| ≤
        ((j + 1 : Nat) : ℝ) ^ 2 * r ^ j * h ^ 2
  | 0 => by
    have h0 : (x + h) ^ 1 - x ^ 1 - ((1 : Nat) : ℝ) * h * x ^ 0 = 0 := by ring
    rw [h0, abs_zero, mul_zero]
    positivity
  | j + 1 => by
    have ih := real_mul_radius_pow_lin_rem_le_disk x h r hr hx hxh j
    have h_id : (x + h) ^ (j + 2) - x ^ (j + 2) - ((j + 2 : Nat) : ℝ) * h * x ^ (j + 1) =
        (x + h) * ((x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * h * x ^ j) +
        ((j + 1 : Nat) : ℝ) * h ^ 2 * x ^ j := by
      push_cast; ring
    rw [h_id]
    have h_tri := abs_add_le
      ((x + h) * ((x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * h * x ^ j))
      (((j + 1 : Nat) : ℝ) * h ^ 2 * x ^ j)
    have h_tri_r := mul_le_mul_of_nonneg_left h_tri hr
    rw [mul_add, abs_mul, abs_mul, abs_mul, abs_pow, sq_abs, abs_pow x j] at h_tri_r
    have hx_pow : |x| ^ j ≤ r ^ j := pow_le_pow_left₀ (abs_nonneg _) hx j
    have h1_swap : r * (|x + h| * |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * h * x ^ j|) =
        |x + h| * (r * |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * h * x ^ j|) := by ring
    have h1_le : |x + h| * (r * |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * h * x ^ j|) ≤
        r * (((j + 1 : Nat) : ℝ) ^ 2 * r ^ j * h ^ 2) :=
      mul_le_mul hxh ih (by positivity) hr
    have h1_eq : r * (((j + 1 : Nat) : ℝ) ^ 2 * r ^ j * h ^ 2) =
        ((j + 1 : Nat) : ℝ) ^ 2 * r ^ (j + 1) * h ^ 2 := by
      rw [pow_succ r j]; ring
    have h2 : r * (|((j + 1 : Nat) : ℝ)| * h ^ 2 * |x| ^ j) ≤
        ((j + 1 : Nat) : ℝ) * r ^ (j + 1) * h ^ 2 := by
      have hj_pos : (0 : ℝ) ≤ ((j + 1 : Nat) : ℝ) := by positivity
      rw [abs_of_nonneg hj_pos]
      have h_nonneg : (0 : ℝ) ≤ r * ((j + 1 : Nat) : ℝ) * h ^ 2 := by positivity
      have h_m := mul_le_mul_of_nonneg_left hx_pow h_nonneg
      have h_lhs : r * ((j + 1 : Nat) : ℝ) * h ^ 2 * |x| ^ j =
          r * (((j + 1 : Nat) : ℝ) * h ^ 2 * |x| ^ j) := by ring
      have h_rhs : r * ((j + 1 : Nat) : ℝ) * h ^ 2 * r ^ j =
          ((j + 1 : Nat) : ℝ) * r ^ (j + 1) * h ^ 2 := by
        rw [pow_succ r j]; ring
      linarith
    have h3 : ((j + 1 : Nat) : ℝ) ^ 2 * r ^ (j + 1) * h ^ 2 +
        ((j + 1 : Nat) : ℝ) * r ^ (j + 1) * h ^ 2 ≤
        ((j + 1 + 1 : Nat) : ℝ) ^ 2 * r ^ (j + 1) * h ^ 2 := by
      have hj_pos : (0 : ℝ) ≤ ((j + 1 : Nat) : ℝ) := by positivity
      have hrj : (0 : ℝ) ≤ r ^ (j + 1) * h ^ 2 := by positivity
      have h_sq : ((j + 1 + 1 : Nat) : ℝ) ^ 2 =
          ((j + 1 : Nat) : ℝ) ^ 2 + 2 * ((j + 1 : Nat) : ℝ) + 1 := by
        push_cast; ring
      rw [h_sq]
      nlinarith
    linarith

/-- Symmetric two-point form of `real_mul_radius_pow_lin_rem_le_disk` for $|x|, |y| \le r$ ($r > 0$). -/
theorem real_pow_lin_rem_le_disk (x y r : ℝ) (hr : 0 < r)
    (hx : |x| ≤ r) (hy : |y| ≤ r) (j : Nat) :
    |y ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * (y - x) * x ^ j| ≤
      (((j + 1 : Nat) : ℝ) ^ 2 * r ^ j / r) * (y - x) ^ 2 := by
  have hxy : |x + (y - x)| ≤ r := by rw [add_sub_cancel]; exact hy
  have hrem := real_mul_radius_pow_lin_rem_le_disk x (y - x) r (le_of_lt hr) hx hxy j
  rw [add_sub_cancel] at hrem
  have hdiv := (le_div_iff₀' hr).mpr hrem
  have hrhs : ((j + 1 : Nat) : ℝ) ^ 2 * r ^ j * (y - x) ^ 2 / r =
      (((j + 1 : Nat) : ℝ) ^ 2 * r ^ j / r) * (y - x) ^ 2 := by ring
  linarith

/-- Single-term quadratic Taylor remainder bound on $r = 1 / (2 : \mathbb{R})^{S.R + 2}$. -/
theorem CertifiedAnalyticRep.realSeriesTerm_quad_rem_le_disk (S : CertifiedAnalyticRep) (x y : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 2))
    (hy : |y| ≤ 1 / (2 : ℝ) ^ (S.R + 2)) (j : Nat) :
    |(S.coeff (j + 1) : ℝ) *
      (y ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * (y - x) * x ^ j)| ≤
      (2 : ℝ) ^ (S.M + 2 * S.R + 4) * (1 / 2 : ℝ) ^ j * (y - x) ^ 2 := by
  set r : ℝ := 1 / (2 : ℝ) ^ (S.R + 2)
  have hr : 0 < r := by positivity
  rw [abs_mul]
  have hmaj := S.majorant_real (j + 1)
  have hrem := real_pow_lin_rem_le_disk x y r hr hx hy j
  have hmul := mul_le_mul hmaj hrem (abs_nonneg _) (by positivity)
  have hj_sq := real_nat_succ_sq_le_four_mul_pow2 j
  have hmul2 :
      (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ (j + 1) *
        ((((j + 1 : Nat) : ℝ) ^ 2 * r ^ j / r) * (y - x) ^ 2) ≤
      (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ (j + 1) *
        (((4 * (2 : ℝ) ^ j * r ^ j / r) * (y - x) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hr)
    exact mul_le_mul_of_nonneg_right hj_sq (by positivity)
  have hr_inv : 1 / r = (2 : ℝ) ^ (S.R + 2) := by
    dsimp [r]; rw [one_div_one_div]
  have hr_half : (2 : ℝ) ^ S.R * 2 * r = 1 / 2 := by
    dsimp [r]
    rw [show S.R + 2 = S.R + 1 + 1 by omega, pow_succ (2 : ℝ) (S.R + 1), pow_succ (2 : ℝ) S.R]
    field_simp
  have h_id :
      (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ (j + 1) *
        (((4 * (2 : ℝ) ^ j * r ^ j / r) * (y - x) ^ 2)) =
      (2 : ℝ) ^ (S.M + 2 * S.R + 4) * ((2 : ℝ) ^ S.R * 2 * r) ^ j * (y - x) ^ 2 := by
    have hdiv_eq : 4 * (2 : ℝ) ^ j * r ^ j / r = 4 * (2 : ℝ) ^ j * r ^ j * (1 / r) := by ring
    rw [hdiv_eq, hr_inv,
        show S.M + 2 * S.R + 4 = S.M + S.R + (S.R + 2) + 2 by omega,
        pow_add (2 : ℝ) (S.M + S.R + (S.R + 2)) 2,
        pow_add (2 : ℝ) (S.M + S.R) (S.R + 2),
        pow_add (2 : ℝ) S.M S.R,
        pow_succ ((2 : ℝ) ^ S.R) j,
        mul_pow, mul_pow]
    norm_num
    ring
  rw [hr_half] at h_id
  linarith

/-- Explicit rational coefficient relation for `P.derivOp`:
    `P.derivOp.toCertifiedAnalyticRep.coeff n = (n + 1) * P.toCertifiedAnalyticRep.coeff (n + 1)`. -/
theorem PolyODEProof.derivOp_coeff_eq (P : PolyODEProof) (n : Nat) :
    P.derivOp.toCertifiedAnalyticRep.coeff n =
      ((n + 1 : Nat) : Rat) * P.toCertifiedAnalyticRep.coeff (n + 1) := by
  rw [P.derivOp_coeff n]
  change (Q.mul (Q.ofNat (n + 1)) (solN P.sys P.v (n + 1))).val =
    ((n + 1 : Nat) : Rat) * P.toCertifiedAnalyticRep.coeff (n + 1)
  rw [Q.val_mul, Q.val_ofNat]
  rfl

/-- Real cast of `PolyODEProof.derivOp_coeff_eq`. -/
theorem PolyODEProof.derivOp_coeff_real (P : PolyODEProof) (n : Nat) :
    (P.derivOp.toCertifiedAnalyticRep.coeff n : ℝ) =
      ((n + 1 : Nat) : ℝ) * (P.toCertifiedAnalyticRep.coeff (n + 1) : ℝ) := by
  have h := P.derivOp_coeff_eq n
  exact_mod_cast h

/-- On `P`'s quarter-radius disk $|x| \le 1 / (2 : \mathbb{R})^{(sysParams P.sys).2 + 2}$,
    the $n$-th series term of `P.derivOp` is bounded by $2^{M + R + 1} \cdot (1/2)^n$ in terms of
    `P`'s own parameters $(M, R) = \operatorname{sysParams}(P.\mathrm{sys})$. -/
theorem PolyODEProof.derivOp_realSeriesTerm_abs_le_of_orig_disk (P : PolyODEProof) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2)) (n : Nat) :
    ‖P.derivOp.toCertifiedAnalyticRep.realSeriesTerm x n‖ ≤
      (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 1) * (1 / 2 : ℝ) ^ n := by
  let S := P.toCertifiedAnalyticRep
  rw [Real.norm_eq_abs]
  unfold CertifiedAnalyticRep.realSeriesTerm
  rw [P.derivOp_coeff_real n, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : Nat) : ℝ))]
  have hmaj := S.majorant_real (n + 1)
  have hn_pow := real_nat_succ_le_two_mul_pow2 n
  have hmul1 : ((n + 1 : Nat) : ℝ) * |(S.coeff (n + 1) : ℝ)| ≤
      (2 * (2 : ℝ) ^ n) * ((2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ (n + 1)) :=
    mul_le_mul hn_pow hmaj (abs_nonneg _) (by positivity)
  have hmul2 := mul_le_mul_of_nonneg_right hmul1 (by positivity : (0 : ℝ) ≤ |x| ^ n)
  have hx_pow : |x| ^ n ≤ (1 / (2 : ℝ) ^ (S.R + 2)) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) hx n
  have hmul3 := mul_le_mul_of_nonneg_left hx_pow
    (by positivity : (0 : ℝ) ≤ (2 * (2 : ℝ) ^ n) * ((2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ (n + 1)))
  have h_id : (2 * (2 : ℝ) ^ n) * ((2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ (n + 1)) *
        (1 / (2 : ℝ) ^ (S.R + 2)) ^ n =
      (2 : ℝ) ^ (S.M + S.R + 1) * ((2 : ℝ) ^ S.R * 2 * (1 / (2 : ℝ) ^ (S.R + 2))) ^ n := by
    rw [show S.M + S.R + 1 = (S.M + S.R) + 1 from rfl,
        pow_succ (2 : ℝ) (S.M + S.R), pow_add (2 : ℝ) S.M S.R,
        pow_succ ((2 : ℝ) ^ S.R) n, mul_pow, mul_pow]
    ring
  have hr_half : (2 : ℝ) ^ S.R * 2 * (1 / (2 : ℝ) ^ (S.R + 2)) = 1 / 2 := by
    rw [show S.R + 2 = S.R + 1 + 1 by omega, pow_succ (2 : ℝ) (S.R + 1), pow_succ (2 : ℝ) S.R]
    field_simp
  rw [hr_half] at h_id
  change ((n + 1 : Nat) : ℝ) * |(S.coeff (n + 1) : ℝ)| * |x| ^ n ≤
    (2 : ℝ) ^ (S.M + S.R + 1) * (1 / 2 : ℝ) ^ n
  linarith

/-- Summability of `P.derivOp`'s power series on `P`'s quarter-radius disk $|x| \le 2^{-(R + 2)}$. -/
theorem PolyODEProof.summable_derivOp_realSeriesTerm_of_orig_disk (P : PolyODEProof) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2)) :
    Summable (P.derivOp.toCertifiedAnalyticRep.realSeriesTerm x) := by
  have hgeom : Summable (fun n : Nat ↦
      (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 1) * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  exact Summable.of_norm_bounded hgeom (P.derivOp_realSeriesTerm_abs_le_of_orig_disk x hx)

/-- Tail remainder bound for `P.derivOp` on `P`'s quarter-radius disk $|x| \le 2^{-(R + 2)}$. -/
theorem PolyODEProof.derivOp_realAnalyticValue_sub_realEvalPoly_le_of_orig_disk
    (P : PolyODEProof) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2)) (N : Nat) :
    |P.derivOp.toCertifiedAnalyticRep.realEvalPoly N x -
        P.derivOp.toCertifiedAnalyticRep.realAnalyticValue x| ≤
      (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) / (2 : ℝ) ^ N := by
  let S' := P.derivOp.toCertifiedAnalyticRep
  set M' := (sysParams P.sys).1 + (sysParams P.sys).2 + 1
  have hsummable := P.summable_derivOp_realSeriesTerm_of_orig_disk x hx
  have hsplit := hsummable.sum_add_tsum_nat_add N
  have hdiff : S'.realEvalPoly N x - S'.realAnalyticValue x =
      - (∑' k : Nat, S'.realSeriesTerm x (k + N)) := by
    unfold CertifiedAnalyticRep.realEvalPoly CertifiedAnalyticRep.realAnalyticValue
    linarith
  rw [hdiff, abs_neg, ← Real.norm_eq_abs]
  have hshift_summable : Summable (fun k : Nat ↦ S'.realSeriesTerm x (k + N)) :=
    hsummable.comp_injective (add_left_injective N)
  have hgeom_shift : Summable (fun k : Nat ↦ ((2 : ℝ) ^ M' * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hterm_le : ∀ k : Nat,
      ‖S'.realSeriesTerm x (k + N)‖ ≤ ((2 : ℝ) ^ M' * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k := by
    intro k
    have hb := P.derivOp_realSeriesTerm_abs_le_of_orig_disk x hx (k + N)
    have hpow : (2 : ℝ) ^ M' * (1 / 2 : ℝ) ^ (k + N) =
        ((2 : ℝ) ^ M' * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k := by
      rw [pow_add]; ring
    linarith
  have htsum_le := norm_tsum_le_tsum_norm hshift_summable.norm
  have hbound := Summable.tsum_le_tsum hterm_le hshift_summable.norm hgeom_shift
  have hgeom_val : (∑' k : Nat, ((2 : ℝ) ^ M' * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k) =
      (2 : ℝ) ^ (M' + 1) / (2 : ℝ) ^ N := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    rw [pow_succ (2 : ℝ) M', one_div_pow]
    ring
  linarith

/-- Finite-degree quadratic Taylor remainder between `P.toCertifiedAnalyticRep.realEvalPoly (N + 1)`
    and `P.derivOp.toCertifiedAnalyticRep.realEvalPoly N` on $|x|, |y| \le 2^{-(R + 2)}$. -/
theorem PolyODEProof.realEvalPoly_quad_rem_disk (P : PolyODEProof) (x y : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2))
    (hy : |y| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2)) :
    ∀ N : Nat,
      |P.toCertifiedAnalyticRep.realEvalPoly (N + 1) y -
        P.toCertifiedAnalyticRep.realEvalPoly (N + 1) x -
        P.derivOp.toCertifiedAnalyticRep.realEvalPoly N x * (y - x)| ≤
        (2 : ℝ) ^ ((sysParams P.sys).1 + 2 * (sysParams P.sys).2 + 5) * (y - x) ^ 2
  | N => by
    let S := P.toCertifiedAnalyticRep
    let S' := P.derivOp.toCertifiedAnalyticRep
    have h_sum_eq :
        S.realEvalPoly (N + 1) y - S.realEvalPoly (N + 1) x - S'.realEvalPoly N x * (y - x) =
          ∑ j ∈ Finset.range N, (S.coeff (j + 1) : ℝ) *
            (y ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * (y - x) * x ^ j) := by
      induction N with
      | zero =>
        rw [S.realEvalPoly_one, S.realEvalPoly_one, S'.realEvalPoly_zero,
            Finset.range_zero, Finset.sum_empty]
        ring
      | succ m ih =>
        rw [S.realEvalPoly_succ (m + 1) y, S.realEvalPoly_succ (m + 1) x,
            S'.realEvalPoly_succ m x, P.derivOp_coeff_real m, Finset.sum_range_succ, ← ih]
        ring
    rw [h_sum_eq]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    set K : ℝ := (2 : ℝ) ^ ((sysParams P.sys).1 + 2 * (sysParams P.sys).2 + 4) * (y - x) ^ 2
    have h_le : ∑ j ∈ Finset.range N,
        |(S.coeff (j + 1) : ℝ) *
          (y ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : ℝ) * (y - x) * x ^ j)| ≤
        ∑ j ∈ Finset.range N, K * (1 / 2 : ℝ) ^ j := by
      refine Finset.sum_le_sum fun j _ ↦ ?_
      have hterm := S.realSeriesTerm_quad_rem_le_disk x y hx hy j
      have hcomm : (2 : ℝ) ^ (S.M + 2 * S.R + 4) * (1 / 2 : ℝ) ^ j * (y - x) ^ 2 =
          K * (1 / 2 : ℝ) ^ j := by
        dsimp [K, S, PolyODEProof.toCertifiedAnalyticRep]; ring
      linarith
    rw [← Finset.mul_sum] at h_le
    have h_geom := mul_le_mul_of_nonneg_left (real_sum_half_pow_le N) (by positivity : 0 ≤ K)
    have h_rhs : K * 2 =
        (2 : ℝ) ^ ((sysParams P.sys).1 + 2 * (sysParams P.sys).2 + 5) * (y - x) ^ 2 := by
      dsimp [K]
      rw [show (sysParams P.sys).1 + 2 * (sysParams P.sys).2 + 5 =
            ((sysParams P.sys).1 + 2 * (sysParams P.sys).2 + 4) + 1 by omega,
          pow_succ (2 : ℝ) _]
      ring
    linarith

/-- **Infinite-Series Quadratic Taylor Remainder on the Real Disk (`realAnalyticValue_quad_rem_disk`)**:
    For every `P : PolyODEProof` and all real points $x, y \in \mathbb{R}$ in the quarter-radius disk
    $|x|, |y| \le 1 / (2 : \mathbb{R})^{(sysParams P.sys).2 + 2}$:
    $$\big|P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}\;y
      - P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}\;x
      - P.\mathrm{derivOp}.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}\;x \cdot (y - x)\big|
      \le (2 : \mathbb{R})^{(sysParams P.sys).1 + 2 \cdot (sysParams P.sys).2 + 5} \cdot (y - x)^2.$$ -/
theorem PolyODEProof.realAnalyticValue_quad_rem_disk (P : PolyODEProof) (x y : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2))
    (hy : |y| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2)) :
    |P.toCertifiedAnalyticRep.realAnalyticValue y -
      P.toCertifiedAnalyticRep.realAnalyticValue x -
      P.derivOp.toCertifiedAnalyticRep.realAnalyticValue x * (y - x)| ≤
      (2 : ℝ) ^ ((sysParams P.sys).1 + 2 * (sysParams P.sys).2 + 5) * (y - x) ^ 2 := by
  let S := P.toCertifiedAnalyticRep
  let S' := P.derivOp.toCertifiedAnalyticRep
  have hx1 : |x| ≤ 1 / (2 : ℝ) ^ (S.R + 1) :=
    le_trans hx (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)))
  have hy1 : |y| ≤ 1 / (2 : ℝ) ^ (S.R + 1) :=
    le_trans hy (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)))
  have hxy_le_one : |y - x| ≤ 1 := by
    have hr_le : 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) ≤ 1 / 4 := by
      have : (4 : ℝ) ≤ (2 : ℝ) ^ ((sysParams P.sys).2 + 2) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      exact one_div_le_one_div_of_le (by norm_num) this
    have htri : |y - x| ≤ |y| + |x| := by
      simpa [sub_eq_add_neg] using abs_add_le y (-x)
    linarith
  set M := (sysParams P.sys).1
  set R := (sysParams P.sys).2
  let C : ℝ := 2 * (2 : ℝ) ^ (M + 1) + (2 : ℝ) ^ (M + R + 2)
  refine real_le_of_forall_sub_pow2_le _ _ C (by positivity) (fun N ↦ ?_)
  have hquad := P.realEvalPoly_quad_rem_disk x y hx hy N
  have hrem_y : |S.realAnalyticValue y - S.realEvalPoly (N + 1) y| ≤ (2 : ℝ) ^ (M + 1) / (2 : ℝ) ^ N := by
    rw [abs_sub_comm]
    refine le_trans (S.realAnalyticValue_sub_realEvalPoly_le y hy1 (N + 1)) ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.le_succ N))
  have hrem_x : |S.realEvalPoly (N + 1) x - S.realAnalyticValue x| ≤ (2 : ℝ) ^ (M + 1) / (2 : ℝ) ^ N := by
    refine le_trans (S.realAnalyticValue_sub_realEvalPoly_le x hx1 (N + 1)) ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.le_succ N))
  have hrem_d := P.derivOp_realAnalyticValue_sub_realEvalPoly_le_of_orig_disk x hx N
  have hrem_d_mul : |(S'.realEvalPoly N x - S'.realAnalyticValue x) * (y - x)| ≤
      (2 : ℝ) ^ (M + R + 2) / (2 : ℝ) ^ N := by
    rw [abs_mul]
    have h1 := mul_le_mul hrem_d hxy_le_one (abs_nonneg _) (by positivity)
    linarith
  set Ry := S.realAnalyticValue y - S.realEvalPoly (N + 1) y
  set Rx := S.realEvalPoly (N + 1) x - S.realAnalyticValue x
  set Rd := (S'.realEvalPoly N x - S'.realAnalyticValue x) * (y - x)
  set QN := S.realEvalPoly (N + 1) y - S.realEvalPoly (N + 1) x - S'.realEvalPoly N x * (y - x)
  have h_id : S.realAnalyticValue y - S.realAnalyticValue x - S'.realAnalyticValue x * (y - x) =
      QN + (Ry + (Rx + Rd)) := by
    dsimp [QN, Ry, Rx, Rd]; ring
  rw [h_id]
  have htri1 := abs_add_le QN (Ry + (Rx + Rd))
  have htri2 := abs_add_le Ry (Rx + Rd)
  have htri3 := abs_add_le Rx Rd
  have hC : (2 : ℝ) ^ (M + 1) / (2 : ℝ) ^ N + (2 : ℝ) ^ (M + 1) / (2 : ℝ) ^ N +
      (2 : ℝ) ^ (M + R + 2) / (2 : ℝ) ^ N = C / (2 : ℝ) ^ N := by
    dsimp [C]; ring
  linarith

/-- **General Bridge Lemma (`hasDerivWithinAt_of_quad_rem_Icc`)**:
    Any function $f : \mathbb{R} \to \mathbb{R}$ satisfying a quadratic first-order Taylor bound
    $|f(y) - f(x) - f'(x)(y - x)| \le C (y - x)^2$ across $y \in [-r, r]$ has derivative
    `HasDerivWithinAt f (f' x) (Set.Icc (-r) r) x` at $x$. -/
theorem hasDerivWithinAt_of_quad_rem_Icc (f : ℝ → ℝ) (f'x r C x : ℝ)
    (hC : 0 ≤ C)
    (hrem : ∀ y ∈ Set.Icc (-r) r, |f y - f x - f'x * (y - x)| ≤ C * (y - x) ^ 2) :
    HasDerivWithinAt f f'x (Set.Icc (-r) r) x := by
  rw [hasDerivWithinAt_iff_tendsto]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨ε / (C + 1), div_pos hε hC1, fun y hy hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_inv, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_abs, abs_abs, smul_eq_mul, mul_comm (y - x) f'x]
  have hbound : |y - x|⁻¹ * |f y - f x - f'x * (y - x)| ≤ C * |y - x| := by
    by_cases hxy : y = x
    · subst hxy; simp
    · have hpos : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hxy)
      have hq := hrem y hy
      rw [← sq_abs] at hq
      have hmul := mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr (le_of_lt hpos))
      have hrhs : |y - x|⁻¹ * (C * |y - x| ^ 2) = C * |y - x| := by
        rw [sq, ← mul_assoc, ← mul_assoc, mul_comm |y - x|⁻¹ C, mul_assoc C,
            inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
      linarith
  have hle2 : C * |y - x| ≤ (C + 1) * |y - x| := by
    have : 0 ≤ |y - x| := abs_nonneg _
    linarith
  have hlt : (C + 1) * |y - x| < (C + 1) * (ε / (C + 1)) :=
    mul_lt_mul_of_pos_left hdist hC1
  have hcancel : (C + 1) * (ε / (C + 1)) = ε := mul_div_cancel₀ ε (ne_of_gt hC1)
  linarith

/-- **Classical `HasDerivWithinAt` for `PolyODEProof` on the Closed Quarter-Radius Disk**:
    For every $x \in [-2^{-(R+2)}, 2^{-(R+2)}] \subseteq \mathbb{R}$, `P.toCertifiedAnalyticRep.realAnalyticValue`
    has within-interval derivative `P.derivOp.toCertifiedAnalyticRep.realAnalyticValue x`. -/
theorem PolyODEProof.hasDerivWithinAt_realAnalyticValue (P : PolyODEProof) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2)) :
    HasDerivWithinAt P.toCertifiedAnalyticRep.realAnalyticValue
      (P.derivOp.toCertifiedAnalyticRep.realAnalyticValue x)
      (Set.Icc (-(1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2)))
               (1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2))) x := by
  refine hasDerivWithinAt_of_quad_rem_Icc P.toCertifiedAnalyticRep.realAnalyticValue
    (P.derivOp.toCertifiedAnalyticRep.realAnalyticValue x)
    (1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2))
    ((2 : ℝ) ^ ((sysParams P.sys).1 + 2 * (sysParams P.sys).2 + 5)) x (by positivity) ?_
  intro y hy
  exact P.realAnalyticValue_quad_rem_disk x y hx (abs_le.mpr hy)

/-- **Classical `HasDerivAt` for `PolyODEProof` on the Open Quarter-Radius Disk (`hasDerivAt_realAnalyticValue`)**:
    For every real point $x \in \mathbb{R}$ with $|x| < 1 / (2 : \mathbb{R})^{(sysParams P.sys).2 + 2}$,
    `P.toCertifiedAnalyticRep.realAnalyticValue` is differentiable at $x$ in the classical Mathlib sense
    with derivative `P.derivOp.toCertifiedAnalyticRep.realAnalyticValue x`. -/
theorem PolyODEProof.hasDerivAt_realAnalyticValue (P : PolyODEProof) (x : ℝ)
    (hx : |x| < 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2)) :
    HasDerivAt P.toCertifiedAnalyticRep.realAnalyticValue
      (P.derivOp.toCertifiedAnalyticRep.realAnalyticValue x) x := by
  have hx_le : |x| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) := le_of_lt hx
  have hwithin := P.hasDerivWithinAt_realAnalyticValue x hx_le
  have hbounds := abs_lt.mp hx
  exact hwithin.hasDerivAt (Icc_mem_nhds hbounds.1 hbounds.2)

/-- **FTC Part 1 in the Classical Real Analytic Interpretation (`derivOp_integ_realAnalyticValue`)**:
    For all $x \in \mathbb{R}$, `(P.integ.derivOp).toCertifiedAnalyticRep.realAnalyticValue x`
    equals `P.toCertifiedAnalyticRep.realAnalyticValue x`. -/
theorem PolyODEProof.derivOp_integ_realAnalyticValue (P : PolyODEProof) (x : ℝ) :
    (P.integ.derivOp).toCertifiedAnalyticRep.realAnalyticValue x =
      P.toCertifiedAnalyticRep.realAnalyticValue x :=
  CertifiedAnalyticRep.realAnalyticValue_congr _ _ P.derivOp_integ_coeff x

/-- **Classical `HasDerivAt` for the Antiderivative `P.integ` (`hasDerivAt_integ_realAnalyticValue`)**:
    At every real point $x \in \mathbb{R}$ with $|x| < 1 / (2 : \mathbb{R})^{(sysParams P.integ.sys).2 + 2}$,
    the antiderivative series `P.integ.toCertifiedAnalyticRep.realAnalyticValue` has classical
    Mathlib derivative `HasDerivAt` equal to `P.toCertifiedAnalyticRep.realAnalyticValue x`. -/
theorem PolyODEProof.hasDerivAt_integ_realAnalyticValue (P : PolyODEProof) (x : ℝ)
    (hx : |x| < 1 / (2 : ℝ) ^ ((sysParams P.integ.sys).2 + 2)) :
    HasDerivAt P.integ.toCertifiedAnalyticRep.realAnalyticValue
      (P.toCertifiedAnalyticRep.realAnalyticValue x) x := by
  rw [← P.derivOp_integ_realAnalyticValue x]
  exact P.integ.hasDerivAt_realAnalyticValue x hx

/-- Helper: if $|a| < r$ and $|b| < r$, then every $x \in \mathrm{Set.uIcc}\;a\;b$ satisfies $|x| < r$
    and $\mathrm{Set.uIcc}\;a\;b \subseteq \mathrm{Set.Icc}\;(-r)\;r$. -/
theorem uIcc_subset_Icc_and_abs_lt {a b r : ℝ} (ha : |a| < r) (hb : |b| < r) :
    Set.uIcc a b ⊆ Set.Icc (-r) r ∧ ∀ x ∈ Set.uIcc a b, |x| < r := by
  have ha' := abs_lt.mp ha
  have hb' := abs_lt.mp hb
  have h_abs : ∀ x ∈ Set.uIcc a b, |x| < r := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rw [abs_lt]
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> linarith
    · constructor <;> linarith
  refine ⟨fun x hx ↦ ?_, h_abs⟩
  have hlt := h_abs x hx
  exact abs_le.mp (le_of_lt hlt)

/-- **Classical Fundamental Theorem of Calculus Part 1 (`intervalIntegral_realAnalyticValue_eq_integ_sub`)**:
    For any real endpoints $a, b \in \mathbb{R}$ with
    $|a|, |b| < 1 / (2 : \mathbb{R})^{(sysParams P.sys).2 + 2}$ and
    $|a|, |b| < 1 / (2 : \mathbb{R})^{(sysParams P.integ.sys).2 + 2}$,
    Mathlib's `intervalIntegral` of `P.toCertifiedAnalyticRep.realAnalyticValue` over `a..b`
    equals the exact antiderivative difference of `P.integ`:
    $$\int_a^b P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}(t)\,dt
      = P.\mathrm{integ}.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}(b)
        - P.\mathrm{integ}.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}(a).$$ -/
theorem PolyODEProof.intervalIntegral_realAnalyticValue_eq_integ_sub (P : PolyODEProof) (a b : ℝ)
    (ha : |a| < 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2))
    (hb : |b| < 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2))
    (ha_int : |a| < 1 / (2 : ℝ) ^ ((sysParams P.integ.sys).2 + 2))
    (hb_int : |b| < 1 / (2 : ℝ) ^ ((sysParams P.integ.sys).2 + 2)) :
    ∫ t in a..b, P.toCertifiedAnalyticRep.realAnalyticValue t =
      P.integ.toCertifiedAnalyticRep.realAnalyticValue b -
      P.integ.toCertifiedAnalyticRep.realAnalyticValue a := by
  have h_uIcc := uIcc_subset_Icc_and_abs_lt ha hb
  have h_uIcc_int := uIcc_subset_Icc_and_abs_lt ha_int hb_int
  have hcont : ContinuousOn P.toCertifiedAnalyticRep.realAnalyticValue (Set.uIcc a b) :=
    P.toCertifiedAnalyticRep.continuousOn_realAnalyticValue_disk.mono h_uIcc.1
  have hint : IntervalIntegrable P.toCertifiedAnalyticRep.realAnalyticValue MeasureTheory.volume a b :=
    hcont.intervalIntegrable
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx ↦ ?_) hint
  exact P.hasDerivAt_integ_realAnalyticValue x (h_uIcc_int.2 x hx)

/-- **Certified Definite Integral Adequacy for Mathlib's `intervalIntegral` (`defIntegralFast_intervalIntegral_spec`)**:
    For any rational endpoints $a, b : Q$ with
    $|a.\mathrm{val}|, |b.\mathrm{val}| < 1 / (2 : \mathrm{Rat})^{(sysParams P.sys).2 + 2}$ and
    $|a.\mathrm{val}|, |b.\mathrm{val}| < 1 / (2 : \mathrm{Rat})^{(sysParams P.integ.sys).2 + 2}$,
    the fast constructive evaluator `P.defIntegralFast a b k` approximates the genuine
    classical Mathlib definite integral $\int_{a.\mathrm{val}}^{b.\mathrm{val}} f_P(t)\,dt$ within $2^{-k}$:
    $$\left|\big((P.\operatorname{defIntegralFast}\;a\;b\;k).\mathrm{val} : \mathbb{R}\big)
      - \int_{(a.\mathrm{val} : \mathbb{R})}^{(b.\mathrm{val} : \mathbb{R})}
          P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}(t)\,dt\right|
      \le \frac{1}{(2 : \mathbb{R})^k}.$$ -/
theorem PolyODEProof.defIntegralFast_intervalIntegral_spec (P : PolyODEProof) (a b : Q) (k : Nat)
    (ha : |a.val| < 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hb : |b.val| < 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (ha_int : |a.val| < 1 / (2 : Rat) ^ ((sysParams P.integ.sys).2 + 2))
    (hb_int : |b.val| < 1 / (2 : Rat) ^ ((sysParams P.integ.sys).2 + 2)) :
    |((P.defIntegralFast a b k).val : ℝ) -
      ∫ t in (a.val : ℝ)..(b.val : ℝ), P.toCertifiedAnalyticRep.realAnalyticValue t| ≤
      1 / (2 : ℝ) ^ k := by
  have ha_real : |(a.val : ℝ)| < 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) :=
    rat_abs_lt_pow2_to_real ha
  have hb_real : |(b.val : ℝ)| < 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) :=
    rat_abs_lt_pow2_to_real hb
  have ha_int_real : |(a.val : ℝ)| < 1 / (2 : ℝ) ^ ((sysParams P.integ.sys).2 + 2) :=
    rat_abs_lt_pow2_to_real ha_int
  have hb_int_real : |(b.val : ℝ)| < 1 / (2 : ℝ) ^ ((sysParams P.integ.sys).2 + 2) :=
    rat_abs_lt_pow2_to_real hb_int
  rw [P.intervalIntegral_realAnalyticValue_eq_integ_sub (a.val : ℝ) (b.val : ℝ)
        ha_real hb_real ha_int_real hb_int_real,
      P.integ.toCertifiedAnalyticRep.realAnalyticValue_coe b,
      P.integ.toCertifiedAnalyticRep.realAnalyticValue_coe a]
  have ha_disk : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.integ.sys).2 + 1) :=
    le_trans (le_of_lt ha_int)
      (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hb_disk : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.integ.sys).2 + 1) :=
    le_trans (le_of_lt hb_int)
      (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  exact P.defIntegralFast_analyticValue_spec a b k ha_disk hb_disk

/-- **Classical Fundamental Theorem of Calculus Part 2 (`intervalIntegral_derivOp_eq_sub`)**:
    For any real endpoints $a, b \in \mathbb{R}$ with
    $|a|, |b| < 1 / (2 : \mathbb{R})^{(sysParams P.sys).2 + 2}$ and
    $|a|, |b| \le 1 / (2 : \mathbb{R})^{(sysParams P.derivOp.sys).2 + 2}$,
    Mathlib's `intervalIntegral` of `P.derivOp.toCertifiedAnalyticRep.realAnalyticValue`
    over `a..b` equals $f_P(b) - f_P(a)$:
    $$\int_a^b P.\mathrm{derivOp}.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}(t)\,dt
      = P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}(b)
        - P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}(a).$$ -/
theorem PolyODEProof.intervalIntegral_derivOp_eq_sub (P : PolyODEProof) (a b : ℝ)
    (ha : |a| < 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2))
    (hb : |b| < 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2))
    (ha_d : |a| ≤ 1 / (2 : ℝ) ^ ((sysParams P.derivOp.sys).2 + 2))
    (hb_d : |b| ≤ 1 / (2 : ℝ) ^ ((sysParams P.derivOp.sys).2 + 2)) :
    ∫ t in a..b, P.derivOp.toCertifiedAnalyticRep.realAnalyticValue t =
      P.toCertifiedAnalyticRep.realAnalyticValue b -
      P.toCertifiedAnalyticRep.realAnalyticValue a := by
  have h_uIcc := uIcc_subset_Icc_and_abs_lt ha hb
  have h_uIcc_d : Set.uIcc a b ⊆
      Set.Icc (-(1 / (2 : ℝ) ^ ((sysParams P.derivOp.sys).2 + 2)))
              (1 / (2 : ℝ) ^ ((sysParams P.derivOp.sys).2 + 2)) := by
    have ha' := abs_le.mp ha_d
    have hb' := abs_le.mp hb_d
    intro x hx
    rw [Set.mem_uIcc] at hx
    rw [Set.mem_Icc]
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> linarith
    · constructor <;> linarith
  have hcont : ContinuousOn P.derivOp.toCertifiedAnalyticRep.realAnalyticValue (Set.uIcc a b) :=
    P.derivOp.toCertifiedAnalyticRep.continuousOn_realAnalyticValue_disk.mono h_uIcc_d
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx ↦ ?_) hcont.intervalIntegrable
  exact P.hasDerivAt_realAnalyticValue x (h_uIcc.2 x hx)

/-! ## Section 3: Unconditional Constructive Root Sequence (`PolyODEProof.rootSeq`) & Real Zero Existence -/

/-- `GPACSys.approxFast` depends on the evaluation point `x : Q` only through `x.val`. -/
theorem GPACSys.approxFast_val_congr (sys : List (Tm [] JetTy × JExprN)) (v : Nat)
    {x y : Q} (hxy : x.val = y.val) (p : Nat) :
    (GPACSys.approxFast sys v x p).val = (GPACSys.approxFast sys v y p).val := by
  unfold GPACSys.approxFast
  rw [extractedJetCauchyModulusComputed_eq, extractedJetCauchyModulusComputed_eq]
  exact nwt_evalPoly_val_congr ⟨solFast sys v⟩ (p + ((sysParams sys).1 + 3)) hxy

/-- Endpoint `0` of `rootGrid a b j` has `.val = a.val`. -/
theorem rootGrid_zero_val (a b : Q) (j : Nat) :
    (rootGrid a b j 0).val = a.val := by
  rw [rootGrid_val]; simp

/-- Endpoint `2 ^ j` of `rootGrid a b j` has `.val = b.val`. -/
theorem rootGrid_pow2_val (a b : Q) (j : Nat) :
    (rootGrid a b j (2 ^ j)).val = b.val := by
  rw [rootGrid_val]
  have h2 : ((2 : Rat) ^ j) ≠ 0 := by positivity
  push_cast
  rw [mul_div_cancel_left₀ _ h2]
  ring

/-- **Automatic Endpoint Sign-Color Discharge (`rootColor_endpoints_ne_of_sign_margin`)**:
    If $P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(a) \le -2^{-k_0}$ and
    $P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(b) \ge 2^{-k_0}$
    for $a, b$ in the certified disk $|x| \le 2^{-(R+1)}$, then for every grid depth $j \in \mathbb{N}$
    and every evaluation precision $p \ge k_0 + 1$,
    `P.rootColor a b j p 0 = 1` and `P.rootColor a b j p (2 ^ j) = 0`, so
    `P.rootColor a b j p 0 ≠ P.rootColor a b j p (2 ^ j)`. -/
theorem PolyODEProof.rootColor_endpoints_ne_of_sign_margin (P : PolyODEProof)
    (a b : Q) (k₀ j p : Nat)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (hfa : P.toCertifiedAnalyticRep.analyticValue a ≤ -(1 / (2 : ℝ) ^ k₀))
    (hfb : 1 / (2 : ℝ) ^ k₀ ≤ P.toCertifiedAnalyticRep.analyticValue b)
    (hp : k₀ + 1 ≤ p) :
    P.rootColor a b j p 0 ≠ P.rootColor a b j p (2 ^ j) := by
  have hp_pow : 1 / (2 : ℝ) ^ p ≤ 1 / (2 : ℝ) ^ (k₀ + 1) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hp)
  have hk0_lt : 1 / (2 : ℝ) ^ (k₀ + 1) < 1 / (2 : ℝ) ^ k₀ := by
    rw [pow_succ (2 : ℝ) k₀]
    have hpos : (0 : ℝ) < 1 / (2 : ℝ) ^ k₀ := by positivity
    have hhalf : 1 / ((2 : ℝ) ^ k₀ * 2) = (1 / 2) * (1 / (2 : ℝ) ^ k₀) := by ring
    linarith
  have hcert_a := certified_evaluation P a p ha
  have hcert_b := certified_evaluation P b p hb
  have ha_grid : ((GPACSys.approxFast P.sys P.v (rootGrid a b j 0) p).val : ℝ) =
      ((GPACSys.approxFast P.sys P.v a p).val : ℝ) := by
    exact_mod_cast GPACSys.approxFast_val_congr P.sys P.v (rootGrid_zero_val a b j) p
  have hb_grid : ((GPACSys.approxFast P.sys P.v (rootGrid a b j (2 ^ j)) p).val : ℝ) =
      ((GPACSys.approxFast P.sys P.v b p).val : ℝ) := by
    exact_mod_cast GPACSys.approxFast_val_congr P.sys P.v (rootGrid_pow2_val a b j) p
  have hcert_a' := (abs_le.mp hcert_a).2
  have hcert_b' := (abs_le.mp hcert_b).1
  have ha_neg_real : ((GPACSys.approxFast P.sys P.v (rootGrid a b j 0) p).val : ℝ) < 0 := by
    linarith
  have hb_nonneg_real : 0 ≤ ((GPACSys.approxFast P.sys P.v (rootGrid a b j (2 ^ j)) p).val : ℝ) := by
    linarith
  have ha_neg_rat : (GPACSys.approxFast P.sys P.v (rootGrid a b j 0) p).val < (Q.ofNat 0).val := by
    rw [Q.val_ofNat_zero]
    exact_mod_cast ha_neg_real
  have hb_nonneg_rat : (Q.ofNat 0).val ≤ (GPACSys.approxFast P.sys P.v (rootGrid a b j (2 ^ j)) p).val := by
    rw [Q.val_ofNat_zero]
    exact_mod_cast hb_nonneg_real
  have hc0 : P.rootColor a b j p 0 = 1 :=
    (Q.ltN_eq_one_iff _ _).mpr ha_neg_rat
  have hc1 : P.rootColor a b j p (2 ^ j) = 0 :=
    (Q.ltN_eq_zero_iff _ _).mpr hb_nonneg_rat
  rw [hc0, hc1]
  decide

/-- Explicit evaluation precision schedule $p(k_0, n) = \max(k_0 + 1, n + 1)$ for `rootSeq`. -/
def PolyODEProof.rootPrecP (k₀ n : Nat) : Nat :=
  max (k₀ + 1) (n + 1)

/-- Explicit bisection grid depth schedule $j(n) = n + 1 + M + R + 2$ for `rootSeq`. -/
def PolyODEProof.rootGridJ (P : PolyODEProof) (n : Nat) : Nat :=
  n + 1 + (sysParams P.sys).1 + (sysParams P.sys).2 + 2

/-- **Unconditional 1-Parameter Constructive Root Sequence (`PolyODEProof.rootSeq`)**:
    Evaluates `P.rootFast` at grid depth `P.rootGridJ n` and evaluation precision `rootPrecP k₀ n`. -/
def PolyODEProof.rootSeq (P : PolyODEProof) (a b : Q) (k₀ n : Nat) : Q :=
  P.rootFast a b (P.rootGridJ n) (PolyODEProof.rootPrecP k₀ n)

/-- **Certified $2^{-n}$ Residual Bound for `rootSeq` (`PolyODEProof.rootSeq_residual_le`)**:
    Under the endpoint sign margin $k_0$ on $[a, b] \subseteq [-2^{-(R+2)}, 2^{-(R+2)}]$,
    every term $r_n = P.\operatorname{rootSeq}\;a\;b\;k_0\;n$ lies in $[a, b]$ and satisfies:
    $$\big|P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(P.\operatorname{rootSeq}\;a\;b\;k_0\;n)\big|
      \le \frac{1}{(2 : \mathbb{R})^n}.$$ -/
theorem PolyODEProof.rootSeq_residual_le (P : PolyODEProof) (a b : Q) (k₀ n : Nat)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hab : a.val ≤ b.val)
    (hfa : P.toCertifiedAnalyticRep.analyticValue a ≤ -(1 / (2 : ℝ) ^ k₀))
    (hfb : 1 / (2 : ℝ) ^ k₀ ≤ P.toCertifiedAnalyticRep.analyticValue b) :
    a.val ≤ (P.rootSeq a b k₀ n).val ∧
    (P.rootSeq a b k₀ n).val ≤ b.val ∧
    |P.toCertifiedAnalyticRep.analyticValue (P.rootSeq a b k₀ n)| ≤ 1 / (2 : ℝ) ^ n := by
  have ha1 : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1) :=
    le_trans ha (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hb1 : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1) :=
    le_trans hb (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hends := P.rootColor_endpoints_ne_of_sign_margin a b k₀ (P.rootGridJ n)
    (PolyODEProof.rootPrecP k₀ n) ha1 hb1 hfa hfb (le_max_left _ _)
  have hspec := P.rootFast_analyticValue_spec a b (P.rootGridJ n)
    (PolyODEProof.rootPrecP k₀ n) ha hb hab hends
  refine ⟨hspec.1, hspec.2.1, le_trans hspec.2.2 ?_⟩
  have hp_le : 1 / (2 : ℝ) ^ (PolyODEProof.rootPrecP k₀ n) ≤ 1 / (2 : ℝ) ^ (n + 1) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))
  have hba_le_one : (b.val : ℝ) - (a.val : ℝ) ≤ 1 := by
    have ha_r : |(a.val : ℝ)| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) :=
      rat_abs_le_pow2_to_real ha
    have hb_r : |(b.val : ℝ)| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) :=
      rat_abs_le_pow2_to_real hb
    have hr_le : 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) ≤ 1 / 4 := by
      have : (4 : ℝ) ≤ (2 : ℝ) ^ ((sysParams P.sys).2 + 2) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      exact one_div_le_one_div_of_le (by norm_num) this
    have ha_bounds := abs_le.mp ha_r
    have hb_bounds := abs_le.mp hb_r
    linarith
  have hj_le :
      (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) *
        (((b.val : ℝ) - (a.val : ℝ)) / (2 : ℝ) ^ (P.rootGridJ n)) ≤
      1 / (2 : ℝ) ^ (n + 1) := by
    have h1 : ((b.val : ℝ) - (a.val : ℝ)) / (2 : ℝ) ^ (P.rootGridJ n) ≤
        1 / (2 : ℝ) ^ (P.rootGridJ n) :=
      div_le_div_of_nonneg_right hba_le_one (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2))
    have h3 : (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) *
        (1 / (2 : ℝ) ^ (P.rootGridJ n)) = 1 / (2 : ℝ) ^ (n + 1) := by
      unfold PolyODEProof.rootGridJ
      rw [show n + 1 + (sysParams P.sys).1 + (sysParams P.sys).2 + 2 =
            (n + 1) + ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) by omega,
          pow_add (2 : ℝ) (n + 1) _]
      field_simp
    linarith
  have hhalf : 1 / (2 : ℝ) ^ (n + 1) + 1 / (2 : ℝ) ^ (n + 1) = 1 / (2 : ℝ) ^ n := by
    rw [pow_succ (2 : ℝ) n]
    field_simp
    ring
  linarith

/-- **Explicit Cauchy Rate of `rootSeq` (`PolyODEProof.rootSeq_cauchy_of_deriv_margin`)**:
    Under the endpoint sign margin $k_0$ and finite rational derivative margin $m > 0$,
    for all $n_1, n_2 \in \mathbb{N}$:
    $$\big|((P.\operatorname{rootSeq}\;a\;b\;k_0\;n_1).\mathrm{val} : \mathbb{R})
      - ((P.\operatorname{rootSeq}\;a\;b\;k_0\;n_2).\mathrm{val} : \mathbb{R})\big|
      \le \frac{1 / (2 : \mathbb{R})^{n_1} + 1 / (2 : \mathbb{R})^{n_2}}{(m : \mathbb{R})}.$$ -/
theorem PolyODEProof.rootSeq_cauchy_of_deriv_margin (P : PolyODEProof)
    (a b : Q) (k₀ k : Nat) (m : Rat) (hm : 0 < m)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hab : a.val ≤ b.val)
    (hfa : P.toCertifiedAnalyticRep.analyticValue a ≤ -(1 / (2 : ℝ) ^ k₀))
    (hfb : 1 / (2 : ℝ) ^ k₀ ≤ P.toCertifiedAnalyticRep.analyticValue b)
    (hmargin : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val →
      m ≤ ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.toJet.evalPoly
            (k + ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.M + 3)) y).val
          - 1 / (2 : Rat) ^ k)
    (n₁ n₂ : Nat) :
    |((P.rootSeq a b k₀ n₁).val : ℝ) - ((P.rootSeq a b k₀ n₂).val : ℝ)| ≤
      (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) / (m : ℝ) := by
  have hm_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have ha1 : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1) :=
    le_trans ha (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hb1 : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1) :=
    le_trans hb (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hends₁ := P.rootColor_endpoints_ne_of_sign_margin a b k₀ (P.rootGridJ n₁)
    (PolyODEProof.rootPrecP k₀ n₁) ha1 hb1 hfa hfb (le_max_left _ _)
  have hends₂ := P.rootColor_endpoints_ne_of_sign_margin a b k₀ (P.rootGridJ n₂)
    (PolyODEProof.rootPrecP k₀ n₂) ha1 hb1 hfa hfb (le_max_left _ _)
  have hcauchy := P.rootFast_cauchy_of_deriv_margin a b k m hm ha hb hab hmargin
    (P.rootGridJ n₁) (PolyODEProof.rootPrecP k₀ n₁)
    (P.rootGridJ n₂) (PolyODEProof.rootPrecP k₀ n₂) hends₁ hends₂
  have hres₁ := (P.rootSeq_residual_le a b k₀ n₁ ha hb hab hfa hfb).2.2
  have hres₂ := (P.rootSeq_residual_le a b k₀ n₂ ha hb hab hfa hfb).2.2
  unfold PolyODEProof.rootSeq at hres₁ hres₂ ⊢
  refine le_trans hcauchy ?_
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hm_real)

/-- General helper: any real sequence satisfying $|u(n_1) - u(n_2)| \le K \cdot (2^{-n_1} + 2^{-n_2})$
    ($K > 0$) is a `CauchySeq` in $\mathbb{R}$. -/
theorem cauchySeq_of_pow2_dist_bound (u : Nat → ℝ) (K : ℝ) (hK : 0 < K)
    (hdist : ∀ n₁ n₂ : Nat, |u n₁ - u n₂| ≤ K * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂)) :
    CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * K / ε)
  refine ⟨N, fun n₁ hn₁ n₂ hn₂ ↦ ?_⟩
  rw [Real.dist_eq]
  have hd := hdist n₁ n₂
  have hpow₁ : 1 / (2 : ℝ) ^ n₁ ≤ 1 / (2 : ℝ) ^ N :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hn₁)
  have hpow₂ : 1 / (2 : ℝ) ^ n₂ ≤ 1 / (2 : ℝ) ^ N :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hn₂)
  have hle : K * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) ≤ 2 * K / (2 : ℝ) ^ N := by
    have : 1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂ ≤ 2 * (1 / (2 : ℝ) ^ N) := by linarith
    have hmul := mul_le_mul_of_nonneg_left this (le_of_lt hK)
    have heq : K * (2 * (1 / (2 : ℝ) ^ N)) = 2 * K / (2 : ℝ) ^ N := by ring
    linarith
  have hN_pow : (N : ℝ) ≤ (2 : ℝ) ^ N := real_nat_le_two_pow N
  have h2N_gt : 2 * K / ε < (2 : ℝ) ^ N := lt_of_lt_of_le hN hN_pow
  have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have h1 : 2 * K < (2 : ℝ) ^ N * ε := (div_lt_iff₀ hε).mp h2N_gt
  have h2 : 2 * K / (2 : ℝ) ^ N < ε := (div_lt_iff₀ h2N_pos).mpr (by linarith)
  linarith

/-- General helper: if $u \to z_*$ and $|u(n_1) - u(n_2)| \le K \cdot (2^{-n_1} + 2^{-n_2})$ ($K \ge 0$),
    then $|u(n) - z_*| \le K / 2^n$ for every $n \in \mathbb{N}$. -/
theorem dist_limit_le_of_pow2_dist_bound (u : Nat → ℝ) (zstar K : ℝ) (hK : 0 ≤ K)
    (hlim : Filter.Tendsto u Filter.atTop (nhds zstar))
    (hdist : ∀ n₁ n₂ : Nat, |u n₁ - u n₂| ≤ K * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂))
    (n : Nat) :
    |u n - zstar| ≤ K / (2 : ℝ) ^ n := by
  by_contra hlt
  push_neg at hlt
  set ε := (|u n - zstar| - K / (2 : ℝ) ^ n) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N₁, hN₁⟩ := hlim ε hε
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (K / ε)
  let M := max N₁ N₂
  have hM₁ : N₁ ≤ M := le_max_left _ _
  have hM₂ : N₂ ≤ M := le_max_right _ _
  have h_close := hN₁ M hM₁
  rw [Real.dist_eq] at h_close
  have hd := hdist n M
  have hKM_lt : K / (2 : ℝ) ^ M ≤ ε := by
    by_cases hK0 : K = 0
    · rw [hK0, zero_div]; exact le_of_lt hε
    · have hK_pos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
      have hM_gt : K / ε < (2 : ℝ) ^ M :=
        lt_of_lt_of_le hN₂ (le_trans (by exact_mod_cast hM₂) (real_nat_le_two_pow M))
      have h2M_pos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
      have h1 : K < (2 : ℝ) ^ M * ε := (div_lt_iff₀ hε).mp hM_gt
      exact le_of_lt ((div_lt_iff₀ h2M_pos).mpr (by linarith))
  have htri : |u n - zstar| ≤ |u n - u M| + |u M - zstar| := by
    have := abs_add_le (u n - u M) (u M - zstar)
    simpa using this
  have hd_expand : K * (1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ M) =
      K / (2 : ℝ) ^ n + K / (2 : ℝ) ^ M := by ring
  rw [hd_expand] at hd
  dsimp [ε] at h_close hKM_lt
  linarith

/-- **Constructive Real Zero Existence & Convergence Theorem (`rootSeq_converges_to_real_zero`)**:
    Under the endpoint sign margin $k_0$ at $a, b \in [-2^{-(R+2)}, 2^{-(R+2)}]$ ($a \le b$) and
    the finite rational derivative margin $m > 0$, there exists a genuine real zero
    $z_* \in \mathbb{R}$ such that:
    1. `Filter.Tendsto (fun n => ((P.rootSeq a b k₀ n).val : ℝ)) Filter.atTop (nhds zstar)`,
    2. $(a.\mathrm{val} : \mathbb{R}) \le z_* \le (b.\mathrm{val} : \mathbb{R})$,
    3. $P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}\;z_* = 0$, and
    4. $\forall n \in \mathbb{N},\; |((P.\operatorname{rootSeq}\;a\;b\;k_0\;n).\mathrm{val} : \mathbb{R}) - z_*| \le (1 / (2 : \mathbb{R})^n) / (m : \mathbb{R})$. -/
theorem PolyODEProof.rootSeq_converges_to_real_zero (P : PolyODEProof)
    (a b : Q) (k₀ k : Nat) (m : Rat) (hm : 0 < m)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hab : a.val ≤ b.val)
    (hfa : P.toCertifiedAnalyticRep.analyticValue a ≤ -(1 / (2 : ℝ) ^ k₀))
    (hfb : 1 / (2 : ℝ) ^ k₀ ≤ P.toCertifiedAnalyticRep.analyticValue b)
    (hmargin : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val →
      m ≤ ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.toJet.evalPoly
            (k + ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.M + 3)) y).val
          - 1 / (2 : Rat) ^ k) :
    ∃ zstar : ℝ,
      Filter.Tendsto (fun n ↦ ((P.rootSeq a b k₀ n).val : ℝ)) Filter.atTop (nhds zstar) ∧
      (a.val : ℝ) ≤ zstar ∧ zstar ≤ (b.val : ℝ) ∧
      P.toCertifiedAnalyticRep.realAnalyticValue zstar = 0 ∧
      ∀ n : Nat,
        |((P.rootSeq a b k₀ n).val : ℝ) - zstar| ≤ (1 / (2 : ℝ) ^ n) / (m : ℝ) := by
  let S := P.toCertifiedAnalyticRep
  let u : Nat → ℝ := fun n ↦ ((P.rootSeq a b k₀ n).val : ℝ)
  have hm_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hK_pos : (0 : ℝ) < 1 / (m : ℝ) := one_div_pos.mpr hm_real
  have hdist : ∀ n₁ n₂ : Nat,
      |u n₁ - u n₂| ≤ (1 / (m : ℝ)) * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) := by
    intro n₁ n₂
    have hc := P.rootSeq_cauchy_of_deriv_margin a b k₀ k m hm ha hb hab hfa hfb hmargin n₁ n₂
    have heq : (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) / (m : ℝ) =
        (1 / (m : ℝ)) * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) := by ring
    linarith
  have hcauchy : CauchySeq u := cauchySeq_of_pow2_dist_bound u (1 / (m : ℝ)) hK_pos hdist
  obtain ⟨zstar, hz_lim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have h_mem_Icc : zstar ∈ Set.Icc (a.val : ℝ) (b.val : ℝ) := by
    refine isClosed_Icc.mem_of_tendsto hz_lim (Filter.Eventually.of_forall fun n ↦ ?_)
    have hres := P.rootSeq_residual_le a b k₀ n ha hb hab hfa hfb
    exact ⟨Rat.cast_le.mpr hres.1, Rat.cast_le.mpr hres.2.1⟩
  have h_rate : ∀ n : Nat, |u n - zstar| ≤ (1 / (2 : ℝ) ^ n) / (m : ℝ) := by
    intro n
    have hd := dist_limit_le_of_pow2_dist_bound u zstar (1 / (m : ℝ)) (le_of_lt hK_pos) hz_lim hdist n
    have heq : (1 / (m : ℝ)) / (2 : ℝ) ^ n = (1 / (2 : ℝ) ^ n) / (m : ℝ) := by ring
    linarith
  have hz_zero : S.realAnalyticValue zstar = 0 := by
    have hz_disk : |zstar| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) := by
      have ha_r : |(a.val : ℝ)| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) :=
        rat_abs_le_pow2_to_real ha
      have hb_r : |(b.val : ℝ)| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) :=
        rat_abs_le_pow2_to_real hb
      rw [abs_le] at ha_r hb_r ⊢
      constructor <;> linarith [h_mem_Icc.1, h_mem_Icc.2]
    set L : ℝ := (2 : ℝ) ^ (S.M + S.R + 2)
    let C : ℝ := L / (m : ℝ) + 1
    have hle0 : |S.realAnalyticValue zstar| ≤ 0 := by
      refine real_le_of_forall_sub_pow2_le |S.realAnalyticValue zstar| 0 C (by positivity) (fun n ↦ ?_)
      have hres := P.rootSeq_residual_le a b k₀ n ha hb hab hfa hfb
      have hun_disk : |u n| ≤ 1 / (2 : ℝ) ^ (S.R + 2) := by
        change |u n| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2)
        have ha_r : |(a.val : ℝ)| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) :=
          rat_abs_le_pow2_to_real ha
        have hb_r : |(b.val : ℝ)| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 2) :=
          rat_abs_le_pow2_to_real hb
        have hun_a : (a.val : ℝ) ≤ u n := Rat.cast_le.mpr hres.1
        have hun_b : u n ≤ (b.val : ℝ) := Rat.cast_le.mpr hres.2.1
        rw [abs_le] at ha_r hb_r ⊢
        constructor <;> linarith
      have hlip := S.realAnalyticValue_lipschitz_disk zstar (u n) hz_disk hun_disk
      rw [abs_sub_comm zstar (u n)] at hlip
      have h_un_val : S.realAnalyticValue (u n) = S.analyticValue (P.rootSeq a b k₀ n) := rfl
      rw [h_un_val] at hlip
      have htri : |S.realAnalyticValue zstar| ≤
          |S.realAnalyticValue zstar - S.analyticValue (P.rootSeq a b k₀ n)| +
          |S.analyticValue (P.rootSeq a b k₀ n)| := by
        have := abs_add_le (S.realAnalyticValue zstar - S.analyticValue (P.rootSeq a b k₀ n))
          (S.analyticValue (P.rootSeq a b k₀ n))
        simpa using this
      have hmul_rate := mul_le_mul_of_nonneg_left (h_rate n) (by positivity : 0 ≤ L)
      have hC_eq : L * ((1 / (2 : ℝ) ^ n) / (m : ℝ)) + 1 / (2 : ℝ) ^ n = C / (2 : ℝ) ^ n := by
        dsimp [C]; ring
      linarith [hres.2.2]
    exact abs_nonpos_iff.mp hle0
  exact ⟨zstar, hz_lim, h_mem_Icc.1, h_mem_Icc.2, hz_zero, h_rate⟩

/-! ## Section 4: Certified Fixed-Point Operators (`PolyODEProof.fixFast` and `PolyODEProof.fixRootSeq`) -/

/-- **Contractive Picard/Banach Fixed-Point Operator (`PolyODEProof.fixFast`)**:
    Iterates the fast certified evaluator `GPACSys.approxFast` from `x₀ : Q` with
    precision schedule `2 * n + 2`:
    $$x_0,\qquad x_{n+1} = \operatorname{GPACSys.approxFast}\;P.\mathrm{sys}\;P.v\;x_n\;(2n + 2).$$ -/
def PolyODEProof.fixFast (P : PolyODEProof) (x₀ : Q) : Nat → Q
  | 0 => x₀
  | n + 1 => GPACSys.approxFast P.sys P.v (P.fixFast x₀ n) (2 * n + 2)

@[simp]
theorem PolyODEProof.fixFast_zero (P : PolyODEProof) (x₀ : Q) :
    P.fixFast x₀ 0 = x₀ := rfl

@[simp]
theorem PolyODEProof.fixFast_succ (P : PolyODEProof) (x₀ : Q) (n : Nat) :
    P.fixFast x₀ (n + 1) = GPACSys.approxFast P.sys P.v (P.fixFast x₀ n) (2 * n + 2) := rfl

/-- **Contractive Secant / A Posteriori Bound**:
    If $f : \mathbb{R} \to \mathbb{R}$ is $(1/2)$-Lipschitz on $[-r, r]$, then for all $x, y \in [-r, r]$:
    $$|x - y| \le 2 \cdot \big(|f(x) - x| + |f(y) - y|\big).$$ -/
theorem contractive_half_secant_bound (f : ℝ → ℝ) (r x y : ℝ)
    (hlip : ∀ u v : ℝ, |u| ≤ r → |v| ≤ r → |f u - f v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hx : |x| ≤ r) (hy : |y| ≤ r) :
    |x - y| ≤ 2 * (|f x - x| + |f y - y|) := by
  have h_id : x - y = (x - f x) + ((f y - y) + (f x - f y)) := by ring
  have htri1 := abs_add_le (x - f x) ((f y - y) + (f x - f y))
  have htri2 := abs_add_le (f y - y) (f x - f y)
  rw [← h_id, abs_sub_comm x (f x)] at htri1
  have hl := hlip x y hx hy
  linarith

/-- One-step residual contraction for `PolyODEProof.fixFast`:
    When `S.realAnalyticValue` is $(1/2)$-Lipschitz on $|x| \le 2^{-(R+1)}$ and `P.fixFast x₀ n`,
    `P.fixFast x₀ (n + 1)` lie in that disk, the fixed-point residual
    $R_n := |S.\operatorname{analyticValue}(x_n) - x_n.\mathrm{val}|$ satisfies:
    $$R_{n+1} \le \frac{1}{2} R_n + 2 \cdot \left(\frac{1}{4}\right)^{n+1}.$$ -/
theorem PolyODEProof.fixFast_residual_step (P : PolyODEProof) (x₀ : Q)
    (hlip : ∀ u v : ℝ,
      |u| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) →
      |v| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) →
      |P.toCertifiedAnalyticRep.realAnalyticValue u -
       P.toCertifiedAnalyticRep.realAnalyticValue v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hdisk : ∀ n : Nat, |(P.fixFast x₀ n).val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (n : Nat) :
    |P.toCertifiedAnalyticRep.analyticValue (P.fixFast x₀ (n + 1)) -
        ((P.fixFast x₀ (n + 1)).val : ℝ)| ≤
      (1 / 2 : ℝ) *
        |P.toCertifiedAnalyticRep.analyticValue (P.fixFast x₀ n) -
          ((P.fixFast x₀ n).val : ℝ)| +
      2 * (1 / 4 : ℝ) ^ (n + 1) := by
  let S := P.toCertifiedAnalyticRep
  set xn := P.fixFast x₀ n
  set xn1 := P.fixFast x₀ (n + 1)
  have hcert : |(xn1.val : ℝ) - S.analyticValue xn| ≤ 1 / (2 : ℝ) ^ (2 * n + 2) :=
    certified_evaluation P xn (2 * n + 2) (hdisk n)
  have hxn_real : |(xn.val : ℝ)| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) :=
    rat_abs_le_pow2_to_real (hdisk n)
  have hxn1_real : |(xn1.val : ℝ)| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) :=
    rat_abs_le_pow2_to_real (hdisk (n + 1))
  have hl := hlip (xn1.val : ℝ) (xn.val : ℝ) hxn1_real hxn_real
  rw [S.realAnalyticValue_coe xn1, S.realAnalyticValue_coe xn] at hl
  have htri1 : |S.analyticValue xn1 - (xn1.val : ℝ)| ≤
      |S.analyticValue xn1 - S.analyticValue xn| + |S.analyticValue xn - (xn1.val : ℝ)| := by
    have := abs_add_le (S.analyticValue xn1 - S.analyticValue xn)
      (S.analyticValue xn - (xn1.val : ℝ))
    simpa using this
  have htri2 : |(xn1.val : ℝ) - (xn.val : ℝ)| ≤
      |(xn1.val : ℝ) - S.analyticValue xn| + |S.analyticValue xn - (xn.val : ℝ)| := by
    have := abs_add_le ((xn1.val : ℝ) - S.analyticValue xn)
      (S.analyticValue xn - (xn.val : ℝ))
    simpa using this
  have htri2_half : (1 / 2 : ℝ) * |(xn1.val : ℝ) - (xn.val : ℝ)| ≤
      (1 / 2 : ℝ) * |(xn1.val : ℝ) - S.analyticValue xn| +
      (1 / 2 : ℝ) * |S.analyticValue xn - (xn.val : ℝ)| := by linarith
  have hcert' : |S.analyticValue xn - (xn1.val : ℝ)| ≤ 1 / (2 : ℝ) ^ (2 * n + 2) := by
    rw [abs_sub_comm]; exact hcert
  have hpow4 : 1 / (2 : ℝ) ^ (2 * n + 2) = (1 / 4 : ℝ) ^ (n + 1) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul (2 : ℝ) 2 (n + 1), one_div_pow]
    norm_num
  rw [hpow4] at hcert hcert'
  have hpow4_nonneg : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (n + 1) := by positivity
  change |S.analyticValue xn1 - (xn1.val : ℝ)| ≤
    (1 / 2 : ℝ) * |S.analyticValue xn - (xn.val : ℝ)| + 2 * (1 / 4 : ℝ) ^ (n + 1)
  linarith

/-- Telescoping inductive bound on the fixed-point residual of `PolyODEProof.fixFast`. -/
theorem PolyODEProof.fixFast_residual_telescoping (P : PolyODEProof) (x₀ : Q)
    (hlip : ∀ u v : ℝ,
      |u| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) →
      |v| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) →
      |P.toCertifiedAnalyticRep.realAnalyticValue u -
       P.toCertifiedAnalyticRep.realAnalyticValue v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hdisk : ∀ n : Nat, |(P.fixFast x₀ n).val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1)) :
    ∀ n : Nat,
      |P.toCertifiedAnalyticRep.analyticValue (P.fixFast x₀ n) -
          ((P.fixFast x₀ n).val : ℝ)| ≤
        (|P.toCertifiedAnalyticRep.analyticValue x₀ - (x₀.val : ℝ)| + 2) * (1 / 2 : ℝ) ^ n -
          2 * (1 / 4 : ℝ) ^ n
  | 0 => by
    simp [PolyODEProof.fixFast_zero]
  | n + 1 => by
    have ih := P.fixFast_residual_telescoping x₀ hlip hdisk n
    have hstep := P.fixFast_residual_step x₀ hlip hdisk n
    have h_alg :
        (1 / 2 : ℝ) *
          ((|P.toCertifiedAnalyticRep.analyticValue x₀ - (x₀.val : ℝ)| + 2) * (1 / 2 : ℝ) ^ n -
            2 * (1 / 4 : ℝ) ^ n) +
        2 * (1 / 4 : ℝ) ^ (n + 1) =
        (|P.toCertifiedAnalyticRep.analyticValue x₀ - (x₀.val : ℝ)| + 2) * (1 / 2 : ℝ) ^ (n + 1) -
          2 * (1 / 4 : ℝ) ^ (n + 1) := by
      rw [pow_succ (1 / 2 : ℝ) n, pow_succ (1 / 4 : ℝ) n]
      ring
    linarith

/-- **Explicit $O(2^{-n})$ Residual Bound for `PolyODEProof.fixFast` (`fixFast_residual_le`)**:
    When `S.realAnalyticValue` is $(1/2)$-contractive on the certified disk and the iterates
    `P.fixFast x₀ n` stay in the disk, every iterate satisfies:
    $$\big|P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(P.\operatorname{fixFast}\;x_0\;n)
      - ((P.\operatorname{fixFast}\;x_0\;n).\mathrm{val} : \mathbb{R})\big|
      \le \frac{|P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(x_0) - (x_0.\mathrm{val} : \mathbb{R})| + 2}{(2 : \mathbb{R})^n}.$$ -/
theorem PolyODEProof.fixFast_residual_le (P : PolyODEProof) (x₀ : Q)
    (hlip : ∀ u v : ℝ,
      |u| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) →
      |v| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) →
      |P.toCertifiedAnalyticRep.realAnalyticValue u -
       P.toCertifiedAnalyticRep.realAnalyticValue v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hdisk : ∀ n : Nat, |(P.fixFast x₀ n).val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (n : Nat) :
    |P.toCertifiedAnalyticRep.analyticValue (P.fixFast x₀ n) -
        ((P.fixFast x₀ n).val : ℝ)| ≤
      (|P.toCertifiedAnalyticRep.analyticValue x₀ - (x₀.val : ℝ)| + 2) / (2 : ℝ) ^ n := by
  have htel := P.fixFast_residual_telescoping x₀ hlip hdisk n
  have hpos : (0 : ℝ) ≤ 2 * (1 / 4 : ℝ) ^ n := by positivity
  have hpow : (|P.toCertifiedAnalyticRep.analyticValue x₀ - (x₀.val : ℝ)| + 2) * (1 / 2 : ℝ) ^ n =
      (|P.toCertifiedAnalyticRep.analyticValue x₀ - (x₀.val : ℝ)| + 2) / (2 : ℝ) ^ n := by
    rw [one_div_pow]; ring
  linarith

/-- **Banach Fixed-Point Existence & `fixFast` Convergence Theorem (`PolyODEProof.fixFast_converges_to_fixedPoint`)**:
    When `P.toCertifiedAnalyticRep.realAnalyticValue` is $(1/2)$-contractive on the certified disk
    $|x| \le 1 / (2 : \mathbb{R})^{(sysParams P.sys).2 + 1}$ and the iterates `P.fixFast x₀ n` lie in the disk,
    there exists a genuine real fixed point $z_* \in \mathbb{R}$ in the disk such that:
    1. `Filter.Tendsto (fun n => ((P.fixFast x₀ n).val : ℝ)) Filter.atTop (nhds z_*)`,
    2. $|z_*| \le 1 / (2 : \mathbb{R})^{(sysParams P.sys).2 + 1}$,
    3. **Exact Real Fixed Point**: $P.\mathrm{toCertifiedAnalyticRep}.\operatorname{realAnalyticValue}\;z_* = z_*$, and
    4. **Certified Convergence Rate**: for all $n \in \mathbb{N}$,
       $$\big|((P.\operatorname{fixFast}\;x_0\;n).\mathrm{val} : \mathbb{R}) - z_*\big|
         \le 2 \cdot \frac{|P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(x_0) - (x_0.\mathrm{val} : \mathbb{R})| + 2}{(2 : \mathbb{R})^n}.$$ -/
theorem PolyODEProof.fixFast_converges_to_fixedPoint (P : PolyODEProof) (x₀ : Q)
    (hlip : ∀ u v : ℝ,
      |u| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) →
      |v| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) →
      |P.toCertifiedAnalyticRep.realAnalyticValue u -
       P.toCertifiedAnalyticRep.realAnalyticValue v| ≤ (1 / 2 : ℝ) * |u - v|)
    (hdisk : ∀ n : Nat, |(P.fixFast x₀ n).val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1)) :
    ∃ zstar : ℝ,
      Filter.Tendsto (fun n ↦ ((P.fixFast x₀ n).val : ℝ)) Filter.atTop (nhds zstar) ∧
      |zstar| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1) ∧
      P.toCertifiedAnalyticRep.realAnalyticValue zstar = zstar ∧
      ∀ n : Nat,
        |((P.fixFast x₀ n).val : ℝ) - zstar| ≤
          2 * (|P.toCertifiedAnalyticRep.analyticValue x₀ - (x₀.val : ℝ)| + 2) / (2 : ℝ) ^ n := by
  let S := P.toCertifiedAnalyticRep
  set r : ℝ := 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1)
  set R₀ : ℝ := |S.analyticValue x₀ - (x₀.val : ℝ)|
  set K : ℝ := 2 * (R₀ + 2)
  have hK_pos : 0 < K := by dsimp [K]; positivity
  let u : Nat → ℝ := fun n ↦ ((P.fixFast x₀ n).val : ℝ)
  have hu_disk : ∀ n : Nat, |u n| ≤ r := fun n ↦ rat_abs_le_pow2_to_real (hdisk n)
  have hdist : ∀ n₁ n₂ : Nat,
      |u n₁ - u n₂| ≤ K * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) := by
    intro n₁ n₂
    have hsec := contractive_half_secant_bound S.realAnalyticValue r (u n₁) (u n₂)
      hlip (hu_disk n₁) (hu_disk n₂)
    have hr₁ := P.fixFast_residual_le x₀ hlip hdisk n₁
    have hr₂ := P.fixFast_residual_le x₀ hlip hdisk n₂
    rw [S.realAnalyticValue_coe (P.fixFast x₀ n₁),
        S.realAnalyticValue_coe (P.fixFast x₀ n₂)] at hsec
    have h_alg : 2 * ((R₀ + 2) / (2 : ℝ) ^ n₁ + (R₀ + 2) / (2 : ℝ) ^ n₂) =
        K * (1 / (2 : ℝ) ^ n₁ + 1 / (2 : ℝ) ^ n₂) := by
      dsimp [K]; ring
    linarith
  have hcauchy : CauchySeq u := cauchySeq_of_pow2_dist_bound u K hK_pos hdist
  obtain ⟨zstar, hz_lim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hz_mem : zstar ∈ Set.Icc (-r) r := by
    refine isClosed_Icc.mem_of_tendsto hz_lim (Filter.Eventually.of_forall fun n ↦ ?_)
    exact abs_le.mp (hu_disk n)
  have hz_disk : |zstar| ≤ r := abs_le.mpr hz_mem
  have h_rate : ∀ n : Nat, |u n - zstar| ≤ K / (2 : ℝ) ^ n :=
    dist_limit_le_of_pow2_dist_bound u zstar K (le_of_lt hK_pos) hz_lim hdist
  have hz_fix : S.realAnalyticValue zstar = zstar := by
    have hle0 : |S.realAnalyticValue zstar - zstar| ≤ 0 := by
      refine real_le_of_forall_sub_pow2_le |S.realAnalyticValue zstar - zstar| 0
        (2 * K) (by positivity) (fun n ↦ ?_)
      have hl := hlip zstar (u n) hz_disk (hu_disk n)
      rw [S.realAnalyticValue_coe (P.fixFast x₀ n), abs_sub_comm zstar (u n)] at hl
      change |S.realAnalyticValue zstar - S.analyticValue (P.fixFast x₀ n)| ≤
        (1 / 2 : ℝ) * |u n - zstar| at hl
      have hres := P.fixFast_residual_le x₀ hlip hdisk n
      change |S.analyticValue (P.fixFast x₀ n) - u n| ≤ (R₀ + 2) / (2 : ℝ) ^ n at hres
      have hrate_n := h_rate n
      have htri1 : |S.realAnalyticValue zstar - zstar| ≤
          |S.realAnalyticValue zstar - S.analyticValue (P.fixFast x₀ n)| +
          (|S.analyticValue (P.fixFast x₀ n) - u n| + |u n - zstar|) := by
        have h1 : |S.realAnalyticValue zstar - zstar| ≤
            |S.realAnalyticValue zstar - S.analyticValue (P.fixFast x₀ n)| +
            |S.analyticValue (P.fixFast x₀ n) - zstar| := by
          have := abs_add_le (S.realAnalyticValue zstar - S.analyticValue (P.fixFast x₀ n))
            (S.analyticValue (P.fixFast x₀ n) - zstar)
          simpa using this
        have h2 : |S.analyticValue (P.fixFast x₀ n) - zstar| ≤
            |S.analyticValue (P.fixFast x₀ n) - u n| + |u n - zstar| := by
          have := abs_add_le (S.analyticValue (P.fixFast x₀ n) - u n) (u n - zstar)
          simpa using this
        linarith
      have hK_half : (R₀ + 2) / (2 : ℝ) ^ n = (1 / 2) * (K / (2 : ℝ) ^ n) := by
        dsimp [K]; ring
      have h2K : (1 / 2 : ℝ) * (K / (2 : ℝ) ^ n) +
          ((1 / 2 : ℝ) * (K / (2 : ℝ) ^ n) + K / (2 : ℝ) ^ n) =
          2 * K / (2 : ℝ) ^ n := by ring
      linarith
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hle0)
  exact ⟨zstar, hz_lim, hz_disk, hz_fix, h_rate⟩

/-! ### General Non-Contractive Fixed-Point Operator via `P.sub PolyODEProof.varX` -/

/-- **Fixed-Point Residual Representation (`PolyODEProof.fixPointEq`)**:
    Constructs the `PolyODEProof` for $g_P(x) = f_P(x) - x$ via `P.sub PolyODEProof.varX`. -/
def PolyODEProof.fixPointEq (P : PolyODEProof) : PolyODEProof :=
  P.sub PolyODEProof.varX

/-- **General Fixed-Point Sequence via Bisection (`PolyODEProof.fixRootSeq`)**:
    Applies the unconditional bisection root sequence `rootSeq` to `P.fixPointEq`. -/
def PolyODEProof.fixRootSeq (P : PolyODEProof) (a b : Q) (k₀ n : Nat) : Q :=
  P.fixPointEq.rootSeq a b k₀ n

/-- The real power series of `PolyODEProof.varX` evaluates to the identity function $x \mapsto x$
    at every real number $x \in \mathbb{R}$. -/
theorem PolyODEProof.varX_realAnalyticValue (x : ℝ) :
    PolyODEProof.varX.toCertifiedAnalyticRep.realAnalyticValue x = x := by
  let S := PolyODEProof.varX.toCertifiedAnalyticRep
  have hc : ∀ n : Nat, S.coeff n = (UExpr.x.eval n).val := by
    intro n
    rw [← S.fast_correct n]
    exact (UExpr.x.eval_eq_extracted_and_fast trivial n).2.symm
  have hsum : S.realAnalyticValue x =
      ∑ n ∈ Finset.range 2, S.realSeriesTerm x n := by
    unfold CertifiedAnalyticRep.realAnalyticValue
    refine tsum_eq_sum fun n hn ↦ ?_
    rw [Finset.mem_range] at hn
    unfold CertifiedAnalyticRep.realSeriesTerm
    rw [hc n]
    rcases n with _ | _ | k
    · omega
    · omega
    · change ((Q.zero : Q).val : ℝ) * x ^ (k + 2) = 0
      rw [Q.val_zero]; simp
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_one]
  unfold CertifiedAnalyticRep.realSeriesTerm
  rw [hc 0, hc 1]
  change ((Q.zero : Q).val : ℝ) * x ^ 0 + ((Q.ofNat 1 : Q).val : ℝ) * x ^ 1 = x
  rw [Q.val_zero, Q.val_ofNat]
  simp

/-- On the certified disks of `P` and `P.fixPointEq`, the real analytic value of
    `P.fixPointEq = P.sub PolyODEProof.varX` equals $P.\operatorname{realAnalyticValue}(x) - x$. -/
theorem PolyODEProof.fixPointEq_realAnalyticValue (P : PolyODEProof) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1)) :
    P.fixPointEq.toCertifiedAnalyticRep.realAnalyticValue x =
      P.toCertifiedAnalyticRep.realAnalyticValue x - x := by
  let SP := P.toCertifiedAnalyticRep
  let SX := PolyODEProof.varX.toCertifiedAnalyticRep
  let SG := P.fixPointEq.toCertifiedAnalyticRep
  have hsumP : Summable (SP.realSeriesTerm x) := SP.summable_realSeriesTerm x hx
  have hsumX : Summable (SX.realSeriesTerm x) := by
    refine summable_of_ne_finset_zero (s := Finset.range 2) fun n hn ↦ ?_
    rw [Finset.mem_range] at hn
    unfold CertifiedAnalyticRep.realSeriesTerm
    have hc : SX.coeff n = (UExpr.x.eval n).val := by
      rw [← SX.fast_correct n]
      exact (UExpr.x.eval_eq_extracted_and_fast trivial n).2.symm
    rw [hc]
    rcases n with _ | _ | k
    · omega
    · omega
    · change ((Q.zero : Q).val : ℝ) * x ^ (k + 2) = 0
      rw [Q.val_zero]; simp
  have hterm : ∀ n : Nat, SG.realSeriesTerm x n = SP.realSeriesTerm x n - SX.realSeriesTerm x n := by
    intro n
    unfold CertifiedAnalyticRep.realSeriesTerm
    have hsub := P.sub_coeff PolyODEProof.varX n
    change SG.coeff n = SP.coeff n - SX.coeff n at hsub
    rw [hsub, Rat.cast_sub, sub_mul]
  unfold CertifiedAnalyticRep.realAnalyticValue
  have hcongr : (∑' n : Nat, SG.realSeriesTerm x n) =
      ∑' n : Nat, (SP.realSeriesTerm x n - SX.realSeriesTerm x n) := by
    congr 1; ext n; exact hterm n
  rw [hcongr, hsumP.tsum_sub hsumX]
  change SP.realAnalyticValue x - SX.realAnalyticValue x = SP.realAnalyticValue x - x
  rw [PolyODEProof.varX_realAnalyticValue x]

/-- **General Fixed-Point Reduction Theorem (`PolyODEProof.fixPoint_iff_fixPointEq_zero`)**:
    For every real point $x \in \mathbb{R}$ in the certified disk $|x| \le 1 / (2 : \mathbb{R})^{(sysParams P.sys).2 + 1}$,
    $x$ is a fixed point of `P.toCertifiedAnalyticRep.realAnalyticValue` ($f_P(x) = x$)
    **if and only if** $x$ is a zero of `P.fixPointEq.toCertifiedAnalyticRep.realAnalyticValue`. -/
theorem PolyODEProof.fixPoint_iff_fixPointEq_zero (P : PolyODEProof) (x : ℝ)
    (hx : |x| ≤ 1 / (2 : ℝ) ^ ((sysParams P.sys).2 + 1)) :
    P.toCertifiedAnalyticRep.realAnalyticValue x = x ↔
      P.fixPointEq.toCertifiedAnalyticRep.realAnalyticValue x = 0 := by
  rw [P.fixPointEq_realAnalyticValue x hx, sub_eq_zero]

#print axioms CertifiedAnalyticRep.realAnalyticValue_coe
#print axioms CertifiedAnalyticRep.realAnalyticValue_sub_realEvalPoly_le
#print axioms CertifiedAnalyticRep.realAnalyticValue_lipschitz_disk
#print axioms CertifiedAnalyticRep.continuousOn_realAnalyticValue_disk
#print axioms PolyODEProof.realAnalyticValue_quad_rem_disk
#print axioms PolyODEProof.hasDerivWithinAt_realAnalyticValue
#print axioms PolyODEProof.hasDerivAt_realAnalyticValue
#print axioms PolyODEProof.hasDerivAt_integ_realAnalyticValue
#print axioms PolyODEProof.intervalIntegral_realAnalyticValue_eq_integ_sub
#print axioms PolyODEProof.defIntegralFast_intervalIntegral_spec
#print axioms PolyODEProof.intervalIntegral_derivOp_eq_sub
#print axioms PolyODEProof.rootColor_endpoints_ne_of_sign_margin
#print axioms PolyODEProof.rootSeq_residual_le
#print axioms PolyODEProof.rootSeq_cauchy_of_deriv_margin
#print axioms PolyODEProof.rootSeq_converges_to_real_zero
#print axioms PolyODEProof.fixFast_residual_le
#print axioms PolyODEProof.fixFast_converges_to_fixedPoint
#print axioms PolyODEProof.fixPointEq_realAnalyticValue
#print axioms PolyODEProof.fixPoint_iff_fixPointEq_zero

end HAomega
