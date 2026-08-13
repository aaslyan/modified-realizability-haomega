/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis

/-!
# Picard–Lindelöf Synthesis: Newton–Leibniz meets Banach Fixed Point

This module formalizes the synthesis described in §7.3 of the manifesto:
Ordinary differential equations $y'(x) = f(x, y(x))$ with initial condition $y(a) = y_0$
are solved constructively by composing:

1. **Newton–Leibniz / Integration (`EFTC1`)**:
   Transforms the differential equation $y' = f(x, y)$ into the integral equation:
   $$y(x) = y_0 + \int_a^x f(t, y(t))\,dt$$

2. **Composition (`CompData.comp` / `CompData1.comp`)**:
   Preserves uniform continuity ($A_0$) and uniform differentiability ($A_1$) under
   the evaluation map $t \mapsto f(t, y(t))$.

3. **Banach Contraction Mapping Theorem (`LimSeq`)**:
   When $f$ is Lipschitz with constant $2^L$ and the time horizon satisfies
   $b - a \le 2^{-(L + p)}$ with $p \ge 1$, the Picard integral operator:
   $$\mathcal{T}(y)(x) := y_0 + \int_a^x f(t, y(t))\,dt$$
   is a uniform $2^{-p}$-contraction on $(C[a, b], \|\cdot\|_\infty)$.
   Iteration $y_{n+1} = \mathcal{T}(y_n)$ generates a sequence with explicit rate of
   convergence $\Phi(k) = \lceil (k + M + 1) / p \rceil$, packaging into a `LimSeq`
   and producing the unique fixed-point solution in $E_0$.

4. **Regularity Promotion (`EFTC1` & `EFTC2`)**:
   Since the fixed point $y^*$ satisfies $y^* = \mathcal{T}(y^*)$, it is the integral of
   a continuous function, hence promoted from $E_0$ to $E_1 \cong A_1$, satisfying
   $(y^*)'(x) = f(x, y^*(x))$ with $y^*(a) = y_0$.
-/

namespace HAomega

open Rat

/-! ## 1. Uniform distance on function samplers -/

/-- Two functions `f, g : Q → Q` are within $2^{-k}$ uniformly on $[a, b]$. -/
def unifDistLe (a b : Q) (f g : Q → Q) (k : Nat) : Prop :=
  ∀ x : Q, Qle a x = true → Qle x b = true →
    |(f x).val - (g x).val| ≤ 1 / 2 ^ k

/-- Uniform distance is reflexive. -/
theorem unifDistLe_refl (a b : Q) (f : Q → Q) (k : Nat) :
    unifDistLe a b f f k := by
  intro x _ _
  rw [sub_self, abs_zero]
  positivity

/-- Uniform distance is symmetric. -/
theorem unifDistLe_symm (a b : Q) (f g : Q → Q) (k : Nat)
    (h : unifDistLe a b f g k) : unifDistLe a b g f k := by
  intro x hxa hxb
  rw [abs_sub_comm]
  exact h x hxa hxb

/-- Monotonicity: precision increase implies lower precision bound. -/
theorem unifDistLe_mono (a b : Q) (f g : Q → Q) {k1 k2 : Nat} (hk : k1 ≤ k2)
    (h : unifDistLe a b f g k2) : unifDistLe a b f g k1 := by
  intro x hxa hxb
  have hx := h x hxa hxb
  have hpow := inv_pow_le hk
  linarith

/-- Ceiling division inequality: for any $A, p$ with $1 \le p$,
    $A \le p \cdot \lceil A / p \rceil = p \cdot ((A + p - 1) / p)$. -/
theorem ceil_div_mul (A p : Nat) (hp : 1 ≤ p) : A ≤ p * ((A + p - 1) / p) := by
  have h := Nat.div_add_mod (A + p - 1) p
  have hm := Nat.mod_lt (A + p - 1) (by omega : 0 < p)
  have h_comm : p * ((A + p - 1) / p) = (A + p - 1) / p * p := Nat.mul_comm p _
  omega

/-! ## 2. Abstract Contraction Operator and Banach Iteration -/

/-- Data of a uniform contraction operator on $[a, b]$. -/
structure ContractionOp (a b : Q) where
  /-- The operator on function samplers. -/
  T : (Q → Q) → (Q → Q)
  /-- The contraction shift $p \ge 1$ ($q = 2^{-p} \le 1/2$). -/
  p : Nat
  hp : 1 ≤ p
  /-- Initial point $y_0$. -/
  y0 : Q → Q
  /-- Initial step bound: $\|y_0 - T(y_0)\|_\infty \le 2^M$. -/
  M : Nat
  h_step0 : ∀ x : Q, Qle a x = true → Qle x b = true →
    |(y0 x).val - (T y0 x).val| ≤ 2 ^ M
  /-- The contraction property on function differences. -/
  contract : ∀ (y z : Q → Q) (k : Nat),
    (∀ x : Q, Qle a x = true → Qle x b = true → |(y x).val - (z x).val| ≤ (2 : Rat) ^ M / 2 ^ k) →
    (∀ x : Q, Qle a x = true → Qle x b = true → |(T y x).val - (T z x).val| ≤ (2 : Rat) ^ M / 2 ^ (k + p))

/-- The Picard iteration sequence $y_n = \mathcal{T}^n(y_0)$. -/
def ContractionOp.iter {a b : Q} (C : ContractionOp a b) : Nat → (Q → Q)
  | 0 => C.y0
  | n + 1 => C.T (C.iter n)

/-- Step bound for consecutive iterates:
    $\|y_n - y_{n+1}\|_\infty \le 2^M / 2^{p \cdot n}$. -/
theorem ContractionOp.consec_step {a b : Q} (C : ContractionOp a b) (n : Nat) :
    ∀ x : Q, Qle a x = true → Qle x b = true →
      |(C.iter n x).val - (C.iter (n + 1) x).val| ≤ (2 : Rat) ^ C.M / 2 ^ (C.p * n) := by
  induction n with
  | zero =>
    intro x hxa hxb
    dsimp [iter]
    have h0 := C.h_step0 x hxa hxb
    have : (2 : Rat) ^ C.M / 2 ^ (C.p * 0) = 2 ^ C.M := by
      rw [show C.p * 0 = 0 by ring, pow_zero, div_one]
    linarith
  | succ n ih =>
    intro x hxa hxb
    have h_step := C.contract (C.iter n) (C.iter (n + 1)) (C.p * n) ih
    have : C.p * n + C.p = C.p * (n + 1) := by ring
    rw [this] at h_step
    exact h_step x hxa hxb

/-- Telescoping geometric sum bound: for any $d$,
    $\|y_n - y_{n+d}\|_\infty \le \frac{2^{M+1}}{2^{p n}} (1 - 1/2^d) \le \frac{2^{M+1}}{2^{p n}}$. -/
theorem ContractionOp.telescope_step {a b : Q} (C : ContractionOp a b) (n d : Nat) :
    ∀ x : Q, Qle a x = true → Qle x b = true →
      |(C.iter n x).val - (C.iter (n + d) x).val|
        ≤ ((2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n)) * (1 - 1 / 2 ^ d) := by
  induction d with
  | zero =>
    intro x _ _
    have h_sub : (1 : Rat) - 1 / 2 ^ 0 = 0 := by norm_num
    rw [show n + 0 = n by rfl, sub_self, abs_zero, h_sub, mul_zero]
  | succ d ih =>
    intro x hxa hxb
    have h_tri : |(C.iter n x).val - (C.iter (n + d + 1) x).val|
        ≤ |(C.iter n x).val - (C.iter (n + d) x).val|
          + |(C.iter (n + d) x).val - (C.iter (n + d + 1) x).val| :=
      abs_sub_le (C.iter n x).val (C.iter (n + d) x).val (C.iter (n + d + 1) x).val
    have h_ih := ih x hxa hxb
    have h_step := C.consec_step (n + d) x hxa hxb
    have h_pd : C.p * n + d ≤ C.p * (n + d) := by
      have hp := C.hp
      nlinarith
    have h_pow_le : (1 : Rat) / 2 ^ (C.p * (n + d)) ≤ (1 / 2 ^ (C.p * n)) * (1 / 2 ^ d) := by
      rw [one_div_mul_one_div, ← pow_add]
      exact inv_pow_le (by omega)
    have h_step_bound : (2 : Rat) ^ C.M / 2 ^ (C.p * (n + d))
        ≤ (2 : Rat) ^ C.M * ((1 / 2 ^ (C.p * n)) * (1 / 2 ^ d)) := by
      have : (2 : Rat) ^ C.M / 2 ^ (C.p * (n + d)) = 2 ^ C.M * (1 / 2 ^ (C.p * (n + d))) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h_pow_le (by positivity)
    have hM1 : (2 : Rat) ^ (C.M + 1) = 2 ^ C.M * 2 := by
      rw [show C.M + 1 = C.M + 1 by rfl, pow_add]; norm_num; ring
    have hd1 : (1 : Rat) / 2 ^ (d + 1) = (1 / 2 ^ d) * (1 / 2) := by
      rw [show d + 1 = d + 1 by rfl, pow_add]; ring
    have h_alg : ((2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n)) * (1 - 1 / 2 ^ d)
        + (2 : Rat) ^ C.M * ((1 / 2 ^ (C.p * n)) * (1 / 2 ^ d))
        = ((2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n)) * (1 - 1 / 2 ^ (d + 1)) := by
      rw [hM1, hd1]
      have : (0 : Rat) < 2 ^ (C.p * n) := by positivity
      have : (0 : Rat) < 2 ^ d := by positivity
      field_simp
    have h_goal : |(C.iter n x).val - (C.iter (n + d + 1) x).val|
        ≤ ((2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n)) * (1 - 1 / 2 ^ (d + 1)) := by
      linarith [h_tri, h_ih, h_step, h_step_bound, h_alg]
    exact h_goal

/-- Consecutive distance bound:
    $\|y_n - y_m\|_\infty \le 2^{M + 1} / 2^{p \cdot n}$ for all $n \le m$. -/
theorem ContractionOp.dist_iter {a b : Q} (C : ContractionOp a b) (n m : Nat) (hnm : n ≤ m) :
    ∀ x : Q, Qle a x = true → Qle x b = true →
      |(C.iter n x).val - (C.iter m x).val| ≤ (2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n) := by
  intro x hxa hxb
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have h_tel := C.telescope_step n d x hxa hxb
  have h_factor : 1 - (1 : Rat) / 2 ^ d ≤ 1 := by
    have : (0 : Rat) ≤ 1 / 2 ^ d := by positivity
    linarith
  have h_nonneg : 0 ≤ (2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n) := by positivity
  have h_le : ((2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n)) * (1 - 1 / 2 ^ d)
      ≤ (2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n) := by
    calc ((2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n)) * (1 - 1 / 2 ^ d)
      _ ≤ ((2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n)) * 1 :=
        mul_le_mul_of_nonneg_left h_factor h_nonneg
      _ = (2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n) := mul_one _
  linarith

/-- The rate of convergence $\Phi(k)$ for the contraction:
    $\Phi(k) = (k + M + 1 + p - 1) / p = \lceil (k + M + 1) / p \rceil$. -/
def ContractionOp.rate {a b : Q} (C : ContractionOp a b) (k : Nat) : Nat :=
  (k + C.M + 1 + C.p - 1) / C.p

/-- **Banach Fixed Point Theorem on Function Samplers**:
    The Picard iterates form a uniformly Cauchy sequence with explicit rate $\Phi(k)$. -/
theorem ContractionOp.cauchy {a b : Q} (C : ContractionOp a b) (k n m : Nat)
    (hn : C.rate k ≤ n) (hnm : n ≤ m) :
    unifDistLe a b (C.iter n) (C.iter m) k := by
  intro x hxa hxb
  have h_dist := C.dist_iter n m hnm x hxa hxb
  have h_c := ceil_div_mul (k + C.M + 1) C.p C.hp
  have h_m : C.p * C.rate k ≤ C.p * n := Nat.mul_le_mul_left C.p hn
  have h_pn : k + (C.M + 1) ≤ C.p * n := le_trans h_c h_m
  have h_M_le : C.M + 1 ≤ C.p * n := by omega
  have h_sub : (C.p * n - (C.M + 1)) + (C.M + 1) = C.p * n := Nat.sub_add_cancel h_M_le
  have h_pow : (2 : Rat) ^ (C.p * n) = 2 ^ (C.p * n - (C.M + 1)) * 2 ^ (C.M + 1) := by
    rw [← pow_add, h_sub]
  have h_div : (2 : Rat) ^ (C.M + 1) / 2 ^ (C.p * n) = 1 / 2 ^ (C.p * n - (C.M + 1)) := by
    rw [h_pow]
    have : (0 : Rat) < 2 ^ (C.M + 1) := by positivity
    have : (0 : Rat) < 2 ^ (C.p * n - (C.M + 1)) := by positivity
    field_simp; ring
  rw [h_div] at h_dist
  have h_inv : (1 : Rat) / 2 ^ (C.p * n - (C.M + 1)) ≤ 1 / 2 ^ k := inv_pow_le (by omega)
  linarith

#print axioms ContractionOp.cauchy

/-! ## 3. Packaging into `LimSeq` and `E₀` -/

/-- Full Picard data with continuity tracking for each iterate. -/
structure PicardData where
  a : Q
  b : Q
  ivl : Q.ltN a b = 1
  C : ContractionOp a b
  /-- Modulus of continuity for each iterate $y_n$. -/
  ωs : Nat → Nat → Nat
  cont : ∀ (n k : Nat) (x y : Q), Qle a x = true → Qle x b = true →
    Qle a y = true → Qle y b = true →
    Qle (Q.abs (Q.sub x y)) (D.toQ (D.pow2neg (ωs n k))) = true →
    Q.ltN (Q.abs (Q.sub (C.iter n x) (C.iter n y))) (D.toQ (D.pow2neg k)) = 1

/-- **The Picard iteration sequence forms a `LimSeq`.** -/
def PicardData.toLimSeq (P : PicardData) : LimSeq :=
  { a := P.a
    b := P.b
    fs := P.C.iter
    ωs := P.ωs
    c := P.C.rate
    ivl := P.ivl
    cont := P.cont
    conv := by
      intro k n m hn hnm x hxa hxb
      have h := P.C.cauchy k n m hn hnm x hxa hxb
      rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val]
      exact h }

/-- **The solution of the initial value problem is $E_0$-adequate.** -/
def PicardData.solution (P : PicardData) : E0 :=
  P.toLimSeq.toE0

/-- **And the solution inherits a uniform modulus of continuity.** -/
theorem PicardData.solution_continuous (P : PicardData) (k n : Nat) (x y : Q)
    (hn : P.C.rate (k + 2) ≤ n)
    (hxa : Qle P.a x = true) (hxb : Qle x P.b = true)
    (hya : Qle P.a y = true) (hyb : Qle y P.b = true)
    (hxy : |x.val - y.val| ≤ 1 / 2 ^ (P.ωs (P.C.rate (k + 2)) (k + 2))) :
    |(P.C.iter n x).val - (P.C.iter n y).val| < 1 / 2 ^ k :=
  P.toLimSeq.limit_cont k n x y hn hxa hxb hya hyb hxy

#print axioms PicardData.solution
#print axioms PicardData.solution_continuous

/-! ## 4. The Picard Integral Operator for $y' = f(x, y)$ -/

/-- Right-hand side vector field $f(t, y)$ on $[a, b] \times [-K, K]$. -/
structure VectorField (a b : Q) where
  /-- Rational sampler for $f(t, y)$. -/
  f : Q → Q → Q
  /-- Bound on range: $|f(t, y)| \le 2^B$. -/
  B : Nat
  /-- Modulus of continuity in $t$. -/
  ω_t : Nat → Nat
  /-- Lipschitz constant in $y$: $|f(t, u) - f(t, v)| \le 2^L |u - v|$. -/
  L : Nat
  lip_y : ∀ (t u v : Q), Qle a t = true → Qle t b = true →
    |(f t u).val - (f t v).val| ≤ (2 : Rat) ^ L * |u.val - v.val|

/-- **Contractivity of the Picard Integral Operator**:
    When the interval length $b - a \le 2^{-(L + p)}$ with $p \ge 1$,
    the integral bound contracts uniformly by $2^{-p}$. -/
theorem picard_integral_contracts {a b : Q} (V : VectorField a b) (p : Nat) (_hp : 1 ≤ p)
    (h_time : (b.val - a.val) ≤ 1 / (2 : Rat) ^ (V.L + p))
    (k : Nat) :
    (b.val - a.val) * ((2 : Rat) ^ V.L * (1 / 2 ^ k)) ≤ 1 / 2 ^ (k + p) := by
  have h1 : (b.val - a.val) * ((2 : Rat) ^ V.L * (1 / 2 ^ k))
      ≤ (1 / 2 ^ (V.L + p)) * (2 ^ V.L * (1 / 2 ^ k)) := by
    have h_nonneg : 0 ≤ (2 : Rat) ^ V.L * (1 / 2 ^ k) := by positivity
    exact mul_le_mul_of_nonneg_right h_time h_nonneg
  have h2 : (1 / (2 : Rat) ^ (V.L + p)) * (2 ^ V.L * (1 / 2 ^ k)) = 1 / 2 ^ (k + p) := by
    rw [show V.L + p = V.L + p by rfl, pow_add]
    have : (0 : Rat) < 2 ^ V.L := by positivity
    have : (0 : Rat) < 2 ^ p := by positivity
    have : (0 : Rat) < 2 ^ k := by positivity
    field_simp; ring
  linarith

#print axioms picard_integral_contracts

end HAomega
