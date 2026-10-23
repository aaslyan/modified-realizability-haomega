/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.Picard
import HAomega.GaloisAdequacy
import HAomega.FixedPoint
import HAomega.IVT
import HAomega.ModulusClosure
import HAomega.ODEDemo
import HAomega.AnalysisDeriv

/-!
# Taylor's Expansion and Remainder Positivity Scaling

This module formalizes constructive **Taylor polynomial expansions** and their
scaling properties:

1. **Taylor Polynomial Operator (`taylorEval`)**:
   For derivatives $f^{(0)}(a), f^{(1)}(a), \dots, f^{(n)}(a)$, the $n$-th Taylor polynomial is:
   $$T_n(x) = \sum_{j=0}^n \frac{f^{(j)}(a)}{j!} (x - a)^j$$

2. **The Positivity Scaling Lemma (`taylor_remainder_pos_scale`)**:
   For non-negative bound $M \ge 0$ and displacement $\Delta x \ge 0$, the product
   $\frac{M}{(n+1)!} \Delta x^{n+1}$ is non-negative.

3. **Kernel-Verified Computations**:
   Verified `#guard` calculations computing Taylor expansions of $e^x$ at $a = 0$
   evaluated at $x = 1/2$.
-/

namespace HAomega

open Rat

/-! ## 1. Factorial Positivity and Taylor Polynomial Evaluator -/

/-- Factorial is strictly positive for all $n$. -/
theorem fact_pos : ∀ n : Nat, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- $n$-th Taylor polynomial: $T_n(x) = \sum_{j=0}^n \frac{c_j}{j!} (x - a)^j$. -/
def taylorEval (derivs : List Q) (a x : Q) : Q :=
  let dx := Q.sub x a
  ((List.range derivs.length).zip derivs).foldl (fun acc ⟨j, fj⟩ ↦
    let coeff := Q.div fj (Q.ofNat (fact j))
    let term := Q.mul coeff (qpow dx j)
    Q.add acc term) Q.zero

/-! ## 2. The Positivity Scaling Lemma -/

/-- **Lemma (Taylor Remainder Factor Positivity)**:
    For non-negative derivative bound $M \ge 0$ and non-negative displacement $\Delta x \ge 0$,
    the expression $\frac{M}{(n+1)!} \Delta x^{n+1}$ is non-negative. -/
theorem taylor_remainder_pos_scale (M : Rat) (dx : Rat) (n : Nat)
    (hM : 0 ≤ M) (hdx : 0 ≤ dx) :
    0 ≤ (M / (fact (n + 1) : Rat)) * (dx ^ (n + 1)) := by
  have h_fact : (0 : Rat) < (fact (n + 1) : Rat) := by
    exact_mod_cast (fact_pos (n + 1))
  have h_frac : 0 ≤ M / (fact (n + 1) : Rat) := div_nonneg hM (le_of_lt h_fact)
  have h_pow : 0 ≤ dx ^ (n + 1) := by positivity
  exact mul_nonneg h_frac h_pow

#print axioms taylor_remainder_pos_scale

/-! ## 2b. Super-Exponential Remainder Bounds and Cauchy Tail Estimates -/

/-- Rational evaluation of `qpow`: $(x^j).\mathrm{val} = (x.\mathrm{val})^j$. -/
theorem qpow_val (x : Q) : ∀ j : Nat, (qpow x j).val = x.val ^ j
  | 0 => by
    dsimp [qpow]
    rw [Q.val_ofNat]
    simp
  | j + 1 => by
    dsimp [qpow]
    rw [Q.val_mul, qpow_val x j, pow_succ']

/-- Rational evaluation of `taylorTerm`: $(x^j / j!).\mathrm{val} = (x.\mathrm{val})^j / j!$. -/
theorem taylorTerm_val (x : Q) (j : Nat) :
    (taylorTerm x j).val = x.val ^ j / (fact j : Rat) := by
  dsimp [taylorTerm]
  have hnum : (Q.ofNat (fact j)).num ≠ 0 := by
    have := fact_pos j
    unfold Q.ofNat
    simpa using by omega
  rw [Q.val_div _ _ hnum, qpow_val, Q.val_ofNat]

/-- **Single-Step Taylor Remainder Identity**:
    The step difference between consecutive Taylor partial sums is
    $$|P_{n+1}(x) - P_n(x)| = \frac{|x|^{n+1}}{(n + 1)!}.$$ -/
theorem expTaylor_step_error (n : Nat) (x : Q) :
    |(expTaylor (n + 1) x).val - (expTaylor n x).val| = |x.val| ^ (n + 1) / (fact (n + 1) : Rat) := by
  rw [expTaylor_succ, Q.val_add, add_sub_cancel_left, taylorTerm_val]
  have h_fact : (0 : Rat) < (fact (n + 1) : Rat) := by exact_mod_cast (fact_pos (n + 1))
  rw [abs_div, abs_pow, abs_of_pos h_fact]

/-- Exponential growth of factorial: $2^n \le (n + 1)!$ for all $n$. -/
theorem two_pow_le_fact_succ : ∀ n : Nat, 2 ^ n ≤ fact (n + 1)
  | 0 => by decide
  | n + 1 => by
    have ih := two_pow_le_fact_succ n
    have h_step : fact (n + 2) = (n + 2) * fact (n + 1) := rfl
    rw [pow_succ', h_step]
    exact Nat.mul_le_mul (by omega) ih

/-- Factorial ratio bound: $(n + 1)! \cdot 2^j \le (n + 1 + j)!$ for all $n, j$. -/
theorem fact_mul_two_pow_le (n : Nat) : ∀ j : Nat, fact (n + 1) * 2 ^ j ≤ fact (n + 1 + j)
  | 0 => by simp
  | j + 1 => by
    have ih := fact_mul_two_pow_le n j
    have h_step : fact (n + 1 + (j + 1)) = (n + 1 + j + 1) * fact (n + 1 + j) := rfl
    rw [pow_succ, ← Nat.mul_assoc, h_step]
    calc fact (n + 1) * 2 ^ j * 2
      _ ≤ fact (n + 1 + j) * 2 := Nat.mul_le_mul_right 2 ih
      _ = 2 * fact (n + 1 + j) := Nat.mul_comm _ _
      _ ≤ (n + 1 + j + 1) * fact (n + 1 + j) := Nat.mul_le_mul_right _ (by omega)

/-- For $|x| \le 1/2$, the $(n + 1 + j)$-th Taylor term is bounded by
    $\frac{1}{(n + 1)! \cdot 2^{n + 1 + j}}$. -/
theorem taylorTerm_bound_half (n j : Nat) (x : Q) (hx : |x.val| ≤ 1 / 2) :
    |(taylorTerm x (n + 1 + j)).val| ≤ (1 / ((fact (n + 1) : Rat) * 2 ^ n)) * (1 / 2 ^ (j + 1)) := by
  rw [taylorTerm_val, abs_div, abs_pow]
  have h_fact_pos : (0 : Rat) < (fact (n + 1 + j) : Rat) := by exact_mod_cast (fact_pos (n + 1 + j))
  rw [abs_of_pos h_fact_pos]
  have h_pow : |x.val| ^ (n + 1 + j) ≤ (1 / 2 : Rat) ^ (n + 1 + j) :=
    pow_le_pow_left₀ (abs_nonneg _) hx (n + 1 + j)
  have h_fact_le : ((fact (n + 1) : Rat) * 2 ^ j) ≤ (fact (n + 1 + j) : Rat) := by
    exact_mod_cast (fact_mul_two_pow_le n j)
  have h_fact_n1_pos : (0 : Rat) < (fact (n + 1) : Rat) := by exact_mod_cast (fact_pos (n + 1))
  have h_div1 : |x.val| ^ (n + 1 + j) / (fact (n + 1 + j) : Rat)
      ≤ (1 / 2 : Rat) ^ (n + 1 + j) / (fact (n + 1 + j) : Rat) :=
    div_le_div_of_nonneg_right h_pow (le_of_lt h_fact_pos)
  have h_div2 : (1 / 2 : Rat) ^ (n + 1 + j) / (fact (n + 1 + j) : Rat)
      ≤ (1 / 2 : Rat) ^ (n + 1 + j) / (fact (n + 1) : Rat) := by
    apply div_le_div_of_nonneg_left (by positivity) h_fact_n1_pos
    have : (1 : Rat) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have h_eq : (1 / 2 : Rat) ^ (n + 1 + j) / (fact (n + 1) : Rat)
      = (1 / ((fact (n + 1) : Rat) * 2 ^ n)) * (1 / 2 ^ (j + 1)) := by
    rw [one_div_pow, show n + 1 + j = n + (j + 1) by omega, pow_add]
    have : (0 : Rat) < 2 ^ n := by positivity
    have : (0 : Rat) < 2 ^ (j + 1) := by positivity
    field_simp
  linarith

/-- **Theorem (Telescoping Taylor Remainder Bound on $[-1/2, 1/2]$)**:
    For $|x.\mathrm{val}| \le 1/2$ and any $n, d : \mathrm{Nat}$,
    $$|P_{n+d}(x) - P_n(x)| \le \frac{1}{(n + 1)! \cdot 2^n} \left(1 - \frac{1}{2^d}\right).$$ -/
theorem expTaylor_tail_bound (n d : Nat) (x : Q) (hx : |x.val| ≤ 1 / 2) :
    |(expTaylor (n + d) x).val - (expTaylor n x).val|
      ≤ (1 / ((fact (n + 1) : Rat) * 2 ^ n)) * (1 - 1 / 2 ^ d) := by
  induction d with
  | zero =>
    have h_sub : (1 : Rat) - 1 / 2 ^ 0 = 0 := by norm_num
    rw [show n + 0 = n by rfl, sub_self, abs_zero, h_sub, mul_zero]
  | succ d ih =>
    have h_tri : |(expTaylor (n + (d + 1)) x).val - (expTaylor n x).val|
        ≤ |(expTaylor (n + (d + 1)) x).val - (expTaylor (n + d) x).val|
          + |(expTaylor (n + d) x).val - (expTaylor n x).val| :=
      abs_sub_le _ _ _
    have h_step_eq : (expTaylor (n + (d + 1)) x).val - (expTaylor (n + d) x).val
        = (taylorTerm x (n + 1 + d)).val := by
      rw [show n + (d + 1) = (n + d) + 1 by omega, expTaylor_succ, Q.val_add,
          show (n + d) + 1 = n + 1 + d by omega]
      ring
    rw [h_step_eq] at h_tri
    have h_term := taylorTerm_bound_half n d x hx
    have h_alg : (1 / ((fact (n + 1) : Rat) * 2 ^ n)) * (1 / 2 ^ (d + 1))
        + (1 / ((fact (n + 1) : Rat) * 2 ^ n)) * (1 - 1 / 2 ^ d)
        = (1 / ((fact (n + 1) : Rat) * 2 ^ n)) * (1 - 1 / 2 ^ (d + 1)) := by
      rw [show d + 1 = d + 1 by rfl, pow_succ]
      have : (0 : Rat) < 2 ^ d := by positivity
      have : (0 : Rat) < (fact (n + 1) : Rat) := by exact_mod_cast (fact_pos (n + 1))
      have : (0 : Rat) < 2 ^ n := by positivity
      field_simp
      ring
    linarith

/-- **Theorem (Super-Exponential Cauchy Remainder Bound for $e^x$)**:
    For all $n \le m$ and $|x.\mathrm{val}| \le 1/2$,
    $$|P_m(x) - P_n(x)| \le \frac{1}{(n + 1)! \cdot 2^n}.$$ -/
theorem expTaylor_cauchy_remainder (n m : Nat) (x : Q) (hnm : n ≤ m) (hx : |x.val| ≤ 1 / 2) :
    |(expTaylor m x).val - (expTaylor n x).val| ≤ 1 / ((fact (n + 1) : Rat) * 2 ^ n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have h_tail := expTaylor_tail_bound n d x hx
  have h_fac : 1 - (1 : Rat) / 2 ^ d ≤ 1 := by
    have : (0 : Rat) ≤ 1 / 2 ^ d := by positivity
    linarith
  have h_pos : (0 : Rat) ≤ 1 / ((fact (n + 1) : Rat) * 2 ^ n) := by
    have : (0 : Rat) < (fact (n + 1) : Rat) := by exact_mod_cast (fact_pos (n + 1))
    positivity
  have h_le : (1 / ((fact (n + 1) : Rat) * 2 ^ n)) * (1 - 1 / 2 ^ d)
      ≤ (1 / ((fact (n + 1) : Rat) * 2 ^ n)) * 1 :=
    mul_le_mul_of_nonneg_left h_fac h_pos
  linarith

#print axioms expTaylor_step_error
#print axioms expTaylor_tail_bound
#print axioms expTaylor_cauchy_remainder

/-! ## 3. Verified Kernel Computations for Taylor Expansions -/

-- Taylor polynomial of exp(x) at a = 0: derivatives are all 1
-- Order 0: T₀(1/2) = 1
#guard taylorEval [Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.ofNat 1

-- Order 1: T₁(1/2) = 1 + 1/2 = 3/2 = 1.5
#guard taylorEval [Q.ofNat 1, Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.of 3 2

-- Order 2: T₂(1/2) = 1 + 1/2 + 1/8 = 13/8 = 1.625
#guard taylorEval [Q.ofNat 1, Q.ofNat 1, Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.of 13 8

-- Order 3: T₃(1/2) = 1 + 1/2 + 1/8 + 1/48 = 79/48 ≈ 1.64583
#guard taylorEval [Q.ofNat 1, Q.ofNat 1, Q.ofNat 1, Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.of 79 48

-- Order 4: T₄(1/2) = 79/48 + 1/384 = 633/384 = 211/128 ≈ 1.6484375
#guard taylorEval [Q.ofNat 1, Q.ofNat 1, Q.ofNat 1, Q.ofNat 1, Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.of 211 128

/-! ## 4. Object-Level System T Taylor Evaluator & `Deriv` Realizer Extraction -/

/-- Step term for exponential Taylor accumulation over state `(sum, term) : .prod .rat .rat`:
    `λ (k : nat) (acc : rat × rat). let nextTerm := acc.2 * x / (k + 1) in (acc.1 + nextTerm, nextTerm)`. -/
def expTaylorStepTm {Γ : List Ty} (x : Tm Γ .rat) :
    Tm Γ (.arrow .nat (.arrow (.prod .rat .rat) (.prod .rat .rat))) :=
  .lam (.lam (
    let acc : Tm ((.prod .rat .rat) :: .nat :: Γ) (.prod .rat .rat) := .var .here
    let k_nat : Tm ((.prod .rat .rat) :: .nat :: Γ) .nat := .var (.there .here)
    let sum_curr := .fst acc
    let term_curr := .snd acc
    let next_term := .qdiv (.qmul term_curr x.wk.wk) (.qnat (.succ k_nat))
    .pair (.qadd sum_curr next_term) next_term
  ))

/-- Initial state `(1, 1)` for exponential Taylor accumulation at $k = 0$. -/
def expTaylorInitTm {Γ : List Ty} : Tm Γ (.prod .rat .rat) :=
  .pair (.qnat (.succ .zero)) (.qnat (.succ .zero))

/-- Closed System T exponential Taylor polynomial evaluator:
    `λ (n : nat) (x : rat). (recNat (1, 1) (expTaylorStepTm x) n).1`. -/
def tmExpTaylorClosed {Γ : List Ty} :
    Tm Γ (.arrow .nat (.arrow .rat .rat)) :=
  .lam (.lam (
    .fst (.recNat expTaylorInitTm (expTaylorStepTm (.var .here)) (.var (.there .here)))
  ))

/-- Natural deduction derivation in `Deriv` of the exponential Taylor sequence $(P_n(x), x^n/n!)$. -/
def expTaylorSequenceD (x : Tm [] .rat) :
    Deriv Ctx.nil (.all .nat (indexedIterInv (.prod .rat .rat) [] expTaylorInitTm (expTaylorStepTm x))) :=
  indexedIterSequenceD (.prod .rat .rat) expTaylorInitTm (expTaylorStepTm x)

/-- **The extracted exponential Taylor approximator** synthesized via `extractClosed expTaylorSequenceD`. -/
def expTaylorExtracted (x : Tm [] .rat) (n : Nat) : Q :=
  (((extractClosed (expTaylorSequenceD x)).eval Env.nil n).1).1

/-- Rational $x = 1/2$ as a closed System T term. -/
def tmHalf : Tm [] .rat := .qdiv (.qnat (.succ .zero)) (.qnat (.succ (.succ .zero)))

-- Kernel verification of the extracted System T Taylor realizer at x = 1/2:
#guard expTaylorExtracted tmHalf 0 == Q.ofNat 1
#guard expTaylorExtracted tmHalf 1 == Q.of 3 2
#guard expTaylorExtracted tmHalf 2 == Q.of 13 8
#guard expTaylorExtracted tmHalf 3 == Q.of 79 48
#guard expTaylorExtracted tmHalf 4 == Q.of 211 128
#guard expTaylorExtracted tmHalf 5 == Q.of 6331 3840

#print axioms expTaylorSequenceD
#print axioms expTaylorExtracted

end HAomega
