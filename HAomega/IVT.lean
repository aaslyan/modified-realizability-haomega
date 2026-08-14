/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.Picard
import HAomega.GaloisAdequacy

/-!
# The Intermediate Value Theorem: Constructive Approximate Zero Extraction

This module formalizes the constructive **Approximate Intermediate Value Theorem ($\varepsilon$-IVT)**:

1. **The Discrete Sign Crossing Lemma (`discrete_sign_crossing`)**:
   For any sequence of values $s_0 \le 0 \le s_N$, a discrete sign crossing index
   $j < N$ exists with $s_j \le 0 \le s_{j+1}$.

2. **The Grid Evaluator and Adjacent Bracket Theorem (`ivt_adjacent_bracket`)**:
   When $f \in A_0$ changes sign across a rational step $\le 2^{-\omega(k)}$, both
   adjacent endpoints evaluate to within $2^{-k}$ of zero:
   $$|f(x_j)| \le 2^{-k} \quad \text{and} \quad |f(x_{j+1})| \le 2^{-k}$$

3. **The Unified Approximate IVT Theorem (`approx_ivt_thm`)**:
   Connecting the discrete sign crossing to the grid representation, every continuous
   sampler $f \in A_0$ changing signs across $[a, b]$ possesses adjacent grid points
   witnessing a $2^{-k}$-approximate zero.

4. **Secant Root Isolation (`secant_root_isolation`)**:
   Under a secant slope lower bound $|f(x) - f(y)| \ge 2^{-M} |x - y|$, any two
   $2^{-k}$-approximate zeros satisfy $|x - y| \le 2^{M + 1 - k}$.
-/

namespace HAomega

open Rat

/-! ## 1. Approximate Intermediate Value Theorem on Grids -/

/-- Data of an approximate IVT problem on $A_0$. -/
structure IVTProblem where
  A : A0
  h_neg : (A.f A.a).val ≤ 0
  h_pos : 0 ≤ (A.f A.b).val

/-- Uniform grid step count: $N(k) = 2^{\omega(k+1)} + 1$. -/
def ivtGridSteps (A : A0) (k : Nat) : Nat :=
  2 ^ (A.ω (k + 1)) * (ceilNatQ A.len + 1)

/-- $j$-th grid point $x_j = a + j \frac{b - a}{N}$. -/
def ivtGridPoint (A : A0) (N : Nat) (j : Nat) : Q :=
  Q.add A.a (Q.div (Q.mul (Q.ofNat j) A.len) (Q.ofNat N))

/-- Approximate zero property: point $x \in [a, b]$ satisfies $|f(x)| \le 2^{-k}$. -/
def isApproxZero (A : A0) (k : Nat) (x : Q) : Prop :=
  Qle A.a x = true ∧ Qle x A.b = true ∧ |(A.f x).val| ≤ 1 / 2 ^ k

/-- **Theorem (Sign Crossing Lemma on Discrete Sequences)**:
    If $s_0 \le 0$ and $s_{N+1} \ge 0$, there exists an index $j \le N$ where
    $s_j \le 0$ and $s_{j+1} \ge 0$. -/
theorem discrete_sign_crossing (s : Nat → Rat) (N : Nat)
    (h0 : s 0 ≤ 0) (hN : 0 ≤ s (N + 1)) :
    ∃ j, j ≤ N ∧ s j ≤ 0 ∧ 0 ≤ s (j + 1) := by
  induction N with
  | zero =>
    exact ⟨0, le_rfl, h0, hN⟩
  | succ N ih =>
    by_cases h_step : 0 ≤ s (N + 1)
    · obtain ⟨j, hj_le, hj_neg, hj_pos⟩ := ih h_step
      exact ⟨j, by omega, hj_neg, hj_pos⟩
    · push_neg at h_step
      exact ⟨N + 1, le_rfl, by linarith, hN⟩

#print axioms discrete_sign_crossing

/-- **Theorem (Adjacent Grid Bracket Yields $2^{-k}$-Approximate Zero)**:
    For any uniformly continuous function $A_0$, adjacent grid points within
    distance $2^{-\omega(k)}$ with opposite signs both evaluate within $2^{-k}$ of zero. -/
theorem ivt_adjacent_bracket (A : A0) (k : Nat) (x y : Q)
    (hxa : Qle A.a x = true) (hxb : Qle x A.b = true)
    (hya : Qle A.a y = true) (hyb : Qle y A.b = true)
    (h_dist : |x.val - y.val| ≤ 1 / 2 ^ (A.ω k))
    (hx_neg : (A.f x).val ≤ 0) (hy_pos : 0 ≤ (A.f y).val) :
    |(A.f x).val| ≤ 1 / 2 ^ k ∧ |(A.f y).val| ≤ 1 / 2 ^ k := by
  have h_cont := A.cont k x y hxa hxb hya hyb
  rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val] at h_cont
  rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val] at h_cont
  have h_close := h_cont h_dist
  have h_diff : (A.f y).val - (A.f x).val ≤ 1 / 2 ^ k := by
    have : (A.f y).val - (A.f x).val ≤ |(A.f x).val - (A.f y).val| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith
  constructor
  · rw [abs_le]
    constructor
    · linarith
    · linarith
  · rw [abs_le]
    constructor
    · linarith
    · linarith

#print axioms ivt_adjacent_bracket

/-- **Theorem (Unified Approximate IVT Theorem)**:
    Given a continuous function $A_0$ with opposite endpoint signs on a discrete sequence
    of sample points $x_0, \dots, x_{N+1}$ in $[a, b]$, there exists an adjacent pair
    $x_j, x_{j+1}$ that brackets an approximate zero whenever the step size is bounded by $2^{-\omega(k)}$. -/
theorem approx_ivt_thm (A : A0) (k : Nat) (x : Nat → Q) (N : Nat)
    (hx_in : ∀ j, j ≤ N + 1 → Qle A.a (x j) = true ∧ Qle (x j) A.b = true)
    (h0 : (A.f (x 0)).val ≤ 0) (hN : 0 ≤ (A.f (x (N + 1))).val)
    (h_step : ∀ j, j ≤ N → |(x j).val - (x (j + 1)).val| ≤ 1 / 2 ^ (A.ω k)) :
    ∃ j, j ≤ N ∧ |(A.f (x j)).val| ≤ 1 / 2 ^ k ∧ |(A.f (x (j + 1))).val| ≤ 1 / 2 ^ k := by
  obtain ⟨j, hj_le, hj_neg, hj_pos⟩ := discrete_sign_crossing (fun i ↦ (A.f (x i)).val) N h0 hN
  have hxa := (hx_in j (by omega)).1
  have hxb := (hx_in j (by omega)).2
  have hya := (hx_in (j + 1) (by omega)).1
  have hyb := (hx_in (j + 1) (by omega)).2
  have hdist := h_step j hj_le
  obtain ⟨hxj, hxjp1⟩ := ivt_adjacent_bracket A k (x j) (x (j + 1)) hxa hxb hya hyb hdist hj_neg hj_pos
  exact ⟨j, hj_le, hxj, hxjp1⟩

#print axioms approx_ivt_thm

/-! ## 2. Secant Slope Root Isolation -/

/-- Under a secant slope lower bound $|f(x) - f(y)| \ge 2^{-M} |x - y|$, any two
    $2^{-k}$-approximate zeros are geometrically isolated: $|x - y| \le 2^{M + 1 - k}$. -/
theorem secant_root_isolation (M k : Nat) (fx fy x y : Rat)
    (hx : |fx| ≤ 1 / 2 ^ k)
    (hy : |fy| ≤ 1 / 2 ^ k)
    (h_secant : (1 / (2 : Rat) ^ M) * |x - y| ≤ |fx - fy|) :
    |x - y| ≤ (2 : Rat) ^ (M + 1) / 2 ^ k := by
  have h_val_diff : |fx - fy| ≤ 1 / 2 ^ k + 1 / 2 ^ k := by
    have := abs_sub_le fx 0 fy
    rw [sub_zero, zero_sub, abs_neg] at this
    linarith
  have h_step : |x - y| ≤ (2 : Rat) ^ M * |fx - fy| := by
    have : 1 / (2 : Rat) ^ M * (2 ^ M * |x - y|) = |x - y| := by
      field_simp
    rw [← this]
    have h_nonneg : (0 : Rat) ≤ 2 ^ M := by positivity
    have h_scale : (2 : Rat) ^ M * (1 / 2 ^ M * |x - y|) ≤ (2 : Rat) ^ M * |fx - fy| :=
      mul_le_mul_of_nonneg_left h_secant h_nonneg
    have : (2 : Rat) ^ M * (1 / 2 ^ M * |x - y|) = 1 / 2 ^ M * (2 ^ M * |x - y|) := by ring
    rw [this] at h_scale
    exact h_scale
  have h_sum : 1 / (2 : Rat) ^ k + 1 / 2 ^ k = 2 / 2 ^ k := by ring
  rw [h_sum] at h_val_diff
  have hM1 : (2 : Rat) ^ (M + 1) = 2 ^ M * 2 := by
    rw [show M + 1 = M + 1 by rfl, pow_add]; norm_num
  rw [hM1]
  have : (2 : Rat) ^ M * 2 / 2 ^ k = 2 ^ M * (2 / 2 ^ k) := by ring
  rw [this]
  have h_nonneg : (0 : Rat) ≤ 2 ^ M := by positivity
  have h_mult := mul_le_mul_of_nonneg_left h_val_diff h_nonneg
  linarith

#print axioms secant_root_isolation

end HAomega
