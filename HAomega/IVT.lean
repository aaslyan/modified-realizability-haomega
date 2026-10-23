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

/-- Uniform grid step count: $N(k) = 2^{\omega(k)} \cdot (\lceil b - a \rceil + 1)$. -/
def ivtGridSteps (A : A0) (k : Nat) : Nat :=
  2 ^ (A.ω k) * (ceilNatQ A.len + 1)

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

/-! ## 1b. Concrete Instantiation on Uniform Grids (`IVTProblem`) -/

/-- The grid step count $N(k) = 2^{\omega(k)} (\lceil b - a \rceil + 1)$ is strictly positive. -/
theorem ivtGridSteps_pos (A : A0) (k : Nat) : 0 < ivtGridSteps A k := by
  unfold ivtGridSteps
  exact Nat.mul_pos (pow_pos (by decide) _) (Nat.succ_pos _)

/-- Rational value of the $j$-th grid point: $x_j = a + j \frac{b - a}{N}$. -/
theorem ivtGridPoint_val (A : A0) (N j : Nat) (hN : 0 < N) :
    (ivtGridPoint A N j).val = A.a.val + (j : Rat) * (A.b.val - A.a.val) / (N : Rat) := by
  unfold ivtGridPoint A0.len
  have hnum : (Q.ofNat N).num ≠ 0 := by
    unfold Q.ofNat
    simpa using by omega
  rw [Q.val_add, Q.val_div _ _ hnum, Q.val_mul, Q.val_ofNat, Q.val_sub, Q.val_ofNat]

/-- Every grid point $x_j$ for $0 \le j \le N$ lies inside $[a, b]$. -/
theorem ivtGridPoint_in_ivl (A : A0) (N j : Nat) (hN : 0 < N) (hj : j ≤ N) :
    Qle A.a (ivtGridPoint A N j) = true ∧ Qle (ivtGridPoint A N j) A.b = true := by
  have hivl : A.a.val < A.b.val := (Q.ltN_eq_one_iff _ _).mp A.ivl
  have hN_pos : (0 : Rat) < (N : Rat) := by exact_mod_cast hN
  have hj_le : (j : Rat) ≤ (N : Rat) := by exact_mod_cast hj
  have hj_nonneg : (0 : Rat) ≤ (j : Rat) := Nat.cast_nonneg j
  have h_frac_nonneg : 0 ≤ (j : Rat) * (A.b.val - A.a.val) / (N : Rat) := by
    apply div_nonneg
    · exact mul_nonneg hj_nonneg (by linarith)
    · exact le_of_lt hN_pos
  have h_frac_le : (j : Rat) * (A.b.val - A.a.val) / (N : Rat) ≤ A.b.val - A.a.val := by
    rw [div_le_iff₀ hN_pos]
    calc (j : Rat) * (A.b.val - A.a.val)
      _ ≤ (N : Rat) * (A.b.val - A.a.val) := mul_le_mul_of_nonneg_right hj_le (by linarith)
      _ = (A.b.val - A.a.val) * (N : Rat) := mul_comm _ _
  rw [Qle_eq_true_iff, Qle_eq_true_iff, ivtGridPoint_val A N j hN]
  exact ⟨by linarith, by linarith⟩

/-- Adjacent points on the `ivtGridSteps A k` grid are within $2^{-\omega(k)}$. -/
theorem ivtGridPoint_step_le (A : A0) (k j : Nat) :
    |(ivtGridPoint A (ivtGridSteps A k) j).val
      - (ivtGridPoint A (ivtGridSteps A k) (j + 1)).val| ≤ 1 / 2 ^ (A.ω k) := by
  have hN := ivtGridSteps_pos A k
  have hN_pos : (0 : Rat) < (ivtGridSteps A k : Rat) := by exact_mod_cast hN
  have hivl : A.a.val < A.b.val := (Q.ltN_eq_one_iff _ _).mp A.ivl
  rw [ivtGridPoint_val A _ j hN, ivtGridPoint_val A _ (j + 1) hN]
  have h_diff : A.a.val + (j : Rat) * (A.b.val - A.a.val) / (ivtGridSteps A k : Rat)
      - (A.a.val + ((j + 1 : Nat) : Rat) * (A.b.val - A.a.val) / (ivtGridSteps A k : Rat))
      = -((A.b.val - A.a.val) / (ivtGridSteps A k : Rat)) := by
    push_cast
    ring
  rw [h_diff, abs_neg, abs_of_pos (div_pos (by linarith) hN_pos)]
  have h_ceil := ceilNatQ_spec A.len
  have h_len : A.len.val = A.b.val - A.a.val := Q.val_sub _ _
  rw [h_len] at h_ceil
  have h_bound : (A.b.val - A.a.val) * 2 ^ (A.ω k) ≤ (ivtGridSteps A k : Rat) := by
    unfold ivtGridSteps
    push_cast
    have h_c1 : A.b.val - A.a.val ≤ (ceilNatQ A.len : Rat) + 1 := by linarith
    have h_pow_pos : (0 : Rat) ≤ 2 ^ (A.ω k) := by positivity
    calc (A.b.val - A.a.val) * 2 ^ (A.ω k)
      _ ≤ ((ceilNatQ A.len : Rat) + 1) * 2 ^ (A.ω k) :=
        mul_le_mul_of_nonneg_right h_c1 h_pow_pos
      _ = 2 ^ (A.ω k) * ((ceilNatQ A.len : Rat) + 1) := mul_comm _ _
  rw [div_le_div_iff₀ hN_pos (by positivity)]
  linarith

/-- **Theorem (Constructive Uniform-Grid Approximate IVT for `IVTProblem`)**:
    For every `P : IVTProblem` and every target precision $k$, the uniform grid
    with `N = ivtGridSteps P.A k` steps contains an adjacent bracket $(x_j, x_{j+1})$
    where both endpoints satisfy `isApproxZero P.A k`. -/
theorem IVTProblem.grid_approx_zero (P : IVTProblem) (k : Nat) :
    ∃ j, j < ivtGridSteps P.A k ∧
      isApproxZero P.A k (ivtGridPoint P.A (ivtGridSteps P.A k) j) ∧
      isApproxZero P.A k (ivtGridPoint P.A (ivtGridSteps P.A k) (j + 1)) := by
  set N := ivtGridSteps P.A k
  have hN : 0 < N := ivtGridSteps_pos P.A k
  set M := N - 1
  have hMN : M + 1 = N := Nat.sub_add_cancel hN
  have hx_in : ∀ j, j ≤ M + 1 →
      Qle P.A.a (ivtGridPoint P.A N j) = true ∧ Qle (ivtGridPoint P.A N j) P.A.b = true := by
    intro j hj
    exact ivtGridPoint_in_ivl P.A N j hN (by omega)
  have h0_val : (ivtGridPoint P.A N 0).val = P.A.a.val := by
    rw [ivtGridPoint_val P.A N 0 hN]
    simp
  have hN_val : (ivtGridPoint P.A N (M + 1)).val = P.A.b.val := by
    rw [hMN, ivtGridPoint_val P.A N N hN]
    have hN_ne : (N : Rat) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
    field_simp
    ring
  have hivl : P.A.a.val ≤ P.A.b.val := le_of_lt ((Q.ltN_eq_one_iff _ _).mp P.A.ivl)
  have h0_f : (P.A.f (ivtGridPoint P.A N 0)).val = (P.A.f P.A.a).val := by
    have hin := hx_in 0 (by omega)
    exact f_val_congr P.A ((Qle_eq_true_iff _ _).mp hin.1) ((Qle_eq_true_iff _ _).mp hin.2)
      le_rfl hivl h0_val
  have hN_f : (P.A.f (ivtGridPoint P.A N (M + 1))).val = (P.A.f P.A.b).val := by
    have hin := hx_in (M + 1) le_rfl
    exact f_val_congr P.A ((Qle_eq_true_iff _ _).mp hin.1) ((Qle_eq_true_iff _ _).mp hin.2)
      hivl le_rfl hN_val
  have h0 : (P.A.f (ivtGridPoint P.A N 0)).val ≤ 0 := by linarith [P.h_neg]
  have hM1 : 0 ≤ (P.A.f (ivtGridPoint P.A N (M + 1))).val := by linarith [P.h_pos]
  have h_step : ∀ j, j ≤ M →
      |(ivtGridPoint P.A N j).val - (ivtGridPoint P.A N (j + 1)).val| ≤ 1 / 2 ^ (P.A.ω k) :=
    fun j _ ↦ ivtGridPoint_step_le P.A k j
  obtain ⟨j, hj_le, hxj, hxjp1⟩ := approx_ivt_thm P.A k (ivtGridPoint P.A N) M hx_in h0 hM1 h_step
  have hin_j := hx_in j (by omega)
  have hin_jp1 := hx_in (j + 1) (by omega)
  exact ⟨j, by omega, ⟨hin_j.1, hin_j.2, hxj⟩, ⟨hin_jp1.1, hin_jp1.2, hxjp1⟩⟩

#print axioms IVTProblem.grid_approx_zero

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
