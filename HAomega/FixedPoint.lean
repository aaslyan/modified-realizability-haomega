/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.Picard
import HAomega.GaloisAdequacy
import HAomega.AnalysisDeriv

/-!
# Non-Expansive Maps and Krasnoselskii–Mann Iteration

This module formalizes the data structures for **non-expansive mappings** ($L = 1$,
$|T(x) - T(y)| \le |x - y|$) and their averaged iterations:

1. **Non-Expansive Maps (`NonExpansiveMap`)**:
   Self-maps $T : [a, b] \to [a, b]$ with Lipschitz constant $L = 1$.

2. **Krasnoselskii–Mann Averaged Operator (`NonExpansiveMap.avg`)**:
   $$T_{1/2}(x) = \frac{1}{2} x + \frac{1}{2} T(x)$$
   We prove the identity $(T_{1/2}(x)).\mathrm{val} - x.\mathrm{val} = \frac{1}{2}((T(x)).\mathrm{val} - x.\mathrm{val})$
   (`step_eq_half_residual`).

3. **Krasnoselskii–Mann Sequence (`NonExpansiveMap.kmIter`)**:
   The sequence $x_n = T_{1/2}^n(x_0)$.
-/

namespace HAomega

open Rat

/-- Data of a non-expansive self-map $T : [a, b] \to [a, b]$. -/
structure NonExpansiveMap (a b : Q) where
  T : Q → Q
  /-- Non-expansiveness: $|T(x) - T(y)| \le |x - y|$. -/
  nonexp : ∀ x y : Q, Qle a x = true → Qle x b = true →
    Qle a y = true → Qle y b = true →
    |(T x).val - (T y).val| ≤ |x.val - y.val|
  /-- Maps $[a, b]$ to itself. -/
  maps_to : ∀ x : Q, Qle a x = true → Qle x b = true →
    Qle a (T x) = true ∧ Qle (T x) b = true

/-- The Krasnoselskii–Mann averaged operator $T_{1/2}(x) = \frac{1}{2} x + \frac{1}{2} T(x)$. -/
def NonExpansiveMap.avg {a b : Q} (N : NonExpansiveMap a b) (x : Q) : Q :=
  Q.div (Q.add x (N.T x)) (Q.ofNat 2)

/-- Krasnoselskii–Mann iteration sequence $x_n = T_{1/2}^n(x_0)$. -/
def NonExpansiveMap.kmIter {a b : Q} (N : NonExpansiveMap a b) (x0 : Q) : Nat → Q
  | 0 => x0
  | n + 1 => N.avg (N.kmIter x0 n)

/-- **Theorem (Averaged Step Equals Half Fixed-Point Residual)**:
    $x_{n+1} - x_n = \frac{1}{2}(T(x_n) - x_n)$. -/
theorem NonExpansiveMap.step_eq_half_residual {a b : Q} (N : NonExpansiveMap a b)
    (x : Q) :
    (N.avg x).val - x.val = (1 / 2 : Rat) * ((N.T x).val - x.val) := by
  dsimp [avg]
  rw [Q.val_div _ _ (by decide)]
  rw [Q.val_add, Q.val_ofNat]
  push_cast
  ring

#print axioms NonExpansiveMap.step_eq_half_residual

/-- Explicit rate of asymptotic regularity bound: $\Phi(k) = 4 (D + 1)^2 \cdot 4^k$. -/
def kmRate (diamSq : Nat) (k : Nat) : Nat :=
  4 * (diamSq + 1) * 4 ^ k

/-- Dividing a summed residual bound by $n$. -/
theorem residual_div_bound (diam : Rat) (k n : Nat) (hn : 0 < n)
    (h_sum : (n : Rat) * (1 / 2 ^ (2 * k + 2)) ≤ diam ^ 2) :
    1 / 2 ^ (2 * k + 2) ≤ diam ^ 2 / (n : Rat) := by
  have hn_pos : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  rw [le_div_iff₀ hn_pos, mul_comm]
  exact h_sum

#print axioms residual_div_bound

/-! ## 2. Self-Mapping, Monotonicity, and Quadratic Parallelogram Descent -/

/-- Value characterization of `avg`: $(T_{1/2}(x)).\mathrm{val} = (x.\mathrm{val} + (T x).\mathrm{val}) / 2$. -/
theorem NonExpansiveMap.val_avg {a b : Q} (N : NonExpansiveMap a b) (x : Q) :
    (N.avg x).val = (x.val + (N.T x).val) / 2 := by
  dsimp [avg]
  rw [Q.val_div _ _ (by decide), Q.val_add, Q.val_ofNat]
  push_cast
  ring

/-- The averaged operator $T_{1/2}$ maps $[a, b]$ to $[a, b]$. -/
theorem NonExpansiveMap.avg_maps_to {a b : Q} (N : NonExpansiveMap a b) (x : Q)
    (hxa : Qle a x = true) (hxb : Qle x b = true) :
    Qle a (N.avg x) = true ∧ Qle (N.avg x) b = true := by
  obtain ⟨hTa, hTb⟩ := N.maps_to x hxa hxb
  rw [Qle_eq_true_iff] at hxa hxb hTa hTb ⊢
  rw [Qle_eq_true_iff, N.val_avg]
  exact ⟨by linarith, by linarith⟩

/-- Every Krasnoselskii–Mann iterate $x_n$ remains in $[a, b]$. -/
theorem NonExpansiveMap.kmIter_maps_to {a b : Q} (N : NonExpansiveMap a b) (x0 : Q)
    (h0a : Qle a x0 = true) (h0b : Qle x0 b = true) (n : Nat) :
    Qle a (N.kmIter x0 n) = true ∧ Qle (N.kmIter x0 n) b = true := by
  induction n with
  | zero => exact ⟨h0a, h0b⟩
  | succ n ih => exact N.avg_maps_to (N.kmIter x0 n) ih.1 ih.2

/-- **Endpoint Sign Property (Brouwer 1D Boundary Condition)**:
    For any self-map $T : [a, b] \to [a, b]$, the displacement $T(x) - x$ is
    non-negative at $a$ and non-positive at $b$. -/
theorem NonExpansiveMap.endpoint_displacement_signs {a b : Q} (N : NonExpansiveMap a b)
    (hab : Qle a b = true) :
    0 ≤ (N.T a).val - a.val ∧ (N.T b).val - b.val ≤ 0 := by
  have ha := (N.maps_to a ((Qle_eq_true_iff a a).mpr le_rfl) hab).1
  have hb := (N.maps_to b hab ((Qle_eq_true_iff b b).mpr le_rfl)).2
  rw [Qle_eq_true_iff] at ha hb
  exact ⟨by linarith, by linarith⟩

/-- **Monotonicity of the Averaged Operator $T_{1/2}$ on $\mathbb{Q}$**:
    Because $|T(y) - T(x)| \le y - x$ for $x \le y$, the averaged operator
    $T_{1/2}(x) = \frac{1}{2}(x + T(x))$ is order-preserving on $[a, b]$. -/
theorem NonExpansiveMap.avg_monotone {a b : Q} (N : NonExpansiveMap a b) (x y : Q)
    (hxa : Qle a x = true) (hxb : Qle x b = true)
    (hya : Qle a y = true) (hyb : Qle y b = true)
    (hxy : x.val ≤ y.val) :
    (N.avg x).val ≤ (N.avg y).val := by
  have h_ne := N.nonexp x y hxa hxb hya hyb
  have h_yx : |x.val - y.val| = y.val - x.val := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [h_yx] at h_ne
  have h_upper := (abs_le.mp h_ne).2
  rw [N.val_avg, N.val_avg]
  linarith

/-- Starting from the left endpoint $x_0 = a$, the KM trajectory is monotonically non-decreasing:
    $x_n.\mathrm{val} \le x_{n+1}.\mathrm{val}$ for all $n$. -/
theorem NonExpansiveMap.kmIter_mono_from_left {a b : Q} (N : NonExpansiveMap a b)
    (hab : Qle a b = true) (n : Nat) :
    (N.kmIter a n).val ≤ (N.kmIter a (n + 1)).val := by
  have haa : Qle a a = true := (Qle_eq_true_iff a a).mpr le_rfl
  induction n with
  | zero =>
    dsimp [kmIter]
    have h_step := N.step_eq_half_residual a
    have h_sign := (N.endpoint_displacement_signs hab).1
    linarith
  | succ n ih =>
    dsimp [kmIter]
    obtain ⟨hna, hnb⟩ := N.kmIter_maps_to a haa hab n
    obtain ⟨hn1a, hn1b⟩ := N.kmIter_maps_to a haa hab (n + 1)
    exact N.avg_monotone (N.kmIter a n) (N.kmIter a (n + 1)) hna hnb hn1a hn1b ih

/-- **Quadratic Parallelogram Identity for Averaged Steps**:
    For any $u, v \in \mathbb{Q}$ with $|v| \le |u|$,
    $\left(\frac{u + v}{2}\right)^2 + \left(\frac{v - u}{2}\right)^2 \le u^2$. -/
theorem parallelogram_contraction_step (u v : Rat) (h_ne : |v| ≤ |u|) :
    ((u + v) / 2) ^ 2 + ((v - u) / 2) ^ 2 ≤ u ^ 2 := by
  have h_sq : v ^ 2 ≤ u ^ 2 := by
    have h1 : |v| * |v| ≤ |u| * |u| := mul_le_mul h_ne h_ne (abs_nonneg v) (abs_nonneg u)
    have hv : |v| * |v| = v ^ 2 := by rw [← sq, sq_abs]
    have hu : |u| * |u| = u ^ 2 := by rw [← sq, sq_abs]
    linarith
  have h_id : ((u + v) / 2) ^ 2 + ((v - u) / 2) ^ 2 = (u ^ 2 + v ^ 2) / 2 := by ring
  linarith

/-- **Theorem (Krasnoselskii–Mann Single-Step Quadratic Descent)**:
    For any fixed point $p \in [a, b]$ with $(T(p)).\mathrm{val} = p.\mathrm{val}$ and any $x \in [a, b]$,
    $$|(T_{1/2}(x)).\mathrm{val} - p.\mathrm{val}|^2 + \frac{1}{4}|(T(x)).\mathrm{val} - x.\mathrm{val}|^2 \le |x.\mathrm{val} - p.\mathrm{val}|^2.$$ -/
theorem NonExpansiveMap.km_quadratic_step {a b : Q} (N : NonExpansiveMap a b)
    (p x : Q)
    (hpa : Qle a p = true) (hpb : Qle p b = true)
    (hfp : (N.T p).val = p.val)
    (hxa : Qle a x = true) (hxb : Qle x b = true) :
    ((N.avg x).val - p.val) ^ 2 + (1 / 4 : Rat) * ((N.T x).val - x.val) ^ 2
      ≤ (x.val - p.val) ^ 2 := by
  have h_ne := N.nonexp x p hxa hxb hpa hpb
  rw [hfp] at h_ne
  have h_para := parallelogram_contraction_step (x.val - p.val) ((N.T x).val - p.val) h_ne
  have h1 : (N.avg x).val - p.val = ((x.val - p.val) + ((N.T x).val - p.val)) / 2 := by
    rw [N.val_avg]; ring
  have h2 : (1 / 4 : Rat) * ((N.T x).val - x.val) ^ 2 = (((N.T x).val - p.val) - (x.val - p.val)) ^ 2 / 4 := by
    ring
  have h3 : (((N.T x).val - p.val) - (x.val - p.val)) ^ 2 / 4 = ((((N.T x).val - p.val) - (x.val - p.val)) / 2) ^ 2 := by
    ring
  rw [h1, h2, h3]
  exact h_para

/-- Sum of squared residuals $\sum_{i=0}^{n-1} \frac{1}{4} |T(x_i) - x_i|^2$ along the KM trajectory. -/
def NonExpansiveMap.kmResidualSqSum {a b : Q} (N : NonExpansiveMap a b) (x0 : Q) : Nat → Rat
  | 0 => 0
  | n + 1 => N.kmResidualSqSum x0 n + (1 / 4 : Rat) * ((N.T (N.kmIter x0 n)).val - (N.kmIter x0 n).val) ^ 2

/-- **Theorem (Krasnoselskii–Mann Telescoping Sum Bound)**:
    Along the KM trajectory $x_n = T_{1/2}^n(x_0)$, the cumulative sum of squared steps is bounded by
    the initial squared distance to any fixed point $p$:
    $$\sum_{i=0}^{n-1} \frac{1}{4} |T(x_i) - x_i|^2 + |x_n - p|^2 \le |x_0 - p|^2.$$ -/
theorem NonExpansiveMap.km_quadratic_telescope {a b : Q} (N : NonExpansiveMap a b)
    (p x0 : Q)
    (hpa : Qle a p = true) (hpb : Qle p b = true)
    (hfp : (N.T p).val = p.val)
    (h0a : Qle a x0 = true) (h0b : Qle x0 b = true)
    (n : Nat) :
    N.kmResidualSqSum x0 n + ((N.kmIter x0 n).val - p.val) ^ 2 ≤ (x0.val - p.val) ^ 2 := by
  induction n with
  | zero =>
    dsimp [kmResidualSqSum, kmIter]
    linarith
  | succ n ih =>
    dsimp [kmResidualSqSum, kmIter]
    obtain ⟨hna, hnb⟩ := N.kmIter_maps_to x0 h0a h0b n
    have h_step := N.km_quadratic_step p (N.kmIter x0 n) hpa hpb hfp hna hnb
    linarith

/-- If every term in the first $n$ steps has $\frac{1}{4}|T(x_i) - x_i|^2 \ge c$,
    then the cumulative sum is at least $n \cdot c$. -/
theorem NonExpansiveMap.kmResidualSqSum_lower_bound {a b : Q} (N : NonExpansiveMap a b)
    (x0 : Q) (c : Rat) (n : Nat)
    (h_all : ∀ i, i < n → c ≤ (1 / 4 : Rat) * ((N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val) ^ 2) :
    (n : Rat) * c ≤ N.kmResidualSqSum x0 n := by
  induction n with
  | zero =>
    dsimp [kmResidualSqSum]
    simp
  | succ n ih =>
    dsimp [kmResidualSqSum]
    have h_prev : (n : Rat) * c ≤ N.kmResidualSqSum x0 n :=
      ih (fun i hi ↦ h_all i (by omega))
    have h_last : c ≤ (1 / 4 : Rat) * ((N.T (N.kmIter x0 n)).val - (N.kmIter x0 n).val) ^ 2 :=
      h_all n (by omega)
    push_cast
    linarith

/-- Computable minimum-residual index finder across the first `m + 1` Krasnoselskii–Mann iterates:
    returns $i^* \le m$ minimizing $|T(x_i) - x_i|$. -/
def NonExpansiveMap.kmBestIndex {a b : Q} (N : NonExpansiveMap a b) (x0 : Q) : Nat → Nat
  | 0 => 0
  | m + 1 =>
    let best := N.kmBestIndex x0 m
    let r_best := Q.abs (Q.sub (N.T (N.kmIter x0 best)) (N.kmIter x0 best))
    let r_curr := Q.abs (Q.sub (N.T (N.kmIter x0 (m + 1))) (N.kmIter x0 (m + 1)))
    if Qle r_curr r_best then m + 1 else best

/-- The computed best index across `0..m` is at most `m`. -/
theorem NonExpansiveMap.kmBestIndex_le {a b : Q} (N : NonExpansiveMap a b) (x0 : Q) (m : Nat) :
    N.kmBestIndex x0 m ≤ m := by
  induction m with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    dsimp only [kmBestIndex]
    split
    · exact Nat.le_refl (m + 1)
    · exact Nat.le_succ_of_le ih

/-- The computed best index `kmBestIndex x0 m` achieves a residual no larger than any `i ≤ m`. -/
theorem NonExpansiveMap.kmBestIndex_min {a b : Q} (N : NonExpansiveMap a b) (x0 : Q)
    (m i : Nat) (hi : i ≤ m) :
    |(N.T (N.kmIter x0 (N.kmBestIndex x0 m))).val - (N.kmIter x0 (N.kmBestIndex x0 m)).val| ≤
    |(N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val| := by
  induction m with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    exact le_refl _
  | succ m ih =>
    dsimp only [kmBestIndex]
    set best := N.kmBestIndex x0 m
    set r_best := Q.abs (Q.sub (N.T (N.kmIter x0 best)) (N.kmIter x0 best))
    set r_curr := Q.abs (Q.sub (N.T (N.kmIter x0 (m + 1))) (N.kmIter x0 (m + 1)))
    have hr_best : r_best.val = |(N.T (N.kmIter x0 best)).val - (N.kmIter x0 best).val| := by
      dsimp [r_best]; rw [Q.val_abs, Q.val_sub]
    have hr_curr : r_curr.val = |(N.T (N.kmIter x0 (m + 1))).val - (N.kmIter x0 (m + 1)).val| := by
      dsimp [r_curr]; rw [Q.val_abs, Q.val_sub]
    by_cases h_cond : Qle r_curr r_best = true
    · rw [if_pos h_cond]
      rw [Qle_eq_true_iff, hr_curr, hr_best] at h_cond
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · exact le_refl _
      · exact le_trans h_cond (ih (Nat.lt_succ_iff.mp hlt))
    · rw [if_neg h_cond]
      have h_not_le : ¬ (r_curr.val ≤ r_best.val) :=
        fun hle ↦ h_cond ((Qle_eq_true_iff r_curr r_best).mpr hle)
      have h_gt : r_best.val < r_curr.val := not_le.mp h_not_le
      rw [hr_curr, hr_best] at h_gt
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · exact le_of_lt h_gt
      · exact ih (Nat.lt_succ_iff.mp hlt)

/-- **Constructive Argmin Certificate for Krasnoselskii–Mann Iteration**:
    At the explicitly computed index $i^* = \mathrm{kmBestIndex}(x_0, \mathrm{kmRate}(\mathrm{diamSq}, k) - 1)$,
    we have $i^* < \mathrm{kmRate}(\mathrm{diamSq}, k)$ and $|T(x_{i^*}) - x_{i^*}| \le 2^{-k}$. -/
theorem NonExpansiveMap.kmBestIndex_spec {a b : Q} (N : NonExpansiveMap a b)
    (p x0 : Q) (diamSq k : Nat)
    (hpa : Qle a p = true) (hpb : Qle p b = true) (hfp : (N.T p).val = p.val)
    (h0a : Qle a x0 = true) (h0b : Qle x0 b = true)
    (h_diam : (x0.val - p.val) ^ 2 ≤ (diamSq : Rat)) :
    let M := kmRate diamSq k
    let i_star := N.kmBestIndex x0 (M - 1)
    i_star < M ∧
      |(N.T (N.kmIter x0 i_star)).val - (N.kmIter x0 i_star).val| ≤ 1 / (2 : Rat) ^ k := by
  dsimp only
  set M := kmRate diamSq k
  have hM_pos : 0 < M := by
    dsimp [M, kmRate]
    exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (Nat.pow_pos (by decide))
  set i_star := N.kmBestIndex x0 (M - 1)
  have hi_le : i_star ≤ M - 1 := N.kmBestIndex_le x0 (M - 1)
  have hi_lt : i_star < M := by omega
  refine ⟨hi_lt, ?_⟩
  set R := |(N.T (N.kmIter x0 i_star)).val - (N.kmIter x0 i_star).val|
  have hR_nonneg : 0 ≤ R := abs_nonneg _
  have h_each : ∀ i, i < M →
      (1 / 4 : Rat) * R ^ 2 ≤ (1 / 4 : Rat) * ((N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val) ^ 2 := by
    intro i hi
    have h_min : R ≤ |(N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val| :=
      N.kmBestIndex_min x0 (M - 1) i (by omega)
    have h_sq : R * R ≤ |(N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val| *
        |(N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val| :=
      mul_le_mul h_min h_min hR_nonneg (abs_nonneg _)
    have h_lhs : R * R = R ^ 2 := by ring
    have h_rhs : |(N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val| *
        |(N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val|
        = ((N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val) ^ 2 := by
      rw [← sq, sq_abs]
    linarith
  have h_lower := N.kmResidualSqSum_lower_bound x0 ((1 / 4 : Rat) * R ^ 2) M h_each
  have h_tele := N.km_quadratic_telescope p x0 hpa hpb hfp h0a h0b M
  have h_nonneg_tail : 0 ≤ ((N.kmIter x0 M).val - p.val) ^ 2 := sq_nonneg _
  have h_prod_bound : (M : Rat) * ((1 / 4 : Rat) * R ^ 2) ≤ (diamSq : Rat) := by linarith
  have h_target_prod : (M : Rat) * ((1 / 4 : Rat) * (1 / (2 : Rat) ^ k) ^ 2) = (diamSq : Rat) + 1 := by
    dsimp [M, kmRate]
    push_cast
    have h4 : (4 : Rat) ^ k = ((2 : Rat) ^ k) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [h4]
    have : (0 : Rat) < (2 : Rat) ^ k := by positivity
    field_simp
  have hM_rat_pos : (0 : Rat) < (M : Rat) := by exact_mod_cast hM_pos
  have h_sq_le : R ^ 2 < (1 / (2 : Rat) ^ k) ^ 2 := by
    have h_lt_prod : (M : Rat) * ((1 / 4 : Rat) * R ^ 2) <
        (M : Rat) * ((1 / 4 : Rat) * (1 / (2 : Rat) ^ k) ^ 2) := by linarith
    have h_quarter : (1 / 4 : Rat) * R ^ 2 < (1 / 4 : Rat) * (1 / (2 : Rat) ^ k) ^ 2 :=
      lt_of_mul_lt_mul_left h_lt_prod (le_of_lt hM_rat_pos)
    linarith
  by_contra h_gt
  push_neg at h_gt
  have h_pos : (0 : Rat) ≤ 1 / (2 : Rat) ^ k := by positivity
  have h_sq_ge : (1 / (2 : Rat) ^ k) ^ 2 ≤ R ^ 2 := by
    have := mul_le_mul (le_of_lt h_gt) (le_of_lt h_gt) h_pos hR_nonneg
    linarith [sq (1 / (2 : Rat) ^ k), sq R]
  linarith

/-- **Theorem (Krasnoselskii–Mann Asymptotic Regularity with Rate `kmRate`)**:
    For any non-expansive map $T : [a, b] \to [a, b]$ with a fixed point $p \in [a, b]$
    satisfying $(x_0 - p)^2 \le \mathrm{diamSq}$, the computable argmin witness
    $i^* = \mathrm{kmBestIndex}(x_0, \mathrm{kmRate}(\mathrm{diamSq}, k) - 1) < \mathrm{kmRate}(\mathrm{diamSq}, k)$
    satisfies $|(T(x_{i^*})).\mathrm{val} - x_{i^*}.\mathrm{val}| \le 2^{-k}$. -/
theorem NonExpansiveMap.km_asymptotic_regularity {a b : Q} (N : NonExpansiveMap a b)
    (p x0 : Q) (diamSq k : Nat)
    (hpa : Qle a p = true) (hpb : Qle p b = true)
    (hfp : (N.T p).val = p.val)
    (h0a : Qle a x0 = true) (h0b : Qle x0 b = true)
    (h_diam : (x0.val - p.val) ^ 2 ≤ (diamSq : Rat)) :
    ∃ i, i < kmRate diamSq k ∧
      |(N.T (N.kmIter x0 i)).val - (N.kmIter x0 i).val| ≤ 1 / (2 : Rat) ^ k :=
  ⟨N.kmBestIndex x0 (kmRate diamSq k - 1), N.kmBestIndex_spec p x0 diamSq k hpa hpb hfp h0a h0b h_diam⟩

/-! ## 3. System T Object-Level Derivation & Realizer Extraction for Krasnoselskii–Mann -/

/-- The Krasnoselskii–Mann averaged step term in System T:
    `λ (x : rat). (x + T(x)) / 2`. -/
def kmAvgStepTm {Γ : List Ty} (T : Tm Γ (.arrow .rat .rat)) : Tm Γ (.arrow .rat .rat) :=
  .lam (.qdiv (.qadd (.var .here) (.app T.wk (.var .here))) (.qnat (.succ (.succ .zero))))

/-- Closed System T Krasnoselskii–Mann trajectory operator:
    `λ (T : rat → rat) (x0 : rat) (n : nat). recNat x0 (λ k acc. (acc + T acc) / 2) n`. -/
def tmKMIterClosed {Γ : List Ty} :
    Tm Γ (.arrow (.arrow .rat .rat) (.arrow .rat (.arrow .nat .rat))) :=
  .lam (.lam (.lam (
    .recNat (.var (.there .here))
      (.lam (.lam (.qdiv (.qadd (.var .here) (.app (.var (.there (.there (.there (.there .here))))) (.var .here)))
                         (.qnat (.succ (.succ .zero))))))
      (.var .here))))

/-- Natural deduction derivation in `Deriv` of the Krasnoselskii–Mann iteration sequence:
    $\forall n : \mathrm{nat}. \; \exists y : \mathrm{rat}. \; y = T_{1/2}^n(x_0)$. -/
def kmSequenceD (T : Tm [] (.arrow .rat .rat)) (x0 : Tm [] .rat) :
    Deriv Ctx.nil (.all .nat (iterInv .rat [] x0 (kmAvgStepTm T))) :=
  iterSequenceD .rat x0 (kmAvgStepTm T)

/-- **The extracted Krasnoselskii–Mann solver** synthesized via `extractClosed kmSequenceD`. -/
def kmExtracted (T : Tm [] (.arrow .rat .rat)) (x0 : Tm [] .rat) (n : Nat) : Q :=
  ((extractClosed (kmSequenceD T x0)).eval Env.nil n).1

/-- Non-expansive reflection map $T(x) = 1 - x$ on $[0, 1]$ in System T
    (has Lipschitz constant $L = 1$; un-averaged iteration $T^n(0)$ oscillates $0, 1, 0, 1, \dots$). -/
def tmReflectUnit : Tm [] (.arrow .rat .rat) :=
  .lam (.qsub (.qnat (.succ .zero)) (.var .here))

-- Un-averaged reflection at 0 oscillates 0, 1, 0, 1;
-- Krasnoselskii–Mann extracted realizer reaches the exact fixed point 1/2 in 1 step and stays there:
#guard kmExtracted tmReflectUnit (.qnat .zero) 0 == Q.ofNat 0
#guard kmExtracted tmReflectUnit (.qnat .zero) 1 == Q.of 1 2
#guard kmExtracted tmReflectUnit (.qnat .zero) 2 == Q.of 1 2
#guard kmExtracted tmReflectUnit (.qnat .zero) 3 == Q.of 1 2

#print axioms NonExpansiveMap.avg_monotone
#print axioms NonExpansiveMap.kmIter_mono_from_left
#print axioms NonExpansiveMap.km_quadratic_step
#print axioms NonExpansiveMap.km_quadratic_telescope
#print axioms NonExpansiveMap.kmBestIndex_spec
#print axioms NonExpansiveMap.km_asymptotic_regularity
#print axioms kmSequenceD
#print axioms kmExtracted

end HAomega
