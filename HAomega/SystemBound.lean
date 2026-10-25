/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseGPAC

/-!
# A geometric coefficient bound for every polynomial system with constant data

The evaluator of `UniverseEval.lean` certifies values for the expression
language `UExpr`, whose coefficient bounds come expression by expression. For an
arbitrary member of the universe — a component of the solution of a
polynomial–integral system `Y_v = A_v + ∫ F_v(Y)` with constant data
(`GPACSys`) — no bound was known. This is the classical majorant theorem for
analytic ODEs, in the form the evaluator needs: explicit `(M, R)` with

    |c_n| ≤ 2^M · (2^R)^n      for every solution coefficient c_n.
-/

namespace HAomega

/-- Quadratic weight `(m + 1)^2` for the weighted Cauchy majorant method. -/
def sbdSq (m : Nat) : Rat := ((m : Rat) + 1) ^ 2

theorem sbdSq_pos (m : Nat) : (0 : Rat) < sbdSq m := by
  unfold sbdSq
  positivity

theorem sbdSq_ge_one (m : Nat) : (1 : Rat) ≤ sbdSq m := by
  unfold sbdSq
  have hm : (0 : Rat) ≤ (m : Rat) := by positivity
  nlinarith

theorem sbdSq_succ_le_four (k : Nat) : sbdSq (k + 1) ≤ 4 * sbdSq k := by
  unfold sbdSq
  push_cast
  have hk : (0 : Rat) ≤ (k : Rat) := by positivity
  nlinarith

/-- If `4 * Φ ≤ K * B`, then `(Φ * B^k) / sbdSq k ≤ (K * B^(k+1)) / sbdSq (k+1)`. -/
theorem sbd_step_scale {Φ K B : Rat} (hΦ : 0 ≤ Φ) (hB : 0 ≤ B)
    (h4 : 4 * Φ ≤ K * B) (k : Nat) :
    Φ * B ^ k / sbdSq k ≤ K * B ^ (k + 1) / sbdSq (k + 1) := by
  have hsq_k : (0 : Rat) < sbdSq k := sbdSq_pos k
  have hsq_sk : (0 : Rat) < sbdSq (k + 1) := sbdSq_pos (k + 1)
  rw [div_le_div_iff₀ hsq_k hsq_sk]
  have h1 : Φ * B ^ k * sbdSq (k + 1) ≤ Φ * B ^ k * (4 * sbdSq k) :=
    mul_le_mul_of_nonneg_left (sbdSq_succ_le_four k) (by positivity)
  have h1' : Φ * B ^ k * (4 * sbdSq k) = (4 * Φ) * (B ^ k * sbdSq k) := by ring
  have h2 : (4 * Φ) * (B ^ k * sbdSq k) ≤ (K * B) * (B ^ k * sbdSq k) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  have h3 : K * B ^ (k + 1) * sbdSq k = (K * B) * (B ^ k * sbdSq k) := by
    rw [pow_succ]
    ring
  linarith

/-- For every `k : Nat`, `1 / (k + 1)^2 ≤ 2 * (1 / (k + 1) - 1 / (k + 2))`. -/
theorem sbd_inv_sq_le_sub (k : Nat) :
    1 / sbdSq k ≤ 2 * (1 / ((k : Rat) + 1) - 1 / ((k : Rat) + 2)) := by
  unfold sbdSq
  have hk1 : (0 : Rat) < (k : Rat) + 1 := by positivity
  have hk2 : (0 : Rat) < (k : Rat) + 2 := by positivity
  have hdiff : 1 / ((k : Rat) + 1) - 1 / ((k : Rat) + 2) =
      1 / (((k : Rat) + 1) * ((k : Rat) + 2)) := by
    rw [div_sub_div _ _ (ne_of_gt hk1) (ne_of_gt hk2)]
    ring
  rw [hdiff, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hk0 : (0 : Rat) ≤ (k : Rat) := by positivity
  nlinarith

/-- Pointwise partial-fraction bound for the convolution weight. -/
theorem sbd_conv_term_le {m j : Nat} (hj : j ≤ m) :
    1 / (sbdSq j * sbdSq (m - j)) ≤
      (2 / sbdSq m) * (1 / sbdSq j + 1 / sbdSq (m - j)) := by
  have hsq_j : (0 : Rat) < sbdSq j := sbdSq_pos j
  have hsq_mj : (0 : Rat) < sbdSq (m - j) := sbdSq_pos (m - j)
  have hsq_m : (0 : Rat) < sbdSq m := sbdSq_pos m
  have h_add : (j : Rat) + ((m - j : Nat) : Rat) = (m : Rat) := by
    exact_mod_cast Nat.add_sub_of_le hj
  have h_sum_sq : sbdSq m ≤ 2 * (sbdSq j + sbdSq (m - j)) := by
    unfold sbdSq
    have h_id : 2 * (((j : Rat) + 1) ^ 2 + (((m - j : Nat) : Rat) + 1) ^ 2) -
        (((j : Rat) + ((m - j : Nat) : Rat) + 1) ^ 2) =
        ((j : Rat) - ((m - j : Nat) : Rat)) ^ 2 + 2 * ((j : Rat) + ((m - j : Nat) : Rat)) + 3 := by
      ring
    have h_sq : (0 : Rat) ≤ ((j : Rat) - ((m - j : Nat) : Rat)) ^ 2 := sq_nonneg _
    have hm0 : (0 : Rat) ≤ (m : Rat) := by positivity
    rw [← h_add]
    linarith
  have h_rhs : (2 / sbdSq m) * (1 / sbdSq j + 1 / sbdSq (m - j)) =
      (2 * (sbdSq j + sbdSq (m - j))) / (sbdSq m * (sbdSq j * sbdSq (m - j))) := by
    field_simp
    ring
  have h_lhs : 1 / (sbdSq j * sbdSq (m - j)) =
      sbdSq m / (sbdSq m * (sbdSq j * sbdSq (m - j))) := by
    field_simp
  rw [h_lhs, h_rhs]
  exact div_le_div_of_nonneg_right h_sum_sq (by positivity)

/-- Telescoping upper bound for the partial sum of `1 / sbdSq j + 1 / sbdSq (m - j)`. -/
def sbdTele (m r : Nat) : Rat :=
  2 * (1 - 1 / ((r : Rat) + 1)) +
    2 * (1 / (((m + 1 - r : Nat) : Rat) + 1) - 1 / ((m : Rat) + 2))

theorem sbd_sum_inv_sq_tele (m : Nat) : ∀ r : Nat, r ≤ m + 1 →
    (∑ j ∈ Finset.range r, (1 / sbdSq j + 1 / sbdSq (m - j))) ≤ sbdTele m r
  | 0, _ => by
    unfold sbdTele
    simp only [Finset.range_zero, Finset.sum_empty, Nat.sub_zero]
    push_cast
    have h_eq : 1 / ((m : Rat) + 1 + 1) = 1 / ((m : Rat) + 2) := by ring_nf
    linarith
  | r + 1, hr => by
    have hr_le : r ≤ m := Nat.lt_succ_iff.mp hr
    have ih := sbd_sum_inv_sq_tele m r (Nat.le_of_lt hr)
    have h1 := sbd_inv_sq_le_sub r
    have h2 := sbd_inv_sq_le_sub (m - r)
    have h_sub1 : m + 1 - r = (m - r) + 1 := Nat.succ_sub hr_le
    have h_sub2 : m + 1 - (r + 1) = m - r := Nat.succ_sub_succ_eq_sub m r
    rw [Finset.sum_range_succ]
    unfold sbdTele at ih ⊢
    rw [h_sub1] at ih
    rw [h_sub2]
    push_cast at ih ⊢
    have h_ring : 2 * (1 - 1 / ((r : Rat) + 1 + 1)) +
        2 * (1 / (((m - r : Nat) : Rat) + 1) - 1 / ((m : Rat) + 2)) =
        (2 * (1 - 1 / ((r : Rat) + 1)) +
          2 * (1 / (((m - r : Nat) : Rat) + 1 + 1) - 1 / ((m : Rat) + 2))) +
        2 * (1 / ((r : Rat) + 1) - 1 / ((r : Rat) + 2)) +
        2 * (1 / (((m - r : Nat) : Rat) + 1) - 1 / (((m - r : Nat) : Rat) + 2)) := by
      ring
    linarith

/-- Convolution inequality: `∑_{j=0}^m 1 / (sbdSq j * sbdSq (m - j)) ≤ 8 / sbdSq m`. -/
theorem sbd_conv_sum_le (m : Nat) :
    (∑ j ∈ Finset.range (m + 1), 1 / (sbdSq j * sbdSq (m - j))) ≤ 8 / sbdSq m := by
  have h_pt : (∑ j ∈ Finset.range (m + 1), 1 / (sbdSq j * sbdSq (m - j))) ≤
      ∑ j ∈ Finset.range (m + 1), (2 / sbdSq m) * (1 / sbdSq j + 1 / sbdSq (m - j)) := by
    refine Finset.sum_le_sum fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    exact sbd_conv_term_le (Nat.lt_succ_iff.mp hj)
  rw [← Finset.mul_sum] at h_pt
  have h_tele := sbd_sum_inv_sq_tele m (m + 1) (le_refl _)
  have h_tele_le_4 : sbdTele m (m + 1) ≤ 4 := by
    unfold sbdTele
    rw [Nat.sub_self]
    push_cast
    have hm_pos : (0 : Rat) ≤ 1 / ((m : Rat) + 2) := by positivity
    have h_eq : 1 / ((m : Rat) + 1 + 1) = 1 / ((m : Rat) + 2) := by ring_nf
    rw [h_eq]
    linarith
  have h_sum_le_4 : (∑ j ∈ Finset.range (m + 1), (1 / sbdSq j + 1 / sbdSq (m - j))) ≤ 4 :=
    le_trans h_tele h_tele_le_4
  have hm_sq_pos : 0 < sbdSq m := sbdSq_pos m
  have h_mul : (2 / sbdSq m) * (∑ j ∈ Finset.range (m + 1), (1 / sbdSq j + 1 / sbdSq (m - j))) ≤
      (2 / sbdSq m) * 4 :=
    mul_le_mul_of_nonneg_left h_sum_le_4 (by positivity)
  have h_8 : (2 / sbdSq m) * 4 = 8 / sbdSq m := by ring
  linarith

/-- Cauchy product bound in the weighted majorant class. -/
theorem sbd_mul_bound (a b : Nat → Q) {K₁ K₂ B : Rat} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hB : 0 ≤ B)
    (m : Nat)
    (ha : ∀ j ≤ m, |(a j).val| ≤ K₁ * B ^ j / sbdSq j)
    (hb : ∀ j ≤ m, |(b j).val| ≤ K₂ * B ^ j / sbdSq j) :
    |(((tmJetMul (Γ := [])).eval Env.nil) a b m).val| ≤ (8 * K₁ * K₂) * B ^ m / sbdSq m := by
  rw [tmJetMul_eval]
  simp only [Jet.mul, TrigPoly.cauchyConvAux_val]
  have h_abs : |∑ j ∈ Finset.range (m + 1), (a j).val * (b (m - j)).val| ≤
      ∑ j ∈ Finset.range (m + 1), |(a j).val * (b (m - j)).val| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_terms : (∑ j ∈ Finset.range (m + 1), |(a j).val * (b (m - j)).val|) ≤
      ∑ j ∈ Finset.range (m + 1), (K₁ * K₂ * B ^ m) * (1 / (sbdSq j * sbdSq (m - j))) := by
    refine Finset.sum_le_sum fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp hj
    have hmjm : m - j ≤ m := Nat.sub_le m j
    rw [abs_mul]
    have hj_pos : 0 < sbdSq j := sbdSq_pos j
    have hmjm_pos : 0 < sbdSq (m - j) := sbdSq_pos (m - j)
    have h_prod := mul_le_mul (ha j hjm) (hb (m - j) hmjm) (abs_nonneg _) (by positivity)
    have h_pow : B ^ j * B ^ (m - j) = B ^ m := by
      rw [← pow_add, Nat.add_sub_of_le hjm]
    have h_eq : (K₁ * B ^ j / sbdSq j) * (K₂ * B ^ (m - j) / sbdSq (m - j)) =
        (K₁ * K₂ * B ^ m) * (1 / (sbdSq j * sbdSq (m - j))) := by
      calc (K₁ * B ^ j / sbdSq j) * (K₂ * B ^ (m - j) / sbdSq (m - j))
          = (K₁ * K₂ * (B ^ j * B ^ (m - j))) / (sbdSq j * sbdSq (m - j)) := by ring
        _ = (K₁ * K₂ * B ^ m) * (1 / (sbdSq j * sbdSq (m - j))) := by rw [h_pow]; ring
    linarith
  rw [← Finset.mul_sum] at h_terms
  have h_conv := mul_le_mul_of_nonneg_left (sbd_conv_sum_le m) (show 0 ≤ K₁ * K₂ * B ^ m by positivity)
  have h_rhs : (K₁ * K₂ * B ^ m) * (8 / sbdSq m) = (8 * K₁ * K₂) * B ^ m / sbdSq m := by ring
  linarith

/-- Evaluation of `F : JExprN` on a state `W : Nat → Nat → Q`. -/
def sbdEvalExpr (F : JExprN) (W : Nat → Nat → Q) : Nat → Q :=
  (F.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil)

/-- Bound multiplier `Φ_F(K) : Rat` for a polynomial–integral expression `F : JExprN`. -/
def sbdExprBound : JExprN → Rat → Rat
  | .var _, K => K
  | .const c, _ => |(c.eval Env.nil 0).val|
  | .add a b, K => sbdExprBound a K + sbdExprBound b K
  | .sub a b, K => sbdExprBound a K + sbdExprBound b K
  | .mul a b, K => 8 * sbdExprBound a K * sbdExprBound b K
  | .integ a, K => sbdExprBound a K

theorem sbdExprBound_nonneg (F : JExprN) {K : Rat} (hK : 0 ≤ K) : 0 ≤ sbdExprBound F K := by
  induction F with
  | var _ => exact hK
  | const _ => exact abs_nonneg _
  | add _ _ iha ihb => exact add_nonneg iha ihb
  | sub _ _ iha ihb => exact add_nonneg iha ihb
  | mul _ _ iha ihb => dsimp [sbdExprBound]; positivity
  | integ _ iha => exact iha

/-- Truncated weighted bound for `sbdEvalExpr F W`: if every variable `< sysLen` satisfies the
    `(K, B)` bound up to degree `n`, then `F(W)` satisfies the `(sbdExprBound F K, B)` bound up to `n`. -/
theorem sbd_evalExpr_bound (F : JExprN) (sysLen : Nat) (hWF : F.WF sysLen) (hCC : F.ConstsConst)
    (W : Nat → Nat → Q) {K B : Rat} (hK : 0 ≤ K) (hB : 4 ≤ B) (n : Nat)
    (hW : ∀ u < sysLen, ∀ m ≤ n, |(W u m).val| ≤ K * B ^ m / sbdSq m) :
    ∀ m ≤ n, |(sbdEvalExpr F W m).val| ≤ sbdExprBound F K * B ^ m / sbdSq m := by
  have hB0 : (0 : Rat) ≤ B := by linarith
  induction F with
  | var i =>
    intro m hm
    have hev : sbdEvalExpr (.var i) W m = W i m := by
      change (Tm.var (Γ := [WTy]) .here).eval (Env.cons (σ := WTy) W Env.nil)
        ((natTm i).eval (Env.cons (σ := WTy) W Env.nil)) m = W i m
      rw [natTm_eval]
      rfl
    rw [hev]
    exact hW i hWF m hm
  | const c =>
    intro m _
    have hev : sbdEvalExpr (.const c) W m = c.eval Env.nil m := by
      dsimp [sbdEvalExpr, JExprN.toTm]
      rw [closedWk_eval]
    rw [hev]
    dsimp [sbdExprBound]
    cases m with
    | zero =>
      have hsq0 : sbdSq 0 = 1 := by unfold sbdSq; norm_num
      rw [hsq0, pow_zero, mul_one, div_one]
    | succ k =>
      rw [hCC k, abs_zero]
      have hsq_pos : 0 < sbdSq (k + 1) := sbdSq_pos (k + 1)
      positivity
  | add a b iha ihb =>
    intro m hm
    have hev : (sbdEvalExpr (.add a b) W m).val =
        (sbdEvalExpr a W m).val + (sbdEvalExpr b W m).val :=
      Q.val_add _ _
    rw [hev]
    dsimp [sbdExprBound]
    have ha_m := iha hWF.1 hCC.1 m hm
    have hb_m := ihb hWF.2 hCC.2 m hm
    have h_tri := abs_add_le (sbdEvalExpr a W m).val (sbdEvalExpr b W m).val
    have h_ring : sbdExprBound a K * B ^ m / sbdSq m + sbdExprBound b K * B ^ m / sbdSq m =
        (sbdExprBound a K + sbdExprBound b K) * B ^ m / sbdSq m := by ring
    linarith
  | sub a b iha ihb =>
    intro m hm
    have hev : (sbdEvalExpr (.sub a b) W m).val =
        (sbdEvalExpr a W m).val - (sbdEvalExpr b W m).val :=
      Q.val_sub _ _
    rw [hev]
    dsimp [sbdExprBound]
    have ha_m := iha hWF.1 hCC.1 m hm
    have hb_m := ihb hWF.2 hCC.2 m hm
    have h_tri := abs_sub (sbdEvalExpr a W m).val (sbdEvalExpr b W m).val
    have h_ring : sbdExprBound a K * B ^ m / sbdSq m + sbdExprBound b K * B ^ m / sbdSq m =
        (sbdExprBound a K + sbdExprBound b K) * B ^ m / sbdSq m := by ring
    linarith
  | mul a b iha ihb =>
    intro m hm
    have hev : sbdEvalExpr (.mul a b) W m =
        ((tmJetMul (Γ := [])).eval Env.nil) (sbdEvalExpr a W) (sbdEvalExpr b W) m := rfl
    rw [hev]
    dsimp [sbdExprBound]
    exact sbd_mul_bound (sbdEvalExpr a W) (sbdEvalExpr b W)
      (sbdExprBound_nonneg a hK) (sbdExprBound_nonneg b hK) hB0 m
      (fun j hj ↦ iha hWF.1 hCC.1 j (le_trans hj hm))
      (fun j hj ↦ ihb hWF.2 hCC.2 j (le_trans hj hm))
  | integ a iha =>
    intro m hm
    dsimp [sbdExprBound]
    cases m with
    | zero =>
      have hev : (sbdEvalExpr (.integ a) W 0).val = 0 := Q.val_ofNat 0
      rw [hev, abs_zero]
      have hΦ : 0 ≤ sbdExprBound a K := sbdExprBound_nonneg a hK
      have hsq_pos : 0 < sbdSq 0 := sbdSq_pos 0
      positivity
    | succ k =>
      have hne : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
      have hev : (sbdEvalExpr (.integ a) W (k + 1)).val =
          (sbdEvalExpr a W k).val / ((k + 1 : Nat) : Rat) := by
        change (Q.div (sbdEvalExpr a W k) (Q.ofNat (k + 1))).val = _
        rw [Q.val_div _ _ hne, Q.val_ofNat]
      have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        exact_mod_cast Nat.succ_pos k
      have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
      rw [hev, abs_div, abs_of_pos hk1_pos]
      have h_div_le : |(sbdEvalExpr a W k).val| / ((k + 1 : Nat) : Rat) ≤
          |(sbdEvalExpr a W k).val| :=
        div_le_self (abs_nonneg _) hk1_ge
      have ha_k := iha hWF hCC k (Nat.le_of_succ_le hm)
      have hΦ : 0 ≤ sbdExprBound a K := sbdExprBound_nonneg a hK
      have h4Φ : 4 * sbdExprBound a K ≤ sbdExprBound a K * B := by nlinarith
      have h_step := sbd_step_scale hΦ hB0 h4Φ k
      linarith

/-- Elementary dominance `(m : Rat) ≤ 2^m`. -/
theorem sbd_nat_le_two_pow : ∀ m : Nat, (m : Rat) ≤ (2 : Rat) ^ m
  | 0 => by norm_num
  | k + 1 => by
    have ih := sbd_nat_le_two_pow k
    have h1 : (1 : Rat) ≤ (2 : Rat) ^ k := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    push_cast
    linarith

/-- Every rational `x : Rat` is bounded above by `(2 : Rat) ^ N` for some `N : Nat`. -/
theorem sbd_exists_two_pow_ge (x : Rat) : ∃ N : Nat, x ≤ (2 : Rat) ^ N := by
  rcases exists_nat_ge x with ⟨N, hN⟩
  exact ⟨N, le_trans hN (sbd_nat_le_two_pow N)⟩

/-- Maximum initial coefficient magnitude across a system `sys` (at least `1`). -/
def sbdMaxInit : List (Tm [] JetTy × JExprN) → Rat
  | [] => 1
  | p :: rest => max |(p.1.eval Env.nil 0).val| (sbdMaxInit rest)

theorem sbdMaxInit_ge_one : ∀ sys : List (Tm [] JetTy × JExprN), 1 ≤ sbdMaxInit sys
  | [] => le_refl 1
  | _ :: rest => le_trans (sbdMaxInit_ge_one rest) (le_max_right _ _)

theorem sbdMaxInit_mem {sys : List (Tm [] JetTy × JExprN)} {p : Tm [] JetTy × JExprN}
    (hp : p ∈ sys) : |(p.1.eval Env.nil 0).val| ≤ sbdMaxInit sys := by
  induction sys with
  | nil => nomatch hp
  | cons hd rest ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact le_max_left _ _
    · exact le_trans (ih hp) (le_max_right _ _)

/-- Maximum expression bound `sbdExprBound p.2 K` across `p ∈ sys` (at least `1`). -/
def sbdMaxPhi (K : Rat) : List (Tm [] JetTy × JExprN) → Rat
  | [] => 1
  | p :: rest => max (sbdExprBound p.2 K) (sbdMaxPhi K rest)

theorem sbdMaxPhi_mem (K : Rat) {sys : List (Tm [] JetTy × JExprN)} {p : Tm [] JetTy × JExprN}
    (hp : p ∈ sys) : sbdExprBound p.2 K ≤ sbdMaxPhi K sys := by
  induction sys with
  | nil => nomatch hp
  | cons hd rest ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact le_max_left _ _
    · exact le_trans (ih hp) (le_max_right _ _)

/-- For `GPACSys sys`, at degree `k + 1` the solution `solN sys v (k + 1)` equals
    `sbdEvalExpr sys[v].2 (solN sys) k / (k + 1)` in rational value. -/
theorem sbd_solN_succ_val (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (v : Nat) (hv : v < sys.length) (k : Nat) :
    (solN sys v (k + 1)).val =
      (sbdEvalExpr sys[v].2 (solN sys) k).val / ((k + 1 : Nat) : Rat) := by
  have hwf := gpac_wf h
  have hpv := h sys[v] (List.getElem_mem hv)
  have hfix := (solN_fixed sys hwf v hv (k + 1)).symm
  rw [genStepN_eval_getElem sys (solN sys) v hv] at hfix
  unfold eqStepEval at hfix
  have hne : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
  change (solN sys v (k + 1)).val =
    (Q.add (sys[v].1.eval Env.nil (k + 1))
      (Q.div (sbdEvalExpr sys[v].2 (solN sys) k) (Q.ofNat (k + 1)))).val at hfix
  rw [hfix, Q.val_add, hpv.2.1 k, zero_add, Q.val_div _ _ hne, Q.val_ofNat]

/-- Strong induction for the weighted majorant bound on `solN sys`. -/
theorem sbd_solN_weighted_bound (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    {K B : Rat} (hK : 0 ≤ K) (hB : 4 ≤ B)
    (hInit : ∀ p ∈ sys, |(p.1.eval Env.nil 0).val| ≤ K)
    (hStep : ∀ p ∈ sys, 4 * sbdExprBound p.2 K ≤ K * B) :
    ∀ n : Nat, ∀ v < sys.length, |(solN sys v n).val| ≤ K * B ^ n / sbdSq n := by
  have hB0 : (0 : Rat) ≤ B := by linarith
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    have hpv := h sys[v] (List.getElem_mem hv)
    cases m with
    | zero =>
      rw [uMul_solN_zero_val sys (gpac_wf h) v hv]
      have hsq0 : sbdSq 0 = 1 := by unfold sbdSq; norm_num
      rw [hsq0, pow_zero, mul_one, div_one]
      exact hInit sys[v] (List.getElem_mem hv)
    | succ k =>
      rw [sbd_solN_succ_val sys h v hv k]
      have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        exact_mod_cast Nat.succ_pos k
      have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
      rw [abs_div, abs_of_pos hk1_pos]
      have h_div_le : |(sbdEvalExpr sys[v].2 (solN sys) k).val| / ((k + 1 : Nat) : Rat) ≤
          |(sbdEvalExpr sys[v].2 (solN sys) k).val| :=
        div_le_self (abs_nonneg _) hk1_ge
      have h_expr := sbd_evalExpr_bound sys[v].2 sys.length hpv.1 hpv.2.2 (solN sys) hK hB k
        (fun u hu j hj ↦ ih j (Nat.lt_succ_of_le hj) u hu) k (le_refl k)
      have hΦ : 0 ≤ sbdExprBound sys[v].2 K := sbdExprBound_nonneg sys[v].2 hK
      have h_scale := sbd_step_scale hΦ hB0 (hStep sys[v] (List.getElem_mem hv)) k
      linarith

/-- **Every polynomial system with constant data has geometrically bounded
solution coefficients.** -/
theorem solN_geom_bound (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys) :
    ∃ M R : Nat, ∀ v, v < sys.length → ∀ n : Nat,
      |(solN sys v n).val| ≤ (2 : Rat) ^ M * ((2 : Rat) ^ R) ^ n := by
  rcases sbd_exists_two_pow_ge (sbdMaxInit sys) with ⟨M, hM⟩
  let K : Rat := (2 : Rat) ^ M
  have hK_pos : (0 : Rat) < K := by positivity
  have hK_nonneg : (0 : Rat) ≤ K := le_of_lt hK_pos
  rcases sbd_exists_two_pow_ge (max 4 (4 * sbdMaxPhi K sys / K)) with ⟨R, hR⟩
  let B : Rat := (2 : Rat) ^ R
  have hB_ge_4 : (4 : Rat) ≤ B := le_trans (le_max_left _ _) hR
  have hB_nonneg : (0 : Rat) ≤ B := by linarith
  have hInit : ∀ p ∈ sys, |(p.1.eval Env.nil 0).val| ≤ K :=
    fun p hp ↦ le_trans (sbdMaxInit_mem hp) hM
  have hStep : ∀ p ∈ sys, 4 * sbdExprBound p.2 K ≤ K * B := by
    intro p hp
    have h1 : 4 * sbdExprBound p.2 K ≤ 4 * sbdMaxPhi K sys := by
      have := sbdMaxPhi_mem K hp
      linarith
    have h2 : 4 * sbdMaxPhi K sys / K ≤ B := le_trans (le_max_right _ _) hR
    have h3 : 4 * sbdMaxPhi K sys ≤ B * K := (div_le_iff₀ hK_pos).mp h2
    linarith
  refine ⟨M, R, fun v hv n ↦ ?_⟩
  have h_w := sbd_solN_weighted_bound sys h hK_nonneg hB_ge_4 hInit hStep n v hv
  have h_drop : K * B ^ n / sbdSq n ≤ K * B ^ n :=
    div_le_self (by positivity) (sbdSq_ge_one n)
  exact le_trans h_w h_drop

#print axioms solN_geom_bound

end HAomega
