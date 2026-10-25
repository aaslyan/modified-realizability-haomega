/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SystemRecenter

/-!
# Helper lemmas for uniform stepping from rational data

Uniform coefficient majorants and re-centering overlap assembly for the data
table `solFastD F a`, with all growth constants depending only on `F` and the
initial-data exponent `D`.
-/

namespace HAomega

/-- Recurrence value at degree `k + 1` for `solFastD F a`. -/
theorem stp_solFastD_succ_val (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    (a : List Q) (v : Nat) (hv : v < F.length) (k : Nat) :
    (solFastD F a v (k + 1)).val =
      (sbdEvalExpr F[v] (solFastD F a) k).val / ((k + 1 : Nat) : Rat) := by
  have hpv := hF F[v] (List.getElem_mem hv)
  have hne : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
  rw [rct_solFastD_succ F a v hv k, Q.val_div _ _ hne, Q.val_ofNat]
  congr 1
  exact sfst_sbdEvalExpr_congr F[v] F.length hpv.1
    (tableW (solRowsD F a k)) (solFastD F a) k
    (fun u _ j hj ↦ by rw [rct_tableW_eq_solFastD F a u k j hj])

/-- Weighted majorant bound for any coefficient table `z` satisfying the ODE recurrence of `F`. -/
theorem stp_z_weighted_bound (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    (z : Nat → Nat → Q) {K B : Rat} (hK : 0 ≤ K) (hB : 4 ≤ B)
    (hz_init : ∀ v < F.length, |(z v 0).val| ≤ K)
    (hz_succ : ∀ v (hv : v < F.length) (k : Nat),
      (z v (k + 1)).val = (sbdEvalExpr F[v] z k).val / ((k + 1 : Nat) : Rat))
    (hStep : ∀ Fv ∈ F, 4 * sbdExprBound Fv K ≤ K * B) :
    ∀ n : Nat, ∀ v < F.length, |(z v n).val| ≤ K * B ^ n / sbdSq n := by
  have hB0 : (0 : Rat) ≤ B := by linarith
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    have hpv := hF F[v] (List.getElem_mem hv)
    cases m with
    | zero =>
      have hsq0 : sbdSq 0 = 1 := by unfold sbdSq; norm_num
      rw [hsq0, pow_zero, mul_one, div_one]
      exact hz_init v hv
    | succ k =>
      rw [hz_succ v hv k]
      have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        exact_mod_cast Nat.succ_pos k
      have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
      rw [abs_div, abs_of_pos hk1_pos]
      have h_div_le : |(sbdEvalExpr F[v] z k).val| / ((k + 1 : Nat) : Rat) ≤
          |(sbdEvalExpr F[v] z k).val| :=
        div_le_self (abs_nonneg _) hk1_ge
      have h_expr := sbd_evalExpr_bound F[v] F.length hpv.1 hpv.2.1 z hK hB k
        (fun u hu j hj ↦ ih j (Nat.lt_succ_of_le hj) u hu) k (le_refl k)
      have hΦ : 0 ≤ sbdExprBound F[v] K := sbdExprBound_nonneg F[v] hK
      have h_scale := sbd_step_scale hΦ hB0 (hStep F[v] (List.getElem_mem hv)) k
      linarith

/-- Uniform weighted majorant bound for `solFastD F a` from bounded initial data `a`. -/
theorem stp_solFastD_weighted_bound (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    (a : List Q) (ha_len : a.length = F.length)
    {K B : Rat} (hK : 0 ≤ K) (hB : 4 ≤ B)
    (hInit : ∀ v (hv : v < a.length), |(a[v]).val| ≤ K)
    (hStep : ∀ Fv ∈ F, 4 * sbdExprBound Fv K ≤ K * B) :
    ∀ n : Nat, ∀ v < F.length, |(solFastD F a v n).val| ≤ K * B ^ n / sbdSq n := by
  refine stp_z_weighted_bound F hF (solFastD F a) hK hB (fun v hv ↦ ?_)
    (stp_solFastD_succ_val F hF a) hStep
  have hva : v < a.length := ha_len ▸ hv
  rw [rct_solFastD_zero F a v hva]
  exact hInit v hva

/-- Weighted bound for the degree-`N` truncation of a bounded table `c`. -/
theorem stp_trunc_weighted_bound (F : List JExprN) (c : Nat → Nat → Q) {K₀ B₀ : Rat}
    (hc_bd : ∀ u < F.length, ∀ m : Nat, |(c u m).val| ≤ K₀ * B₀ ^ m / sbdSq m)
    (N u : Nat) (hu : u < F.length) (m : Nat) :
    |(rctTrunc N (c u) m).val| ≤ K₀ * B₀ ^ m / sbdSq m := by
  by_cases hm : m < N
  · rw [rctTrunc_lt hm]
    exact hc_bd u hu m
  · rw [rctTrunc_ge (not_lt.mp hm), Q.val_zero, abs_zero]
    exact le_trans (abs_nonneg (c u m).val) (hc_bd u hu m)

/-- Below degree `N - 1`, the residual of `rctTrunc N (c u)` vanishes. -/
theorem stp_residual_zero_lt (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    (c : Nat → Nat → Q)
    (hc_succ : ∀ v (hv : v < F.length) (k : Nat),
      (c v (k + 1)).val = (sbdEvalExpr F[v] c k).val / ((k + 1 : Nat) : Rat))
    (N v : Nat) (hv : v < F.length) (m : Nat) (hm : m < N - 1) :
    (rctResidual F[v] (fun u ↦ rctTrunc N (c u)) v m).val = 0 := by
  have hm1 : m + 1 < N := by omega
  have hpv := hF F[v] (List.getElem_mem hv)
  unfold rctResidual
  dsimp only
  rw [Q.val_sub, Q.val_mul, Q.val_ofNat, rctTrunc_lt hm1, hc_succ v hv m]
  have hk1_ne : ((m + 1 : Nat) : Rat) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hk1_ne]
  have hcongr := sfst_sbdEvalExpr_congr F[v] F.length hpv.1
    (fun u ↦ rctTrunc N (c u)) c m fun u _ j hj ↦ by
      have hjN : j < N := by omega
      dsimp only
      rw [rctTrunc_lt hjN]
  rw [hcongr, sub_self]

/-- From degree `N - 1` onwards, the residual is bounded by `(K₀ * B₀) * B₀^m`. -/
theorem stp_residual_bound_ge (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    (c : Nat → Nat → Q) {K₀ B₀ : Rat} (hK₀ : 0 ≤ K₀) (hB₀ : 4 ≤ B₀)
    (hStep₀ : ∀ Fv ∈ F, 4 * sbdExprBound Fv K₀ ≤ K₀ * B₀)
    (hc_bd : ∀ u < F.length, ∀ m : Nat, |(c u m).val| ≤ K₀ * B₀ ^ m / sbdSq m)
    (N v : Nat) (hv : v < F.length) (m : Nat) (hm : N - 1 ≤ m) :
    |(rctResidual F[v] (fun u ↦ rctTrunc N (c u)) v m).val| ≤
      (K₀ * B₀) * B₀ ^ m := by
  have hm1 : N ≤ m + 1 := by omega
  have hpv := hF F[v] (List.getElem_mem hv)
  have hB₀_nonneg : (0 : Rat) ≤ B₀ := by linarith
  unfold rctResidual
  dsimp only
  rw [Q.val_sub, Q.val_mul, rctTrunc_ge hm1, Q.val_zero, mul_zero, zero_sub, abs_neg]
  have h_phi_nonneg : (0 : Rat) ≤ sbdExprBound F[v] K₀ :=
    sbdExprBound_nonneg F[v] hK₀
  have h_eb := sbd_evalExpr_bound F[v] F.length hpv.1 hpv.2.1
    (fun u ↦ rctTrunc N (c u)) hK₀ hB₀ m
    (fun u hu j _ ↦ stp_trunc_weighted_bound F c hc_bd N u hu j) m (le_refl m)
  have h_drop : sbdExprBound F[v] K₀ * B₀ ^ m / sbdSq m ≤ sbdExprBound F[v] K₀ * B₀ ^ m :=
    div_le_self (by positivity) (sbdSq_ge_one m)
  have h_step := hStep₀ F[v] (List.getElem_mem hv)
  have h_phi_le : sbdExprBound F[v] K₀ ≤ K₀ * B₀ := by linarith
  have h_mul : sbdExprBound F[v] K₀ * B₀ ^ m ≤ (K₀ * B₀) * B₀ ^ m :=
    mul_le_mul_of_nonneg_right h_phi_le (by positivity)
  linarith

/-- Geometric bound on the shifted truncated base table `d`. -/
theorem stp_d_geom_bound (F : List JExprN) (c : Nat → Nat → Q)
    {K₀ B₀ : Rat} (hK₀ : 0 ≤ K₀) (hB₀ : 4 ≤ B₀)
    (hc_bd : ∀ u < F.length, ∀ m : Nat, |(c u m).val| ≤ K₀ * B₀ ^ m / sbdSq m)
    (x₀ : Q) (N : Nat) (hx₀ : |x₀.val| ≤ 1 / (8 * B₀))
    (u : Nat) (hu : u < F.length) (n : Nat) :
    |(rctShift x₀.val N (rctTrunc N (c u)) n).val| ≤ (2 * K₀) * (8 * B₀) ^ n := by
  have hB₀_pos : (0 : Rat) < B₀ := by linarith
  have h_bd : ∀ m, 0 ≤ m → |(rctTrunc N (c u) m).val| ≤ K₀ * B₀ ^ m := by
    intro m _
    have hw := stp_trunc_weighted_bound F c hc_bd N u hu m
    exact le_trans hw (div_le_self (by positivity) (sbdSq_ge_one m))
  have h1 := rctShift_geom_bound x₀.val N 0 (rctTrunc N (c u))
    hK₀ hB₀_pos hx₀ (fun _ hm ↦ absurd hm (Nat.not_lt_zero _)) h_bd n
  rw [pow_zero, mul_one] at h1
  exact h1

/-- Weighted bound on the shifted truncated base table `d`. -/
theorem stp_d_weighted_bound (F : List JExprN) (c : Nat → Nat → Q)
    {K₀ B₀ : Rat} (hK₀ : 0 ≤ K₀) (hB₀ : 4 ≤ B₀)
    (hc_bd : ∀ u < F.length, ∀ m : Nat, |(c u m).val| ≤ K₀ * B₀ ^ m / sbdSq m)
    (x₀ : Q) (N : Nat) (hx₀ : |x₀.val| ≤ 1 / (8 * B₀))
    {B : Rat} (hB_32 : 32 * B₀ ≤ B)
    (u : Nat) (hu : u < F.length) (n : Nat) :
    |(rctShift x₀.val N (rctTrunc N (c u)) n).val| ≤ (2 * K₀) * B ^ n / sbdSq n := by
  have hB₀_pos : (0 : Rat) < B₀ := by linarith
  have h_bd : ∀ m, 0 ≤ m → |(rctTrunc N (c u) m).val| ≤ K₀ * B₀ ^ m := by
    intro m _
    have hw := stp_trunc_weighted_bound F c hc_bd N u hu m
    exact le_trans hw (div_le_self (by positivity) (sbdSq_ge_one m))
  have h1 := rctShift_weighted_bound x₀.val N 0 (rctTrunc N (c u))
    hK₀ hB₀_pos hx₀ (fun _ hm ↦ absurd hm (Nat.not_lt_zero _)) h_bd n
  rw [pow_zero, mul_one] at h1
  have hpow : (32 * B₀) ^ n ≤ B ^ n := pow_le_pow_left₀ (by positivity) hB_32 n
  have h2 : (2 * K₀) * (32 * B₀) ^ n / sbdSq n ≤ (2 * K₀) * B ^ n / sbdSq n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
      (le_of_lt (sbdSq_pos n))
  exact le_trans h1 h2

/-- Residual perturbation bound between `z` and `d := fun u ↦ rctShift x₀.val N (rctTrunc N (c u))`. -/
theorem stp_z_diff_weighted_bound (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    (c z : Nat → Nat → Q) {K₀ B₀ : Rat} (hK₀ : 0 ≤ K₀) (hB₀ : 4 ≤ B₀)
    (hStep₀ : ∀ Fv ∈ F, 4 * sbdExprBound Fv K₀ ≤ K₀ * B₀)
    (hc_bd : ∀ u < F.length, ∀ m : Nat, |(c u m).val| ≤ K₀ * B₀ ^ m / sbdSq m)
    (hc_succ : ∀ v (hv : v < F.length) (k : Nat),
      (c v (k + 1)).val = (sbdEvalExpr F[v] c k).val / ((k + 1 : Nat) : Rat))
    (x₀ : Q) {N : Nat} (hN : 1 ≤ N)
    (hx₀ : |x₀.val| ≤ 1 / (8 * B₀))
    {B : Rat} (hB_32 : 32 * B₀ ≤ B)
    (hStep : ∀ Fv ∈ F, 4 * sbdExprBound Fv (2 * K₀) ≤ (2 * K₀) * B)
    (hDiffStep : ∀ Fv ∈ F, 4 * (sptDiffBound Fv (2 * K₀) 1 + 1) ≤ B)
    (hz_zero : ∀ v < F.length, (z v 0).val = (Jet.evalPoly ⟨c v⟩ N x₀).val)
    (hz_succ : ∀ v (hv : v < F.length) (k : Nat),
      (z v (k + 1)).val = (sbdEvalExpr F[v] z k).val / ((k + 1 : Nat) : Rat)) :
    ∀ n : Nat, ∀ v < F.length,
      |(z v n).val - (rctShift x₀.val N (rctTrunc N (c v)) n).val| ≤
        (2 * (K₀ * B₀) * (1 / 2 : Rat) ^ (N - 1)) * 1 * B ^ n / sbdSq n := by
  let K : Rat := 2 * K₀
  let δ : Rat := 2 * (K₀ * B₀) * (1 / 2 : Rat) ^ (N - 1)
  let p : Nat → Nat → Q := fun u ↦ rctTrunc N (c u)
  let d : Nat → Nat → Q := fun u ↦ rctShift x₀.val N (p u)
  have hB_ge_4 : (4 : Rat) ≤ B := by linarith
  have hB0 : (0 : Rat) ≤ B := by linarith
  have hB₀_nonneg : (0 : Rat) ≤ B₀ := by linarith
  have hK_nonneg : (0 : Rat) ≤ K := by positivity
  have hδ_nonneg : (0 : Rat) ≤ δ := by positivity
  have hd_zero_eq : ∀ v < F.length, (z v 0).val = (d v 0).val := by
    intro v hv
    dsimp [d, p]
    rw [rctShift_zero_deg x₀ N (rctTrunc N (c v)),
        rct_evalPoly_trunc_eq N (c v) x₀, hz_zero v hv]
  have hz_init : ∀ v < F.length, |(z v 0).val| ≤ K := by
    intro v hv
    rw [hd_zero_eq v hv]
    have hd0 := stp_d_geom_bound F c hK₀ hB₀ hc_bd x₀ N hx₀ v hv 0
    rw [pow_zero, mul_one] at hd0
    exact hd0
  have hW_z := stp_z_weighted_bound F hF z hK_nonneg hB_ge_4 hz_init hz_succ hStep
  have hW_d : ∀ n : Nat, ∀ u < F.length, |(d u n).val| ≤ K * B ^ n / sbdSq n :=
    fun n u hu ↦ stp_d_weighted_bound F c hK₀ hB₀ hc_bd x₀ N hx₀ hB_32 u hu n
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    have hpv := hF F[v] (List.getElem_mem hv)
    cases m with
    | zero =>
      change |(z v 0).val - (d v 0).val| ≤ δ * 1 * B ^ 0 / sbdSq 0
      rw [hd_zero_eq v hv, sub_self, abs_zero]
      have hsq0 : (0 : Rat) < sbdSq 0 := sbdSq_pos 0
      positivity
    | succ k =>
      change |(z v (k + 1)).val - (d v (k + 1)).val| ≤ δ * 1 * B ^ (k + 1) / sbdSq (k + 1)
      let Deg := rctExprDeg F[v] N
      have h_rec := rct_shift_recurrence F[v] F.length hpv.1 hpv.2.1 hpv.2.2
        p x₀.val hN (le_refl Deg)
        (fun u _ ↦ rctSuppAt_trunc N (c u)) v hv k
      have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        exact_mod_cast Nat.succ_pos k
      have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
      have hk1_ne : ((k + 1 : Nat) : Rat) ≠ 0 := ne_of_gt hk1_pos
      have hd_succ : (d v (k + 1)).val =
          ((sbdEvalExpr F[v] d k).val +
            (rctShift x₀.val Deg (rctResidual F[v] p v) k).val) / ((k + 1 : Nat) : Rat) := by
        rw [eq_div_iff hk1_ne]
        linarith
      rw [hz_succ v hv k, hd_succ, ← sub_div, abs_div, abs_of_pos hk1_pos]
      have h_div_le :
          |(sbdEvalExpr F[v] z k).val -
            ((sbdEvalExpr F[v] d k).val +
              (rctShift x₀.val Deg (rctResidual F[v] p v) k).val)| /
            ((k + 1 : Nat) : Rat) ≤
          |(sbdEvalExpr F[v] z k).val -
            ((sbdEvalExpr F[v] d k).val +
              (rctShift x₀.val Deg (rctResidual F[v] p v) k).val)| :=
        div_le_self (abs_nonneg _) hk1_ge
      have h_split :
          (sbdEvalExpr F[v] z k).val -
            ((sbdEvalExpr F[v] d k).val +
              (rctShift x₀.val Deg (rctResidual F[v] p v) k).val) =
          ((sbdEvalExpr F[v] z k).val - (sbdEvalExpr F[v] d k).val) -
            (rctShift x₀.val Deg (rctResidual F[v] p v) k).val := by ring
      have h_tri :
          |(sbdEvalExpr F[v] z k).val -
            ((sbdEvalExpr F[v] d k).val +
              (rctShift x₀.val Deg (rctResidual F[v] p v) k).val)| ≤
          |(sbdEvalExpr F[v] z k).val - (sbdEvalExpr F[v] d k).val| +
            |(rctShift x₀.val Deg (rctResidual F[v] p v) k).val| := by
        rw [h_split]
        exact abs_sub _ _
      have h_expr := spt_evalExpr_diff_bound F[v] F.length hpv.1 hpv.2.1
        z d hK_nonneg (by norm_num) hδ_nonneg hB_ge_4 k
        (fun u hu j _ ↦ hW_z j u hu)
        (fun u hu j _ ↦ hW_d j u hu)
        (fun u hu j hj ↦ ih j (Nat.lt_succ_of_le hj) u hu)
        k (le_refl k)
      have h_res_32 := rctShift_weighted_bound x₀.val Deg (N - 1) (rctResidual F[v] p v)
        (show 0 ≤ K₀ * B₀ by positivity) (show 0 < B₀ by linarith) hx₀
        (stp_residual_zero_lt F hF c hc_succ N v hv)
        (stp_residual_bound_ge F hF c hK₀ hB₀ hStep₀ hc_bd N v hv) k
      have hpow_k : (32 * B₀) ^ k ≤ B ^ k := pow_le_pow_left₀ (by positivity) hB_32 k
      have h_res_B : δ * (32 * B₀) ^ k / sbdSq k ≤ δ * B ^ k / sbdSq k :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow_k hδ_nonneg)
          (le_of_lt (sbdSq_pos k))
      have h_res : |(rctShift x₀.val Deg (rctResidual F[v] p v) k).val| ≤ δ * B ^ k / sbdSq k :=
        le_trans h_res_32 h_res_B
      have h_comb :
          δ * sptDiffBound F[v] K 1 * B ^ k / sbdSq k + δ * B ^ k / sbdSq k =
          (δ * (sptDiffBound F[v] K 1 + 1)) * B ^ k / sbdSq k := by ring
      have hΨ_nonneg : (0 : Rat) ≤ δ * (sptDiffBound F[v] K 1 + 1) := by
        have := sptDiffBound_nonneg F[v] hK_nonneg (show (0 : Rat) ≤ 1 by norm_num)
        positivity
      have h4Ψ : 4 * (δ * (sptDiffBound F[v] K 1 + 1)) ≤ (δ * 1) * B := by
        have hstep_v := mul_le_mul_of_nonneg_left (hDiffStep F[v] (List.getElem_mem hv)) hδ_nonneg
        linarith
      have h_scale := sbd_step_scale hΨ_nonneg hB0 h4Ψ k
      linarith

/-- **Uniform overlap consistency for any base table `c` and re-centered table `z`**
    sharing the `(K₀, B₀)` majorant and ODE recurrence of `F`. -/
theorem stp_overlap_of_table (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    {K₀ B₀ : Rat} (hK₀ : 0 < K₀) (hB₀ : 4 ≤ B₀)
    (hStep₀ : ∀ Fv ∈ F, 4 * sbdExprBound Fv K₀ ≤ K₀ * B₀) :
    ∃ R : Nat, ∀ (c : Nat → Nat → Q) (z : Q → Nat → Nat → Nat → Q),
      (∀ u < F.length, ∀ m : Nat, |(c u m).val| ≤ K₀ * B₀ ^ m / sbdSq m) →
      (∀ v (hv : v < F.length) (k : Nat),
        (c v (k + 1)).val = (sbdEvalExpr F[v] c k).val / ((k + 1 : Nat) : Rat)) →
      (∀ (x₀ : Q) (N v : Nat), v < F.length →
        (z x₀ N v 0).val = (Jet.evalPoly ⟨c v⟩ N x₀).val) →
      (∀ (x₀ : Q) (N v : Nat) (hv : v < F.length) (k : Nat),
        (z x₀ N v (k + 1)).val = (sbdEvalExpr F[v] (z x₀ N) k).val / ((k + 1 : Nat) : Rat)) →
      ∀ x₀ t : Q,
      |x₀.val| ≤ 1 / (2 : Rat) ^ (R + 2) → |t.val| ≤ 1 / (2 : Rat) ^ (R + 2) →
      ∀ ε : Rat, 0 < ε → ∃ N₀ : Nat, ∀ N L : Nat, N₀ ≤ N → N₀ ≤ L →
        ∀ v, v < F.length →
          |(Jet.evalPoly ⟨z x₀ N v⟩ L t).val
            - (Jet.evalPoly ⟨c v⟩ L (Q.add x₀ t)).val| < ε := by
  let K : Rat := 2 * K₀
  have hK₀_nonneg : (0 : Rat) ≤ K₀ := le_of_lt hK₀
  have hB₀_ge_1 : (1 : Rat) ≤ B₀ := by linarith
  have hB₀_pos : (0 : Rat) < B₀ := by linarith
  have hK_pos : (0 : Rat) < K := by positivity
  rcases sbd_exists_two_pow_ge
    (max (32 * B₀) (max (4 * sptMaxPhi K F / K) (4 * (sptMaxPsi K 1 F + 1))))
    with ⟨R, hR⟩
  let B : Rat := (2 : Rat) ^ R
  have hB_32 : 32 * B₀ ≤ B := le_trans (le_max_left _ _) hR
  have hB_pos : (0 : Rat) < B := by linarith
  have hR_right : max (4 * sptMaxPhi K F / K) (4 * (sptMaxPsi K 1 F + 1)) ≤ B :=
    le_trans (le_max_right _ _) hR
  have hStep : ∀ Fv ∈ F, 4 * sbdExprBound Fv K ≤ K * B := by
    intro Fv hFv
    have h1 := sptMaxPhi_mem K hFv
    have h2 : 4 * sptMaxPhi K F / K ≤ B := le_trans (le_max_left _ _) hR_right
    have h3 : 4 * sptMaxPhi K F ≤ B * K := (div_le_iff₀ hK_pos).mp h2
    linarith
  have hDiffStep : ∀ Fv ∈ F, 4 * (sptDiffBound Fv K 1 + 1) ≤ B := by
    intro Fv hFv
    have h1 := sptMaxPsi_mem K 1 hFv
    have h2 : 4 * (sptMaxPsi K 1 F + 1) ≤ B := le_trans (le_max_right _ _) hR_right
    linarith
  refine ⟨R, fun c z hc_bd hc_succ hz_zero hz_succ x₀ t hx₀_in ht_in ε hε ↦ ?_⟩
  have hpow_R2 : (2 : Rat) ^ (R + 2) = 4 * B := by
    change (2 : Rat) ^ (R + 2) = 4 * (2 : Rat) ^ R
    rw [pow_add]
    ring
  have hx₀_4B : |x₀.val| ≤ 1 / (4 * B) := by rwa [hpow_R2] at hx₀_in
  have ht_4B : |t.val| ≤ 1 / (4 * B) := by rwa [hpow_R2] at ht_in
  have hx₀_8B₀ : |x₀.val| ≤ 1 / (8 * B₀) :=
    le_trans hx₀_4B (one_div_le_one_div_of_le (by positivity) (by linarith))
  have ht_32B₀ : |t.val| ≤ 1 / (4 * (8 * B₀)) :=
    le_trans ht_4B (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hxt_4B₀ : |(Q.add x₀ t).val| ≤ 1 / (4 * B₀) := by
    rw [Q.val_add]
    have h_sum : |x₀.val + t.val| ≤ 1 / (2 * B) := by
      have h_tri := abs_add_le x₀.val t.val
      have h_eq : 1 / (4 * B) + 1 / (4 * B) = 1 / (2 * B) := by ring
      linarith
    exact le_trans h_sum (one_div_le_one_div_of_le (by positivity) (by linarith))
  rcases sbd_exists_two_pow_ge ((12 * (K₀ * B₀) + 1) / ε) with ⟨M_eps, hM_eps⟩
  refine ⟨M_eps + 1, fun N L hN₀N hN₀L v hv ↦ ?_⟩
  have hN1 : 1 ≤ N := by omega
  let d : Nat → Q := rctShift x₀.val N (rctTrunc N (c v))
  let δ : Rat := 2 * (K₀ * B₀) * (1 / 2 : Rat) ^ (N - 1)
  have h_term1 : |(Jet.evalPoly ⟨z x₀ N v⟩ L t).val - (Jet.evalPoly ⟨d⟩ L t).val| ≤
      4 * (K₀ * B₀ * (1 / 2 : Rat) ^ M_eps) := by
    have h_z_d_coeff : ∀ n, 0 ≤ n → |(z x₀ N v n).val - (d n).val| ≤ δ * B ^ n := by
      intro n _
      have hw := stp_z_diff_weighted_bound F hF c (z x₀ N) hK₀_nonneg hB₀ hStep₀ hc_bd hc_succ
        x₀ hN1 hx₀_8B₀ hB_32 hStep hDiffStep (hz_zero x₀ N) (hz_succ x₀ N) n v hv
      have hdrop : δ * 1 * B ^ n / sbdSq n ≤ δ * B ^ n := by
        rw [mul_one]
        exact div_le_self (by positivity) (sbdSq_ge_one n)
      exact le_trans hw hdrop
    have h_raw := rct_evalPoly_diff_bound (z x₀ N v) d L 0 t
      (by positivity) hB_pos ht_4B (fun _ hn ↦ absurd hn (Nat.not_lt_zero _)) h_z_d_coeff
    rw [pow_zero, mul_one] at h_raw
    exact rct_scale_delta hK₀_nonneg (le_of_lt hB₀_pos) (by omega) h_raw
  have h_term2 :
      |(Jet.evalPoly ⟨c v⟩ N (Q.add x₀ t)).val - (Jet.evalPoly ⟨d⟩ L t).val| ≤
      4 * (K₀ * B₀ * (1 / 2 : Rat) ^ M_eps) := by
    have h_raw := rct_evalPoly_tail_bound d (le_max_right N L) t
      (by positivity) (by positivity) ht_32B₀
      (fun n _ ↦ stp_d_geom_bound F c hK₀_nonneg hB₀ hc_bd x₀ N hx₀_8B₀ v hv n)
    have h_shift_id :
        (Jet.evalPoly ⟨d⟩ (max N L) t).val =
          (Jet.evalPoly ⟨c v⟩ N (Q.add x₀ t)).val := by
      dsimp [d]
      rw [rct_evalPoly_shift x₀ t N (max N L) (le_max_left N L) (rctTrunc N (c v)),
          rct_evalPoly_trunc_eq N (c v) (Q.add x₀ t)]
    rw [h_shift_id] at h_raw
    exact rct_scale_half_pow hK₀_nonneg hB₀_ge_1 (by omega) h_raw
  have h_c_bd : ∀ n : Nat, |(c v n).val| ≤ K₀ * B₀ ^ n := by
    intro n
    exact le_trans (hc_bd v hv n)
      (div_le_self (by positivity) (sbdSq_ge_one n))
  have h_term3 :
      |(Jet.evalPoly ⟨c v⟩ (max N L) (Q.add x₀ t)).val -
        (Jet.evalPoly ⟨c v⟩ N (Q.add x₀ t)).val| ≤
      2 * (K₀ * B₀ * (1 / 2 : Rat) ^ M_eps) := by
    have h_raw := rct_evalPoly_tail_bound (c v) (le_max_left N L) (Q.add x₀ t)
      hK₀_nonneg hB₀_pos hxt_4B₀ (fun n _ ↦ h_c_bd n)
    exact rct_scale_half_pow_two hK₀_nonneg hB₀_ge_1 (by omega) h_raw
  have h_term4 :
      |(Jet.evalPoly ⟨c v⟩ (max N L) (Q.add x₀ t)).val -
        (Jet.evalPoly ⟨c v⟩ L (Q.add x₀ t)).val| ≤
      2 * (K₀ * B₀ * (1 / 2 : Rat) ^ M_eps) := by
    have h_raw := rct_evalPoly_tail_bound (c v) (le_max_right N L) (Q.add x₀ t)
      hK₀_nonneg hB₀_pos hxt_4B₀ (fun n _ ↦ h_c_bd n)
    exact rct_scale_half_pow_two hK₀_nonneg hB₀_ge_1 (by omega) h_raw
  exact lt_of_le_of_lt
    (rct_abs_chain_le h_term1 h_term2 h_term3 h_term4)
    (rct_twelve_half_pow_lt hε hM_eps)

/-- `sbdExprBound F K` is monotone in `K` for `0 ≤ K ≤ K'`. -/
theorem stp_sbdExprBound_mono (F : JExprN) {K K' : Rat} (hK : 0 ≤ K) (hKK' : K ≤ K') :
    sbdExprBound F K ≤ sbdExprBound F K' := by
  induction F with
  | var _ => exact hKK'
  | const _ => exact le_refl _
  | add _ _ iha ihb => exact add_le_add iha ihb
  | sub _ _ iha ihb => exact add_le_add iha ihb
  | mul a b iha ihb =>
    dsimp [sbdExprBound]
    have ha0 := sbdExprBound_nonneg a hK
    have hb0 := sbdExprBound_nonneg b hK
    have hK' : 0 ≤ K' := le_trans hK hKK'
    have ha'0 := sbdExprBound_nonneg a hK'
    exact mul_le_mul (mul_le_mul_of_nonneg_left iha (by norm_num)) ihb hb0 (by positivity)
  | integ _ iha => exact iha

/-- Uniform weighted bound for `solFastD F a` for any `1 ≤ K ≤ K_max` when `4 * Φ(K_max) ≤ B`. -/
theorem stp_solFastD_weighted_bound_getD (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    (a : List Q) {K K_max B : Rat} (hK1 : 1 ≤ K) (hKK : K ≤ K_max) (hB : 4 ≤ B)
    (hInit : ∀ v < F.length, |(a.getD v Q.zero).val| ≤ K)
    (hStep_max : ∀ Fv ∈ F, 4 * sbdExprBound Fv K_max ≤ B) :
    ∀ n : Nat, ∀ v < F.length, |(solFastD F a v n).val| ≤ K * B ^ n / sbdSq n := by
  have hK0 : (0 : Rat) ≤ K := by linarith
  have hB0 : (0 : Rat) ≤ B := by linarith
  refine stp_z_weighted_bound F hF (solFastD F a) hK0 hB hInit
    (stp_solFastD_succ_val F hF a) fun Fv hFv ↦ ?_
  have h1 := stp_sbdExprBound_mono Fv hK0 hKK
  have h2 := hStep_max Fv hFv
  have h3 : B ≤ K * B := le_mul_of_one_le_left hB0 hK1
  linarith

/-- Geometric sum bound `|S_N(f)(x)| ≤ 2 * K` when `|f n| ≤ K * B^n / sbdSq n` and `|x| ≤ 1 / (4 * B)`. -/
theorem stp_evalPoly_bound (f : Nat → Q) (N : Nat) (x : Q) {K B : Rat}
    (hK : 0 ≤ K) (hB : 0 < B) (hx : |x.val| ≤ 1 / (4 * B))
    (hf : ∀ n : Nat, |(f n).val| ≤ K * B ^ n / sbdSq n) :
    |(Jet.evalPoly ⟨f⟩ N x).val| ≤ 2 * K := by
  have h_bd : ∀ n, 0 ≤ n → |(f n).val| ≤ K * B ^ n := fun n _ ↦
    le_trans (hf n) (div_le_self (by positivity) (sbdSq_ge_one n))
  have h_tail := rct_evalPoly_tail_bound f (Nat.zero_le N) x hK hB hx h_bd
  have h_zero : (Jet.evalPoly ⟨f⟩ 0 x).val = 0 := by
    rw [rct_evalPoly_val_eq_sum, Finset.sum_range_zero]
  rw [h_zero, sub_zero, pow_zero, mul_one] at h_tail
  exact h_tail

/-- Weighted difference bound between `solFastD F a` and `solFastD F a'` for data `≤ K`. -/
theorem stp_solFastD_diff_weighted_bound (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    (a a' : List Q) {K δ B : Rat} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hB : 4 ≤ B)
    (ha : ∀ v < F.length, |(a.getD v Q.zero).val| ≤ K)
    (ha' : ∀ v < F.length, |(a'.getD v Q.zero).val| ≤ K)
    (hStep : ∀ Fv ∈ F, 4 * sbdExprBound Fv K ≤ K * B)
    (hDiffInit : ∀ v < F.length, |(a.getD v Q.zero).val - (a'.getD v Q.zero).val| ≤ δ)
    (hDiffStep : ∀ Fv ∈ F, 4 * sptDiffBound Fv K 1 ≤ B) :
    ∀ n : Nat, ∀ v < F.length,
      |(solFastD F a v n).val - (solFastD F a' v n).val| ≤ δ * 1 * B ^ n / sbdSq n := by
  have hB0 : (0 : Rat) ≤ B := by linarith
  have hW := stp_z_weighted_bound F hF (solFastD F a) hK hB ha
    (stp_solFastD_succ_val F hF a) hStep
  have hW' := stp_z_weighted_bound F hF (solFastD F a') hK hB ha'
    (stp_solFastD_succ_val F hF a') hStep
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    have hpv := hF F[v] (List.getElem_mem hv)
    cases m with
    | zero =>
      have hsq0 : sbdSq 0 = 1 := by unfold sbdSq; norm_num
      rw [hsq0, pow_zero, mul_one, mul_one, div_one]
      exact hDiffInit v hv
    | succ k =>
      rw [stp_solFastD_succ_val F hF a v hv k, stp_solFastD_succ_val F hF a' v hv k]
      have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        exact_mod_cast Nat.succ_pos k
      have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
      rw [← sub_div, abs_div, abs_of_pos hk1_pos]
      have h_div_le :
          |(sbdEvalExpr F[v] (solFastD F a) k).val -
            (sbdEvalExpr F[v] (solFastD F a') k).val| / ((k + 1 : Nat) : Rat) ≤
          |(sbdEvalExpr F[v] (solFastD F a) k).val -
            (sbdEvalExpr F[v] (solFastD F a') k).val| :=
        div_le_self (abs_nonneg _) hk1_ge
      have h_expr := spt_evalExpr_diff_bound F[v] F.length hpv.1 hpv.2.1
        (solFastD F a) (solFastD F a') hK (by norm_num) hδ hB k
        (fun u hu j _ ↦ hW j u hu)
        (fun u hu j _ ↦ hW' j u hu)
        (fun u hu j hj ↦ ih j (Nat.lt_succ_of_le hj) u hu)
        k (le_refl k)
      have hΨ : 0 ≤ δ * sptDiffBound F[v] K 1 :=
        mul_nonneg hδ (sptDiffBound_nonneg F[v] hK (by norm_num))
      have h4Ψ : 4 * (δ * sptDiffBound F[v] K 1) ≤ (δ * 1) * B := by
        have hstep_v := mul_le_mul_of_nonneg_left (hDiffStep F[v] (List.getElem_mem hv)) hδ
        linarith
      have h_scale := sbd_step_scale hΨ hB0 h4Ψ k
      linarith

/-- Combined data-Lipschitz and truncation bound for `evalPoly ⟨solFastD F a v⟩ N x`. -/
theorem stp_evalPoly_solFastD_diff (F : List JExprN)
    (hF : ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg)
    (a a' : List Q) {K δ B : Rat} (hK1 : 1 ≤ K) (hδ : 0 ≤ δ) (hB : 4 ≤ B)
    (ha : ∀ v < F.length, |(a.getD v Q.zero).val| ≤ K)
    (ha' : ∀ v < F.length, |(a'.getD v Q.zero).val| ≤ K)
    (hStep_max : ∀ Fv ∈ F, 4 * sbdExprBound Fv K ≤ B)
    (hDiffInit : ∀ v < F.length, |(a.getD v Q.zero).val - (a'.getD v Q.zero).val| ≤ δ)
    (hDiffStep : ∀ Fv ∈ F, 4 * sptDiffBound Fv K 1 ≤ B)
    (x : Q) (hx : |x.val| ≤ 1 / (4 * B))
    {N₀ N N' : Nat} (hN : N₀ ≤ N) (hN' : N₀ ≤ N') (v : Nat) (hv : v < F.length) :
    |(Jet.evalPoly ⟨solFastD F a v⟩ N x).val -
      (Jet.evalPoly ⟨solFastD F a' v⟩ N' x).val| ≤
      2 * δ + 4 * K * (1 / 2 : Rat) ^ N₀ := by
  have hK0 : (0 : Rat) ≤ K := by linarith
  have hB_pos : (0 : Rat) < B := by linarith
  have hStep : ∀ Fv ∈ F, 4 * sbdExprBound Fv K ≤ K * B := fun Fv hFv ↦
    le_trans (hStep_max Fv hFv) (le_mul_of_one_le_left (le_of_lt hB_pos) hK1)
  have h_diff_w := stp_solFastD_diff_weighted_bound F hF a a' hK0 hδ hB
    ha ha' hStep hDiffInit hDiffStep
  have h_diff_bd : ∀ n, 0 ≤ n →
      |(solFastD F a v n).val - (solFastD F a' v n).val| ≤ δ * B ^ n := by
    intro n _
    have hw := h_diff_w n v hv
    rw [mul_one] at hw
    exact le_trans hw (div_le_self (by positivity) (sbdSq_ge_one n))
  have h_lip := rct_evalPoly_diff_bound (solFastD F a v) (solFastD F a' v) N 0 x
    hδ hB_pos hx (fun _ hn ↦ absurd hn (Nat.not_lt_zero _)) h_diff_bd
  rw [pow_zero, mul_one] at h_lip
  have hW' := stp_solFastD_weighted_bound_getD F hF a' hK1 (le_refl K) hB ha' hStep_max
  have h_a'_bd : ∀ n, N₀ ≤ n → |(solFastD F a' v n).val| ≤ K * B ^ n := fun n _ ↦
    le_trans (hW' n v hv) (div_le_self (by positivity) (sbdSq_ge_one n))
  have h_tail1 := rct_evalPoly_tail_bound (solFastD F a' v) hN x hK0 hB_pos hx h_a'_bd
  have h_tail2 := rct_evalPoly_tail_bound (solFastD F a' v) hN' x hK0 hB_pos hx h_a'_bd
  have h_split :
      (Jet.evalPoly ⟨solFastD F a v⟩ N x).val - (Jet.evalPoly ⟨solFastD F a' v⟩ N' x).val =
      ((Jet.evalPoly ⟨solFastD F a v⟩ N x).val - (Jet.evalPoly ⟨solFastD F a' v⟩ N x).val) +
      (((Jet.evalPoly ⟨solFastD F a' v⟩ N x).val - (Jet.evalPoly ⟨solFastD F a' v⟩ N₀ x).val) -
        ((Jet.evalPoly ⟨solFastD F a' v⟩ N' x).val - (Jet.evalPoly ⟨solFastD F a' v⟩ N₀ x).val)) := by
    ring
  rw [h_split]
  have h_tri1 := abs_add_le
    ((Jet.evalPoly ⟨solFastD F a v⟩ N x).val - (Jet.evalPoly ⟨solFastD F a' v⟩ N x).val)
    (((Jet.evalPoly ⟨solFastD F a' v⟩ N x).val - (Jet.evalPoly ⟨solFastD F a' v⟩ N₀ x).val) -
      ((Jet.evalPoly ⟨solFastD F a' v⟩ N' x).val - (Jet.evalPoly ⟨solFastD F a' v⟩ N₀ x).val))
  have h_tri2 := abs_sub
    ((Jet.evalPoly ⟨solFastD F a' v⟩ N x).val - (Jet.evalPoly ⟨solFastD F a' v⟩ N₀ x).val)
    ((Jet.evalPoly ⟨solFastD F a' v⟩ N' x).val - (Jet.evalPoly ⟨solFastD F a' v⟩ N₀ x).val)
  linarith

end HAomega
