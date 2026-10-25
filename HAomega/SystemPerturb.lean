/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SystemBound

/-!
# Perturbation of the initial data of a polynomial system

Two polynomial–integral systems with the same equations `F` and constant
initial data `A`, `A'` of size at most `2^D`: if the initial values differ by at
most `δ`, every solution coefficient differs by at most `δ · 2^M · (2^R)^n`, with
`(M, R)` depending only on `F` and `D` — not on the data, and not on `δ`.

This is what re-centering needs: at a new centre the initial values are known
only approximately, and the bound turns the error in them into an error in every
coefficient, uniformly over all data of the given size.
-/

namespace HAomega

/-- Cauchy product difference bound in the weighted majorant class:
    `a * b - a' * b' = (a - a') * b + a' * (b - b')`. -/
theorem spt_mul_diff_bound (a a' b b' : Nat → Q) {K₁ K₂ D₁ D₂ B : Rat}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hB : 0 ≤ B)
    (m : Nat)
    (ha' : ∀ j ≤ m, |(a' j).val| ≤ K₁ * B ^ j / sbdSq j)
    (hb : ∀ j ≤ m, |(b j).val| ≤ K₂ * B ^ j / sbdSq j)
    (hda : ∀ j ≤ m, |(a j).val - (a' j).val| ≤ D₁ * B ^ j / sbdSq j)
    (hdb : ∀ j ≤ m, |(b j).val - (b' j).val| ≤ D₂ * B ^ j / sbdSq j) :
    |(((tmJetMul (Γ := [])).eval Env.nil) a b m).val -
      (((tmJetMul (Γ := [])).eval Env.nil) a' b' m).val| ≤
      (8 * D₁ * K₂ + 8 * K₁ * D₂) * B ^ m / sbdSq m := by
  rw [tmJetMul_eval, tmJetMul_eval]
  simp only [Jet.mul, TrigPoly.cauchyConvAux_val]
  rw [← Finset.sum_sub_distrib]
  have h_abs :
      |∑ j ∈ Finset.range (m + 1), ((a j).val * (b (m - j)).val - (a' j).val * (b' (m - j)).val)| ≤
      ∑ j ∈ Finset.range (m + 1), |(a j).val * (b (m - j)).val - (a' j).val * (b' (m - j)).val| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_terms :
      (∑ j ∈ Finset.range (m + 1), |(a j).val * (b (m - j)).val - (a' j).val * (b' (m - j)).val|) ≤
      ∑ j ∈ Finset.range (m + 1), ((D₁ * K₂ + K₁ * D₂) * B ^ m) * (1 / (sbdSq j * sbdSq (m - j))) := by
    refine Finset.sum_le_sum fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp hj
    have hmjm : m - j ≤ m := Nat.sub_le m j
    have hj_pos : 0 < sbdSq j := sbdSq_pos j
    have hmjm_pos : 0 < sbdSq (m - j) := sbdSq_pos (m - j)
    have h_split : (a j).val * (b (m - j)).val - (a' j).val * (b' (m - j)).val =
        ((a j).val - (a' j).val) * (b (m - j)).val +
        (a' j).val * ((b (m - j)).val - (b' (m - j)).val) := by ring
    have h_tri : |(a j).val * (b (m - j)).val - (a' j).val * (b' (m - j)).val| ≤
        |(a j).val - (a' j).val| * |(b (m - j)).val| +
        |(a' j).val| * |(b (m - j)).val - (b' (m - j)).val| := by
      rw [h_split]
      have h1 := abs_add_le (((a j).val - (a' j).val) * (b (m - j)).val)
        ((a' j).val * ((b (m - j)).val - (b' (m - j)).val))
      rw [abs_mul, abs_mul] at h1
      exact h1
    have h_p1 := mul_le_mul (hda j hjm) (hb (m - j) hmjm) (abs_nonneg _) (by positivity)
    have h_p2 := mul_le_mul (ha' j hjm) (hdb (m - j) hmjm) (abs_nonneg _) (by positivity)
    have h_pow : B ^ j * B ^ (m - j) = B ^ m := by
      rw [← pow_add, Nat.add_sub_of_le hjm]
    have h_eq : (D₁ * B ^ j / sbdSq j) * (K₂ * B ^ (m - j) / sbdSq (m - j)) +
        (K₁ * B ^ j / sbdSq j) * (D₂ * B ^ (m - j) / sbdSq (m - j)) =
        ((D₁ * K₂ + K₁ * D₂) * B ^ m) * (1 / (sbdSq j * sbdSq (m - j))) := by
      calc (D₁ * B ^ j / sbdSq j) * (K₂ * B ^ (m - j) / sbdSq (m - j)) +
            (K₁ * B ^ j / sbdSq j) * (D₂ * B ^ (m - j) / sbdSq (m - j))
          = ((D₁ * K₂ + K₁ * D₂) * (B ^ j * B ^ (m - j))) / (sbdSq j * sbdSq (m - j)) := by ring
        _ = ((D₁ * K₂ + K₁ * D₂) * B ^ m) * (1 / (sbdSq j * sbdSq (m - j))) := by
          rw [h_pow]; ring
    linarith
  rw [← Finset.mul_sum] at h_terms
  have h_conv := mul_le_mul_of_nonneg_left (sbd_conv_sum_le m)
    (show 0 ≤ (D₁ * K₂ + K₁ * D₂) * B ^ m by positivity)
  have h_rhs : ((D₁ * K₂ + K₁ * D₂) * B ^ m) * (8 / sbdSq m) =
      (8 * D₁ * K₂ + 8 * K₁ * D₂) * B ^ m / sbdSq m := by ring
  linarith

/-- Perturbation bound multiplier `Ψ_F(K, K₁) : Rat` for a polynomial–integral expression `F : JExprN`. -/
def sptDiffBound : JExprN → Rat → Rat → Rat
  | .var _, _, K₁ => K₁
  | .const _, _, _ => 0
  | .add a b, K, K₁ => sptDiffBound a K K₁ + sptDiffBound b K K₁
  | .sub a b, K, K₁ => sptDiffBound a K K₁ + sptDiffBound b K K₁
  | .mul a b, K, K₁ =>
      8 * sptDiffBound a K K₁ * sbdExprBound b K + 8 * sbdExprBound a K * sptDiffBound b K K₁
  | .integ a, K, K₁ => sptDiffBound a K K₁

theorem sptDiffBound_nonneg (F : JExprN) {K K₁ : Rat} (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁) :
    0 ≤ sptDiffBound F K K₁ := by
  induction F with
  | var _ => exact hK₁
  | const _ => exact le_refl 0
  | add _ _ iha ihb => exact add_nonneg iha ihb
  | sub _ _ iha ihb => exact add_nonneg iha ihb
  | mul a b iha ihb =>
    dsimp [sptDiffBound]
    have ha := sbdExprBound_nonneg a hK
    have hb := sbdExprBound_nonneg b hK
    positivity
  | integ _ iha => exact iha

/-- Truncated weighted difference bound for `sbdEvalExpr F`: if `W` and `W'` satisfy the `(K, B)`
    bound and their difference satisfies the `(δ * K₁, B)` bound up to degree `n`, then
    `F(W) - F(W')` satisfies the `(δ * sptDiffBound F K K₁, B)` bound up to degree `n`. -/
theorem spt_evalExpr_diff_bound (F : JExprN) (sysLen : Nat) (hWF : F.WF sysLen) (hCC : F.ConstsConst)
    (W W' : Nat → Nat → Q) {K K₁ δ B : Rat}
    (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁) (hδ : 0 ≤ δ) (hB : 4 ≤ B) (n : Nat)
    (hW : ∀ u < sysLen, ∀ m ≤ n, |(W u m).val| ≤ K * B ^ m / sbdSq m)
    (hW' : ∀ u < sysLen, ∀ m ≤ n, |(W' u m).val| ≤ K * B ^ m / sbdSq m)
    (hDiff : ∀ u < sysLen, ∀ m ≤ n, |(W u m).val - (W' u m).val| ≤ δ * K₁ * B ^ m / sbdSq m) :
    ∀ m ≤ n, |(sbdEvalExpr F W m).val - (sbdEvalExpr F W' m).val| ≤
      δ * sptDiffBound F K K₁ * B ^ m / sbdSq m := by
  have hB0 : (0 : Rat) ≤ B := by linarith
  induction F with
  | var i =>
    intro m hm
    have hev : sbdEvalExpr (.var i) W m = W i m := by
      change (Tm.var (Γ := [WTy]) .here).eval (Env.cons (σ := WTy) W Env.nil)
        ((natTm i).eval (Env.cons (σ := WTy) W Env.nil)) m = W i m
      rw [natTm_eval]
      rfl
    have hev' : sbdEvalExpr (.var i) W' m = W' i m := by
      change (Tm.var (Γ := [WTy]) .here).eval (Env.cons (σ := WTy) W' Env.nil)
        ((natTm i).eval (Env.cons (σ := WTy) W' Env.nil)) m = W' i m
      rw [natTm_eval]
      rfl
    rw [hev, hev']
    exact hDiff i hWF m hm
  | const c =>
    intro m _
    have hev : sbdEvalExpr (.const c) W m = c.eval Env.nil m := by
      dsimp [sbdEvalExpr, JExprN.toTm]
      rw [closedWk_eval]
    have hev' : sbdEvalExpr (.const c) W' m = c.eval Env.nil m := by
      dsimp [sbdEvalExpr, JExprN.toTm]
      rw [closedWk_eval]
    rw [hev, hev', sub_self, abs_zero]
    dsimp [sptDiffBound]
    simp only [mul_zero, zero_mul, zero_div, le_refl]
  | add a b iha ihb =>
    intro m hm
    have hev : (sbdEvalExpr (.add a b) W m).val =
        (sbdEvalExpr a W m).val + (sbdEvalExpr b W m).val :=
      Q.val_add _ _
    have hev' : (sbdEvalExpr (.add a b) W' m).val =
        (sbdEvalExpr a W' m).val + (sbdEvalExpr b W' m).val :=
      Q.val_add _ _
    rw [hev, hev']
    dsimp [sptDiffBound]
    have ha_m := iha hWF.1 hCC.1 m hm
    have hb_m := ihb hWF.2 hCC.2 m hm
    have h_split : ((sbdEvalExpr a W m).val + (sbdEvalExpr b W m).val) -
        ((sbdEvalExpr a W' m).val + (sbdEvalExpr b W' m).val) =
        ((sbdEvalExpr a W m).val - (sbdEvalExpr a W' m).val) +
        ((sbdEvalExpr b W m).val - (sbdEvalExpr b W' m).val) := by ring
    rw [h_split]
    have h_tri := abs_add_le ((sbdEvalExpr a W m).val - (sbdEvalExpr a W' m).val)
      ((sbdEvalExpr b W m).val - (sbdEvalExpr b W' m).val)
    have h_ring : δ * sptDiffBound a K K₁ * B ^ m / sbdSq m +
        δ * sptDiffBound b K K₁ * B ^ m / sbdSq m =
        δ * (sptDiffBound a K K₁ + sptDiffBound b K K₁) * B ^ m / sbdSq m := by ring
    linarith
  | sub a b iha ihb =>
    intro m hm
    have hev : (sbdEvalExpr (.sub a b) W m).val =
        (sbdEvalExpr a W m).val - (sbdEvalExpr b W m).val :=
      Q.val_sub _ _
    have hev' : (sbdEvalExpr (.sub a b) W' m).val =
        (sbdEvalExpr a W' m).val - (sbdEvalExpr b W' m).val :=
      Q.val_sub _ _
    rw [hev, hev']
    dsimp [sptDiffBound]
    have ha_m := iha hWF.1 hCC.1 m hm
    have hb_m := ihb hWF.2 hCC.2 m hm
    have h_split : ((sbdEvalExpr a W m).val - (sbdEvalExpr b W m).val) -
        ((sbdEvalExpr a W' m).val - (sbdEvalExpr b W' m).val) =
        ((sbdEvalExpr a W m).val - (sbdEvalExpr a W' m).val) -
        ((sbdEvalExpr b W m).val - (sbdEvalExpr b W' m).val) := by ring
    rw [h_split]
    have h_tri := abs_sub ((sbdEvalExpr a W m).val - (sbdEvalExpr a W' m).val)
      ((sbdEvalExpr b W m).val - (sbdEvalExpr b W' m).val)
    have h_ring : δ * sptDiffBound a K K₁ * B ^ m / sbdSq m +
        δ * sptDiffBound b K K₁ * B ^ m / sbdSq m =
        δ * (sptDiffBound a K K₁ + sptDiffBound b K K₁) * B ^ m / sbdSq m := by ring
    linarith
  | mul a b iha ihb =>
    intro m hm
    have hev : sbdEvalExpr (.mul a b) W m =
        ((tmJetMul (Γ := [])).eval Env.nil) (sbdEvalExpr a W) (sbdEvalExpr b W) m := rfl
    have hev' : sbdEvalExpr (.mul a b) W' m =
        ((tmJetMul (Γ := [])).eval Env.nil) (sbdEvalExpr a W') (sbdEvalExpr b W') m := rfl
    rw [hev, hev']
    dsimp [sptDiffBound]
    have ha' := sbd_evalExpr_bound a sysLen hWF.1 hCC.1 W' hK hB n hW'
    have hb := sbd_evalExpr_bound b sysLen hWF.2 hCC.2 W hK hB n hW
    have hΨa := sptDiffBound_nonneg a hK hK₁
    have hΨb := sptDiffBound_nonneg b hK hK₁
    have h_mul := spt_mul_diff_bound (sbdEvalExpr a W) (sbdEvalExpr a W')
      (sbdEvalExpr b W) (sbdEvalExpr b W')
      (sbdExprBound_nonneg a hK) (sbdExprBound_nonneg b hK)
      (mul_nonneg hδ hΨa) (mul_nonneg hδ hΨb) hB0 m
      (fun j hj ↦ ha' j (le_trans hj hm))
      (fun j hj ↦ hb j (le_trans hj hm))
      (fun j hj ↦ iha hWF.1 hCC.1 j (le_trans hj hm))
      (fun j hj ↦ ihb hWF.2 hCC.2 j (le_trans hj hm))
    have h_ring : (8 * (δ * sptDiffBound a K K₁) * sbdExprBound b K +
        8 * sbdExprBound a K * (δ * sptDiffBound b K K₁)) * B ^ m / sbdSq m =
        δ * (8 * sptDiffBound a K K₁ * sbdExprBound b K +
          8 * sbdExprBound a K * sptDiffBound b K K₁) * B ^ m / sbdSq m := by ring
    linarith
  | integ a iha =>
    intro m hm
    dsimp [sptDiffBound]
    cases m with
    | zero =>
      have hev : (sbdEvalExpr (.integ a) W 0).val = 0 := Q.val_ofNat 0
      have hev' : (sbdEvalExpr (.integ a) W' 0).val = 0 := Q.val_ofNat 0
      rw [hev, hev', sub_self, abs_zero]
      have hΨ : 0 ≤ sptDiffBound a K K₁ := sptDiffBound_nonneg a hK hK₁
      have hsq_pos : 0 < sbdSq 0 := sbdSq_pos 0
      positivity
    | succ k =>
      have hne : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
      have hev : (sbdEvalExpr (.integ a) W (k + 1)).val =
          (sbdEvalExpr a W k).val / ((k + 1 : Nat) : Rat) := by
        change (Q.div (sbdEvalExpr a W k) (Q.ofNat (k + 1))).val = _
        rw [Q.val_div _ _ hne, Q.val_ofNat]
      have hev' : (sbdEvalExpr (.integ a) W' (k + 1)).val =
          (sbdEvalExpr a W' k).val / ((k + 1 : Nat) : Rat) := by
        change (Q.div (sbdEvalExpr a W' k) (Q.ofNat (k + 1))).val = _
        rw [Q.val_div _ _ hne, Q.val_ofNat]
      have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        exact_mod_cast Nat.succ_pos k
      have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
      rw [hev, hev', ← sub_div, abs_div, abs_of_pos hk1_pos]
      have h_div_le : |(sbdEvalExpr a W k).val - (sbdEvalExpr a W' k).val| / ((k + 1 : Nat) : Rat) ≤
          |(sbdEvalExpr a W k).val - (sbdEvalExpr a W' k).val| :=
        div_le_self (abs_nonneg _) hk1_ge
      have ha_k := iha hWF hCC k (Nat.le_of_succ_le hm)
      have hΨ : 0 ≤ δ * sptDiffBound a K K₁ := mul_nonneg hδ (sptDiffBound_nonneg a hK hK₁)
      have h4Ψ : 4 * (δ * sptDiffBound a K K₁) ≤ (δ * sptDiffBound a K K₁) * B := by nlinarith
      have h_step := sbd_step_scale hΨ hB0 h4Ψ k
      linarith

/-- If `sys.map Prod.snd = sys'.map Prod.snd`, then `sys[v].2 = sys'[v].2` at every valid index `v`. -/
theorem spt_snd_eq_of_map_eq : ∀ (sys sys' : List (Tm [] JetTy × JExprN))
    (_ : sys.map Prod.snd = sys'.map Prod.snd) (v : Nat)
    (hv : v < sys.length) (hv' : v < sys'.length),
    sys[v].2 = sys'[v].2
  | [], _, _, _, hv, _ => absurd hv (Nat.not_lt_zero _)
  | _, [], _, _, _, hv' => absurd hv' (Nat.not_lt_zero _)
  | _ :: _, _ :: _, h, 0, _, _ => (List.cons.inj h).1
  | _ :: tl, _ :: tl', h, k + 1, hv, hv' =>
    spt_snd_eq_of_map_eq tl tl' (List.cons.inj h).2 k
      (Nat.lt_of_succ_lt_succ hv) (Nat.lt_of_succ_lt_succ hv')

/-- Convert an index-wise initial bound on `sys` into a membership-wise bound. -/
theorem spt_init_mem_of_getElem (sys : List (Tm [] JetTy × JExprN)) {K : Rat}
    (h : ∀ v (hv : v < sys.length), |((sys[v].1.eval Env.nil) 0).val| ≤ K) :
    ∀ p ∈ sys, |(p.1.eval Env.nil 0).val| ≤ K := by
  induction sys with
  | nil => intro _ hp; nomatch hp
  | cons _ tl ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact h 0 (Nat.zero_lt_succ _)
    · exact ih (fun v hv ↦ h (v + 1) (Nat.succ_lt_succ hv)) p hp'

/-- Maximum expression bound `sbdExprBound G K` across `G ∈ F` (at least `1`). -/
def sptMaxPhi (K : Rat) : List JExprN → Rat
  | [] => 1
  | G :: rest => max (sbdExprBound G K) (sptMaxPhi K rest)

theorem sptMaxPhi_mem (K : Rat) {F : List JExprN} {G : JExprN} (hG : G ∈ F) :
    sbdExprBound G K ≤ sptMaxPhi K F := by
  induction F with
  | nil => nomatch hG
  | cons hd rest ih =>
    simp only [List.mem_cons] at hG
    rcases hG with rfl | hG
    · exact le_max_left _ _
    · exact le_trans (ih hG) (le_max_right _ _)

/-- Maximum perturbation multiplier `sptDiffBound G K K₁` across `G ∈ F` (at least `1`). -/
def sptMaxPsi (K K₁ : Rat) : List JExprN → Rat
  | [] => 1
  | G :: rest => max (sptDiffBound G K K₁) (sptMaxPsi K K₁ rest)

theorem sptMaxPsi_mem (K K₁ : Rat) {F : List JExprN} {G : JExprN} (hG : G ∈ F) :
    sptDiffBound G K K₁ ≤ sptMaxPsi K K₁ F := by
  induction F with
  | nil => nomatch hG
  | cons hd rest ih =>
    simp only [List.mem_cons] at hG
    rcases hG with rfl | hG
    · exact le_max_left _ _
    · exact le_trans (ih hG) (le_max_right _ _)

/-- Strong induction for the weighted difference bound between `solN sys` and `solN sys'`. -/
theorem spt_solN_diff_weighted_bound (sys sys' : List (Tm [] JetTy × JExprN))
    (h : GPACSys sys) (h' : GPACSys sys') (hmap : sys.map Prod.snd = sys'.map Prod.snd)
    {K K₁ δ B : Rat} (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁) (hδ : 0 ≤ δ) (hB : 4 ≤ B)
    (hInit : ∀ p ∈ sys, |(p.1.eval Env.nil 0).val| ≤ K)
    (hInit' : ∀ p ∈ sys', |(p.1.eval Env.nil 0).val| ≤ K)
    (hStep : ∀ p ∈ sys, 4 * sbdExprBound p.2 K ≤ K * B)
    (hStep' : ∀ p ∈ sys', 4 * sbdExprBound p.2 K ≤ K * B)
    (hDiffInit : ∀ v (hv : v < sys.length) (hv' : v < sys'.length),
      |((sys[v].1.eval Env.nil) 0).val - ((sys'[v].1.eval Env.nil) 0).val| ≤ δ * K₁)
    (hDiffStep : ∀ p ∈ sys, 4 * sptDiffBound p.2 K K₁ ≤ K₁ * B) :
    ∀ n : Nat, ∀ v < sys.length,
      |(solN sys v n).val - (solN sys' v n).val| ≤ δ * K₁ * B ^ n / sbdSq n := by
  have hB0 : (0 : Rat) ≤ B := by linarith
  have hlen : sys.length = sys'.length := by
    have := congrArg List.length hmap
    simpa only [List.length_map] using this
  have hW := sbd_solN_weighted_bound sys h hK hB hInit hStep
  have hW' := sbd_solN_weighted_bound sys' h' hK hB hInit' hStep'
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    have hv' : v < sys'.length := hlen ▸ hv
    have hpv := h sys[v] (List.getElem_mem hv)
    cases m with
    | zero =>
      rw [uMul_solN_zero_val sys (gpac_wf h) v hv, uMul_solN_zero_val sys' (gpac_wf h') v hv']
      have hsq0 : sbdSq 0 = 1 := by unfold sbdSq; norm_num
      rw [hsq0, pow_zero, mul_one, div_one]
      exact hDiffInit v hv hv'
    | succ k =>
      rw [sbd_solN_succ_val sys h v hv k, sbd_solN_succ_val sys' h' v hv' k]
      rw [← spt_snd_eq_of_map_eq sys sys' hmap v hv hv']
      have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        exact_mod_cast Nat.succ_pos k
      have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
      rw [← sub_div, abs_div, abs_of_pos hk1_pos]
      have h_div_le :
          |(sbdEvalExpr sys[v].2 (solN sys) k).val - (sbdEvalExpr sys[v].2 (solN sys') k).val| /
            ((k + 1 : Nat) : Rat) ≤
          |(sbdEvalExpr sys[v].2 (solN sys) k).val - (sbdEvalExpr sys[v].2 (solN sys') k).val| :=
        div_le_self (abs_nonneg _) hk1_ge
      have h_expr := spt_evalExpr_diff_bound sys[v].2 sys.length hpv.1 hpv.2.2
        (solN sys) (solN sys') hK hK₁ hδ hB k
        (fun u hu j _ ↦ hW j u hu)
        (fun u hu j _ ↦ hW' j u (hlen ▸ hu))
        (fun u hu j hj ↦ ih j (Nat.lt_succ_of_le hj) u hu)
        k (le_refl k)
      have hΨ : 0 ≤ δ * sptDiffBound sys[v].2 K K₁ :=
        mul_nonneg hδ (sptDiffBound_nonneg sys[v].2 hK hK₁)
      have h4Ψ : 4 * (δ * sptDiffBound sys[v].2 K K₁) ≤ (δ * K₁) * B := by
        have hstep_v := mul_le_mul_of_nonneg_left (hDiffStep sys[v] (List.getElem_mem hv)) hδ
        linarith
      have h_scale := sbd_step_scale hΨ hB0 h4Ψ k
      linarith

/-- **Initial-data perturbation, uniform in the data.** -/
theorem solN_perturb_bound (F : List JExprN) (D : Nat) :
    ∃ M R : Nat, ∀ sys sys' : List (Tm [] JetTy × JExprN),
      GPACSys sys → GPACSys sys' → sys.map Prod.snd = F → sys'.map Prod.snd = F →
      (∀ v (hv : v < sys.length), |((sys[v].1.eval Env.nil) 0).val| ≤ (2 : Rat) ^ D) →
      (∀ v (hv : v < sys'.length), |((sys'[v].1.eval Env.nil) 0).val| ≤ (2 : Rat) ^ D) →
      ∀ δ : Rat,
      (∀ v (hv : v < sys.length) (hv' : v < sys'.length),
        |((sys[v].1.eval Env.nil) 0).val - ((sys'[v].1.eval Env.nil) 0).val| ≤ δ) →
      ∀ v, v < sys.length → ∀ n : Nat,
        |(solN sys v n).val - (solN sys' v n).val| ≤ δ * (2 : Rat) ^ M * ((2 : Rat) ^ R) ^ n := by
  let K : Rat := (2 : Rat) ^ D
  have hK_pos : (0 : Rat) < K := by positivity
  have hK_nonneg : (0 : Rat) ≤ K := le_of_lt hK_pos
  let K₁ : Rat := (2 : Rat) ^ (0 : Nat)
  have hK₁_pos : (0 : Rat) < K₁ := by positivity
  have hK₁_nonneg : (0 : Rat) ≤ K₁ := le_of_lt hK₁_pos
  rcases sbd_exists_two_pow_ge
    (max 4 (max (4 * sptMaxPhi K F / K) (4 * sptMaxPsi K K₁ F / K₁))) with ⟨R, hR⟩
  let B : Rat := (2 : Rat) ^ R
  have hB_ge_4 : (4 : Rat) ≤ B := le_trans (le_max_left _ _) hR
  have hB_nonneg : (0 : Rat) ≤ B := by linarith
  have hR_right : max (4 * sptMaxPhi K F / K) (4 * sptMaxPsi K K₁ F / K₁) ≤ B :=
    le_trans (le_max_right _ _) hR
  have hB_phi : 4 * sptMaxPhi K F ≤ K * B := by
    have h1 : 4 * sptMaxPhi K F / K ≤ B := le_trans (le_max_left _ _) hR_right
    have h2 : 4 * sptMaxPhi K F ≤ B * K := (div_le_iff₀ hK_pos).mp h1
    linarith
  have hB_psi : 4 * sptMaxPsi K K₁ F ≤ K₁ * B := by
    have h1 : 4 * sptMaxPsi K K₁ F / K₁ ≤ B := le_trans (le_max_right _ _) hR_right
    have h2 : 4 * sptMaxPsi K K₁ F ≤ B * K₁ := (div_le_iff₀ hK₁_pos).mp h1
    linarith
  refine ⟨0, R, fun sys sys' h h' hF hF' hInit_idx hInit'_idx δ hδ_init v hv n ↦ ?_⟩
  have hmap : sys.map Prod.snd = sys'.map Prod.snd := hF.trans hF'.symm
  have hlen : sys.length = sys'.length := by
    have := congrArg List.length hmap
    simpa only [List.length_map] using this
  have hv' : v < sys'.length := hlen ▸ hv
  have hδ_nonneg : 0 ≤ δ :=
    le_trans (abs_nonneg _) (hδ_init v hv hv')
  have hInit : ∀ p ∈ sys, |(p.1.eval Env.nil 0).val| ≤ K :=
    spt_init_mem_of_getElem sys hInit_idx
  have hInit' : ∀ p ∈ sys', |(p.1.eval Env.nil 0).val| ≤ K :=
    spt_init_mem_of_getElem sys' hInit'_idx
  have hStep : ∀ p ∈ sys, 4 * sbdExprBound p.2 K ≤ K * B := by
    intro p hp
    have hpF : p.2 ∈ F := hF ▸ List.mem_map_of_mem hp
    have := sptMaxPhi_mem K hpF
    linarith
  have hStep' : ∀ p ∈ sys', 4 * sbdExprBound p.2 K ≤ K * B := by
    intro p hp
    have hpF : p.2 ∈ F := hF' ▸ List.mem_map_of_mem hp
    have := sptMaxPhi_mem K hpF
    linarith
  have hDiffInit : ∀ u (hu : u < sys.length) (hu' : u < sys'.length),
      |((sys[u].1.eval Env.nil) 0).val - ((sys'[u].1.eval Env.nil) 0).val| ≤ δ * K₁ := by
    intro u hu hu'
    have hK₁_eq : K₁ = 1 := by norm_num [K₁]
    rw [hK₁_eq, mul_one]
    exact hδ_init u hu hu'
  have hDiffStep : ∀ p ∈ sys, 4 * sptDiffBound p.2 K K₁ ≤ K₁ * B := by
    intro p hp
    have hpF : p.2 ∈ F := hF ▸ List.mem_map_of_mem hp
    have := sptMaxPsi_mem K K₁ hpF
    linarith
  have h_w := spt_solN_diff_weighted_bound sys sys' h h' hmap
    hK_nonneg hK₁_nonneg hδ_nonneg hB_ge_4
    hInit hInit' hStep hStep' hDiffInit hDiffStep n v hv
  have h_drop : δ * K₁ * B ^ n / sbdSq n ≤ δ * K₁ * B ^ n :=
    div_le_self (by positivity) (sbdSq_ge_one n)
  exact le_trans h_w h_drop

#print axioms solN_perturb_bound

end HAomega
