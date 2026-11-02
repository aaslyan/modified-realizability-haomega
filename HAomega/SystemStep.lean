/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SystemRecenter
import HAomega.StepKit

/-!
# Stepping: re-centering from data, uniformly

`recenter_overlap` re-centres a system whose data are jets. After one step only
rational data remain, so iterating needs the same theorem for the table
`solFastD F a` of equations `F` from data `a`, with the radius **uniform over
all data of size `≤ 2^D`**: the data each step produces are not known in
advance, only bounded.

`stepData F a x₀ N` is one step (new data `S_N(Y_v)(x₀)`), and `stepIter`
iterates it along a list of increments.
-/

namespace HAomega

/-- Equations that can be stepped: well formed, constant leaves constant jets, flat. -/
def StepEqs (F : List JExprN) : Prop :=
  ∀ Fv ∈ F, Fv.WF F.length ∧ Fv.ConstsConst ∧ Fv.NoInteg

/-- One step: the data re-centred at `x₀`, to degree `N`. -/
def stepData (F : List JExprN) (a : List Q) (x₀ : Q) (N : Nat) : List Q :=
  (List.range F.length).map fun v ↦ Jet.evalPoly ⟨solFastD F a v⟩ N x₀

/-- Steps along the increments `hs`, each to degree `N`. -/
def stepIter (F : List JExprN) (N : Nat) : List Q → List Q → List Q
  | a, [] => a
  | a, h :: hs => stepIter F N (stepData F a h N) hs

theorem stp_stepData_zero_val (F : List JExprN) (a : List Q) (x₀ : Q) (N v : Nat)
    (hv : v < F.length) :
    (solFastD F (stepData F a x₀ N) v 0).val =
      (Jet.evalPoly ⟨solFastD F a v⟩ N x₀).val := by
  have hva : v < (stepData F a x₀ N).length := by
    simp [stepData, hv]
  rw [rct_solFastD_zero F (stepData F a x₀ N) v hva]
  simp [stepData]

/-- **Consistency of one step, uniformly in the data.** -/
theorem stepData_overlap (F : List JExprN) (hF : StepEqs F) (D : Nat) :
    ∃ R : Nat, ∀ a : List Q, a.length = F.length →
      (∀ v (hv : v < a.length), |(a[v]).val| ≤ (2 : Rat) ^ D) →
      ∀ x₀ t : Q,
      |x₀.val| ≤ 1 / (2 : Rat) ^ (R + 2) → |t.val| ≤ 1 / (2 : Rat) ^ (R + 2) →
      ∀ ε : Rat, 0 < ε → ∃ N₀ : Nat, ∀ N L : Nat, N₀ ≤ N → N₀ ≤ L →
        ∀ v, v < F.length →
          |(Jet.evalPoly ⟨solFastD F (stepData F a x₀ N) v⟩ L t).val
            - (Jet.evalPoly ⟨solFastD F a v⟩ L (Q.add x₀ t)).val| < ε := by
  let K₀ : Rat := (2 : Rat) ^ D
  have hK₀_pos : (0 : Rat) < K₀ := by positivity
  have hK₀_nonneg : (0 : Rat) ≤ K₀ := le_of_lt hK₀_pos
  rcases sbd_exists_two_pow_ge (max 4 (4 * sptMaxPhi K₀ F / K₀)) with ⟨R₀, hR₀⟩
  let B₀ : Rat := (2 : Rat) ^ R₀
  have hB₀_ge_4 : (4 : Rat) ≤ B₀ := le_trans (le_max_left _ _) hR₀
  have hStep₀ : ∀ Fv ∈ F, 4 * sbdExprBound Fv K₀ ≤ K₀ * B₀ := by
    intro Fv hFv
    have h1 := sptMaxPhi_mem K₀ hFv
    have h2 : 4 * sptMaxPhi K₀ F / K₀ ≤ B₀ := le_trans (le_max_right _ _) hR₀
    have h3 : 4 * sptMaxPhi K₀ F ≤ B₀ * K₀ := (div_le_iff₀ hK₀_pos).mp h2
    linarith
  rcases stp_overlap_of_table F hF hK₀_pos hB₀_ge_4 hStep₀ with ⟨R, hR⟩
  refine ⟨R, fun a ha_len ha_bd ↦ ?_⟩
  exact hR (solFastD F a) (fun x₀ N ↦ solFastD F (stepData F a x₀ N))
    (fun u hu m ↦ stp_solFastD_weighted_bound F hF a ha_len hK₀_nonneg hB₀_ge_4 ha_bd hStep₀ m u hu)
    (stp_solFastD_succ_val F hF a)
    (stp_stepData_zero_val F a)
    (fun x₀ N ↦ stp_solFastD_succ_val F hF (stepData F a x₀ N))

/-- One-step data growth bound: `stepData F a h N` doubles the initial data bound `K`
    when `1 ≤ K ≤ K_max` and `|h.val| ≤ 1 / (4 * B)`. -/
theorem stp_stepData_bound (F : List JExprN) (hF : StepEqs F)
    (a : List Q) {K K_max B : Rat} (hK1 : 1 ≤ K) (hKK : K ≤ K_max) (hB : 4 ≤ B)
    (ha : ∀ v < F.length, |(a.getD v Q.zero).val| ≤ K)
    (hStep_max : ∀ Fv ∈ F, 4 * sbdExprBound Fv K_max ≤ B)
    (h : Q) (hh : |h.val| ≤ 1 / (4 * B)) (N v : Nat) (hv : v < F.length) :
    |((stepData F a h N).getD v Q.zero).val| ≤ 2 * K := by
  have h0 : ((stepData F a h N).getD v Q.zero).val =
      (Jet.evalPoly ⟨solFastD F a v⟩ N h).val :=
    stp_stepData_zero_val F a h N v hv
  rw [h0]
  exact stp_evalPoly_bound (solFastD F a v) N h (by linarith) (by linarith) hh
    (fun n ↦ stp_solFastD_weighted_bound_getD F hF a hK1 hKK hB ha hStep_max n v hv)

/-- Inductive error and growth bound along `hs` for `stepIter F N a hs` vs `stepIter F N' a' hs`. -/
theorem stp_stepIter_diff_bound (F : List JExprN) (hF : StepEqs F)
    (D k : Nat) {B : Rat} (hB : 4 ≤ B)
    (hStep_max : ∀ Fv ∈ F, 4 * sbdExprBound Fv ((2 : Rat) ^ (D + k)) ≤ B)
    (hDiffStep : ∀ Fv ∈ F, 4 * sptDiffBound Fv ((2 : Rat) ^ (D + k)) 1 ≤ B)
    {N₀ N N' : Nat} (hN : N₀ ≤ N) (hN' : N₀ ≤ N')
    (hs : List Q) (hh : ∀ h ∈ hs, |h.val| ≤ 1 / (4 * B))
    (j : Nat) (hj : j + hs.length ≤ k)
    (a a' : List Q) {δ : Rat} (hδ : 0 ≤ δ)
    (ha : ∀ v < F.length, |(a.getD v Q.zero).val| ≤ (2 : Rat) ^ (D + j))
    (ha' : ∀ v < F.length, |(a'.getD v Q.zero).val| ≤ (2 : Rat) ^ (D + j))
    (hDiff : ∀ v < F.length, |(a.getD v Q.zero).val - (a'.getD v Q.zero).val| ≤ δ)
    (v : Nat) (hv : v < F.length) :
    |((stepIter F N a hs).getD v Q.zero).val -
      ((stepIter F N' a' hs).getD v Q.zero).val| ≤
      (2 : Rat) ^ hs.length * δ +
        ((2 : Rat) ^ hs.length - 1) * (4 * (2 : Rat) ^ (D + k) * (1 / 2 : Rat) ^ N₀) := by
  induction hs generalizing j a a' δ with
  | nil =>
    simp only [stepIter, List.length_nil, pow_zero, one_mul, sub_self, zero_mul, add_zero]
    exact hDiff v hv
  | cons h tl ih =>
    let K_max : Rat := (2 : Rat) ^ (D + k)
    let K_j : Rat := (2 : Rat) ^ (D + j)
    let τ : Rat := 4 * K_max * (1 / 2 : Rat) ^ N₀
    have hh_in : |h.val| ≤ 1 / (4 * B) := hh h (List.mem_cons_self ..)
    have htl_in : ∀ h' ∈ tl, |h'.val| ≤ 1 / (4 * B) :=
      fun h' hh' ↦ hh h' (List.mem_cons_of_mem h hh')
    have hj_tl : (j + 1) + tl.length ≤ k := by
      simp only [List.length_cons] at hj
      omega
    have hj_le : D + j ≤ D + k := by omega
    have hKj_ge_1 : (1 : Rat) ≤ K_j := one_le_pow₀ (by norm_num)
    have hKmax_ge_1 : (1 : Rat) ≤ K_max := one_le_pow₀ (by norm_num)
    have hKj_le_max : K_j ≤ K_max := pow_le_pow_right₀ (by norm_num) hj_le
    have h2Kj : 2 * K_j = (2 : Rat) ^ (D + (j + 1)) := by
      change 2 * (2 : Rat) ^ (D + j) = (2 : Rat) ^ (D + (j + 1))
      rw [show D + (j + 1) = (D + j) + 1 by omega, pow_succ]
      ring
    have hb : ∀ u < F.length, |((stepData F a h N).getD u Q.zero).val| ≤ (2 : Rat) ^ (D + (j + 1)) := by
      intro u hu
      rw [← h2Kj]
      exact stp_stepData_bound F hF a hKj_ge_1 hKj_le_max hB ha hStep_max h hh_in N u hu
    have hb' : ∀ u < F.length, |((stepData F a' h N').getD u Q.zero).val| ≤ (2 : Rat) ^ (D + (j + 1)) := by
      intro u hu
      rw [← h2Kj]
      exact stp_stepData_bound F hF a' hKj_ge_1 hKj_le_max hB ha' hStep_max h hh_in N' u hu
    have ha_max : ∀ u < F.length, |(a.getD u Q.zero).val| ≤ K_max :=
      fun u hu ↦ le_trans (ha u hu) hKj_le_max
    have ha'_max : ∀ u < F.length, |(a'.getD u Q.zero).val| ≤ K_max :=
      fun u hu ↦ le_trans (ha' u hu) hKj_le_max
    have hb_diff : ∀ u < F.length,
        |((stepData F a h N).getD u Q.zero).val - ((stepData F a' h N').getD u Q.zero).val| ≤
          2 * δ + τ := by
      intro u hu
      have h0 : ((stepData F a h N).getD u Q.zero).val =
          (Jet.evalPoly ⟨solFastD F a u⟩ N h).val :=
        stp_stepData_zero_val F a h N u hu
      have h0' : ((stepData F a' h N').getD u Q.zero).val =
          (Jet.evalPoly ⟨solFastD F a' u⟩ N' h).val :=
        stp_stepData_zero_val F a' h N' u hu
      rw [h0, h0']
      exact stp_evalPoly_solFastD_diff F hF a a' hKmax_ge_1 hδ hB
        ha_max ha'_max hStep_max hDiff hDiffStep h hh_in hN hN' u hu
    have hδ' : 0 ≤ 2 * δ + τ := by
      dsimp [τ, K_max]
      positivity
    have h_step := ih htl_in (j + 1) hj_tl (stepData F a h N) (stepData F a' h N') hδ' hb hb' hb_diff
    have h_id :
        (2 : Rat) ^ tl.length * (2 * δ + τ) + ((2 : Rat) ^ tl.length - 1) * τ =
        (2 : Rat) ^ (h :: tl).length * δ + ((2 : Rat) ^ (h :: tl).length - 1) * τ := by
      simp only [List.length_cons, pow_succ]
      ring
    dsimp only [stepIter]
    linarith

/-- **The continuation is well defined**: after `k` steps of size at most
`2^{-(R+2)}`, the data computed at precisions `N, N'` agree within any `ε` once
both pass some `N₀` (`R` depends on the equations, `D` and `k` — the data can
double at each step). -/
theorem stepIter_cauchy (F : List JExprN) (hF : StepEqs F) (D k : Nat) :
    ∃ R : Nat, ∀ a : List Q, a.length = F.length →
      (∀ v (hv : v < a.length), |(a[v]).val| ≤ (2 : Rat) ^ D) →
      ∀ hs : List Q, hs.length ≤ k → (∀ h ∈ hs, |h.val| ≤ 1 / (2 : Rat) ^ (R + 2)) →
      ∀ ε : Rat, 0 < ε → ∃ N₀ : Nat, ∀ N N' : Nat, N₀ ≤ N → N₀ ≤ N' →
        ∀ v, v < F.length →
          |((stepIter F N a hs).getD v Q.zero).val
            - ((stepIter F N' a hs).getD v Q.zero).val| < ε := by
  let K_max : Rat := (2 : Rat) ^ (D + k)
  rcases sbd_exists_two_pow_ge
    (max 4 (max (4 * sptMaxPhi K_max F) (4 * sptMaxPsi K_max 1 F))) with ⟨R, hR⟩
  let B : Rat := (2 : Rat) ^ R
  have hB_ge_4 : (4 : Rat) ≤ B := le_trans (le_max_left _ _) hR
  have hR_right : max (4 * sptMaxPhi K_max F) (4 * sptMaxPsi K_max 1 F) ≤ B :=
    le_trans (le_max_right _ _) hR
  have hStep_max : ∀ Fv ∈ F, 4 * sbdExprBound Fv K_max ≤ B := by
    intro Fv hFv
    have h1 := sptMaxPhi_mem K_max hFv
    have h2 : 4 * sptMaxPhi K_max F ≤ B := le_trans (le_max_left _ _) hR_right
    linarith
  have hDiffStep : ∀ Fv ∈ F, 4 * sptDiffBound Fv K_max 1 ≤ B := by
    intro Fv hFv
    have h1 := sptMaxPsi_mem K_max 1 hFv
    have h2 : 4 * sptMaxPsi K_max 1 F ≤ B := le_trans (le_max_right _ _) hR_right
    linarith
  have hpow_R2 : (2 : Rat) ^ (R + 2) = 4 * B := by
    change (2 : Rat) ^ (R + 2) = 4 * (2 : Rat) ^ R
    rw [pow_add]
    ring
  refine ⟨R, fun a ha_len ha_bd hs hhs_len hhs_bd ε hε ↦ ?_⟩
  let A : Rat := (2 : Rat) ^ k * K_max
  rcases sbd_exists_two_pow_ge ((12 * A + 1) / ε) with ⟨N₀, hN₀⟩
  refine ⟨N₀, fun N N' hN hN' v hv ↦ ?_⟩
  have hh : ∀ h ∈ hs, |h.val| ≤ 1 / (4 * B) := by
    intro h hh_mem
    have := hhs_bd h hh_mem
    rwa [hpow_R2] at this
  have ha_getD : ∀ u < F.length, |(a.getD u Q.zero).val| ≤ (2 : Rat) ^ (D + 0) := by
    intro u hu
    have hua : u < a.length := ha_len ▸ hu
    rw [uDeriv_getD_eq_getElem a Q.zero u hua, Nat.add_zero]
    exact ha_bd u hua
  have hDiff0 : ∀ u < F.length, |(a.getD u Q.zero).val - (a.getD u Q.zero).val| ≤ 0 := by
    intro u _
    rw [sub_self, abs_zero]
  have h_iter := stp_stepIter_diff_bound F hF D k hB_ge_4 hStep_max hDiffStep
    hN hN' hs hh 0 (by omega) a a (le_refl 0) ha_getD ha_getD hDiff0 v hv
  have h_pow_le : (2 : Rat) ^ hs.length - 1 ≤ (2 : Rat) ^ k := by
    have : (2 : Rat) ^ hs.length ≤ (2 : Rat) ^ k :=
      pow_le_pow_right₀ (by norm_num) hhs_len
    linarith
  have h_tau_nonneg : (0 : Rat) ≤ 4 * K_max * (1 / 2 : Rat) ^ N₀ := by
    dsimp [K_max]
    positivity
  have h_le_4A :
      (2 : Rat) ^ hs.length * 0 +
        ((2 : Rat) ^ hs.length - 1) * (4 * K_max * (1 / 2 : Rat) ^ N₀) ≤
      12 * (A * (1 / 2 : Rat) ^ N₀) := by
    have h1 : ((2 : Rat) ^ hs.length - 1) * (4 * K_max * (1 / 2 : Rat) ^ N₀) ≤
        (2 : Rat) ^ k * (4 * K_max * (1 / 2 : Rat) ^ N₀) :=
      mul_le_mul_of_nonneg_right h_pow_le h_tau_nonneg
    have h2 : (2 : Rat) ^ k * (4 * K_max * (1 / 2 : Rat) ^ N₀) =
        4 * (A * (1 / 2 : Rat) ^ N₀) := by
      dsimp [A]
      ring
    have hA_nonneg : (0 : Rat) ≤ A * (1 / 2 : Rat) ^ N₀ := by
      dsimp [A, K_max]
      positivity
    linarith
  exact lt_of_le_of_lt (le_trans h_iter h_le_4A) (rct_twelve_half_pow_lt hε hN₀)

/-! ## Explicit syntax-computed radii and moduli (choice-free)

Just as `sysParams` (`SystemEval.lean`) replaces the existential `∃ (M, R)` in
`solN_geom_bound` with a syntax-computed pair, the definitions below replace the
existentials `∃ R, ... ∃ N₀` in `stepData_overlap` and `stepIter_cauchy` with
explicit functions of the system equations `F`, initial-data exponent `D`, step
count `k`, and dyadic precision `2⁻ᵐ`. -/

/-- Computed base radius exponent `R₀` for data bounded by `2^D`:
    `2^R₀ ≥ 4 * stepMaxPhiN (2^D) F + 4`. -/
def stepBaseRadius (F : List JExprN) (D : Nat) : Nat :=
  (4 * stepMaxPhiN (2 ^ D) F + 4).log2 + 1

/-- Computed overlap radius exponent `R` for one re-centering step from data `≤ 2^D`. -/
def stepOverlapRadius (F : List JExprN) (D : Nat) : Nat :=
  let R₀ := stepBaseRadius F D
  let K := 2 ^ (D + 1)
  (max (32 * 2 ^ R₀) (max (4 * stepMaxPhiN K F) (4 * (stepMaxPsiN K 1 F + 1)))).log2 + 1

/-- Computed truncation modulus `N₀(D, m)` for one re-centering step to precision `2⁻ᵐ`. -/
def stepOverlapModulus (F : List JExprN) (D m : Nat) : Nat :=
  m + D + stepBaseRadius F D + 5

/-- **Choice-free one-step overlap with computed radius and modulus.** -/
theorem stepData_overlap_computed (F : List JExprN) (hF : StepEqs F) (D : Nat)
    (a : List Q) (ha_len : a.length = F.length)
    (ha_bd : ∀ v (hv : v < a.length), |(a[v]).val| ≤ (2 : Rat) ^ D)
    (x₀ t : Q)
    (hx₀ : |x₀.val| ≤ 1 / (2 : Rat) ^ (stepOverlapRadius F D + 2))
    (ht : |t.val| ≤ 1 / (2 : Rat) ^ (stepOverlapRadius F D + 2))
    (m N L : Nat)
    (hN : stepOverlapModulus F D m ≤ N) (hL : stepOverlapModulus F D m ≤ L)
    (v : Nat) (hv : v < F.length) :
    |(Jet.evalPoly ⟨solFastD F (stepData F a x₀ N) v⟩ L t).val
      - (Jet.evalPoly ⟨solFastD F a v⟩ L (Q.add x₀ t)).val| < 1 / (2 : Rat) ^ m := by
  let R₀ := stepBaseRadius F D
  let R := stepOverlapRadius F D
  let K₀ : Rat := (2 : Rat) ^ D
  let B₀ : Rat := (2 : Rat) ^ R₀
  let B : Rat := (2 : Rat) ^ R
  have hK₀_pos : (0 : Rat) < K₀ := by positivity
  have hK₀_nonneg : (0 : Rat) ≤ K₀ := le_of_lt hK₀_pos
  have hK₀_ge_1 : (1 : Rat) ≤ K₀ := one_le_pow₀ (by norm_num)
  have hK₀_cast : (((2 ^ D : Nat) : Nat) : Rat) = K₀ := by push_cast; rfl
  have h2K₀_cast : (((2 ^ (D + 1) : Nat) : Nat) : Rat) = 2 * K₀ := by
    change (((2 ^ (D + 1) : Nat) : Nat) : Rat) = 2 * (2 : Rat) ^ D
    push_cast; rw [pow_succ]; ring
  have hR₀_le : ((4 * stepMaxPhiN (2 ^ D) F + 4 : Nat) : Rat) ≤ (2 : Rat) ^ R₀ := by
    exact_mod_cast (Nat.lt_log2_self (n := 4 * stepMaxPhiN (2 ^ D) F + 4)).le
  have hB₀_ge_4 : (4 : Rat) ≤ B₀ := by
    push_cast at hR₀_le
    have : (0 : Rat) ≤ (stepMaxPhiN (2 ^ D) F : Rat) := Nat.cast_nonneg _
    linarith
  have hStep₀ : ∀ Fv ∈ F, 4 * sbdExprBound Fv K₀ ≤ K₀ * B₀ := by
    intro Fv hFv
    have h1 := sbdExprBound_le_natBound Fv (2 ^ D)
    rw [hK₀_cast] at h1
    have h2 : (Fv.natBound (2 ^ D) : Rat) ≤ (stepMaxPhiN (2 ^ D) F : Rat) := by
      exact_mod_cast stepMaxPhiN_mem (2 ^ D) hFv
    push_cast at hR₀_le
    have hB₀_0 : (0 : Rat) ≤ B₀ := by linarith
    have h4 : 4 * sbdExprBound Fv K₀ ≤ B₀ := by linarith
    exact le_trans h4 (le_mul_of_one_le_left hB₀_0 hK₀_ge_1)
  let M_R := max (32 * 2 ^ R₀) (max (4 * stepMaxPhiN (2 ^ (D + 1)) F) (4 * (stepMaxPsiN (2 ^ (D + 1)) 1 F + 1)))
  have hR_le : (M_R : Rat) ≤ (2 : Rat) ^ R := by
    exact_mod_cast (Nat.lt_log2_self (n := M_R)).le
  have hB_32 : 32 * B₀ ≤ B := by
    have h1 : (32 * 2 ^ R₀ : Nat) ≤ M_R := le_max_left _ _
    have h2 : ((32 * 2 ^ R₀ : Nat) : Rat) ≤ (M_R : Rat) := by exact_mod_cast h1
    push_cast at h2
    exact le_trans h2 hR_le
  have hStep : ∀ Fv ∈ F, 4 * sbdExprBound Fv (2 * K₀) ≤ (2 * K₀) * B := by
    intro Fv hFv
    have h1 := sbdExprBound_le_natBound Fv (2 ^ (D + 1))
    rw [h2K₀_cast] at h1
    have h2 : Fv.natBound (2 ^ (D + 1)) ≤ stepMaxPhiN (2 ^ (D + 1)) F :=
      stepMaxPhiN_mem (2 ^ (D + 1)) hFv
    have h3 : 4 * stepMaxPhiN (2 ^ (D + 1)) F ≤ M_R :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have h4 : ((4 * Fv.natBound (2 ^ (D + 1)) : Nat) : Rat) ≤ B := by
      refine le_trans ?_ hR_le
      exact_mod_cast le_trans (Nat.mul_le_mul_left 4 h2) h3
    push_cast at h4
    have h4' : 4 * sbdExprBound Fv (2 * K₀) ≤ B := by linarith
    have hB_0 : (0 : Rat) ≤ B := by positivity
    have h2K₀_ge_1 : (1 : Rat) ≤ 2 * K₀ := by linarith
    exact le_trans h4' (le_mul_of_one_le_left hB_0 h2K₀_ge_1)
  have hDiffStep : ∀ Fv ∈ F, 4 * (sptDiffBound Fv (2 * K₀) 1 + 1) ≤ B := by
    intro Fv hFv
    have h1 := sptDiffBound_le_natDiffBound Fv (2 ^ (D + 1)) 1
    rw [h2K₀_cast] at h1
    change sptDiffBound Fv (2 * K₀) 1 ≤ (Fv.natDiffBound (2 ^ (D + 1)) 1 : Rat) at h1
    have h2 : Fv.natDiffBound (2 ^ (D + 1)) 1 ≤ stepMaxPsiN (2 ^ (D + 1)) 1 F :=
      stepMaxPsiN_mem (2 ^ (D + 1)) 1 hFv
    have h3 : 4 * (stepMaxPsiN (2 ^ (D + 1)) 1 F + 1) ≤ M_R :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have h4 : ((4 * (Fv.natDiffBound (2 ^ (D + 1)) 1 + 1) : Nat) : Rat) ≤ B := by
      refine le_trans ?_ hR_le
      exact_mod_cast le_trans (Nat.mul_le_mul_left 4 (Nat.add_le_add_right h2 1)) h3
    push_cast at h4
    linarith
  have hpow_R2 : (2 : Rat) ^ (R + 2) = 4 * B := by
    change (2 : Rat) ^ (R + 2) = 4 * (2 : Rat) ^ R
    rw [pow_add]; ring
  have hx₀_4B : |x₀.val| ≤ 1 / (4 * B) := by rwa [hpow_R2] at hx₀
  have ht_4B : |t.val| ≤ 1 / (4 * B) := by rwa [hpow_R2] at ht
  let M_eps := m + D + R₀ + 4
  have h_ov := stp_overlap_of_table_bound F hF hK₀_pos hB₀_ge_4 hStep₀ hB_32 hStep hDiffStep
    (solFastD F a) (fun x₀ N ↦ solFastD F (stepData F a x₀ N))
    (fun u hu n ↦ stp_solFastD_weighted_bound F hF a ha_len hK₀_nonneg hB₀_ge_4 ha_bd hStep₀ n u hu)
    (stp_solFastD_succ_val F hF a)
    (stp_stepData_zero_val F a)
    (fun x₀ N ↦ stp_solFastD_succ_val F hF (stepData F a x₀ N))
    x₀ t hx₀_4B ht_4B (M_eps := M_eps) hN hL v hv
  have h_scale :
      12 * (K₀ * B₀ * (1 / 2 : Rat) ^ M_eps) = (3 / 4 : Rat) * (1 / (2 : Rat) ^ m) := by
    dsimp [K₀, B₀, M_eps]
    rw [one_div_pow, show m + D + R₀ + 4 = D + R₀ + m + 4 by omega,
        pow_add, pow_add, pow_add]
    have h2D : (2 : Rat) ^ D ≠ 0 := by positivity
    have h2R : (2 : Rat) ^ R₀ ≠ 0 := by positivity
    have h2m : (2 : Rat) ^ m ≠ 0 := by positivity
    field_simp
    norm_num
  have h2m_pos : (0 : Rat) < 1 / (2 : Rat) ^ m := by positivity
  linarith

/-- Computed step radius exponent `R` for `k` iterated steps from data `≤ 2^D`. -/
def stepRadius (F : List JExprN) (D k : Nat) : Nat :=
  let K_max := 2 ^ (D + k)
  (4 * max (stepMaxPhiN K_max F) (stepMaxPsiN K_max 1 F) + 4).log2 + 1

/-- Explicit linear convergence modulus `N₀(D, k, m) = m + D + 2k + 3` for `k` steps
    from data `≤ 2^D` to precision `2⁻ᵐ`. -/
def stepModulus (D k m : Nat) : Nat :=
  m + D + 2 * k + 3

/-- **Choice-free multi-step Cauchy convergence with explicit computed radius and modulus.** -/
theorem stepIter_cauchy_computed (F : List JExprN) (hF : StepEqs F) (D k : Nat)
    (a : List Q) (ha_len : a.length = F.length)
    (ha_bd : ∀ v (hv : v < a.length), |(a[v]).val| ≤ (2 : Rat) ^ D)
    (hs : List Q) (hhs_len : hs.length ≤ k)
    (hhs_bd : ∀ h ∈ hs, |h.val| ≤ 1 / (2 : Rat) ^ (stepRadius F D k + 2))
    (m N N' : Nat) (hN : stepModulus D k m ≤ N) (hN' : stepModulus D k m ≤ N')
    (v : Nat) (hv : v < F.length) :
    |((stepIter F N a hs).getD v Q.zero).val
      - ((stepIter F N' a hs).getD v Q.zero).val| < 1 / (2 : Rat) ^ m := by
  let R := stepRadius F D k
  let B : Rat := (2 : Rat) ^ R
  let K_max : Rat := (2 : Rat) ^ (D + k)
  let N₀ := stepModulus D k m
  have hKmax_cast : (((2 ^ (D + k) : Nat) : Nat) : Rat) = K_max := by push_cast; rfl
  let M_R := 4 * max (stepMaxPhiN (2 ^ (D + k)) F) (stepMaxPsiN (2 ^ (D + k)) 1 F) + 4
  have hR_le : (M_R : Rat) ≤ (2 : Rat) ^ R := by
    exact_mod_cast (Nat.lt_log2_self (n := M_R)).le
  have hB_ge_4 : (4 : Rat) ≤ B := by
    have h4_le : (4 : Rat) ≤ (M_R : Rat) := by
      exact_mod_cast (show 4 ≤ M_R by dsimp [M_R]; omega)
    exact le_trans h4_le hR_le
  have hStep_max : ∀ Fv ∈ F, 4 * sbdExprBound Fv K_max ≤ B := by
    intro Fv hFv
    have h1 := sbdExprBound_le_natBound Fv (2 ^ (D + k))
    rw [hKmax_cast] at h1
    have h2 : Fv.natBound (2 ^ (D + k)) ≤ stepMaxPhiN (2 ^ (D + k)) F :=
      stepMaxPhiN_mem (2 ^ (D + k)) hFv
    have h3 : 4 * stepMaxPhiN (2 ^ (D + k)) F ≤ M_R := by
      dsimp [M_R]
      have := le_max_left (stepMaxPhiN (2 ^ (D + k)) F) (stepMaxPsiN (2 ^ (D + k)) 1 F)
      omega
    have h4 : ((4 * Fv.natBound (2 ^ (D + k)) : Nat) : Rat) ≤ B := by
      refine le_trans ?_ hR_le
      exact_mod_cast le_trans (Nat.mul_le_mul_left 4 h2) h3
    push_cast at h4
    linarith
  have hDiffStep : ∀ Fv ∈ F, 4 * sptDiffBound Fv K_max 1 ≤ B := by
    intro Fv hFv
    have h1 := sptDiffBound_le_natDiffBound Fv (2 ^ (D + k)) 1
    rw [hKmax_cast] at h1
    change sptDiffBound Fv K_max 1 ≤ (Fv.natDiffBound (2 ^ (D + k)) 1 : Rat) at h1
    have h2 : Fv.natDiffBound (2 ^ (D + k)) 1 ≤ stepMaxPsiN (2 ^ (D + k)) 1 F :=
      stepMaxPsiN_mem (2 ^ (D + k)) 1 hFv
    have h3 : 4 * stepMaxPsiN (2 ^ (D + k)) 1 F ≤ M_R := by
      dsimp [M_R]
      have := le_max_right (stepMaxPhiN (2 ^ (D + k)) F) (stepMaxPsiN (2 ^ (D + k)) 1 F)
      omega
    have h4 : ((4 * Fv.natDiffBound (2 ^ (D + k)) 1 : Nat) : Rat) ≤ B := by
      refine le_trans ?_ hR_le
      exact_mod_cast le_trans (Nat.mul_le_mul_left 4 h2) h3
    push_cast at h4
    linarith
  have hpow_R2 : (2 : Rat) ^ (R + 2) = 4 * B := by
    change (2 : Rat) ^ (R + 2) = 4 * (2 : Rat) ^ R
    rw [pow_add]; ring
  have hh : ∀ h ∈ hs, |h.val| ≤ 1 / (4 * B) := by
    intro h hh_mem
    have := hhs_bd h hh_mem
    rwa [hpow_R2] at this
  have ha_getD : ∀ u < F.length, |(a.getD u Q.zero).val| ≤ (2 : Rat) ^ (D + 0) := by
    intro u hu
    have hua : u < a.length := ha_len ▸ hu
    rw [uDeriv_getD_eq_getElem a Q.zero u hua, Nat.add_zero]
    exact ha_bd u hua
  have hDiff0 : ∀ u < F.length, |(a.getD u Q.zero).val - (a.getD u Q.zero).val| ≤ 0 := by
    intro u _
    rw [sub_self, abs_zero]
  have h_iter := stp_stepIter_diff_bound F hF D k hB_ge_4 hStep_max hDiffStep
    hN hN' hs hh 0 (by omega) a a (le_refl 0) ha_getD ha_getD hDiff0 v hv
  have h_pow_le : (2 : Rat) ^ hs.length - 1 ≤ (2 : Rat) ^ k := by
    have : (2 : Rat) ^ hs.length ≤ (2 : Rat) ^ k :=
      pow_le_pow_right₀ (by norm_num) hhs_len
    linarith
  have h_tau_nonneg : (0 : Rat) ≤ 4 * K_max * (1 / 2 : Rat) ^ N₀ := by
    dsimp [K_max]; positivity
  have h_le :
      (2 : Rat) ^ hs.length * 0 +
        ((2 : Rat) ^ hs.length - 1) * (4 * K_max * (1 / 2 : Rat) ^ N₀) ≤
      (2 : Rat) ^ k * (4 * K_max * (1 / 2 : Rat) ^ N₀) := by
    have := mul_le_mul_of_nonneg_right h_pow_le h_tau_nonneg
    linarith
  have h_scale :
      (2 : Rat) ^ k * (4 * K_max * (1 / 2 : Rat) ^ N₀) =
        (1 / 2 : Rat) * (1 / (2 : Rat) ^ m) := by
    dsimp [K_max, N₀, stepModulus]
    rw [one_div_pow, show m + D + 2 * k + 3 = k + D + k + m + 3 by omega,
        pow_add (2 : Rat) D k, pow_add, pow_add, pow_add, pow_add]
    have h2k : (2 : Rat) ^ k ≠ 0 := by positivity
    have h2D : (2 : Rat) ^ D ≠ 0 := by positivity
    have h2m : (2 : Rat) ^ m ≠ 0 := by positivity
    field_simp
    norm_num
  have h2m_pos : (0 : Rat) < 1 / (2 : Rat) ^ m := by positivity
  linarith

/-- **Certified multi-step continuation operator**: steps `a` along `hs` at the
    computed degree `stepModulus D k m`. -/
def stepIterApprox (F : List JExprN) (D k m : Nat) (a hs : List Q) : List Q :=
  stepIter F (stepModulus D k m) a hs

/-- **Every later degree `stepModulus D k m + d` is within `2⁻ᵐ` of `stepIterApprox`.** -/
theorem stepIterApprox_spec (F : List JExprN) (hF : StepEqs F) (D k : Nat)
    (a : List Q) (ha_len : a.length = F.length)
    (ha_bd : ∀ v (hv : v < a.length), |(a[v]).val| ≤ (2 : Rat) ^ D)
    (hs : List Q) (hhs_len : hs.length ≤ k)
    (hhs_bd : ∀ h ∈ hs, |h.val| ≤ 1 / (2 : Rat) ^ (stepRadius F D k + 2))
    (m d v : Nat) (hv : v < F.length) :
    |((stepIter F (stepModulus D k m + d) a hs).getD v Q.zero).val
      - ((stepIterApprox F D k m a hs).getD v Q.zero).val| < 1 / (2 : Rat) ^ m :=
  stepIter_cauchy_computed F hF D k a ha_len ha_bd hs hhs_len hhs_bd m
    (stepModulus D k m + d) (stepModulus D k m) (Nat.le_add_right _ _) (le_refl _) v hv

/-! ## Checks

`tan` (`sysTan`) from its data `[0]`, stepped twice by `1/1024`, against one
step by `2/1024` and against the original series at `2/1024`. -/

#guard stepRadius (sysTan.map Prod.snd) 0 2 = 10
#guard stepModulus 0 2 10 = 17
#guard stepOverlapRadius (sysTan.map Prod.snd) 0 = 12
#guard stepOverlapModulus (sysTan.map Prod.snd) 0 10 = 21
#guard (let F := sysTan.map Prod.snd
        let a := stepIter F 12 [Q.zero] [⟨1, 1023⟩, ⟨1, 1023⟩]
        let b := stepData F [Q.zero] ⟨1, 511⟩ 12
        decide (|(Q.sub (a.getD 0 Q.zero) (b.getD 0 Q.zero)).val| < (1 : Rat) / 10 ^ 25))
#guard (let F := sysTan.map Prod.snd
        let a := stepIter F 12 [Q.zero] [⟨1, 1023⟩, ⟨1, 1023⟩]
        let b := Jet.evalPoly ⟨solFast sysTan 0⟩ 12 ⟨1, 511⟩
        decide (|(Q.sub (a.getD 0 Q.zero) b).val| < (1 : Rat) / 10 ^ 25))

#print axioms stepData
#print axioms stepIter
#print axioms stepModulus
#print axioms stepRadius
#print axioms stepOverlapRadius
#print axioms stepOverlapModulus
#print axioms stepIterApprox
#print axioms stepData_overlap
#print axioms stepData_overlap_computed
#print axioms stepIter_cauchy
#print axioms stepIter_cauchy_computed
#print axioms stepIterApprox_spec

end HAomega
