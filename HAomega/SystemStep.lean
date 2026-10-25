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

/-! ## Checks

`tan` (`sysTan`) from its data `[0]`, stepped twice by `1/1024`, against one
step by `2/1024` and against the original series at `2/1024`. -/

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
#print axioms stepData_overlap

end HAomega
