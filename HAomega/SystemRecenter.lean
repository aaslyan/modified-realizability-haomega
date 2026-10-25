/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.RecenterKit
import HAomega.SystemFast
import HAomega.SystemPerturb
import HAomega.UniverseExpr

/-!
# Re-centering a polynomial system

To continue a solution past its certified disk, re-expand it at a point `x₀`
inside the disk: the system is autonomous, so `t ↦ Y(x₀ + t)` solves the same
equations with initial data `Y(x₀)`. `recenterData sys x₀ N` is the new data,
`S_N(Y_v)(x₀)` (the degree-`N` partial sum of each variable at `x₀`), and
`solFastD` the coefficient table of the same equations from that data.

**Scope.** Only flat systems (`NoInteg`: no `∫` inside an equation): an inner
integral `∫₀ˣ g` is not shift-invariant (`∫₀^{x₀+t} g = ∫₀^{x₀} g + ∫₀ᵗ g(x₀+s)`).
Every system can be flattened first (`flatAll`, `ux_flatAll_props`).

**The consistency theorem** (`recenter_overlap`): on the overlap of the two
disks the re-centered series agrees with the original one — for `x₀`, `t` small
enough (uniformly), the partial sums of the re-centered solution at `t` and of
the original at `x₀ + t` come within any `ε` once the data precision `N` and the
partial-sum length `L` are past some `N₀`. Past the first disk the re-centered
system *defines* the continuation; this theorem is what makes it the right one.
-/

namespace HAomega

/-- The coefficient table of the equations `F` from initial row `a` given as
rationals (`solRows` reads it off the initial jets instead). Runs without
building numeral terms for the data. -/
def solRowsD (F : List JExprN) (a : List Q) : Nat → List (List Q)
  | 0 => [a]
  | n + 1 =>
    let rows := solRowsD F a n
    rows ++ [F.map fun Fv ↦ Q.div (sbdEvalExpr Fv (tableW rows) n) (Q.ofNat (n + 1))]

/-- Coefficient `n` of variable `v` from data `a`. -/
def solFastD (F : List JExprN) (a : List Q) (v n : Nat) : Q :=
  tableW (solRowsD F a n) v n

/-- The re-centred data: `S_N(Y_v)(x₀)` for every variable `v`. -/
def recenterData (sys : List (Tm [] JetTy × JExprN)) (x₀ : Q) (N : Nat) : List Q :=
  (List.range sys.length).map fun v ↦ Jet.evalPoly ⟨solFast sys v⟩ N x₀

theorem rct_solRowsD_length (F : List JExprN) (a : List Q) :
    ∀ n : Nat, (solRowsD F a n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [solRowsD, rct_solRowsD_length F a n]

theorem rct_solRowsD_getD_eq (F : List JExprN) (a : List Q) (j : Nat) :
    ∀ n : Nat, j ≤ n → (solRowsD F a n).getD j [] = (solRowsD F a j).getD j []
  | 0, hj => by
    have hj0 : j = 0 := by omega
    subst hj0
    rfl
  | n + 1, hj => by
    rcases Nat.of_le_succ hj with hle | rfl
    · dsimp only [solRowsD]
      have hlt : j < (solRowsD F a n).length := by
        rw [rct_solRowsD_length]
        omega
      rw [sfst_getD_append_left _ _ [] j hlt]
      exact rct_solRowsD_getD_eq F a j n hle
    · rfl

theorem rct_tableW_eq_solFastD (F : List JExprN) (a : List Q) (v n j : Nat) (hj : j ≤ n) :
    tableW (solRowsD F a n) v j = solFastD F a v j := by
  unfold solFastD tableW
  rw [rct_solRowsD_getD_eq F a j n hj]

theorem rct_solFastD_zero (F : List JExprN) (a : List Q) (v : Nat) (hv : v < a.length) :
    solFastD F a v 0 = a[v] := by
  unfold solFastD tableW solRowsD
  change a.getD v Q.zero = a[v]
  exact uDeriv_getD_eq_getElem a Q.zero v hv

theorem rct_solFastD_succ (F : List JExprN) (a : List Q) (v : Nat) (hv : v < F.length) (n : Nat) :
    solFastD F a v (n + 1) =
      Q.div (sbdEvalExpr F[v] (tableW (solRowsD F a n)) n) (Q.ofNat (n + 1)) := by
  change ((solRowsD F a (n + 1)).getD (n + 1) []).getD v Q.zero = _
  have hrow := sfst_getD_append_singleton (solRowsD F a n)
    (F.map fun Fv ↦ Q.div (sbdEvalExpr Fv (tableW (solRowsD F a n)) n) (Q.ofNat (n + 1))) []
  rw [rct_solRowsD_length F a n] at hrow
  dsimp only [solRowsD]
  rw [hrow]
  have hv' : v < (F.map fun Fv ↦
      Q.div (sbdEvalExpr Fv (tableW (solRowsD F a n)) n) (Q.ofNat (n + 1))).length := by
    simp [hv]
  rw [uDeriv_getD_eq_getElem _ Q.zero v hv', List.getElem_map]

theorem rct_recenterData_zero_val (sys : List (Tm [] JetTy × JExprN)) (x₀ : Q) (N v : Nat)
    (hv : v < sys.length) :
    (solFastD (sys.map Prod.snd) (recenterData sys x₀ N) v 0).val =
      (Jet.evalPoly ⟨solFast sys v⟩ N x₀).val := by
  have hva : v < (recenterData sys x₀ N).length := by
    simp [recenterData, hv]
  rw [rct_solFastD_zero (sys.map Prod.snd) (recenterData sys x₀ N) v hva]
  simp [recenterData]

theorem rct_recenterData_succ_val (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (x₀ : Q) (N v : Nat) (hv : v < sys.length) (k : Nat) :
    (solFastD (sys.map Prod.snd) (recenterData sys x₀ N) v (k + 1)).val =
      (sbdEvalExpr sys[v].2 (solFastD (sys.map Prod.snd) (recenterData sys x₀ N)) k).val /
        ((k + 1 : Nat) : Rat) := by
  have hvF : v < (sys.map Prod.snd).length := by simp [hv]
  have hpv := h sys[v] (List.getElem_mem hv)
  have hne : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
  rw [rct_solFastD_succ (sys.map Prod.snd) (recenterData sys x₀ N) v hvF k,
      List.getElem_map, Q.val_div _ _ hne, Q.val_ofNat]
  congr 1
  exact sfst_sbdEvalExpr_congr sys[v].2 sys.length hpv.1
    (tableW (solRowsD (sys.map Prod.snd) (recenterData sys x₀ N) k))
    (solFastD (sys.map Prod.snd) (recenterData sys x₀ N)) k
    (fun u _ j hj ↦ by rw [rct_tableW_eq_solFastD _ _ u k j hj])

/-- **Consistency on the overlap.** -/
theorem recenter_overlap (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (hflat : ∀ p ∈ sys, p.2.NoInteg) :
    ∃ R : Nat, ∀ x₀ t : Q,
      |x₀.val| ≤ 1 / (2 : Rat) ^ (R + 2) → |t.val| ≤ 1 / (2 : Rat) ^ (R + 2) →
      ∀ ε : Rat, 0 < ε → ∃ N₀ : Nat, ∀ N L : Nat, N₀ ≤ N → N₀ ≤ L →
        ∀ v, v < sys.length →
          |(Jet.evalPoly ⟨solFastD (sys.map Prod.snd) (recenterData sys x₀ N) v⟩ L t).val
            - (Jet.evalPoly ⟨solFast sys v⟩ L (Q.add x₀ t)).val| < ε := by
  exact rct_overlap_of_table sys h hflat
    (fun x₀ N ↦ solFastD (sys.map Prod.snd) (recenterData sys x₀ N))
    (rct_recenterData_zero_val sys)
    (rct_recenterData_succ_val sys h)

/-! ## Checks

`solFastD` from the jets' constant terms is `solFast`; re-centring `sin`
(`memSinCosSys`) and `tan` (`sysTan`) at `x₀` and summing at `t = x₀` gives the
original series at `2x₀`. -/

#guard (List.range 8).all fun n ↦
  Q.norm (solFastD (sysTan.map Prod.snd) [Q.zero] 0 n) == Q.norm (solFast sysTan 0 n)
#guard (let a := Jet.evalPoly ⟨solFastD (memSinCosSys.map Prod.snd) (recenterData memSinCosSys ⟨1, 63⟩ 20) 0⟩ 20 ⟨1, 63⟩
        let b := Jet.evalPoly ⟨solFast memSinCosSys 0⟩ 20 (Q.add ⟨1, 63⟩ ⟨1, 63⟩)
        decide (|(Q.sub a b).val| < (1 : Rat) / 10 ^ 20))
#guard (let a := Jet.evalPoly ⟨solFastD (sysTan.map Prod.snd) (recenterData sysTan ⟨1, 1023⟩ 12) 0⟩ 12 ⟨1, 1023⟩
        let b := Jet.evalPoly ⟨solFast sysTan 0⟩ 12 (Q.add ⟨1, 1023⟩ ⟨1, 1023⟩)
        decide (|(Q.sub a b).val| < (1 : Rat) / 10 ^ 30))

#print axioms solFastD
#print axioms recenterData
#print axioms recenter_overlap

end HAomega
