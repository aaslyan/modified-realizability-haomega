/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Hydra.HydraGeneral

/-!
# The any-head move: computable tree surgery for the general Hercules theorem

The first-order H7 (`HydraGeneral.lean`) proves `hercules_wins` for the
**general** game — any head, any replication — but as metatheory: `Play` is a
relation, not a function, so no object-language symbol can evaluate by it.
This file closes that gap with a *computable* move:

    moveF p n f   -- cut head #p (DFS order) of forest f, replication n
    playAt p n h  -- the move on a hydra, p taken mod the head count
    playAtN       -- the same on codes: the value `hcutAt` evaluates by

`moveF` is `cutH` with the hardwired "leftmost" replaced by a position
argument: the same nested-pattern recursion, the same `Bool` flag reporting
"the head I cut was a direct member of this forest" so the caller can decide
whether it is the grandparent that must grow the copies.  At `p = 0` it *is*
the leftmost move (`#guard`s below).

The two flag lemmas mirror `cutH_flag_cut`/`cutH_flag_move` line for line:
every in-range move is a legal `Play`.  The descent `olt_ordOfHydraN_playAt`
is then `play_descends` pulled back along the coding — the analogue of
`olt_ordOfHydraN_step`, and the single fact the `hordCutAtLt` rule imports.

**Definitions here are inside `Tm.eval`'s dependency graph** (the `hcutAt`
symbol evaluates by `playAtN`), so they must stay choice-free and
kernel-computable; the proofs need not.
-/

namespace HAomega

open Realizability

/-- The number of heads (cuttable leaves) in a forest.  A leaf member is one
head; an internal member contributes the heads inside it. -/
def headCountF : Forest → ℕ
  | .nil => 0
  | .cons (.node .nil) rest => 1 + headCountF rest
  | .cons (.node (.cons c cs)) rest =>
      headCountF (.cons c cs) + headCountF rest

/-- Every nonempty forest has a head. -/
theorem headCountF_pos : ∀ (c : Hydra) (rest : Forest),
    0 < headCountF (.cons c rest)
  | .node .nil, _ => by simp only [headCountF]; omega
  | .node (.cons c cs), rest => by
      have h := headCountF_pos c cs
      simp only [headCountF]; omega

/-- **The any-head move on a forest.**  Cut head `#p` (DFS order, direct leaf
members counting where they stand) with replication `n`.  The `Bool` reports
whether the cut head was a direct member of *this* forest — exactly `cutH`'s
flag, so the caller one level up performs the Kirby–Paris regrowth. -/
def moveF (p n : ℕ) : Forest → Forest × Bool
  | .nil => (.nil, false)
  | .cons (.node .nil) rest =>
      if p = 0 then (rest, true)
      else
        let r := moveF (p - 1) n rest
        (.cons (.node .nil) r.1, r.2)
  | .cons (.node (.cons c cs)) rest =>
      if p < headCountF (.cons c cs) then
        let r := moveF p n (.cons c cs)
        (if r.2 then
            .cons (.node r.1)
              (Forest.append (Forest.replicate n (.node r.1)) rest)
          else .cons (.node r.1) rest, false)
      else
        let r := moveF (p - headCountF (.cons c cs)) n rest
        (.cons (.node (.cons c cs)) r.1, r.2)

/-- The move on a hydra: the position is taken mod the head count, so *every*
`p` names a legal head as long as the hydra is alive; the flag is discarded at
the root, where a cut head simply disappears (no grandparent). -/
def playAt (p n : ℕ) : Hydra → Hydra
  | .node f => .node (moveF (p % headCountF f) n f).1

/-- The move on **codes** — the value `hcutAt` evaluates by. -/
def playAtN (p n code : ℕ) : ℕ := encodeH (playAt p n (hydraOf code))

/-- In-range moves that report `true` are `CutF`s — mirror of `cutH_flag_cut`. -/
theorem moveF_flag_cut (n : ℕ) : ∀ (p : ℕ) (f : Forest),
    p < headCountF f → (moveF p n f).2 = true → CutF f (moveF p n f).1
  | _, .nil, hb, _ => absurd hb (by simp [headCountF])
  | p, .cons (.node .nil) rest, hb, hf => by
      by_cases h0 : p = 0
      · subst h0
        simp only [moveF]
        exact CutF.here
      · have hb' : p - 1 < headCountF rest := by
          simp only [headCountF] at hb; omega
        have hf' : (moveF (p - 1) n rest).2 = true := by
          simpa only [moveF, if_neg h0] using hf
        have ih := moveF_flag_cut n (p - 1) rest hb' hf'
        simp only [moveF, if_neg h0]
        exact CutF.there ih
  | p, .cons (.node (.cons c cs)) rest, hb, hf => by
      by_cases hk : p < headCountF (.cons c cs)
      · -- the flag is literally `false` in this branch
        simp [moveF, hk] at hf
      · have hb' : p - headCountF (.cons c cs) < headCountF rest := by
          simp only [headCountF] at hb; omega
        have hf' : (moveF (p - headCountF (.cons c cs)) n rest).2 = true := by
          simpa only [moveF, if_neg hk] using hf
        have ih := moveF_flag_cut n _ rest hb' hf'
        simp only [moveF, if_neg hk]
        exact CutF.there ih

/-- In-range moves that report `false` are `MoveF`s — mirror of
`cutH_flag_move`.  The `grand` case is where the regrowth happens: the inner
cut was a direct member of the child's forest, so this level appends the
copies. -/
theorem moveF_flag_move (n : ℕ) : ∀ (p : ℕ) (f : Forest),
    p < headCountF f → (moveF p n f).2 = false → MoveF n f (moveF p n f).1
  | _, .nil, hb, _ => absurd hb (by simp [headCountF])
  | p, .cons (.node .nil) rest, hb, hf => by
      by_cases h0 : p = 0
      · simp [moveF, h0] at hf
      · have hb' : p - 1 < headCountF rest := by
          simp only [headCountF] at hb; omega
        have hf' : (moveF (p - 1) n rest).2 = false := by
          simpa only [moveF, if_neg h0] using hf
        have ih := moveF_flag_move n (p - 1) rest hb' hf'
        simp only [moveF, if_neg h0]
        exact MoveF.tail ih
  | p, .cons (.node (.cons c cs)) rest, hb, hf => by
      by_cases hk : p < headCountF (.cons c cs)
      · by_cases hg : (moveF p n (.cons c cs)).2 = true
        · have hcut := moveF_flag_cut n p (.cons c cs) hk hg
          simp only [moveF, if_pos hk, hg]
          exact MoveF.grand hcut
        · simp only [Bool.not_eq_true] at hg
          have ih := moveF_flag_move n p (.cons c cs) hk hg
          simp only [moveF, if_pos hk, hg, Bool.false_eq_true, if_neg,
            not_false_eq_true]
          exact MoveF.deep ih
      · have hb' : p - headCountF (.cons c cs) < headCountF rest := by
          simp only [headCountF] at hb; omega
        have hf' : (moveF (p - headCountF (.cons c cs)) n rest).2 = false := by
          simpa only [moveF, if_neg hk] using hf
        have ih := moveF_flag_move n _ rest hb' hf'
        simp only [moveF, if_neg hk]
        exact MoveF.tail ih

/-- **Every `playAt` move on a live hydra is a legal play** — any position,
any replication.  The analogue of `hydraStep_play`, quantified over the head. -/
theorem playAt_play (p n : ℕ) (h : Hydra) (hne : h ≠ Hydra.leaf) :
    Play n h (playAt p n h) := by
  cases h with
  | node f =>
    have hfne : f ≠ .nil := by
      rintro rfl; exact hne rfl
    have hpos : 0 < headCountF f := by
      cases f with
      | nil => exact absurd rfl hfne
      | cons c rest => exact headCountF_pos c rest
    have hb : p % headCountF f < headCountF f := Nat.mod_lt _ hpos
    by_cases hf : (moveF (p % headCountF f) n f).2 = true
    · exact Play.root (moveF_flag_cut n _ f hb hf)
    · simp only [Bool.not_eq_true] at hf
      exact Play.inner (moveF_flag_move n _ f hb hf)

/-- **The descent, on codes**: any move on a live hydra strictly lowers the
ordinal — whichever head, however many copies.  This is `play_descends`
pulled back along the coding; the single fact `Deriv.hordCutAtLt` imports,
the analogue of `olt_ordOfHydraN_step`. -/
theorem olt_ordOfHydraN_playAt (p n code : ℕ) (h : code ≠ 0) :
    OLt (ordOfHydraN (playAtN p n code)) (ordOfHydraN code) := by
  have hne : hydraOf code ≠ Hydra.leaf :=
    fun hl ↦ h (hydraOf_eq_leaf_iff.mp hl)
  have hd := play_descends (playAt_play p n (hydraOf code) hne)
  unfold ordOfHydraN playAtN
  rw [hydraOf_encodeH]
  exact hd

-- At `p = 0` the move is the leftmost cut — the fragment's own `hydraStepN`
-- (evidence at instances, not a theorem; nothing downstream depends on it).
#guard [playAtN 0 1 1, playAtN 0 2 2, playAtN 0 3 3, playAtN 0 5 2]
  == [Realizability.hydraStepN 1 1, Realizability.hydraStepN 2 2,
      Realizability.hydraStepN 3 3, Realizability.hydraStepN 5 2]
-- Distinct positions are genuinely distinct moves: at code 5 (a deep head
-- and a shallow one), cutting head 0 grows copies (code 66), cutting head 1
-- does not (code 2).
#guard (playAtN 0 2 5, playAtN 1 2 5) == (66, 2)
#guard playAtN 1 0 1 == 0     -- position mod head count: 1 % 1 = 0, kill the head
#guard playAtN 7 0 0 == 0     -- the dead hydra stays dead

-- The definitions `Tm.eval` will depend on must be axiom-free.
#print axioms playAtN
#print axioms headCountF

end HAomega
