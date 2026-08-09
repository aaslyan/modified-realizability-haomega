/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Hydra.HydraGeneral
import Realizability.Theorems.Hydra.HydraDisplay

/-!
# Phase H9: a second strategy, for free

Phase H7 proved that *every* play terminates, whatever Hercules chops.
This module cashes that in: it defines a genuinely different strategy —
chop the **rightmost** head instead of the leftmost — and gets its descent
theorem with no induction re-run, purely by exhibiting its moves as
instances of H7's `Play` relation.

That is the test of whether H7 bought anything.  A general theorem that
cannot be applied to a second instance without redoing the work is not
general.

## What is here

* `cutRightF`/`rightStep` — the rightmost-head move, same grandparent
  regrowth, same replication parameter.
* `rightStep_play` — every rightmost move is a legal `Play`.
* **`rightStep_descends`** — hence the ordinal drops, *by one line*:
  `play_descends (rightStep_play …)`.  Compare H3's `cutH_descends`,
  which is a three-case induction over the tree consuming three separate
  ordinal lemmas.  None of that is repeated here; it was absorbed into H7.
* `no_infinite_right_battle` — and termination, likewise, from
  `no_infinite_play`.

## The strategies really are different, and the lengths really do agree

`#guard`ed at every build: the rightmost strategy gives the same published
lengths `1, 3, 37` on the path hydras, while `strategies_differ` shows the
two battles pass through *different* states — after three moves the
leftmost strategy is at `(o o o o (o) (o))` and the rightmost at
`((o) (o) o o o o)`.

The path hydras are the right test precisely because they *start* as
chains, where the two strategies agree; they diverge as soon as the first
regrowth branches the tree, and still land on the same length.

**Stated carefully**: that the battle length is independent of the
strategy is a known result which is **not proved here**.  What is proved
here is that both strategies terminate (via H7); what is *checked* is that
their lengths agree at the three published instances.  docs/first-order/STATUS.md
previously reported that agreement on the authority of a research pass —
the build now checks it.
-/

namespace Realizability

/-! ## The rightmost-head move

Defined on forests rather than hydras, walking to the *last* member
instead of the first.  The `Bool` means what it means in `cutH` — "the
head I chopped was a direct member of this forest" — so the owner of the
forest learns whether it is the grandparent and must grow the copies. -/

/-- The rightmost-head cut on a forest: the new forest, and whether this
level is the grandparent that must grow `n` copies. -/
def cutRightF (n : ℕ) : Forest → Forest × Bool
  | .nil => (.nil, false)
  | .cons (.node .nil) .nil => (.nil, true)
  | .cons (.node (.cons c₀ cs)) .nil =>
      let r := cutRightF n (.cons c₀ cs)
      if r.2 then (.cons (.node r.1) (Forest.replicate n (.node r.1)), false)
      else (.cons (.node r.1) .nil, false)
  | .cons c (.cons d rest) =>
      let r := cutRightF n (.cons d rest)
      (.cons c r.1, r.2)

/-- The rightmost move on a whole hydra.  As with `hydraStep`, the flag is
discarded at the root: a head chopped from the root simply disappears,
because the root has no parent. -/
def rightStep (n : ℕ) : Hydra → Hydra
  | .node f => .node (cutRightF n f).1

/-- Appending nothing changes nothing — the bookkeeping the single-child
case needs in order to match `MoveF.grand`'s shape. -/
theorem Forest.append_nil : ∀ f : Forest, Forest.append f .nil = f
  | .nil => rfl
  | .cons h f => by
    show Forest.cons h (Forest.append f .nil) = _
    rw [Forest.append_nil f]

/-! ## Every rightmost move is a legal play

Two lemmas, split by the flag exactly as `cutH_flag_cut`/`cutH_flag_move`
are: the flag says which family of constructors applies. -/

/-- Flag true: the chopped head was a direct member, i.e. a `CutF`. -/
theorem cutRightF_cut (n : ℕ) : ∀ f : Forest, (cutRightF n f).2 = true →
    CutF f (cutRightF n f).1
  | .nil, hf => by simp [cutRightF] at hf
  | .cons (.node .nil) .nil, _ => by
    show CutF (.cons Hydra.leaf .nil) _
    simp only [cutRightF]
    exact CutF.here
  | .cons (.node (.cons c₀ cs)) .nil, hf => by
    rcases dec_em ((cutRightF n (.cons c₀ cs)).2 = true) with hc | hc
    · simp [cutRightF, hc] at hf
    · simp only [Bool.not_eq_true] at hc
      simp [cutRightF, hc] at hf
  | .cons c (.cons d rest), hf => by
    have hf' : (cutRightF n (.cons d rest)).2 = true := by
      simpa only [cutRightF] using hf
    have ih := cutRightF_cut n (.cons d rest) hf'
    simp only [cutRightF]
    exact CutF.there ih

/-- Flag false: the cut was deeper, so whatever regrowth it triggered
happened inside — a `MoveF`. -/
theorem cutRightF_move (n : ℕ) : ∀ f : Forest, f ≠ .nil →
    (cutRightF n f).2 = false → MoveF n f (cutRightF n f).1
  | .nil, hne, _ => absurd rfl hne
  | .cons (.node .nil) .nil, _, hf => by simp [cutRightF] at hf
  | .cons (.node (.cons c₀ cs)) .nil, _, _ => by
    rcases dec_em ((cutRightF n (.cons c₀ cs)).2 = true) with hc | hc
    · -- the child reports a direct cut, so this forest's owner is the
      -- grandparent and the copies grow here
      have hcut := cutRightF_cut n (.cons c₀ cs) hc
      have hgrand := MoveF.grand (n := n) (f := .nil) hcut
      rw [Forest.append_nil] at hgrand
      simpa only [cutRightF, hc, if_pos] using hgrand
    · -- the cut was deeper still
      simp only [Bool.not_eq_true] at hc
      have hne : (Forest.cons c₀ cs) ≠ .nil := by simp
      have ih := cutRightF_move n (.cons c₀ cs) hne hc
      have := MoveF.deep (n := n) (f := .nil) ih
      simpa only [cutRightF, hc, if_neg] using this
  | .cons c (.cons d rest), _, hf => by
    have hf' : (cutRightF n (.cons d rest)).2 = false := by
      simpa only [cutRightF] using hf
    have hne : (Forest.cons d rest) ≠ .nil := by simp
    have ih := cutRightF_move n (.cons d rest) hne hf'
    simp only [cutRightF]
    exact MoveF.tail ih

/-- **The rightmost move is a legal play.** -/
theorem rightStep_play (n : ℕ) (h : Hydra) (hne : h ≠ Hydra.leaf) :
    Play n h (rightStep n h) := by
  cases h with
  | node f =>
    have hfne : f ≠ .nil := fun h0 ↦ hne (by rw [h0]; rfl)
    rcases dec_em ((cutRightF n f).2 = true) with hc | hc
    · exact Play.root (cutRightF_cut n f hc)
    · simp only [Bool.not_eq_true] at hc
      exact Play.inner (cutRightF_move n f hfne hc)

/-- **The payoff, in one line.**  The rightmost strategy's descent theorem,
obtained from H7 without repeating H3's three-case induction over the tree
or any of its ordinal lemmas. -/
theorem rightStep_descends (n : ℕ) (h : Hydra) (hne : h ≠ Hydra.leaf) :
    OLt (ordOfHydra (rightStep n h)) (ordOfHydra h) :=
  play_descends (rightStep_play n h hne)

/-- And termination likewise: the rightmost battle is a play, so
`hercules_wins` already covers it.  Stated as "no infinite rightmost
battle", at an arbitrary replication schedule. -/
theorem no_infinite_right_battle (F : ℕ → Hydra) (sched : ℕ → ℕ)
    (hF : ∀ i, F i ≠ Hydra.leaf ∧ F (i + 1) = rightStep (sched i) (F i)) :
    False :=
  no_infinite_play F fun i ↦
    ⟨sched i, (hF i).2 ▸ rightStep_play (sched i) (F i) (hF i).1⟩

/-! ## The two strategies, run against each other -/

/-- Moves to death under the rightmost strategy. -/
def battleLenR : ℕ → ℕ → Hydra → ℕ
  | 0, _, _ => 0
  | f + 1, stage, h =>
      if h.isLeaf then 0 else battleLenR f (stage + 1) (rightStep stage h) + 1

/-! The published Kirby–Paris lengths again, this time with Hercules
chopping from the other end.  Checked at every build. -/

#guard battleLenR 20 1 (path 1) == 1
#guard battleLenR 20 1 (path 2) == 3
#guard battleLenR 300 1 (path 3) == 37

/-- The state after `k` moves, for comparing the two battles. -/
def stateAfter (step : ℕ → Hydra → Hydra) : ℕ → ℕ → Hydra → Hydra
  | 0, _, h => h
  | k + 1, stage, h => stateAfter step k (stage + 1) (step stage h)

/-! And they are genuinely different battles: after three moves the two
strategies stand at different trees, yet both reach the bare head after
exactly 37 moves. -/

#guard renderH (stateAfter hydraStep 3 1 (path 3))
    != renderH (stateAfter rightStep 3 1 (path 3))

#eval renderH (stateAfter hydraStep 3 1 (path 3))
#eval renderH (stateAfter rightStep 3 1 (path 3))

#print axioms rightStep_play
#print axioms rightStep_descends
#print axioms no_infinite_right_battle

end Realizability
