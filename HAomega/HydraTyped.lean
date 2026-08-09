/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.HydraSurgery
import HAomega.OrdCnf

/-!
# The typed hydra layer: trees as a base type, ordinals as notations

The last coded object in the development.  `Realizability.Signature.Hydra`
already has hydras as an inductive `Hydra`/`Forest` pair and H7 already proves
the descent *about trees* — what is coded is only the interface to `Tm.eval`,
where `hcut`/`hydra`/`hord` take and return the ℕ codes `encodeH` produces.
Those codes grow doubly exponentially, which is what overflows the interpreter
on the coded battle extract at hydra codes 4 and 7.

This file supplies the value layer for a base type `.hyd` whose values *are*
trees, with the ordinal assignment landing in `OrdCnf.lean`'s `Eps0` rather
than in a code:

    ordEOfHydra : Hydra → Eps0        (not  ordOfHydra : Hydra → ℕ)

so a battle state and its ordinal are both structural, and no encoding is
evaluated anywhere in the extracted program.

## Two things the structural version gets for free

* **`Eps0.insert` needs no fuel.**  `insertExp` on codes is fueled, because
  its recursion is on `oR c < c` — an arithmetic fact about the decoding.
  Structurally it is plain recursion on the third component.
* **The descent is H7's theorem, unchanged.**  `oltE_ordEOfHydra_step` below
  is `play_descends ∘ hydraStep_play` composed with the alignment, with no
  `encodeH`/`hydraOf` round trip in between — where the coded
  `olt_ordOfHydraN_step` has to go through `hydraOf_encodeH`.

As in `OrdCnf.lean`, the coding survives only in *proofs*: `toCode_insert`
and `toCode_ordEOfHydra` align the structural assignment with the certified
coded one, and every fact transfers along them.  No new mathematics is
imported.
-/

namespace HAomega

open Realizability

/-! ## The CNF sum, structurally -/

/-- `ω^e ⊕ c` on notations — `insertExp`'s clauses, with the fuel gone:
the recursion is structural on `c`'s remainder. -/
def Eps0.insert (e : Eps0) : Eps0 → Eps0
  | .zero => .node e 0 .zero
  | .node e' c' r' =>
      if e = e' then .node e' (c' + 1) r'
      else if Eps0.olt e' e then .node e 0 (.node e' c' r')
      else .node e' c' (Eps0.insert e r')

/-- The structural sum computes the coded one. -/
theorem toCode_insert (e : Eps0) : ∀ c : Eps0,
    (Eps0.insert e c).toCode = insertExp e.toCode c.toCode
  | .zero => by
      simp only [Eps0.insert, Eps0.toCode, insertExp_zero]
  | .node e' c' r' => by
      have hne : (Eps0.node e' c' r').toCode ≠ 0 := by
        simp only [Eps0.toCode]; exact mkO_ne_zero _ _ _
      rw [insertExp_pos hne]
      -- align the two branch conditions: `precB` on codes *is* `olt` on trees
      simp only [Eps0.toCode, oE_mkO, oC_mkO, oR_mkO, Eps0.toCode_olt]
      by_cases hE : e = e'
      · subst hE; simp [Eps0.insert, Eps0.toCode]
      · have hE' : ¬ (e.toCode = e'.toCode) := fun h ↦ hE (Eps0.toCode_inj h)
        by_cases hlt : Eps0.olt e' e = true
        · simp [Eps0.insert, hE, hE', hlt, Eps0.toCode]
        · simp [Eps0.insert, hE, hE', hlt, Eps0.toCode, toCode_insert e r']

/-! ## The ordinal of a tree, as a notation -/

mutual

/-- The Kirby–Paris ordinal of a hydra, **structurally** — `ordOfHydra`'s
recursion with `Eps0` nodes in place of codes. -/
def ordEOfHydra : Hydra → Eps0
  | .node f => ordEOfForest f

/-- The natural sum of `ω^(ord ·)` over a forest. -/
def ordEOfForest : Forest → Eps0
  | .nil => .zero
  | .cons h f => Eps0.insert (ordEOfHydra h) (ordEOfForest f)

end

@[simp] theorem ordEOfHydra_node (f : Forest) :
    ordEOfHydra (.node f) = ordEOfForest f := rfl

@[simp] theorem ordEOfForest_nil : ordEOfForest .nil = .zero := rfl

@[simp] theorem ordEOfForest_cons (h : Hydra) (f : Forest) :
    ordEOfForest (.cons h f) = Eps0.insert (ordEOfHydra h) (ordEOfForest f) :=
  rfl

mutual

/-- **The mirror is exact**: the structural assignment encodes to the coded
one, so every certified fact about `ordOfHydra` transfers. -/
theorem toCode_ordEOfHydra : ∀ h : Hydra,
    (ordEOfHydra h).toCode = ordOfHydra h
  | .node f => toCode_ordEOfForest f

theorem toCode_ordEOfForest : ∀ f : Forest,
    (ordEOfForest f).toCode = ordOfForest f
  | .nil => rfl
  | .cons h f => by
      simp only [ordEOfForest_cons, ordOfForest_cons, toCode_insert,
        toCode_ordEOfHydra h, toCode_ordEOfForest f]

end

/-! ## The battle, on trees -/

/-- Is this hydra dead?  `0` for the bare head, `1` otherwise — a `ℕ`-valued
test, so the derivation's case split can use the existing numeric `eqDec`
rather than an equality test at type `.hyd`. -/
def isLeafN (h : Hydra) : ℕ := if h.isLeaf then 0 else 1

@[simp] theorem isLeafN_eq_zero_iff {h : Hydra} : isLeafN h = 0 ↔ h = Hydra.leaf := by
  cases h with
  | node f =>
      cases f with
      | nil => simp [isLeafN, Hydra.isLeaf, Hydra.leaf]
      | cons c cs => simp [isLeafN, Hydra.isLeaf, Hydra.leaf]

/-- **The descent, on trees.**  H7's `play_descends` applied to the fragment's
own move, transported along the assignment mirror — no coding round trip.
This is the single fact the `hordCutLtH` schema imports. -/
theorem oltE_ordEOfHydra_step (n : ℕ) (h : Hydra) (hne : h ≠ Hydra.leaf) :
    Eps0.OLtE (ordEOfHydra (hydraStep n h)) (ordEOfHydra h) := by
  refine Eps0.OLtE_iff_OLt.mpr ?_
  rw [toCode_ordEOfHydra, toCode_ordEOfHydra]
  exact play_descends (hydraStep_play n h hne)

/-- The same for the **any-head** surgery move, so the typed layer supports
the general game too. -/
theorem oltE_ordEOfHydra_playAt (p n : ℕ) (h : Hydra) (hne : h ≠ Hydra.leaf) :
    Eps0.OLtE (ordEOfHydra (playAt p n h)) (ordEOfHydra h) := by
  refine Eps0.OLtE_iff_OLt.mpr ?_
  rw [toCode_ordEOfHydra, toCode_ordEOfHydra]
  exact play_descends (playAt_play p n h hne)

-- The structural assignment agrees with the coded one at instances, and the
-- structural notation stays small where the code does not.
#guard (ordEOfHydra (hydraOf 3)).toCode == Realizability.ordOfHydraN 3
#guard (ordEOfHydra (hydraOf 7)).toCode == Realizability.ordOfHydraN 7
#guard Eps0.nf (ordEOfHydra (hydraOf 7)) == true
#guard isLeafN (hydraOf 0) == 0
#guard isLeafN (hydraOf 1) == 1

-- Everything `Tm.eval` will depend on must be axiom-free.
#print axioms ordEOfHydra
#print axioms Eps0.insert
#print axioms isLeafN

end HAomega
