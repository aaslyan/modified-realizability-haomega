/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Goodstein.OrdinalDescent

/-!
# Phase H4: the Hydra game inside the fragment

`Hydra.lean` (Phases H1–H3) is pure metatheory: trees coded as naturals,
the Kirby–Paris move, an ordinal assignment, and the theorem that every
move strictly decreases it.  This module makes the fragment *speak* about
all of that — three new function symbols and four new axiom schemas — so
that Phase H5 can prove termination as a closed derivation, exactly the
way Phase D2 proved Goodstein's theorem.

## The symbols

| symbol | arity | evaluated by | reading |
|---|---|---|---|
| `hcut n c` | 2 | `hydraStepN` | one move on hydra `c`, growing `n` copies at the grandparent |
| `hydra s t` | 2 | `hydraSeqN` | the state after `t` moves from the hydra coded `s` |
| `hord c` | 1 | `ordOfHydraN` | the ordinal notation assigned to the hydra coded `c` |

The fragment has one sort, `ℕ`, and the coding of H1 is a *bijection*
between `ℕ` and finite rooted trees — both round trips proved — so `∀h`
ranges over exactly the hydras, and no coding side condition is needed
anywhere.  The dead hydra is the bare head, whose code is `0`
(`hydraOf_eq_leaf_iff`), so `hydra(h, t) = 0` is literally "the battle
from `h` is over after `t` moves".  No new predicate, and no new
equality: termination is an equation of the fragment's own atomic
language.

## The schemas, and what is imported

* `hydraZero`, `hydraSucc` — the battle's recursion equations, in the
  style of `goodZero`/`goodSucc`.  Honest first-order schemas.
* `hcutNum` — the move's numeral graph, for the same reason `bump` and
  `prec` have one (a move is tree surgery through the decoding, which is
  course-of-values recursion, not a first-order equation schema).  It is
  what lets the fragment compute a concrete battle, below.
* `hordCutLt` — **the one imported mathematical fact of the phase**: a
  move on a live hydra strictly decreases its ordinal.  Its Lean twin is
  `olt_ordOfHydraN_step`, which is Phase H3's `cutH_descends` read on
  codes.

`hordCutLt` follows the `ordPredLt` pattern that Phase D5 established: it
is a property of *one* function symbol (`hcut`) relative to *one* ordinal
symbol (`hord`), and it says nothing whatever about the battle — no
sequence, no step counter, no stage-indexed replication.  It quantifies
over the number of regrown copies, so H5's derivation never inspects the
replication factor.  Everything Hydra-specific about the *battle* —
gluing the descent to the recursion equation, the case split on death,
the induction — is the fragment's own work in H5.

Read that carefully, though: it says the *derivation* is uniform in the
factor, not that the *theorem* quantifies over schedules.  `hydra` names
one battle — leftmost head, `s + 1` copies at step `s`, the standard
Kirby–Paris one — because a schedule is a function and the fragment has
no function variables.  The fully general statement ("every play
terminates, whatever Hercules chops and however many heads grow") is
proved in the metatheory instead, in `HydraGeneral.lean` (Phase H7).

What is *not* claimed: that the fragment proves `hordCutLt` itself.  Like
Goodstein's three schemas it is an axiom of the object theory justified
by a Lean theorem, and internalizing it would mean formalizing tree
surgery and Cantor normal forms inside the fragment's equational
language.  The round trip `hydra_descent_via_fragment` below checks the
import is faithful — reading the schema back through `soundness` returns
exactly the H3 theorem — and docs/first-order/STATUS.md records the gap.
-/

namespace Realizability

open ContinuousFunctionals

/-! ## Congruence for the new symbols, as derivation-formers -/

/-- Congruence of the move. -/
def Deriv.congHcutE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.hcut s₁ s₂) (.hcut t₁ t₂)) :=
  .impE (.impE (.eqCongHcut s₁ t₁ s₂ t₂) D₁) D₂

/-- Congruence of the battle. -/
def Deriv.congHydraE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.hydra s₁ s₂) (.hydra t₁ t₂)) :=
  .impE (.impE (.eqCongHydra s₁ t₁ s₂ t₂) D₁) D₂

/-- Congruence of the Hydra ordinal assignment. -/
def Deriv.congHordE {Γ : List Formula} {s t : Term}
    (D : Deriv Γ (.eq s t)) : Deriv Γ (.eq (.hord s) (.hord t)) :=
  .impE (.eqCongHord s t) D

/-! ## The battle, computed inside the fragment

The fragment does not merely *talk* about the battle: with the two
recursion equations and the move's numeral graph it derives the value of
every state of every concrete battle, by a derivation whose length is the
number of moves.  This is the Hydra analogue of `good_compute` in
`Goodstein.lean`. -/

/-- **The fragment computes the battle.**  For every start code and every
number of moves, the fragment derives the state's numeral — the same
number `hydraSeqN` computes. -/
def hydraComputeDeriv (start : ℕ) : (t : ℕ) →
    Deriv [] (Formula.eq (.hydra (numeral start) (numeral t))
      (numeral (hydraSeqN start t)))
  | 0 => .hydraZero _
  | t + 1 =>
      ((Deriv.hydraSucc (numeral start) (numeral t)).transE
        (Deriv.congHcutE (.eqRefl _) (hydraComputeDeriv start t))).transE
        (Deriv.hcutNum (t + 1) (hydraSeqN start t))

/-- The worked battle of Phase H2, derived rather than computed: starting
from the two-deep chain (code `2`), the fragment proves the hydra is dead
after three moves.  The middle state is code `3` — two heads — so this
derivation passes through the step where the tree *grows*. -/
def hydra_chain_derivable :
    Deriv [] (Formula.eq (.hydra (numeral 2) (numeral 3)) .zero) :=
  hydraComputeDeriv 2 3

/-- And the three intermediate states, as the fragment sees them:
`2 → 3 → 1 → 0`. -/
def hydra_chain_states :
    Deriv [] (Formula.eq (.hydra (numeral 2) (numeral 1)) (numeral 3)) ×
    Deriv [] (Formula.eq (.hydra (numeral 2) (numeral 2)) (numeral 1)) ×
    Deriv [] (Formula.eq (.hydra (numeral 2) (numeral 3)) (numeral 0)) :=
  (hydraComputeDeriv 2 1, hydraComputeDeriv 2 2, hydraComputeDeriv 2 3)

/-! ## The formula Phase H5 proves

Variable convention, kept identical to `GoodsteinTheorem.lean`: `1` is the
ordinal, `2` the start hydra, `3` the move counter, `4` the existential
witness, `5` the transfinite-induction binder. -/

/-- `∃t. hydra(h, t) = 0` — the battle from `h` ends. -/
abbrev hydraTerminates : Formula :=
  .ex 4 (Formula.eq (.hydra (.var 2) (.var 4)) .zero)

/-- `∀h. ∃t. hydra(h, t) = 0` — **Hercules wins**, the statement Phase H5
derives. -/
abbrev hydraGoal : Formula := .all 2 hydraTerminates

/-! ## Certification

The schemas are ordinary rules of the fragment, so soundness and generic
continuity apply to them with no new argument — that is the point of the
per-rule discipline.  The instances below are the ones H5 uses. -/

/-- The imported descent schema realizes what it says. -/
theorem hord_cut_lt_realized (n c : Term) (ρ : ℕ → ℕ) {m : ℕ}
    (hm : derivBound (Deriv.hordCutLt (Γ := []) n c) ≤ m) :
    MR ρ ((Formula.eq c .zero).neg.imp
      (Formula.eq (.prec (.hord (.hcut n c)) (.hord c)) (.succ .zero))) m
      (extract (Deriv.hordCutLt (Γ := []) n c) ρ [] m) :=
  soundness (Deriv.hordCutLt (Γ := []) n c) ρ [] trivial m hm

/-- And its type-2 extract is continuous. -/
theorem hord_cut_lt_extract_continuous (n c : Term) (ρ : ℕ → ℕ) :
    Continuous2 (extract (Deriv.hordCutLt (Γ := []) n c) ρ [] 1) :=
  extract_continuous (Deriv.hordCutLt (Γ := []) n c) ρ

/-- The computed battle realizes what it says. -/
theorem hydra_chain_realized (ρ : ℕ → ℕ) {m : ℕ}
    (hm : derivBound hydra_chain_derivable ≤ m) :
    MR ρ (Formula.eq (.hydra (numeral 2) (numeral 3)) .zero) m
      (extract hydra_chain_derivable ρ [] m) :=
  soundness hydra_chain_derivable ρ [] trivial m hm

/-- And is continuous. -/
theorem hydra_chain_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract hydra_chain_derivable ρ [] 1) :=
  extract_continuous hydra_chain_derivable ρ

/-- **The round trip**: reading the imported schema back through
`soundness` recovers exactly Phase H3's descent theorem, at every
replication factor and every live hydra.

This is what makes the import faithful rather than merely consistent: the
fragment's `hordCutLt`, passed through the realizability interpretation,
*is* `cutH_descends` on codes — not a weaker or differently-quantified
statement. -/
theorem hydra_descent_via_fragment {n code : ℕ} (hc : code ≠ 0) :
    OLt (ordOfHydraN (hydraStepN n code)) (ordOfHydraN code) := by
  have hreal := hord_cut_lt_realized (numeral n) (numeral code) (fun _ ↦ 0)
    (m := derivBound (Deriv.hordCutLt (Γ := []) (numeral n) (numeral code)) + 2)
    (Nat.le_add_right _ _)
  obtain ⟨p, hp⟩ : ∃ p, derivBound (Deriv.hordCutLt (Γ := []) (numeral n)
      (numeral code)) + 2 = p + 1 + 1 := ⟨_, rfl⟩
  rw [hp] at hreal
  -- the antecedent `code ≠ 0` is realized by anything: its own antecedent
  -- is the false equation `code = 0`
  have hante : MR (fun _ ↦ 0) (Formula.eq (numeral code) .zero).neg (p + 1)
      (defaultPT (p + 2)) := by
    intro y hy
    have hy' : (numeral code).eval (fun _ ↦ 0) = (0 : ℕ) := hy
    rw [numeral_eval] at hy'
    exact absurd hy' hc
  have hconc := hreal _ hante
  have hval : Term.eval (fun _ ↦ 0)
      (.prec (.hord (.hcut (numeral n) (numeral code))) (.hord (numeral code)))
      = Term.eval (fun _ ↦ 0) (.succ .zero) := hconc
  simp only [Term.eval, numeral_eval] at hval
  refine oltN_eq_one_iff.mp ?_
  show oltN (ordOfHydraN (hydraStepN n code)) (ordOfHydraN code) = 1
  omega

#print axioms hord_cut_lt_realized
#print axioms hord_cut_lt_extract_continuous
#print axioms hydra_chain_realized
#print axioms hydra_chain_extract_continuous
#print axioms hydra_descent_via_fragment

end Realizability
