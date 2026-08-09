/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Goodstein.TransfiniteInduction

/-!
# Phase D5: the Goodstein descent, derived instead of imported

Phase D2 gave the fragment its Goodstein proof but imported one composite
fact as an axiom schema: *bump the base, subtract one, and the ordinal
strictly decreases*.  That fact is the mathematical heart of Goodstein's
theorem, so importing it was the honest weak point of the D2 result — the
fragment proved the theorem *relative to* the very step that makes it
true.

This module removes that import.  The fragment now derives the descent
(`Deriv.ordDescent`, same statement and same name as the former
constructor, so `GoodsteinTheorem.lean` is unchanged) from three
*separate* properties, each of which is a property of a single symbol
rather than of a Goodstein step:

| schema | says | Phase-D1 theorem discharging it |
|---|---|---|
| `ordBump` | base change leaves the ordinal alone | `ordOf_bumpN` |
| `ordPredLt` | the assignment is strictly monotone at `pred` | `olt_ordOf_of_lt` |
| `bumpNeZero` | bumping a nonzero number gives a nonzero number | `bumpN_ne_zero` |

## What this does and does not achieve

**Does**: the composite — D1's obligation 3, `ordOf_descent` — is no
longer assumed anywhere.  The fragment reproves it syntactically, and
`ordOf_descent` is now unused by the pipeline (it survives in
`OrdinalAssignment.lean` as the semantic twin of what is derived here).
No imported schema is about the Goodstein sequence, or about a *step* of
anything; each is one property of one function symbol.

**Does not**: eliminate the fragment's dependence on metatheory.  The
three schemas are still axioms of the fragment, justified by theorems
proved in Lean rather than derivations inside the object theory.  Fully
internalizing them would require the fragment to *state and prove*
elementary number theory about the hereditary representation — it would
need `hlog`, `div` and `mod` as symbols with their recursion equations, an
order relation (the fragment has only equations), course-of-values
induction derived from `ind`, and then the whole of Phase D1 redone
syntactically.  That is a research-scale project, not a phase; docs/first-order/STATUS.md
records what it would take.

So the gap is narrowed from "the theorem's core lemma is assumed" to
"three general properties of the ordinal assignment are assumed", and the
Goodstein-specific reasoning is now entirely the fragment's own.
-/

namespace Realizability

open ContinuousFunctionals

/-- Congruence of the ordinal assignment, as a derivation-former. -/
def Deriv.congOrdE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.ord s₁ s₂) (.ord t₁ t₂)) :=
  .impE (.impE (.eqCongOrd s₁ t₁ s₂ t₂) D₁) D₂

/-- If the fragment has proved that `t` is a successor, it can prove that
`t` is nonzero. -/
def Deriv.neZeroOfEqSucc {Γ : List Formula} {t : Term} (u : Term)
    (D : Deriv Γ (.eq t (.succ u))) :
    Deriv Γ (Formula.eq t .zero).neg := by
  refine Deriv.impI ?_
  have ht0 : Deriv (Formula.eq t .zero :: Γ) (Formula.eq t .zero) := .ax
  have hts : Deriv (Formula.eq t .zero :: Γ) (Formula.eq t (.succ u)) := .wk D
  have hs0 : Deriv (Formula.eq t .zero :: Γ) (Formula.eq (.succ u) .zero) :=
    (Deriv.symmE hts).transE ht0
  exact Deriv.impE (Deriv.succNeZero u) hs0

/-- **Closed numeral instances of `bumpNeZero`, without using the
`bumpNeZero` schema.**

The open-term schema

`n ≠ 0 → bump (b + 2) n ≠ 0`

is still imported by the object theory.  But for every concrete numeral `n`,
the fragment can derive the corresponding instance from the numeral graph
`bumpNum`, equality reasoning, and `succNeZero`.  This is the first
internalization step: the remaining gap is the uniform open-term argument. -/
def Deriv.bumpNeZeroNumeral {Γ : List Formula} (b n : ℕ) :
    Deriv Γ ((Formula.eq (numeral n) .zero).neg.imp
      (Formula.eq (.bump (.succ (.succ (numeral b))) (numeral n)) .zero).neg) := by
  refine Deriv.impI ?_
  cases n with
  | zero =>
      have hne : Deriv ((Formula.eq (numeral 0) .zero).neg :: Γ)
          (Formula.eq (numeral 0) .zero).neg := .ax
      have hz : Deriv ((Formula.eq (numeral 0) .zero).neg :: Γ)
          (Formula.eq (numeral 0) .zero) := .eqRefl .zero
      exact Deriv.botE (Deriv.impE hne hz)
  | succ n =>
      have hnonzero : bumpN (b + 2) (n + 1) ≠ 0 :=
        bumpN_ne_zero (k := b + 2) (n := n + 1) (by omega) (by omega)
      cases hval : bumpN (b + 2) (n + 1) with
      | zero =>
          exact False.elim (hnonzero hval)
      | succ p =>
          have hgraph : Deriv ((Formula.eq (numeral (n + 1)) .zero).neg :: Γ)
              (Formula.eq (.bump (.succ (.succ (numeral b))) (numeral (n + 1)))
                (.succ (numeral p))) := by
            have hnum : Deriv ((Formula.eq (numeral (n + 1)) .zero).neg :: Γ)
                (Formula.eq (.bump (numeral (b + 2)) (numeral (n + 1)))
                  (numeral (p + 1))) := by
              simpa [hval] using
                (Deriv.bumpNum (Γ := (Formula.eq (numeral (n + 1)) .zero).neg :: Γ)
                  (b + 2) (n + 1))
            simpa [numeral] using hnum
          exact Deriv.neZeroOfEqSucc (numeral p) hgraph

/-- **The Goodstein descent, derived inside the fragment.**

From `n ≠ 0`: bumping gives a nonzero number (`bumpNeZero`), so taking
its predecessor strictly decreases the ordinal at the bumped base
(`ordPredLt`), and the bumped base's ordinal is the original one
(`ordBump`) — rewriting the right-hand side with that equation, by
congruence of `prec`, is what turns the two facts into the descent.

Same statement and same name as the axiom schema D2 used, so every use
site — in particular `GoodsteinTheorem.lean`'s `descentDeriv` and hence
`goodsteinTheorem` itself — is untouched by the change. -/
def Deriv.ordDescent {Γ : List Formula} (b n : Term) :
    Deriv Γ ((Formula.eq n .zero).neg.imp
      (Formula.eq
        (.prec (.ord (.succ (.succ (.succ b)))
            (.pred (.bump (.succ (.succ b)) n)))
          (.ord (.succ (.succ b)) n))
        (.succ .zero))) := by
  refine Deriv.impI ?_
  -- context: the hypothesis `n ≠ 0`
  have hne : Deriv ((Formula.eq n .zero).neg :: Γ) ((Formula.eq n .zero).neg) := .ax
  -- the bumped value is nonzero …
  have hbz : Deriv ((Formula.eq n .zero).neg :: Γ)
      ((Formula.eq (.bump (.succ (.succ b)) n) .zero).neg) :=
    .impE (.bumpNeZero b n) hne
  -- … so its predecessor has strictly smaller ordinal, at the bumped base
  have hlt : Deriv ((Formula.eq n .zero).neg :: Γ)
      (Formula.eq
        (.prec (.ord (.succ (.succ (.succ b)))
            (.pred (.bump (.succ (.succ b)) n)))
          (.ord (.succ (.succ (.succ b))) (.bump (.succ (.succ b)) n)))
        (.succ .zero)) :=
    .impE (.ordPredLt (.succ b) (.bump (.succ (.succ b)) n)) hbz
  -- … and the bumped base's ordinal is the original one
  have hbump : Deriv ((Formula.eq n .zero).neg :: Γ)
      (Formula.eq (.ord (.succ (.succ (.succ b))) (.bump (.succ (.succ b)) n))
        (.ord (.succ (.succ b)) n)) :=
    .ordBump b n
  exact (Deriv.symmE (Deriv.congPrecE (.eqRefl _) hbump)).transE hlt

/-! ## Certification

The derived descent is a closed derivation-former like any other, so
soundness and generic continuity apply to it with no new argument.  The
instance below is the one `goodsteinTheorem` actually uses (base `s`,
value `good m s`), at the empty context. -/

/-- The derived descent realizes what it says. -/
theorem ord_descent_realized (b n : Term) (ρ : ℕ → ℕ) {m : ℕ}
    (hm : derivBound (Deriv.ordDescent (Γ := []) b n) ≤ m) :
    MR ρ ((Formula.eq n .zero).neg.imp
      (Formula.eq
        (.prec (.ord (.succ (.succ (.succ b)))
            (.pred (.bump (.succ (.succ b)) n)))
          (.ord (.succ (.succ b)) n))
        (.succ .zero))) m
      (extract (Deriv.ordDescent (Γ := []) b n) ρ [] m) :=
  soundness (Deriv.ordDescent (Γ := []) b n) ρ [] trivial m hm

/-- And its type-2 extract is continuous. -/
theorem ord_descent_extract_continuous (b n : Term) (ρ : ℕ → ℕ) :
    Continuous2 (extract (Deriv.ordDescent (Γ := []) b n) ρ [] 1) :=
  extract_continuous (Deriv.ordDescent (Γ := []) b n) ρ

/-- **The round trip, and the point of the phase**: reading the fragment's
*derived* descent back through soundness recovers the semantic descent —
D1's obligation 3 — at every base `≥ 2` and every nonzero value.

This is what makes the derivation non-vacuous.  `ordOf_descent` is proved
independently in `OrdinalAssignment.lean`, but it is no longer *assumed*
by the fragment: the statement below is obtained from
`Deriv.ordDescent`'s derivation via `soundness`, using only the three
component schemas.  Fragment-side derivation and metatheoretic theorem now
agree, and neither is defined in terms of the other. -/
theorem ord_descent_via_fragment {k n : ℕ} (hk : 2 ≤ k) (hn : n ≠ 0) :
    OLt (ordOf (k + 1) (bumpN k n - 1)) (ordOf k n) := by
  obtain ⟨b, hb⟩ : ∃ b, k = b + 2 := ⟨k - 2, by omega⟩
  subst hb
  have hreal := ord_descent_realized (numeral b) (numeral n) (fun _ ↦ 0)
    (m := derivBound (Deriv.ordDescent (Γ := []) (numeral b) (numeral n)) + 2)
    (Nat.le_add_right _ _)
  -- the antecedent `n ≠ 0` is realized by anything: its own antecedent is
  -- the false equation `n̂ = 0`
  obtain ⟨p, hp⟩ : ∃ p, derivBound (Deriv.ordDescent (Γ := []) (numeral b)
      (numeral n)) + 2 = p + 1 + 1 := ⟨_, rfl⟩
  rw [hp] at hreal
  have hante : MR (fun _ ↦ 0) (Formula.eq (numeral n) .zero).neg (p + 1)
      (defaultPT (p + 2)) := by
    intro y hy
    have hy' : (numeral n).eval (fun _ ↦ 0) = (0 : ℕ) := hy
    rw [numeral_eval] at hy'
    exact absurd hy' hn
  have hconc := hreal _ hante
  have hval : Term.eval (fun _ ↦ 0)
      (.prec (.ord (.succ (.succ (.succ (numeral b))))
          (.pred (.bump (.succ (.succ (numeral b))) (numeral n))))
        (.ord (.succ (.succ (numeral b))) (numeral n)))
      = Term.eval (fun _ ↦ 0) (.succ .zero) := hconc
  simp only [Term.eval, numeral_eval] at hval
  refine oltN_eq_one_iff.mp ?_
  show oltN (ordOf (b + 1 + 1 + 1) (bumpN (b + 1 + 1) n - 1))
    (ordOf (b + 1 + 1) n) = 1
  omega

#print axioms ord_descent_realized
#print axioms ord_descent_extract_continuous
#print axioms ord_descent_via_fragment
#print axioms bumpN_ne_zero
#print axioms Deriv.neZeroOfEqSucc
#print axioms Deriv.bumpNeZeroNumeral

end Realizability
