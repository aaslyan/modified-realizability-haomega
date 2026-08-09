/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Goodstein.Goodstein

/-!
# Phase C: transfinite induction up to `ε₀` (`tiEps0`)

The rule

    ∀x. (∀y. y ≺ x → φ(y)) → φ(x)
    ─────────────────────────────
             ∀x. φ(x)

added to the fragment, with its realizer extracted, certified, and
proved continuous.  The value-level notation system and the order `≺`
live in `Epsilon0.lean`; the combinator `tiRecC` in `Extraction.lean`;
the correctness theorem `MR_tiRecC` in `Soundness.lean`; the tracking
lemma `tiC_tracked` in `GenericContinuity.lean`.  This module is the
headline: the bridge to Phase B's notation grammar, the ordinal
assignment Phase D will descend along, the rule exercised end to end,
and the `#print axioms` checks.

## Why this is a new *rule* and not a theorem

It is not hard for *Lean* to justify the recursion — see below.  The
reason `tiEps0` is nevertheless *added* rather than derived is the
standard metatheory: by Gentzen's theorem PA does not prove `TI(ε₀)`
(only `TI(α)` for each fixed `α < ε₀`), and by Kirby–Paris the same gap
is what makes Goodstein's theorem unprovable there.  **This development
neither proves nor claims non-derivability for its own fragment** — that
would need an interpretation of the fragment in PA, which is not part of
this project.  What is recorded here is only that the rule is added with
its own realizer, and why such a rule is worth adding.

## What Lean needed, and what it did not

The brief predicted the recursor could be built by structural recursion
on the notation's subterms, with no well-foundedness theorem needed, and
asked that the finding be recorded either way.  **It could not**, and the
reason is worth stating precisely: `≺`-descent is not structural
descent.  From `ω^ω` one descends to `ω^2·2 + ω·2 + 2`, a *larger* tree;
Phase B's own numbers show it (`hrep 2 4` is `ω^ω`, and one Goodstein
step lands on the three-summand notation for 26).  Structural recursion
on the notation therefore cannot reach the predecessors the rule
quantifies over.

So `Epsilon0.lean` proves `oLt_wf` — well-foundedness of `≺` on normal
forms — and `tiRecC` is defined by `WellFounded.fix` on it.  What
survives of the brief's framing, and is the real payoff, is this: that
proof is **elementary and choice-free** — three nested inductions
(accessibility of the head exponent, the coefficient, accessibility of
the remainder), no ordinals, no `Classical`, nothing outside what Lean's
own inductive types give.  Gentzen's answer to Hilbert was that direct
inspection of a concretely presented notation system convinces us it is
well-ordered, and that this conviction is not reducible to the arithmetic
it justifies.  Here that inspection is an 85-line induction the kernel
checks, and its axiom footprint (`[propext, Quot.sound]`) is *visibly
weaker* than the `Classical.choice` the realization theorems use.

## Canonicity: load-bearing here, and answered

Phase B deferred canonicity of hereditary representations, flagging that
it would become load-bearing exactly when something quantified over
*arbitrary* representations.  This rule does.  The finding
(`Epsilon0.lean`, with machine-checked witnesses):

* on arbitrary notations the Cantor comparison is **not well-founded** —
  `ω ≻ 1 + ω ≻ 1 + (1 + ω) ≻ …`, an infinite descent through terms all
  denoting the same ordinal `ω` (`precB_onePlus_omega`,
  `precB_onePlus_onePlus_omega`);
* so `≺` (`oltB`) is the comparison **conjoined with normal form**
  (`nfB`), the `NFBelow`/`NF` layer Phase B deferred, now built;
* the rule's conclusion is nevertheless unrestricted: a non-normal code
  has no `≺`-predecessors, so progressiveness proves `φ` of it outright.
  No side condition on `tiEps0` mentions normality.

## Out of scope, per the brief

Goodstein's theorem itself (Phase D: this rule plus Phase B's sequence
machinery, and the missing `∃` — see docs/internal/QUESTIONS.md); any conservativity,
consistency, or other metatheoretic claim about the extended fragment;
ordinals beyond `ε₀`.
-/

namespace Realizability

open ContinuousFunctionals

/-! ## The notations are Phase B's grammar, read at base `ω`

Phase B's hereditary representations are *terms of the fragment* in one
distinguished base variable (`hrep`), and its grammar of such terms is
`HTerm`.  Decoding a Phase-C notation code yields exactly such a term:
same signature, same shape `x^e·c + r`, with the base variable now read
as `ω` rather than as a numeral.  That is the sense in which this phase
reuses Phase B's notation system instead of introducing a second one —
`ordTerm` is the identification, and `ordTerm_hterm` certifies it. -/

/-- Decode a notation code into a term of Phase B's grammar (fueled, like
`hrepAux`; `oE`/`oR` strictly decrease the code). -/
def ordTermAux : ℕ → ℕ → Term
  | 0, _ => .zero
  | _ + 1, 0 => .zero
  | f + 1, n + 1 =>
      .plus
        (.times (.exp (.var 0) (ordTermAux f (oE (n + 1))))
          (numeral (oC (n + 1) + 1)))
        (ordTermAux f (oR (n + 1)))

/-- The term of Phase B's grammar denoted by a notation code, with the
base variable standing for `ω`. -/
def ordTerm (c : ℕ) : Term := ordTermAux c c

theorem ordTermAux_hterm : ∀ (f n : ℕ), HTerm (ordTermAux f n)
  | 0, _ => .zero
  | _ + 1, 0 => .zero
  | f + 1, _ + 1 =>
      .plus (.times (.exp .var0 (ordTermAux_hterm f _)) (numeral_hterm _))
        (ordTermAux_hterm f _)

/-- **Every notation is a Phase-B representation term**: the ordinal
notations of this phase are the `HTerm`s of Phase B, no second
encoding. -/
theorem ordTerm_hterm (c : ℕ) : HTerm (ordTerm c) :=
  ordTermAux_hterm c c

/-! ## The ordinal assignment for the Goodstein sequence

`ordOf k n` (`OrdinalAssignment.lean`) is the code of the ordinal
obtained from `n`'s hereditary base-`k` representation by reading the
base as `ω` — clause for clause the mirror of Phase B's `hrepAux`, with
`mkO` in place of the term constructors.  Phase C verified concrete
instances here; Phase D proved the general theorems (`nfB_ordOf`,
`ordOf_bumpN`, `ordOf_descent`), and moved the definition next to
them. -/

/-! ### Kernel-verified instances of the Phase-D descent

The Goodstein sequence from `3` (Phase B: `3, 3, 3, 2, 1, 0, 0`, with
step `s` at base `s + 2`) carries the ordinals

    ω + 1  ≻  ω  ≻  3  ≻  2  ≻  1  ≻  0

whose codes are `9, 2, 10, 3, 1, 0`.  Two things are worth reading off
this list.  First, **bumping the base does not change the ordinal** —
that is the whole point of the hereditary representation, and Phase B
made it definitional at the term level (`hrep_eval_bump`).  Second, the
codes are **not numerically decreasing** (`2` then `10`): the descent is
genuinely along `≺`, and does not track `<` at all, so the ordinary
induction of Phase 2 does not follow it.  That is the concrete form of the
difficulty Gentzen's theorem makes precise. -/

/-- The ordinals along `G(3)`, as codes. -/
theorem ordOf_goodstein_three :
    (ordOf 2 (goodN 3 0), ordOf 3 (goodN 3 1), ordOf 4 (goodN 3 2),
      ordOf 5 (goodN 3 3), ordOf 6 (goodN 3 4), ordOf 7 (goodN 3 5))
      = (9, 2, 10, 3, 1, 0) := rfl

/-- All of them are normal, so `≺` applies to them. -/
theorem ordOf_goodstein_three_nf :
    (nfB (ordOf 2 (goodN 3 0)), nfB (ordOf 3 (goodN 3 1)),
      nfB (ordOf 4 (goodN 3 2)), nfB (ordOf 5 (goodN 3 3)))
      = (true, true, true, true) := by decide

/-- **Bumping the base preserves the ordinal**, at `(k, n) = (2, 3)`. -/
theorem ordOf_bump_two_three : ordOf 3 (bumpN 2 3) = ordOf 2 3 := rfl

/-- **The Goodstein step strictly decreases the ordinal**, kernel-verified
for the first four steps from `3`.  The codes `9 ≻ 2 ≻ 10 ≻ 3` are not
numerically decreasing — the second step *increases* the code. -/
theorem ordOf_goodstein_three_descends :
    OLt (ordOf 3 (goodN 3 1)) (ordOf 2 (goodN 3 0)) ∧
    OLt (ordOf 4 (goodN 3 2)) (ordOf 3 (goodN 3 1)) ∧
    OLt (ordOf 5 (goodN 3 3)) (ordOf 4 (goodN 3 2)) ∧
    OLt (ordOf 6 (goodN 3 4)) (ordOf 5 (goodN 3 3)) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ### What Phase D still has to prove

Stated here so the boundary is explicit, not implied:

1. `nfB (ordOf k n) = true` for `2 ≤ k` — normality of the assignment's
   image.  This is Phase B's deferred canonicity for `hrep`, in code
   form: it needs the digit bounds (`1 ≤ n / k^e < k`) and the exponent
   ordering (`hlog k (n % k^e) < e`), i.e. genuine `hlog` theory beyond
   the two facts Phase B needed.
2. `ordOf (k + 1) (bumpN k n) = ordOf k n` — base change preserves the
   ordinal.  Phase B's `hrepAux_eval_bump` is the term-level analogue and
   goes through because both sides recurse at the *same* fuel; here the
   fuels differ (`bumpN k n` is far larger than `n`), so a fuel-adequacy
   lemma for `ordOfAux` comes first.
3. `OLt (ordOf (k + 1) (bumpN k n - 1)) (ordOf k n)` for `n ≠ 0` — the
   descent itself, from 2 plus "predecessor decreases the ordinal".

Only (3) needs `tiEps0`; (1) and (2) are ordinary Phase-B-style work. -/

/-! ## The order inside the fragment -/

/-- Congruence of `prec`, as a derivation-former (completing the
equational kit for the extended signature). -/
def Deriv.congPrecE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.prec s₁ s₂) (.prec t₁ t₂)) :=
  .impE (.impE (.eqCongPrec s₁ t₁ s₂ t₂) D₁) D₂

/-- **The fragment computes the order on notations**: `⊢ prec 1̂ 2̂ = 1̂`,
i.e. it proves `1 ≺ ω` (code `1` is the notation `1`, code `2` is `ω`).
Via the numeral graph `precNum`, exactly as Phase B computes `bump` and
`good` on numerals. -/
def precOneOmegaDeriv :
    Deriv [] (.eq (.prec (numeral 1) (numeral 2)) (numeral 1)) := by
  have h : oltN 1 2 = 1 := by decide
  have d := Deriv.precNum (Γ := []) 1 2
  rw [h] at d
  exact d

/-! ## The rule, exercised end to end

A closed derivation that fires `tiEps0`, so that extraction, soundness
and generic continuity are all exercised on the new rule.  The formula is
deliberately trivial (`0 = 0`): the *interesting* progressiveness
premises — the ones whose recursive hypothesis carries real content — are
Phase D's, and cannot be stated before `∃` is added (docs/internal/QUESTIONS.md).  What
this demo certifies is the machinery: the recursor is extracted, it
realizes the concluded `∀x φ(x)` at every ambient above the bound, and
its type-2 instance is continuous. -/

/-- Progressiveness of `0 = 0`, trivially (the recursive hypothesis is
discarded). -/
def tiDemoPremise :
    Deriv [] (Formula.all 1
      ((Formula.all 2 ((Formula.eq (.prec (.var 2) (.var 1)) (.succ .zero)).imp
        (Formula.subst 1 (.var 2) (Formula.eq .zero .zero)))).imp
        (Formula.eq .zero .zero))) :=
  .allI (.impI (.eqRefl .zero)) (fun _ h ↦ absurd h List.not_mem_nil)

/-- **The rule in action**: `⊢ ∀x. 0 = 0`, by transfinite induction along
`≺`.  (Provable far more cheaply, of course — the point is that the
derivation goes *through* `tiEps0`, hence through `tiRecC`.) -/
def tiDemoDeriv : Deriv [] (Formula.all 1 (Formula.eq .zero .zero)) :=
  .tiEps0 tiDemoPremise (by decide) (fun _ _ h ↦ by simp [Formula.binders] at h)
    (by simp [Formula.FreeIn, Term.vars])

/-! ## Extraction and certification

The usual discipline: the extracted realizer realizes the conclusion
(`soundness` at the empty context), the type-2 extract is continuous
(`extract_continuous`), and `#print axioms` runs at every build. -/

/-- The extracted transfinite recursor realizes the concluded
`∀x. φ(x)`. -/
theorem ti_demo_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound tiDemoDeriv ≤ n) :
    MR ρ (Formula.all 1 (Formula.eq .zero .zero)) n
      (extract tiDemoDeriv ρ [] n) :=
  soundness tiDemoDeriv ρ [] trivial n hn

/-- Continuity of the type-2 extract of a `tiEps0` derivation: generic
continuity covers the new rule with no per-derivation certificate. -/
theorem ti_demo_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract tiDemoDeriv ρ [] 1) :=
  extract_continuous tiDemoDeriv ρ

/-- The fragment's computation of the order realizes it too. -/
theorem prec_one_omega_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound precOneOmegaDeriv ≤ n) :
    MR ρ (.eq (.prec (numeral 1) (numeral 2)) (numeral 1)) n
      (extract precOneOmegaDeriv ρ [] n) :=
  soundness precOneOmegaDeriv ρ [] trivial n hn

#print axioms oLt_wf
#print axioms MR_tiRecC
-- The two capstones, now covering the `tiEps0` rule; checked here so the
-- extended versions are verified at every build.
#print axioms soundness
#print axioms extract_continuous
#print axioms ti_demo_realized
#print axioms ti_demo_extract_continuous
#print axioms prec_one_omega_realized
#print axioms ordOf_goodstein_three_descends

end Realizability
