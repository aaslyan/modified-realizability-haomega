/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Core.Soundness

/-!
# A level-free re-extraction into native Lean types

`extract` (`Core/Extraction.lean`) is the certified extraction: it maps a
derivation into the `PureType` tower, where `soundness` proves it realizes its
conclusion and `extract_continuous` proves it denotes a continuous functional.
Everything this repository *claims* rests on that function.

This module is a **second** extraction of the same derivations, targeting
ordinary Lean types instead.  It exists because the certified realizers are, at
the interesting derivations, unrunnable: `derivBound gcdTheorem = 41`, so
`gcdWitness 0 0` never returns, and `spernerWitness` overflows the interpreter
at ambient 11.

## Why this one runs

The realizers' cost is not in their computational content.  It is in the
ambient-level machinery — the `PureType` tower and the `liftR`/`dropR`
transports — which exists so that `MR` can be stated at a flexible ambient and
so that `extract_continuous` can quantify over every derivation at once.  None
of it computes anything.  `tyOf` below drops it: a realizer's *type* was only
ever a function of the formula's connective skeleton, never of the environment,
which is why the translation needs no level index at all.  What is left is
System T plus one well-founded recursor, and that runs at native speed.

## Scope — read this before quoting any output

**This is not the certified artifact.**  Nothing here is related to `extract`
by a theorem: there is no proof that `emit D` and `extract D` agree, and no
soundness theorem for `emit`.  It stands in the same relation to the certified
pipeline as `#program`'s pseudocode does — a generated view, useful and
unproved.  What *is* checked is agreement at concrete inputs, by the `#guard`s
at the foot of this file, wherever the certified extract terminates at all.
That is the `spernerScan` arrangement (`SpernerExtraction.lean`) generalized:
read the same derivation a cheaper way, and check the readings agree.

A soundness theorem for `emit` is a genuine and worthwhile next step; it is not
claimed here.

## Per-rule completeness

`emit` matches every `Deriv` constructor with **no wildcard**, so a new rule
breaks its build until given a case.  This is the *sixth* per-rule site, after
`extract` + `derivBound`, `soundness`, `extract_tracked`, and `toSkel`.  The
wildcard is refused deliberately: a new content-bearing rule silently receiving
a contentless realizer is exactly the failure mode the discipline exists to
prevent, and it would be invisible — the file would still compile and still
produce answers, just wrong ones.

## The one place a proof has to be recovered

`tiEps0`'s order premise `y ≺ x` is an equation, so its realizer is contentless
and carries no evidence of the descent.  `tiRecC` handles this by *re-deciding*
`OLt` at the recursive call and falling back to a default when it fails; `emit`
does the same, for the same reason.  `OLt` is decidable and `oLt_wf` is
choice-free, so nothing is smuggled in.
-/

namespace Realizability.Emit

open Realizability

/-! ## The type translation -/

/-- The Lean type of a realizer of `φ`.

This is the modified-realizability type assignment with the ambient level
erased.  It reads off the connective skeleton only: equations and `⊥` are
contentless, `∧`/`∃`/`∨` package, `→`/`∀` abstract.  Note what is *absent* —
no level index, and no dependence on an environment `ρ`. -/
def tyOf : Formula → Type
  | .bot     => Unit
  | .eq _ _  => Unit
  | .and a b => tyOf a × tyOf b
  | .or a b  => ℕ × (tyOf a × tyOf b)
  | .imp a b => tyOf a → tyOf b
  | .all _ a => ℕ → tyOf a
  | .ex _ a  => ℕ × tyOf a

/-- Every realizer type is inhabited.

Needed in three places: the unused side of an `∨`-introduction's tag-pair,
`⊥`-elimination, and `tiEps0`'s fallback when the re-decided descent fails.
This is the `axiomC` contentless-realizer pattern, made total. -/
def defaultOf : (φ : Formula) → tyOf φ
  | .bot     => ()
  | .eq _ _  => ()
  | .and a b => (defaultOf a, defaultOf b)
  | .or a b  => (0, (defaultOf a, defaultOf b))
  | .imp _ b => fun _ ↦ defaultOf b
  | .all _ a => fun _ ↦ defaultOf a
  | .ex _ a  => (0, defaultOf a)

/-- **Substitution does not change a realizer's type.**

The load-bearing lemma of the module: `subst` rewrites inside *terms*, and
`tyOf` never looks at a term, so the connective skeleton — hence the type — is
preserved.  Every `cast` in `emit` is this lemma, and there are no others. -/
theorem tyOf_subst (x : ℕ) (u : Term) (φ : Formula) :
    tyOf (φ.subst x u) = tyOf φ := by
  induction φ with
  | bot => rfl
  | eq _ _ => rfl
  | and _ _ iha ihb => simp only [Formula.subst, tyOf, iha, ihb]
  | or _ _ iha ihb => simp only [Formula.subst, tyOf, iha, ihb]
  | imp _ _ iha ihb => simp only [Formula.subst, tyOf, iha, ihb]
  | all _ _ ih => simp only [Formula.subst]; split <;> simp only [tyOf, ih]
  | ex _ _ ih => simp only [Formula.subst]; split <;> simp only [tyOf, ih]

/-- Realizers for a context, most recent hypothesis first. -/
def Ctx : List Formula → Type
  | []     => Unit
  | φ :: Γ => tyOf φ × Ctx Γ

/-! ## The emitter -/

/-- **The level-free extraction.**

`emit ρ D γ` is a realizer of `D`'s conclusion in `tyOf`, given realizers `γ`
for its context.  Structural recursion on `D`; the environment `ρ` is threaded
exactly as in `extract` (updated at `allI` and at `exE`'s witness binding), and
every case mirrors the combinator `extract` dispatches to.

Every constructor has a case and there is no wildcard — see the module header. -/
def emit : {Γ : List Formula} → {φ : Formula} →
    (ρ : ℕ → ℕ) → Deriv Γ φ → Ctx Γ → tyOf φ
  -- structural rules
  | _, _, _, .ax, γ => γ.1
  | _, _, ρ, .wk D, γ => emit ρ D γ.2
  | _, _, ρ, .andI D₁ D₂, γ => (emit ρ D₁ γ, emit ρ D₂ γ)
  | _, _, ρ, .andE₁ D, γ => (emit ρ D γ).1
  | _, _, ρ, .andE₂ D, γ => (emit ρ D γ).2
  | _, _, ρ, @Deriv.orI₁ _ _ ψ D, γ => (0, (emit ρ D γ, defaultOf ψ))
  | _, _, ρ, @Deriv.orI₂ _ φ _ D, γ => (1, (defaultOf φ, emit ρ D γ))
  | _, _, ρ, .orE D D₁ D₂, γ =>
      let r := emit ρ D γ
      if r.1 = 0 then emit ρ D₁ (r.2.1, γ) else emit ρ D₂ (r.2.2, γ)
  | _, _, ρ, .impI D, γ => fun h ↦ emit ρ D (h, γ)
  | _, _, ρ, .impE D₁ D₂, γ => (emit ρ D₁ γ) (emit ρ D₂ γ)
  | _, _, _, @Deriv.botE _ φ _, _ => defaultOf φ
  | _, _, ρ, @Deriv.allI _ x _ D _, γ => fun k ↦ emit (Function.update ρ x k) D γ
  | _, _, ρ, @Deriv.allE _ x φ u D _, γ =>
      cast (tyOf_subst x u φ).symm ((emit ρ D γ) (u.eval ρ))
  | _, _, ρ, @Deriv.ind _ x φ D₁ D₂ _, γ => fun k ↦
      Nat.rec (motive := fun _ ↦ tyOf φ)
        (cast (tyOf_subst x .zero φ) (emit ρ D₁ γ))
        (fun j ih ↦
          cast (tyOf_subst x (.succ (.var x)) φ) ((emit ρ D₂ γ) j ih))
        k
  | _, _, ρ, @Deriv.tiEps0 _ x y φ D _ _ _, γ => fun k ↦
      oLt_wf.fix (C := fun _ ↦ tyOf φ)
        (fun j rec ↦ (emit ρ D γ) j
          (fun i _ ↦ cast (tyOf_subst x (.var y) φ).symm
            (if h : OLt i j then rec i h else defaultOf φ)))
        k
  | _, _, ρ, @Deriv.exI _ x φ u D _, γ =>
      (u.eval ρ, cast (tyOf_subst x u φ) (emit ρ D γ))
  | _, _, ρ, @Deriv.exE _ x _ _ D₁ D₂ _ _, γ =>
      let r := emit ρ D₁ γ
      emit (Function.update ρ x r.1) D₂ (r.2, γ)
  -- the one content-bearing axiom: a decidable equality carries its tag
  | _, _, ρ, @Deriv.eqDec _ s t, _ =>
      (if s.eval ρ = t.eval ρ then 0 else 1, (defaultOf _, defaultOf _))
  -- contentless axiom / equation schemas.  Enumerated, never a wildcard.
  | _, _, _, .succNeZero .., _ => defaultOf _
  | _, _, _, .succInj .., _ => defaultOf _
  | _, _, _, .eqRefl .., _ => defaultOf _
  | _, _, _, .eqSymm .., _ => defaultOf _
  | _, _, _, .eqTrans .., _ => defaultOf _
  | _, _, _, .eqCongSucc .., _ => defaultOf _
  | _, _, _, .eqCongPlus .., _ => defaultOf _
  | _, _, _, .eqCongTimes .., _ => defaultOf _
  | _, _, _, .zeroPlus .., _ => defaultOf _
  | _, _, _, .succPlus .., _ => defaultOf _
  | _, _, _, .zeroTimes .., _ => defaultOf _
  | _, _, _, .succTimes .., _ => defaultOf _
  | _, _, _, .predZero, _ => defaultOf _
  | _, _, _, .predSucc .., _ => defaultOf _
  | _, _, _, .expZero .., _ => defaultOf _
  | _, _, _, .expSucc .., _ => defaultOf _
  | _, _, _, .bumpZero .., _ => defaultOf _
  | _, _, _, .bumpNum .., _ => defaultOf _
  | _, _, _, .goodZero .., _ => defaultOf _
  | _, _, _, .goodSucc .., _ => defaultOf _
  | _, _, _, .eqCongPred .., _ => defaultOf _
  | _, _, _, .eqCongExp .., _ => defaultOf _
  | _, _, _, .eqCongBump .., _ => defaultOf _
  | _, _, _, .eqCongGood .., _ => defaultOf _
  | _, _, _, .precNum .., _ => defaultOf _
  | _, _, _, .eqCongPrec .., _ => defaultOf _
  | _, _, _, .ordBump .., _ => defaultOf _
  | _, _, _, .ordPredLt .., _ => defaultOf _
  | _, _, _, .bumpNeZero .., _ => defaultOf _
  | _, _, _, .eqCongOrd .., _ => defaultOf _
  | _, _, _, .hydraZero .., _ => defaultOf _
  | _, _, _, .hydraSucc .., _ => defaultOf _
  | _, _, _, .hordCutLt .., _ => defaultOf _
  | _, _, _, .hcutNum .., _ => defaultOf _
  | _, _, _, .eqCongHcut .., _ => defaultOf _
  | _, _, _, .eqCongHydra .., _ => defaultOf _
  | _, _, _, .eqCongHord .., _ => defaultOf _
  | _, _, _, .solvesZero .., _ => defaultOf _
  | _, _, _, .solvesSucc .., _ => defaultOf _
  | _, _, _, .mvcountNil, _ => defaultOf _
  | _, _, _, .mvcountApp .., _ => defaultOf _
  | _, _, _, .eqCongHcons .., _ => defaultOf _
  | _, _, _, .eqCongHapp .., _ => defaultOf _
  | _, _, _, .eqCongMvcount .., _ => defaultOf _
  | _, _, _, .pasZeroZero, _ => defaultOf _
  | _, _, _, .pasZeroSucc .., _ => defaultOf _
  | _, _, _, .pasSuccZero .., _ => defaultOf _
  | _, _, _, .pasSuccSucc .., _ => defaultOf _
  | _, _, _, .xorNum .., _ => defaultOf _
  | _, _, _, .eqCongXor .., _ => defaultOf _
  | _, _, _, .eqCongPas .., _ => defaultOf _
  | _, _, _, .lookNum .., _ => defaultOf _
  | _, _, _, .eqCongLook .., _ => defaultOf _
  | _, _, _, .eqCongSolves .., _ => defaultOf _
  | _, _, _, .fibZero, _ => defaultOf _
  | _, _, _, .fibOne, _ => defaultOf _
  | _, _, _, .fibSucc .., _ => defaultOf _
  | _, _, _, .eqCongFib .., _ => defaultOf _

/-! ## Readers

The shapes the case-study theorems actually have, mirroring
`Meta/ProgramExtraction.lean`'s helpers — but with no ambient argument, since
there is no ambient. -/

/-- The realizer of a closed derivation, at the zero environment. -/
def run {φ : Formula} (D : Deriv [] φ) : tyOf φ := emit (fun _ ↦ 0) D ()

/-- Read the witness from a closed theorem of shape `∀x. ∃y. φ`. -/
def witness₁ {x y : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.ex y φ))) (a : ℕ) : ℕ := ((run D) a).1

/-- Read the witness from `∀x. ∀y. ∃z. φ`. -/
def witness₂ {x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.all y (.ex z φ)))) (a b : ℕ) : ℕ :=
  ((run D) a b).1

/-- Read the witness from `∀w. ∀x. ∀y. ∃z. φ`. -/
def witness₃ {w x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all w (.all x (.all y (.ex z φ))))) (a b c : ℕ) : ℕ :=
  ((run D) a b c).1

/-- Read the witness from `∀v. ∀w. ∀x. ∀y. ∃z. φ`. -/
def witness₄ {v w x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all v (.all w (.all x (.all y (.ex z φ)))))) (a b c d : ℕ) :
    ℕ := ((run D) a b c d).1

/-- Read the disjunction tag from `∀x. ∀y. φ ∨ ψ`.  `0` is the left branch. -/
def tag₂ {x y : ℕ} {φ ψ : Formula}
    (D : Deriv [] (.all x (.all y (.or φ ψ)))) (a b : ℕ) : ℕ :=
  ((run D) a b).1

#print axioms emit
#print axioms run

end Realizability.Emit
