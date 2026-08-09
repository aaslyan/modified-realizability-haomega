/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Signature.OrdinalAssignment
import Realizability.Signature.Hydra
import Realizability.Signature.Hanoi
import Realizability.Signature.Pascal
import Realizability.Signature.Coloring
import Realizability.Signature.Fibonacci

/-!
# Syntax: terms, formulas, and derivations for the fragment

The fragment of the project brief: intuitionistic propositional logic
(`∧, ∨, →`, with `¬φ` as `φ → ⊥`) over atomic equations between
`0`/`succ`/`+`/`×`-terms with variables, one quantifier rule pair
(`∀`-intro / `∀`-elim over `ℕ`), three arithmetic axiom schemas:
decidable equality (`s = t ∨ ¬ s = t`), `succ s ≠ 0`, and injectivity
of `succ` — and, since the Phase-2 extension, the **arithmetic
induction rule** `ind`: from `φ(0)` and `∀x (φ(x) → φ(succ x))`,
conclude `∀x φ(x)` (see docs/first-order/STATUS.md for its realizer, the
primitive-recursion combinator).

Since the Phase-A extension the signature includes `+` and `×` as
genuine function symbols, with two further schema groups (all with
contentless realizers, like the successor axioms): the
**equational-logic kit** (reflexivity, and symmetry / transitivity /
congruence as implication schemas, one congruence per function symbol),
and the **recursion equations defining `+` and `×`** — recursing on the
*first* argument (`0 + t = t`, `succ s + t = succ (s + t)`,
`0 × t = 0`, `succ s × t = (s × t) + t`), so that the classical
second-argument equations (`x + 0 = x`, …) are genuine theorems proved
by `ind` in `Arithmetic.lean`.

The value-level functions the Phase-B symbols evaluate by (`hlog`,
`bumpN`, `goodN`) live in `OrdinalAssignment.lean`, together with the
ordinal assignment `ordOf` that Phase D's `ord` symbol evaluates by:
they must be available before `Term.eval`, and `Soundness.lean` needs
the theorems about them (Phase D1) for the `ordDescent` case.

Since the Phase-B extension the signature further includes `pred`,
`exp`, hereditary base change `bump`, and the Goodstein sequence
`good`, with their recursion-equation schemas, the numeral graph of
`bump` (see the rule comment and docs/first-order/STATUS.md for why `bump` alone enters
by its graph), and the matching congruence schemas.  The hereditary
base-`k` *representation* itself lives in `Goodstein.lean` as a term of
this very syntax in one distinguished base variable.

Natural deduction is an inductive family `Deriv Γ φ` in `Type`, so the
extraction function of `Extraction.lean` can recurse on it.  Hypotheses
are managed structurally (`ax` reads the head of the context, `wk`
weakens), which matches the curried-context extraction discipline.

Substitution bookkeeping is kept minimal: `∀`-elim carries the side
condition that the substituted term's variables are not bound in the
formula (no capture), `∀`-intro the usual freshness condition for
the context, and `ind` the same no-capture condition as `∀`-elim for
`succ x` — the term its step case substitutes.
-/

namespace Realizability

/-- Terms: variables (named by numbers), zero, successor; since the
Phase-A extension, sum and product; since the Phase-B extension,
predecessor, exponentiation, hereditary base change (`bump`), and the
Goodstein sequence (`good`); since the Phase-H4 extension, the Hydra
move (`hcut`), the Hydra battle (`hydra`) and the Hydra ordinal
assignment (`hord`), all on the tree codes of `Hydra.lean`. -/
inductive Term : Type where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | plus : Term → Term → Term
  | times : Term → Term → Term
  | pred : Term → Term
  | exp : Term → Term → Term
  | bump : Term → Term → Term
  | good : Term → Term → Term
  | prec : Term → Term → Term
  | ord : Term → Term → Term
  | hcut : Term → Term → Term
  | hydra : Term → Term → Term
  | hord : Term → Term
  | hcons : Term → Term → Term
  | happ : Term → Term → Term
  | mvcount : Term → Term
  | solves : Term → Term → Term → Term → Term → Term
  | xor : Term → Term → Term
  | pas : Term → Term → Term
  | look : Term → Term → Term
  | fib : Term → Term
deriving DecidableEq, Repr

namespace Term

/-- Evaluation in an environment.  The Phase-B symbols evaluate by the
value-level functions above (`pred` is truncated predecessor, `exp` is
`^`, `bump` is `bumpN`, `good` is `goodN`). -/
def eval (ρ : ℕ → ℕ) : Term → ℕ
  | var i => ρ i
  | zero => 0
  | succ t => t.eval ρ + 1
  | plus s t => s.eval ρ + t.eval ρ
  | times s t => s.eval ρ * t.eval ρ
  | pred t => t.eval ρ - 1
  | exp s t => s.eval ρ ^ t.eval ρ
  | bump s t => bumpN (s.eval ρ) (t.eval ρ)
  | good s t => goodN (s.eval ρ) (t.eval ρ)
  | prec s t => oltN (s.eval ρ) (t.eval ρ)
  | ord s t => ordOf (s.eval ρ) (t.eval ρ)
  | hcut s t => hydraStepN (s.eval ρ) (t.eval ρ)
  | hydra s t => hydraSeqN (s.eval ρ) (t.eval ρ)
  | hord t => ordOfHydraN (t.eval ρ)
  | hcons s t => hconsN (s.eval ρ) (t.eval ρ)
  | happ s t => happN (s.eval ρ) (t.eval ρ)
  | mvcount t => hlen (t.eval ρ)
  | solves n f t v k =>
      solvesN (n.eval ρ) (f.eval ρ) (t.eval ρ) (v.eval ρ) (k.eval ρ)
  | xor s t => xorN (s.eval ρ) (t.eval ρ)
  | pas s t => pasN (s.eval ρ) (t.eval ρ)
  | look s t => lookN (s.eval ρ) (t.eval ρ)
  | fib t => fibN (t.eval ρ)

/-- The variables occurring in a term. -/
def vars : Term → List ℕ
  | var i => [i]
  | zero => []
  | succ t => t.vars
  | plus s t => s.vars ++ t.vars
  | times s t => s.vars ++ t.vars
  | pred t => t.vars
  | exp s t => s.vars ++ t.vars
  | bump s t => s.vars ++ t.vars
  | good s t => s.vars ++ t.vars
  | prec s t => s.vars ++ t.vars
  | ord s t => s.vars ++ t.vars
  | hcut s t => s.vars ++ t.vars
  | hydra s t => s.vars ++ t.vars
  | hord t => t.vars
  | hcons s t => s.vars ++ t.vars
  | happ s t => s.vars ++ t.vars
  | mvcount t => t.vars
  | solves n f t v k => n.vars ++ f.vars ++ t.vars ++ v.vars ++ k.vars
  | xor s t => s.vars ++ t.vars
  | pas s t => s.vars ++ t.vars
  | look s t => s.vars ++ t.vars
  | fib t => t.vars

/-- Substitution of a term for a variable. -/
def subst (x : ℕ) (u : Term) : Term → Term
  | var i => if i = x then u else var i
  | zero => zero
  | succ t => succ (subst x u t)
  | plus s t => plus (subst x u s) (subst x u t)
  | times s t => times (subst x u s) (subst x u t)
  | pred t => pred (subst x u t)
  | exp s t => exp (subst x u s) (subst x u t)
  | bump s t => bump (subst x u s) (subst x u t)
  | good s t => good (subst x u s) (subst x u t)
  | prec s t => prec (subst x u s) (subst x u t)
  | ord s t => ord (subst x u s) (subst x u t)
  | hcut s t => hcut (subst x u s) (subst x u t)
  | hydra s t => hydra (subst x u s) (subst x u t)
  | hord t => hord (subst x u t)
  | hcons s t => hcons (subst x u s) (subst x u t)
  | happ s t => happ (subst x u s) (subst x u t)
  | mvcount t => mvcount (subst x u t)
  | solves n f t v k =>
      solves (subst x u n) (subst x u f) (subst x u t) (subst x u v) (subst x u k)
  | xor s t => xor (subst x u s) (subst x u t)
  | pas s t => pas (subst x u s) (subst x u t)
  | look s t => look (subst x u s) (subst x u t)
  | fib t => fib (subst x u t)

/-- Evaluation after substitution is evaluation in the updated
environment. -/
theorem eval_subst (ρ : ℕ → ℕ) (x : ℕ) (u : Term) :
    ∀ t : Term, (subst x u t).eval ρ
      = t.eval (Function.update ρ x (u.eval ρ)) := by
  intro t
  induction t with
  | var i =>
    by_cases h : i = x
    · subst h
      simp [subst, eval, Function.update]
    · simp [subst, eval, h, Function.update]
  | zero => rfl
  | succ t ih => simp [subst, eval, ih]
  | plus s t ihs iht => simp [subst, eval, ihs, iht]
  | times s t ihs iht => simp [subst, eval, ihs, iht]
  | pred t ih => simp [subst, eval, ih]
  | exp s t ihs iht => simp [subst, eval, ihs, iht]
  | bump s t ihs iht => simp [subst, eval, ihs, iht]
  | good s t ihs iht => simp [subst, eval, ihs, iht]
  | prec s t ihs iht => simp [subst, eval, ihs, iht]
  | ord s t ihs iht => simp [subst, eval, ihs, iht]
  | hcut s t ihs iht => simp [subst, eval, ihs, iht]
  | hydra s t ihs iht => simp [subst, eval, ihs, iht]
  | hord t ih => simp [subst, eval, ih]
  | hcons s t ihs iht => simp [subst, eval, ihs, iht]
  | happ s t ihs iht => simp [subst, eval, ihs, iht]
  | mvcount t ih => simp [subst, eval, ih]
  | solves n f t v k ihn ihf iht ihv ihk =>
      simp [subst, eval, ihn, ihf, iht, ihv, ihk]
  | xor s t ihs iht => simp [subst, eval, ihs, iht]
  | pas s t ihs iht => simp [subst, eval, ihs, iht]
  | look s t ihs iht => simp [subst, eval, ihs, iht]
  | fib t ih => simp [subst, eval, ih]

/-- Evaluation only depends on the values of the occurring variables. -/
theorem eval_congr {ρ ρ' : ℕ → ℕ} :
    ∀ {t : Term}, (∀ y ∈ t.vars, ρ y = ρ' y) → t.eval ρ = t.eval ρ' := by
  intro t
  induction t with
  | var i => intro h; exact h i (by simp [vars])
  | zero => intro _; rfl
  | succ t ih => intro h; simp only [eval]; rw [ih h]
  | plus s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | times s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | pred t ih => intro h; simp only [eval]; rw [ih h]
  | exp s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | bump s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | good s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | prec s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | ord s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | hcut s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | hydra s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | hord t ih => intro h; simp only [eval]; rw [ih h]
  | hcons s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | happ s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | mvcount t ih => intro h; simp only [eval]; rw [ih h]
  | solves n f t v k ihn ihf iht ihv ihk =>
    intro h
    simp only [eval]
    simp only [vars, List.mem_append] at h
    rw [ihn fun y hy ↦ h y (Or.inl (Or.inl (Or.inl (Or.inl hy)))),
      ihf fun y hy ↦ h y (Or.inl (Or.inl (Or.inl (Or.inr hy)))),
      iht fun y hy ↦ h y (Or.inl (Or.inl (Or.inr hy))),
      ihv fun y hy ↦ h y (Or.inl (Or.inr hy)),
      ihk fun y hy ↦ h y (Or.inr hy)]
  | xor s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | pas s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | look s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy ↦ h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy ↦ h y (List.mem_append.mpr (Or.inr hy))]
  | fib t ih => intro h; simp only [eval]; rw [ih h]

end Term

/-- The numeral for `n`: an `n`-fold `succ` of `zero`. -/
def numeral : ℕ → Term
  | 0 => .zero
  | n + 1 => .succ (numeral n)

/-- Numerals evaluate to their number, in every environment. -/
@[simp] theorem numeral_eval (ρ : ℕ → ℕ) : ∀ n : ℕ, (numeral n).eval ρ = n
  | 0 => rfl
  | n + 1 => by simp only [numeral, Term.eval, numeral_eval ρ n]

/-- Formulas of the fragment. -/
inductive Formula : Type where
  | bot : Formula
  | eq : Term → Term → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | all : ℕ → Formula → Formula
  | ex : ℕ → Formula → Formula
deriving DecidableEq, Repr

namespace Formula

/-- Negation is implication into absurdity. -/
def neg (φ : Formula) : Formula := φ.imp bot

/-- Free occurrence of a variable. -/
def FreeIn (x : ℕ) : Formula → Prop
  | bot => False
  | eq s t => x ∈ s.vars ∨ x ∈ t.vars
  | and φ ψ => FreeIn x φ ∨ FreeIn x ψ
  | or φ ψ => FreeIn x φ ∨ FreeIn x ψ
  | imp φ ψ => FreeIn x φ ∨ FreeIn x ψ
  | all y φ => x ≠ y ∧ FreeIn x φ
  | ex y φ => x ≠ y ∧ FreeIn x φ

/-- The variables bound somewhere in a formula. -/
def binders : Formula → List ℕ
  | bot => []
  | eq _ _ => []
  | and φ ψ => φ.binders ++ ψ.binders
  | or φ ψ => φ.binders ++ ψ.binders
  | imp φ ψ => φ.binders ++ ψ.binders
  | all y φ => y :: φ.binders
  | ex y φ => y :: φ.binders

/-- Substitution of a term for a variable (stops at a rebinding of the
same variable; capture is excluded by the `SubstOK` side condition). -/
def subst (x : ℕ) (u : Term) : Formula → Formula
  | bot => bot
  | eq s t => eq (Term.subst x u s) (Term.subst x u t)
  | and φ ψ => and (subst x u φ) (subst x u ψ)
  | or φ ψ => or (subst x u φ) (subst x u ψ)
  | imp φ ψ => imp (subst x u φ) (subst x u ψ)
  | all y φ => if y = x then all y φ else all y (subst x u φ)
  | ex y φ => if y = x then ex y φ else ex y (subst x u φ)

/-- Side condition for `∀`-elimination: no variable of the substituted
term is bound in the formula. -/
def SubstOK (u : Term) (φ : Formula) : Prop :=
  ∀ y ∈ u.vars, y ∉ φ.binders

end Formula

/-- A variable is fresh for a context when it is free in none of its
formulas. -/
def FreshIn (x : ℕ) (Γ : List Formula) : Prop :=
  ∀ φ ∈ Γ, ¬ φ.FreeIn x

/-! ## The side conditions are decidable

All three conditions carried by the quantifier rules are decidable, so
concrete derivations discharge them by `decide +kernel` rather than by
hand.  (Introduced for Phase D2; shared with the Hydra layer since H5.) -/

/-- Free occurrence is decidable. -/
instance decidableFreeIn (x : ℕ) : (φ : Formula) → Decidable (Formula.FreeIn x φ)
  | .bot => inferInstanceAs (Decidable False)
  | .eq s t => inferInstanceAs (Decidable (x ∈ s.vars ∨ x ∈ t.vars))
  | .and φ ψ =>
      @instDecidableOr _ _ (decidableFreeIn x φ) (decidableFreeIn x ψ)
  | .or φ ψ =>
      @instDecidableOr _ _ (decidableFreeIn x φ) (decidableFreeIn x ψ)
  | .imp φ ψ =>
      @instDecidableOr _ _ (decidableFreeIn x φ) (decidableFreeIn x ψ)
  | .all y φ =>
      @instDecidableAnd _ _ (inferInstanceAs (Decidable (x ≠ y)))
        (decidableFreeIn x φ)
  | .ex y φ =>
      @instDecidableAnd _ _ (inferInstanceAs (Decidable (x ≠ y)))
        (decidableFreeIn x φ)

/-- Substitutability is decidable as well. -/
instance decidableSubstOK (u : Term) (φ : Formula) :
    Decidable (Formula.SubstOK u φ) :=
  inferInstanceAs (Decidable (∀ y ∈ u.vars, y ∉ φ.binders))

/-- Freshness for a context is then decidable too. -/
instance decidableFreshIn (x : ℕ) (Γ : List Formula) : Decidable (FreshIn x Γ) :=
  inferInstanceAs (Decidable (∀ φ ∈ Γ, ¬ φ.FreeIn x))

open Formula in
/-- **Natural deduction for the fragment.**  Contexts are lists (head =
most recent hypothesis); `Type`-valued so extraction can recurse. -/
inductive Deriv : List Formula → Formula → Type where
  | ax {Γ : List Formula} {φ : Formula} : Deriv (φ :: Γ) φ
  | wk {Γ : List Formula} {φ ψ : Formula} : Deriv Γ φ → Deriv (ψ :: Γ) φ
  | andI {Γ : List Formula} {φ ψ : Formula} :
      Deriv Γ φ → Deriv Γ ψ → Deriv Γ (φ.and ψ)
  | andE₁ {Γ : List Formula} {φ ψ : Formula} : Deriv Γ (φ.and ψ) → Deriv Γ φ
  | andE₂ {Γ : List Formula} {φ ψ : Formula} : Deriv Γ (φ.and ψ) → Deriv Γ ψ
  | orI₁ {Γ : List Formula} {φ ψ : Formula} : Deriv Γ φ → Deriv Γ (φ.or ψ)
  | orI₂ {Γ : List Formula} {φ ψ : Formula} : Deriv Γ ψ → Deriv Γ (φ.or ψ)
  | orE {Γ : List Formula} {φ ψ χ : Formula} : Deriv Γ (φ.or ψ) →
      Deriv (φ :: Γ) χ → Deriv (ψ :: Γ) χ → Deriv Γ χ
  | impI {Γ : List Formula} {φ ψ : Formula} :
      Deriv (φ :: Γ) ψ → Deriv Γ (φ.imp ψ)
  | impE {Γ : List Formula} {φ ψ : Formula} :
      Deriv Γ (φ.imp ψ) → Deriv Γ φ → Deriv Γ ψ
  | botE {Γ : List Formula} {φ : Formula} : Deriv Γ .bot → Deriv Γ φ
  | allI {Γ : List Formula} {x : ℕ} {φ : Formula} :
      Deriv Γ φ → FreshIn x Γ → Deriv Γ (.all x φ)
  | allE {Γ : List Formula} {x : ℕ} {φ : Formula} (u : Term) :
      Deriv Γ (.all x φ) → Formula.SubstOK u φ → Deriv Γ (φ.subst x u)
  | ind {Γ : List Formula} {x : ℕ} {φ : Formula} :
      Deriv Γ (φ.subst x .zero) →
      Deriv Γ (.all x (φ.imp (φ.subst x (.succ (.var x))))) →
      Formula.SubstOK (.succ (.var x)) φ →
      Deriv Γ (.all x φ)
  | eqDec {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).or (eq s t).neg)
  | succNeZero {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.succ s) .zero).neg
  | succInj {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq (.succ s) (.succ t)).imp (eq s t))
  -- Phase A: the equational-logic kit for the signature `{0, succ, +, ×}`,
  -- as implication schemas in the style of `succInj` (all contentless).
  | eqRefl {Γ : List Formula} (t : Term) :
      Deriv Γ (eq t t)
  | eqSymm {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).imp (eq t s))
  | eqTrans {Γ : List Formula} (s t u : Term) :
      Deriv Γ ((eq s t).imp ((eq t u).imp (eq s u)))
  | eqCongSucc {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).imp (eq (.succ s) (.succ t)))
  | eqCongPlus {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.plus s₁ s₂) (.plus t₁ t₂))))
  | eqCongTimes {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.times s₁ s₂) (.times t₁ t₂))))
  -- Phase A: the recursion equations *defining* `+` and `×`, recursing on
  -- the **first** argument (the mirror of the briefed equations, which are
  -- thereby genuine `ind` theorems — see `Arithmetic.lean` and docs/first-order/STATUS.md).
  | zeroPlus {Γ : List Formula} (t : Term) :
      Deriv Γ (eq (.plus .zero t) t)
  | succPlus {Γ : List Formula} (s t : Term) :
      Deriv Γ (eq (.plus (.succ s) t) (.succ (.plus s t)))
  | zeroTimes {Γ : List Formula} (t : Term) :
      Deriv Γ (eq (.times .zero t) .zero)
  | succTimes {Γ : List Formula} (s t : Term) :
      Deriv Γ (eq (.times (.succ s) t) (.plus (.times s t) t))
  -- Phase B: recursion equations for predecessor and exponentiation
  -- (honest first-order schemas, like the Phase-A group) …
  | predZero {Γ : List Formula} :
      Deriv Γ (eq (.pred .zero) .zero)
  | predSucc {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.pred (.succ s)) s)
  | expZero {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.exp s .zero) (.succ .zero))
  | expSucc {Γ : List Formula} (s t : Term) :
      Deriv Γ (eq (.exp s (.succ t)) (.times (.exp s t) s))
  -- … the two axioms for hereditary base change: absorption at zero
  -- (a term schema) and the numeral graph (an `ℕ`-parameterized schema —
  -- `bump`'s course-of-values recursion through the hereditary exponent
  -- structure is not a first-order equation schema; the semantic
  -- characterization "`bump` is the representation read at the next
  -- base" is *derived*, per numeral instance, in `Goodstein.lean`) …
  | bumpZero {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.bump s .zero) .zero)
  | bumpNum {Γ : List Formula} (k n : ℕ) :
      Deriv Γ (eq (.bump (numeral k) (numeral n)) (numeral (bumpN k n)))
  -- … the Goodstein sequence's own defining recursion (genuine
  -- first-order schemas again: one step bumps the base `t + 2` and
  -- takes the predecessor) …
  | goodZero {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.good s .zero) s)
  | goodSucc {Γ : List Formula} (s t : Term) :
      Deriv Γ (eq (.good s (.succ t))
        (.pred (.bump (.succ (.succ t)) (.good s t))))
  -- … and the congruence schemas completing the equational-logic kit
  -- for the extended signature.
  | eqCongPred {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).imp (eq (.pred s) (.pred t)))
  | eqCongExp {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.exp s₁ s₂) (.exp t₁ t₂))))
  | eqCongBump {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.bump s₁ s₂) (.bump t₁ t₂))))
  | eqCongGood {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.good s₁ s₂) (.good t₁ t₂))))
  -- Phase C: **transfinite induction along the ordinal notations below
  -- `ε₀`** (`tiEps0`), the one rule of the fragment that is not a
  -- consequence of its own resources — this is the content of
  -- Gentzen/Kirby–Paris.  Variables range over `ℕ`, read as notation
  -- *codes* (`Epsilon0.lean`), and `y ≺ x` is the atomic formula
  -- `prec y x = 1`, so the rule stays inside the fragment's
  -- equations-only formula language.  Progressiveness of `φ` yields
  -- `∀x φ(x)`; its realizer is the recursor `tiRecC`, whose defining
  -- recursion runs along `≺` rather than along `succ` (contrast `ind`).
  --
  -- Side conditions, all three needed by the soundness proof: the two
  -- variables are distinct (so that `x`'s value survives the inner
  -- binder), the substituted variable does not get captured, and `y` is
  -- not free in `φ` (so that `φ(y)` under the inner environment is
  -- `φ` under `x ↦ y`'s value).
  | tiEps0 {Γ : List Formula} {x y : ℕ} {φ : Formula} :
      Deriv Γ (Formula.all x
        ((Formula.all y ((eq (.prec (.var y) (.var x)) (.succ .zero)).imp
          (φ.subst x (.var y)))).imp φ)) →
      x ≠ y →
      Formula.SubstOK (.var y) φ →
      ¬ φ.FreeIn y →
      Deriv Γ (.all x φ)
  -- Phase C: the numeral graph of the order (`prec` is a *decidable*
  -- comparison of codes, so the fragment computes it on numerals — the
  -- same device as Phase B's `bumpNum`, and for the same reason: the
  -- recursion is course-of-values through the notation structure, not a
  -- first-order equation schema) …
  | precNum {Γ : List Formula} (a b : ℕ) :
      Deriv Γ (eq (.prec (numeral a) (numeral b)) (numeral (oltN a b)))
  -- … and its congruence schema, completing the equational kit.
  | eqCongPrec {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.prec s₁ s₂) (.prec t₁ t₂))))
  -- Phase D0: the **existential quantifier**.  Its two rules are the
  -- standard ones; the side conditions are `∀`-elim's no-capture
  -- condition for introduction, and for elimination the usual freshness
  -- of the bound variable in the context and in the conclusion (without
  -- which the witness could leak out of the scope it was introduced in).
  -- Phase D2/D5: the **ordinal assignment** `ord` (base, value), evaluated
  -- by `ordOf`, and the three facts about it the fragment imports.  D2
  -- imported their *composite* — "one Goodstein step descends" — as a
  -- single schema; D5 split it into the three separate properties below
  -- and derives the composite inside the fragment
  -- (`OrdinalDescent.lean`).  Each of the three corresponds to exactly one
  -- theorem of Phase D1, and none of them mentions the Goodstein sequence:
  --
  --   `ordBump`      ↔  `ordOf_bumpN`       (base change preserves it)
  --   `ordPredLt`    ↔  `olt_ordOf_of_lt`   (it is strictly monotone)
  --   `bumpNeZero`   ↔  `bumpN_ne_zero`     (bump is non-degenerate)
  --
  -- They are schemas for the reason Phase B's `bumpNum` is: their content
  -- is course-of-values recursion through the hereditary structure, which
  -- is not a first-order equation schema over the fragment's terms.  The
  -- bases are written `succ (succ b)` because base change is false at
  -- base 1 (see docs/first-order/STATUS.md).
  | ordBump {Γ : List Formula} (b n : Term) :
      Deriv Γ (eq (.ord (.succ (.succ (.succ b))) (.bump (.succ (.succ b)) n))
        (.ord (.succ (.succ b)) n))
  | ordPredLt {Γ : List Formula} (b n : Term) :
      Deriv Γ ((eq n .zero).neg.imp
        (eq (.prec (.ord (.succ (.succ b)) (.pred n))
              (.ord (.succ (.succ b)) n))
          (.succ .zero)))
  | bumpNeZero {Γ : List Formula} (b n : Term) :
      Deriv Γ ((eq n .zero).neg.imp
        (eq (.bump (.succ (.succ b)) n) .zero).neg)
  | eqCongOrd {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.ord s₁ s₂) (.ord t₁ t₂))))
  | exI {Γ : List Formula} {x : ℕ} {φ : Formula} (u : Term) :
      Deriv Γ (φ.subst x u) → Formula.SubstOK u φ → Deriv Γ (.ex x φ)
  | exE {Γ : List Formula} {x : ℕ} {φ ψ : Formula} :
      Deriv Γ (.ex x φ) → Deriv (φ :: Γ) ψ →
      FreshIn x Γ → ¬ ψ.FreeIn x → Deriv Γ ψ
  -- Phase H4: the **Hydra layer**.  `hcut (n, c)` is one Kirby–Paris move
  -- on the hydra coded `c`, growing `n` copies at the grandparent;
  -- `hydra (s, t)` is the state after `t` moves from the hydra coded `s`,
  -- with `t + 1` copies at move `t`; `hord c` is the ordinal notation
  -- assigned to the hydra coded `c` (`Hydra.lean`).  A code is `0` exactly
  -- when the hydra is a bare head, so "`= 0`" is the fragment's
  -- termination test — no new predicate is needed.
  --
  -- Two of the three schemas are the battle's own recursion equations, in
  -- the style of `goodZero`/`goodSucc`.  The third is the single imported
  -- fact of the phase, and it follows the `ordPredLt` pattern exactly: it
  -- is a property of *one move symbol* relative to *one ordinal symbol*,
  -- and it does not mention the battle.  Its Lean twin is
  -- `olt_ordOfHydraN_step`, i.e. Phase H3's `cutH_descends` read on codes.
  | hydraZero {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.hydra s .zero) s)
  | hydraSucc {Γ : List Formula} (s t : Term) :
      Deriv Γ (eq (.hydra s (.succ t)) (.hcut (.succ t) (.hydra s t)))
  | hordCutLt {Γ : List Formula} (n c : Term) :
      Deriv Γ ((eq c .zero).neg.imp
        (eq (.prec (.hord (.hcut n c)) (.hord c)) (.succ .zero)))
  -- The move's numeral graph, for the same reason `bump` and `prec` have
  -- one: a move is tree surgery on a code, which is course-of-values
  -- recursion through the decoding, not a first-order equation schema over
  -- the fragment's terms.  It is what lets the fragment *compute* a
  -- concrete battle (`hydra_chain_derivable`) as well as reason about it.
  | hcutNum {Γ : List Formula} (n c : ℕ) :
      Deriv Γ (eq (.hcut (numeral n) (numeral c)) (numeral (hydraStepN n c)))
  | eqCongHcut {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.hcut s₁ s₂) (.hcut t₁ t₂))))
  | eqCongHydra {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.hydra s₁ s₂) (.hydra t₁ t₂))))
  | eqCongHord {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).imp (eq (.hord s) (.hord t)))
  -- Phase E2: the **Tower of Hanoi**.  `hcons m k` prepends a move to an
  -- encoded sequence and `happ` concatenates two (the cons coding of
  -- `Hanoi.lean`, over the same pairing as everything else); `mvcount k`
  -- is the sequence's length; and `solves n f t v k` is the
  -- characteristic function of "`k` is a valid `n`-disk solution moving
  -- `f → t` via `v`", so the fragment writes `Solves` as the equation
  -- `solves(n,f,t,v,k) = 1`.  A move `f → t` needs no symbol of its own:
  -- it is the term `f × 3 + t`, written with the arithmetic Phase A
  -- already has.
  --
  -- Two schemas give `solves` its recursion, and they are the *only*
  -- mathematical import of the phase.  Unlike Goodstein's and Hydra's,
  -- both are ordinary statements of PA, and the induction that consumes
  -- them is `ind` — no `tiEps0`, no ordinals anywhere in this layer.
  --
  --   `solvesZero` ↔ `solvesN_hanoiN` at `n = 0`
  --   `solvesSucc` ↔ `solvesN_succ`      (the branching step)
  --   `mvcountNil` ↔ `hlen_nil`
  --   `mvcountApp` ↔ `hlen_happN` with `hlen_cons`
  --
  -- The move count is carried in the subtraction-free form
  -- `succ (mvcount k) = 2^n`, because the fragment has `pred` but no
  -- order relation; `2^n - 1` is recovered at the end by `predSucc`.
  | solvesZero {Γ : List Formula} (f t v : Term) :
      Deriv Γ (eq (.solves .zero f t v .zero) (.succ .zero))
  | solvesSucc {Γ : List Formula} (n f t v k₁ k₂ : Term) :
      Deriv Γ ((eq (.solves n f v t k₁) (.succ .zero)).imp
        ((eq (.solves n v t f k₂) (.succ .zero)).imp
          (eq (.solves (.succ n) f t v
              (.happ k₁ (.hcons (.plus (.times f (numeral 3)) t) k₂)))
            (.succ .zero))))
  | mvcountNil {Γ : List Formula} :
      Deriv Γ (eq (.mvcount .zero) .zero)
  | mvcountApp {Γ : List Formula} (k₁ m k₂ : Term) :
      Deriv Γ (eq (.succ (.mvcount (.happ k₁ (.hcons m k₂))))
        (.plus (.succ (.mvcount k₁)) (.succ (.mvcount k₂))))
  | eqCongHcons {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.hcons s₁ s₂) (.hcons t₁ t₂))))
  | eqCongHapp {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.happ s₁ s₂) (.happ t₁ t₂))))
  | eqCongMvcount {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).imp (eq (.mvcount s) (.mvcount t)))
  -- Phase F2: **Pascal's triangle mod 2**.  `pas n k` is the parity of
  -- the binomial coefficient and `xor` is exclusive or; the four
  -- equations below are `pasN`'s own structural recursion, and they are
  -- the phase's *entire* import.  The characteristic clauses
  -- `pas(n,n) = 1` and "`pas` vanishes above the diagonal" are **not**
  -- axioms: `PascalTheorem.lean` derives them by `ind`.
  --
  -- `xor` enters by its numeral graph, like `bump`, `prec` and `hcut`
  -- before it, because `a + b − 2ab` is **not expressible** in this
  -- signature: `pred` subtracts constants from terms, and a composition
  -- of monotone operations under outer `pred`s cannot be `1 − x`.
  | pasZeroZero {Γ : List Formula} :
      Deriv Γ (eq (.pas .zero .zero) (.succ .zero))
  | pasZeroSucc {Γ : List Formula} (k : Term) :
      Deriv Γ (eq (.pas .zero (.succ k)) .zero)
  | pasSuccZero {Γ : List Formula} (n : Term) :
      Deriv Γ (eq (.pas (.succ n) .zero) (.succ .zero))
  | pasSuccSucc {Γ : List Formula} (n k : Term) :
      Deriv Γ (eq (.pas (.succ n) (.succ k))
        (.xor (.pas n k) (.pas n (.succ k))))
  | xorNum {Γ : List Formula} (a b : ℕ) :
      Deriv Γ (eq (.xor (numeral a) (numeral b)) (numeral (xorN a b)))
  | eqCongXor {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.xor s₁ s₂) (.xor t₁ t₂))))
  | eqCongPas {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.pas s₁ s₂) (.pas t₁ t₂))))
  -- Sperner (1D): the coloring lookup symbol.  A numeral graph (a lookup
  -- is a cons-list decode — course-of-values through the encoding, not a
  -- first-order equation schema, the same reason `bump`/`hcut` have one)
  -- plus its congruence.
  | lookNum {Γ : List Formula} (a b : ℕ) :
      Deriv Γ (eq (.look (numeral a) (numeral b)) (numeral (lookN a b)))
  | eqCongLook {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.look s₁ s₂) (.look t₁ t₂))))
  | eqCongSolves {Γ : List Formula} (n₁ n₂ f₁ f₂ t₁ t₂ v₁ v₂ k₁ k₂ : Term) :
      Deriv Γ ((eq n₁ n₂).imp ((eq f₁ f₂).imp ((eq t₁ t₂).imp ((eq v₁ v₂).imp
        ((eq k₁ k₂).imp
          (eq (.solves n₁ f₁ t₁ v₁ k₁) (.solves n₂ f₂ t₂ v₂ k₂)))))))
  -- Fibonacci: the value symbol `fib`, with its defining recursion as
  -- honest first-order equation schemas (like `good`/`exp`, not a numeral
  -- graph — both `fib (n+1)` and `fib n` on the right are fragment terms)
  -- plus its congruence.  The base needs *two* seeds (`fibZero`, `fibOne`),
  -- because `fibSucc` reaches only `fib (n+2)`.  The step order
  -- `fib n + fib (n+1)` matches `FibonacciTheorem.lean`'s paired invariant
  -- `(y, z) ↦ (z, y + z)` and `fibN_succ_succ`.
  | fibZero {Γ : List Formula} :
      Deriv Γ (eq (.fib .zero) .zero)
  | fibOne {Γ : List Formula} :
      Deriv Γ (eq (.fib (.succ .zero)) (.succ .zero))
  | fibSucc {Γ : List Formula} (n : Term) :
      Deriv Γ (eq (.fib (.succ (.succ n)))
        (.plus (.fib n) (.fib (.succ n))))
  | eqCongFib {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).imp (eq (.fib s) (.fib t)))

end Realizability
