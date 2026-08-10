/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.KitAttr

/-!
# The derivation-authoring kit

Writing derivations by hand in a de Bruijn calculus is the practical
bottleneck of this development, and the tools that fixed it were discovered
one case study at a time — which is why they ended up scattered through the
files that happened to need them first. `Deriv.symmE` and `Deriv.transE` lived
in `Pascal.lean`; `Deriv.congFun` in `PascalTheorem.lean`; the normalization
tactic in `GcdDvd.lean`. Every later derivation — Goodstein, Hydra, both
Hercules theorems, Sperner — therefore imported the gcd development in order
to write an equational chain.

This module collects them. It sits directly on the core, so a new derivation
file needs `import HAomega.Kit` and nothing else.

## What is here

* **Equational combinators.** `symmE`, `transE`, `congFun`, `congArg` — all
  derived from the single Leibniz rule `eqSubst`, which is why the rule set
  has no congruence schemas.
* **`deriv_norm`** — reduce every `Ctx.wk`, `Formula.wk`/`rename`/`subst` and
  term-level weakening in a goal or hypothesis to ground form. This is the fix
  for the failure mode that dominated early authoring: an elimination whose
  motive contains an un-normalized substitution will not unify with a
  hypothesis that is otherwise literally it.
* **`deriv_assumption`** — normalize, then find the hypothesis at whatever
  context depth it sits, replacing hand-pinned `axₙ` accessors.

## Extensibility

`deriv_norm` is driven by the `derivNorm` simp attribute, not by a fixed list.
A layer that introduces its own definitions tags them where they are defined —
`attribute [derivNorm] Dvd mulT_subst` in the gcd files, and so on — and every
later derivation gets the stronger normalizer without this module knowing
anything about them. That is the difference between a tactic that was written
for gcd and a tactic other developments can use.
-/

namespace HAomega

/-! ## Core substitution lemmas

Facts about the term and formula calculus, with no case study in them.  They
lived in `Pascal.lean` only because Pascal needed them first. -/

theorem Sub.ext_ren {Γ Δ Θ : List Ty} {σ : Ty} (ρ : Ren Γ Δ) (s : Sub Δ Θ) :
    (fun τ v ↦ Sub.ext (σ := σ) s τ (Ren.ext ρ τ v))
      = Sub.ext (σ := σ) (fun τ v ↦ s τ (ρ τ v)) := by
  funext τ v; cases v <;> rfl

theorem Tm.subst_rename {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ Θ : List Ty} (ρ : Ren Γ Δ) (s : Sub Δ Θ),
      (t.rename ρ).subst s = t.subst (fun σ v ↦ s σ (ρ σ v)) := by
  induction t with
  | var v => intros; rfl
  | lam b ih =>
      intro Δ Θ ρ s
      simp only [Tm.rename, Tm.subst]
      rw [ih ρ.ext s.ext, Sub.ext_ren]
  | app f a ihf iha => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihf, iha]
  | star => intros; rfl
  | pair a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | fst t ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | snd t ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | zero => intros; rfl
  | succ t ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | add a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | prec a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | pred a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | bump a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | good a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | ord a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | hcut a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | hcutAt p a b ihp iha ihb =>
      intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihp, iha, ihb]
  | ezero => intros; rfl
  | orde a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | olte a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | tiRecE sc n ihs ihn =>
      intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihs, ihn]
  | hleaf => intros; rfl
  | hcutH a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | hleafQ a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | hordH a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | hcutAtH p a b ihp iha ihb =>
      intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihp, iha, ihb]
  | qnat a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | dnat a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | dhalf a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | dtoq a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | qadd a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | qsub a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | qmul a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | qdiv a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | qlt a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | dadd a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | dsub a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | dmul a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | dlt a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | hydra a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | hord a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | tiRec sc n ihs ihn => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihs, ihn]
  | recNat z sc n ihz ihs ihn =>
      intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihz, ihs, ihn]

theorem Tm.subst_id {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    t.subst (fun _ v ↦ Tm.var v) = t := by
  induction t with
  | var v => rfl
  | lam b ih =>
      simp only [Tm.subst]
      rw [show (Sub.ext (fun σ (v : Var _ σ) ↦ Tm.var v))
          = (fun σ (v : Var _ σ) ↦ Tm.var v) from by funext σ v; cases v <;> rfl, ih]
  | app f a ihf iha => simp only [Tm.subst, ihf, iha]
  | star => rfl
  | pair a b iha ihb => simp only [Tm.subst, iha, ihb]
  | fst t ih => simp only [Tm.subst, ih]
  | snd t ih => simp only [Tm.subst, ih]
  | zero => rfl
  | succ t ih => simp only [Tm.subst, ih]
  | add a b iha ihb => simp only [Tm.subst, iha, ihb]
  | prec a b iha ihb => simp only [Tm.subst, iha, ihb]
  | pred a ih => simp only [Tm.subst, ih]
  | bump a b iha ihb => simp only [Tm.subst, iha, ihb]
  | good a b iha ihb => simp only [Tm.subst, iha, ihb]
  | ord a b iha ihb => simp only [Tm.subst, iha, ihb]
  | hcut a b iha ihb => simp only [Tm.subst, iha, ihb]
  | hcutAt p a b ihp iha ihb => simp only [Tm.subst, ihp, iha, ihb]
  | ezero => rfl
  | orde a b iha ihb => simp only [Tm.subst, iha, ihb]
  | olte a b iha ihb => simp only [Tm.subst, iha, ihb]
  | tiRecE sc n ihs ihn => simp only [Tm.subst, ihs, ihn]
  | hleaf => rfl
  | hcutH a b iha ihb => simp only [Tm.subst, iha, ihb]
  | hleafQ a ih => simp only [Tm.subst, ih]
  | hordH a ih => simp only [Tm.subst, ih]
  | hcutAtH p a b ihp iha ihb => simp only [Tm.subst, ihp, iha, ihb]
  | qnat a ih => simp only [Tm.subst, ih]
  | dnat a ih => simp only [Tm.subst, ih]
  | dhalf a ih => simp only [Tm.subst, ih]
  | dtoq a ih => simp only [Tm.subst, ih]
  | qadd a b iha ihb => simp only [Tm.subst, iha, ihb]
  | qsub a b iha ihb => simp only [Tm.subst, iha, ihb]
  | qmul a b iha ihb => simp only [Tm.subst, iha, ihb]
  | qdiv a b iha ihb => simp only [Tm.subst, iha, ihb]
  | qlt a b iha ihb => simp only [Tm.subst, iha, ihb]
  | dadd a b iha ihb => simp only [Tm.subst, iha, ihb]
  | dsub a b iha ihb => simp only [Tm.subst, iha, ihb]
  | dmul a b iha ihb => simp only [Tm.subst, iha, ihb]
  | dlt a b iha ihb => simp only [Tm.subst, iha, ihb]
  | hydra a b iha ihb => simp only [Tm.subst, iha, ihb]
  | hord a ih => simp only [Tm.subst, ih]
  | tiRec sc n ihs ihn => simp only [Tm.subst, ihs, ihn]
  | recNat z sc n ihz ihs ihn => simp only [Tm.subst, ihz, ihs, ihn]

theorem Tm.subst1_wk {Γ : List Ty} {σ τ : Ty} (t : Tm Γ τ) (u : Tm Γ σ) :
    (t.wk (σ := σ)).subst1 u = t := by
  rw [Tm.wk, Tm.subst1, Tm.subst_rename]
  rw [show (fun τ' (v : Var Γ τ') ↦ Sub.one u τ' (Ren.wk σ τ' v))
      = (fun τ' (v : Var Γ τ') ↦ Tm.var v) from rfl, Tm.subst_id]

theorem Formula.subst1_eq_var_wk {Γ : List Ty} {τ : Ty} (s u : Tm Γ τ) :
    (Formula.eq (Tm.var .here) (s.wk)).subst1 u = Formula.eq u s := by
  show Formula.eq u ((s.wk).subst1 u) = _
  rw [Tm.subst1_wk]

theorem Formula.subst1_eq_wk_var {Γ : List Ty} {τ : Ty} (s u : Tm Γ τ) :
    (Formula.eq (s.wk) (Tm.var .here)).subst1 u = Formula.eq s u := by
  show Formula.eq ((s.wk).subst1 u) u = _
  rw [Tm.subst1_wk]

/-! ## The normalization simp set -/

@[derivNorm] theorem Ctx.wk_cons {Γ : List Ty} {σ a : Ty} {as : List Ty}
    (φ : Formula Γ a) (Δ : Ctx Γ as) :
    (Ctx.cons φ Δ).wk (σ := σ) = .cons φ.wk Δ.wk := rfl

@[derivNorm] theorem Ctx.wk_nil {Γ : List Ty} {σ : Ty} :
    (Ctx.nil (Γ := Γ)).wk (σ := σ) = .nil := rfl

-- Negation is a definition, so substitution does not push through it unless
-- the normalizer is told to unfold it.  Sperner's conclusion has one, and any
-- derivation that eliminates a negated equation will.
attribute [derivNorm] Formula.neg

/-! ## The tactics -/

/-- **Normalize a `Deriv` goal or hypothesis.** Reduces every context and
formula weakening, and every substitution, to ground normal form, so that
accessors and lemmas match structurally.

The fix for the whnf-versus-metavariable unification failures that make nested
eliminations fail even when the hypothesis is present. -/
macro "deriv_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| try simp only [derivNorm, Formula.wk, Formula.rename,
      Formula.subst1, Formula.subst, Tm.wk, Tm.rename, Tm.subst1, Tm.subst,
      Sub.one, Sub.ext, Ren.wk, Ren.ext] $(loc)?)

/-- **Close a `Deriv` goal by context search**: normalize, then take the
hypothesis at whatever depth it sits. The search is recursive rather than a
fixed ladder, so it is not bounded by a hard-coded context size. -/
syntax "deriv_assumption" : tactic

macro_rules
  | `(tactic| deriv_assumption) =>
      `(tactic| (deriv_norm
                 first
                   | exact Deriv.ax
                   | (refine Deriv.wk ?_; deriv_assumption)))

/-! ## Equational combinators

All four come from the one Leibniz rule. They are what makes an equational
chain writable at all, and every case study after Pascal uses them. -/

/-- Symmetry of the object-level equality. -/
def Deriv.symmE {Γ as} {Δ : Ctx Γ as} {τ : Ty} {s t : Tm Γ τ}
    (h : Deriv Δ (.eq s t)) : Deriv Δ (.eq t s) := by
  have key := Deriv.eqSubst (Δ := Δ) (Formula.eq (Tm.var .here) (s.wk)) h
    (by rw [Formula.subst1_eq_var_wk]; exact Deriv.eqRefl s)
  rw [Formula.subst1_eq_var_wk] at key; exact key

/-- Transitivity. Chains of these are how every conversion argument in the
development is written; ending a chain with `Deriv.eqRefl _` keeps the middle
term from being a metavariable. -/
def Deriv.transE {Γ as} {Δ : Ctx Γ as} {τ : Ty} {s t u : Tm Γ τ}
    (h1 : Deriv Δ (.eq s t)) (h2 : Deriv Δ (.eq t u)) : Deriv Δ (.eq s u) := by
  have key := Deriv.eqSubst (Δ := Δ) (Formula.eq (s.wk) (Tm.var .here)) h2
    (by rw [Formula.subst1_eq_wk_var]; exact h1)
  rw [Formula.subst1_eq_wk_var] at key; exact key

/-- Congruence in the function position — from Leibniz, at every type. -/
def Deriv.congFun {Γ as : List Ty} {Δ : Ctx Γ as} {c d : Ty}
    {f g : Tm Γ (.arrow c d)} (h : Deriv Δ (.eq f g)) (x : Tm Γ c) :
    Deriv Δ (.eq (.app f x) (.app g x)) := by
  have hs : ∀ u : Tm Γ (.arrow c d),
      (Formula.eq (.app (Tm.var .here) (x.wk)) ((Tm.app f x).wk)).subst1 u
        = Formula.eq (.app u x) (.app f x) := by
    intro u
    show Formula.eq (.app u ((x.wk).subst1 u)) (((Tm.app f x).wk).subst1 u) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.app (Tm.var .here) (x.wk)) ((Tm.app f x).wk)) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

/-- Congruence in the argument position. -/
def Deriv.congArg {Γ as : List Ty} {Δ : Ctx Γ as} {c d : Ty}
    (f : Tm Γ (.arrow c d)) {x y : Tm Γ c} (h : Deriv Δ (.eq x y)) :
    Deriv Δ (.eq (.app f x) (.app f y)) := by
  have hs : ∀ u : Tm Γ c,
      (Formula.eq (.app (f.wk) (Tm.var .here)) ((Tm.app f x).wk)).subst1 u
        = Formula.eq (.app f u) (.app f x) := by
    intro u
    show Formula.eq (.app ((f.wk).subst1 u) u) (((Tm.app f x).wk).subst1 u) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.app (f.wk) (Tm.var .here)) ((Tm.app f x).wk)) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

end HAomega
