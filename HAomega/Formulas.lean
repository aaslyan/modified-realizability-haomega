/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Syntax

/-!
# HA^ω, part 2: formulas, indexed by their realizer type

    Formula : List Ty → Ty → Type

`Formula Γ α` is a formula whose terms live in context `Γ` and **whose
realizers have type `α`**.  The realizer type is an *index*, not a function
computed after the fact.

## Why the index, and what it buys

The first version of this module had `Formula Γ` and a separate
`tyOf : Formula Γ → Ty`.  That works, and extraction against it works, but it
makes `tyOf (φ.subst s) = tyOf φ` a *propositional* equality — `Formula.subst`
is stuck on a variable formula, so the two types are never definitionally
equal.  Six casts appeared in `extract`, and soundness stalled completely:
`MR_subst` would have had to relate `cast` along an opaque equality to casts
on subformula components, which needs the equality's shape.

Indexing removes the problem at the source:

* `subst`, `rename`, `wk` all preserve the index **by construction**, so the
  four `tyOf_*` lemmas are not lemmas — they do not need to exist;
* **every cast disappears from `extract`** (all six);
* `MR_subst` becomes a statement with no `cast` in it, and a routine
  induction.

The cost is that `Formula`'s constructors now record how each connective
builds the realizer type, which is really just `tyOf`'s clauses moved into the
declaration — `and` builds a product, `imp` builds a function, and so on.

## Equality at every type

`Formula.eq` is at an arbitrary `τ`.  Its realizer type is still `unit` —
equations carry no information whatever their type — so nothing downstream
changes except that conversion becomes statable.

**This revises an earlier decision, and Pascal is what forced it.**  Equality
was first restricted to type `0`, on the HA^ω convention that higher-type
equality is *defined* extensionally.  That is fine for `MR` and soundness, and
`eqAt`/`interp_eqAt` below still prove it.  But it is wrong for the
**conversion rules**: `recNat`'s step has type `ℕ → τ → τ`, so unfolding
`s n ih` passes through `s n` at a higher type, and a theory that cannot state
an equation there cannot unfold its own definitions.  Working around it needed
one ad-hoc applied-form rule per nesting depth — a family, not a fix.

`eqAt` is kept: it now proves higher-type equality is *definable* as well as
primitive, which is a theorem rather than a necessity.
-/

namespace HAomega

/-! ## Formulas -/

/-- Formulas of HA^ω, indexed by context and by realizer type.

Read the second index off the constructors: `∧` and `∃` pair, `∨` pairs behind
a tag, `→` and `∀` abstract, and equations and `⊥` are contentless. -/
inductive Formula : List Ty → Ty → Type where
  | bot {Γ : List Ty} : Formula Γ .unit
  | eq {Γ : List Ty} {τ : Ty} : Tm Γ τ → Tm Γ τ → Formula Γ .unit
  | and {Γ : List Ty} {a b : Ty} :
      Formula Γ a → Formula Γ b → Formula Γ (.prod a b)
  | or {Γ : List Ty} {a b : Ty} :
      Formula Γ a → Formula Γ b → Formula Γ (.prod .nat (.prod a b))
  | imp {Γ : List Ty} {a b : Ty} :
      Formula Γ a → Formula Γ b → Formula Γ (.arrow a b)
  | all {Γ : List Ty} {a : Ty} (τ : Ty) :
      Formula (τ :: Γ) a → Formula Γ (.arrow τ a)
  | ex {Γ : List Ty} {a : Ty} (τ : Ty) :
      Formula (τ :: Γ) a → Formula Γ (.prod τ a)

/-- Negation. -/
def Formula.neg {Γ : List Ty} {a : Ty} (φ : Formula Γ a) :
    Formula Γ (.arrow a .unit) := φ.imp .bot

/-- Truth, as the trivial equation. -/
def Formula.top {Γ : List Ty} : Formula Γ .unit := .eq .zero .zero

/-! ## Renaming and substitution

Each preserves the realizer index by construction — that is the entire point
of the redesign, and the reason there is nothing to prove here. -/

/-- Apply a renaming to a formula. -/
def Formula.rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    {a : Ty} → Formula Γ a → Formula Δ a
  | _, .bot => .bot
  | _, .eq s t => .eq (s.rename ρ) (t.rename ρ)
  | _, .and x y => .and (x.rename ρ) (y.rename ρ)
  | _, .or x y => .or (x.rename ρ) (y.rename ρ)
  | _, .imp x y => .imp (x.rename ρ) (y.rename ρ)
  | _, .all τ x => .all τ (x.rename ρ.ext)
  | _, .ex τ x => .ex τ (x.rename ρ.ext)

/-- Weaken a formula into a context with one more variable. -/
def Formula.wk {Γ : List Ty} {σ a : Ty} (φ : Formula Γ a) :
    Formula (σ :: Γ) a :=
  φ.rename (Ren.wk σ)

/-- Apply a substitution to a formula. -/
def Formula.subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    {a : Ty} → Formula Γ a → Formula Δ a
  | _, .bot => .bot
  | _, .eq x y => .eq (x.subst s) (y.subst s)
  | _, .and x y => .and (x.subst s) (y.subst s)
  | _, .or x y => .or (x.subst s) (y.subst s)
  | _, .imp x y => .imp (x.subst s) (y.subst s)
  | _, .all τ x => .all τ (x.subst s.ext)
  | _, .ex τ x => .ex τ (x.subst s.ext)

/-- Substitute a term for the outermost variable.  No side condition, and — now
— no change of realizer type. -/
def Formula.subst1 {Γ : List Ty} {c a : Ty} (φ : Formula (c :: Γ) a)
    (u : Tm Γ c) : Formula Γ a :=
  φ.subst (Sub.one u)

/-- `φ`, re-pointed at the **inner** of two `ℕ` binders.  What `tiEps0`'s
premise needs: inside `∀x. (∀y. y ≺ x → φ(y)) → φ(x)`, the occurrence of `φ`
under the inner binder must refer to `y`, not `x`. -/
def Formula.atInner {Γ : List Ty} {a : Ty} (φ : Formula (.nat :: Γ) a) :
    Formula (.nat :: .nat :: Γ) a :=
  φ.rename (Ren.wk .nat).ext

/-- The substitution `x ↦ succ x` on the outermost variable, used by induction. -/
def Sub.succHere {Γ : List Ty} : Sub (.nat :: Γ) (.nat :: Γ)
  | _, .here => .succ (.var .here)
  | _, .there v => .var (.there v)

/-! ## The intended meaning -/

/-- The set-theoretic interpretation.  The realizer index is not used — truth
does not depend on it. -/
def Formula.interp : {Γ : List Ty} → {a : Ty} → Formula Γ a → Env Γ → Prop
  | _, _, .bot, _ => False
  | _, _, .eq s t, e => s.eval e = t.eval e
  | _, _, .and x y, e => x.interp e ∧ y.interp e
  | _, _, .or x y, e => x.interp e ∨ y.interp e
  | _, _, .imp x y, e => x.interp e → y.interp e
  | _, _, .all τ x, e => ∀ v : τ.interp, x.interp (Env.cons v e)
  | _, _, .ex τ x, e => ∃ v : τ.interp, x.interp (Env.cons v e)

/-! ## Equality at every finite type -/

/-- The realizer type of extensional equality at `τ`. -/
def eqIdx : Ty → Ty
  | .unit => .unit
  | .nat => .unit
  | .arrow a b => .arrow a (eqIdx b)
  | .prod a b => .prod (eqIdx a) (eqIdx b)

/-- **Extensional equality at an arbitrary finite type**, from equality at
`nat`.  Recursion is on the type. -/
def eqAt : {Γ : List Ty} → (τ : Ty) → Tm Γ τ → Tm Γ τ → Formula Γ (eqIdx τ)
  | _, .unit, _, _ => .top
  | _, .nat, s, t => .eq s t
  | _, .arrow a b, s, t =>
      .all a (eqAt b (.app s.wk (.var .here)) (.app t.wk (.var .here)))
  | _, .prod a b, s, t =>
      .and (eqAt a (.fst s) (.fst t)) (eqAt b (.snd s) (.snd t))

/-- **The definition is correct.** -/
theorem interp_eqAt : ∀ (τ : Ty) {Γ : List Ty} (s t : Tm Γ τ) (e : Env Γ),
    (eqAt τ s t).interp e ↔ s.eval e = t.eval e := by
  intro τ
  induction τ with
  | unit => intro Γ s t e; exact ⟨fun _ ↦ Subsingleton.elim _ _, fun _ ↦ rfl⟩
  | nat => intro Γ s t e; exact Iff.rfl
  | arrow a b _ ihb =>
      intro Γ s t e
      constructor
      · intro h
        funext x
        have hx := (ihb (.app s.wk (.var .here)) (.app t.wk (.var .here))
          (Env.cons x e)).mp (h x)
        simpa [Tm.eval, Tm.wk, Tm.eval_wk] using hx
      · intro h x
        refine (ihb (.app s.wk (.var .here)) (.app t.wk (.var .here))
          (Env.cons x e)).mpr ?_
        simp only [Tm.eval, Tm.wk, Tm.eval_wk, h]
  | prod a b iha ihb =>
      intro Γ s t e
      constructor
      · intro h
        have h1 := (iha (.fst s) (.fst t) e).mp h.1
        have h2 := (ihb (.snd s) (.snd t) e).mp h.2
        simp only [Tm.eval] at h1 h2
        exact Prod.ext h1 h2
      · intro h
        exact ⟨(iha (.fst s) (.fst t) e).mpr (by simp only [Tm.eval, h]),
               (ihb (.snd s) (.snd t) e).mpr (by simp only [Tm.eval, h])⟩

/-! ## The substitution lemmas -/

/-- Renaming commutes with interpretation. -/
theorem Formula.interp_rename {Γ : List Ty} {a : Ty} (φ : Formula Γ a) :
    ∀ {Δ : List Ty} (ρ : Ren Γ Δ) (e : Env Δ),
      (φ.rename ρ).interp e ↔ φ.interp (fun _ v ↦ e _ (ρ _ v)) := by
  induction φ with
  | bot => intros; exact Iff.rfl
  | eq s t => intro Δ ρ e; simp only [Formula.rename, Formula.interp, Tm.eval_rename]
  | and _ _ iha ihb =>
      intro Δ ρ e; simp only [Formula.rename, Formula.interp]
      exact and_congr (iha ρ e) (ihb ρ e)
  | or _ _ iha ihb =>
      intro Δ ρ e; simp only [Formula.rename, Formula.interp]
      exact or_congr (iha ρ e) (ihb ρ e)
  | imp _ _ iha ihb =>
      intro Δ ρ e; simp only [Formula.rename, Formula.interp]
      exact imp_congr (iha ρ e) (ihb ρ e)
  | all τ _ ih =>
      intro Δ ρ e; simp only [Formula.rename, Formula.interp]
      refine forall_congr' fun x ↦ ?_
      refine (ih ρ.ext (Env.cons x e)).trans (Iff.of_eq ?_)
      congr 1; funext σ v; cases v <;> rfl
  | ex τ _ ih =>
      intro Δ ρ e; simp only [Formula.rename, Formula.interp]
      refine exists_congr fun x ↦ ?_
      refine (ih ρ.ext (Env.cons x e)).trans (Iff.of_eq ?_)
      congr 1; funext σ v; cases v <;> rfl

/-- Weakening and interpreting in an extended environment. -/
theorem Formula.interp_wk {Γ : List Ty} {σ a : Ty} (φ : Formula Γ a)
    (x : σ.interp) (e : Env Γ) :
    (φ.wk (σ := σ)).interp (Env.cons x e) ↔ φ.interp e := by
  have h : (fun (τ' : Ty) (v : Var Γ τ') ↦ Env.cons x e τ' (Ren.wk σ τ' v))
      = e := by funext τ' v; rfl
  rw [Formula.wk, Formula.interp_rename, h]

/-- **Substitution commutes with interpretation.** -/
theorem Formula.interp_subst {Γ : List Ty} {a : Ty} (φ : Formula Γ a) :
    ∀ {Δ : List Ty} (s : Sub Γ Δ) (e : Env Δ),
      (φ.subst s).interp e ↔ φ.interp (fun _ v ↦ (s _ v).eval e) := by
  induction φ with
  | bot => intros; exact Iff.rfl
  | eq x y => intro Δ s e; simp only [Formula.subst, Formula.interp, Tm.eval_subst]
  | and _ _ iha ihb =>
      intro Δ s e; simp only [Formula.subst, Formula.interp]
      exact and_congr (iha s e) (ihb s e)
  | or _ _ iha ihb =>
      intro Δ s e; simp only [Formula.subst, Formula.interp]
      exact or_congr (iha s e) (ihb s e)
  | imp _ _ iha ihb =>
      intro Δ s e; simp only [Formula.subst, Formula.interp]
      exact imp_congr (iha s e) (ihb s e)
  | all τ _ ih =>
      intro Δ s e; simp only [Formula.subst, Formula.interp]
      refine forall_congr' fun x ↦ ?_
      refine (ih s.ext (Env.cons x e)).trans (Iff.of_eq ?_)
      congr 1; funext σ v
      cases v with
      | here => rfl
      | there v => exact Tm.eval_wk (s _ v) x e
  | ex τ _ ih =>
      intro Δ s e; simp only [Formula.subst, Formula.interp]
      refine exists_congr fun x ↦ ?_
      refine (ih s.ext (Env.cons x e)).trans (Iff.of_eq ?_)
      congr 1; funext σ v
      cases v with
      | here => rfl
      | there v => exact Tm.eval_wk (s _ v) x e

/-- **Single substitution commutes with interpretation.** -/
theorem Formula.interp_subst1 {Γ : List Ty} {c a : Ty} (φ : Formula (c :: Γ) a)
    (u : Tm Γ c) (e : Env Γ) :
    (φ.subst1 u).interp e ↔ φ.interp (Env.cons (u.eval e) e) := by
  rw [Formula.subst1, Formula.interp_subst]
  have h : (fun (σ : Ty) (v : Var (c :: Γ) σ) ↦ (Sub.one u σ v).eval e)
      = Env.cons (u.eval e) e := by funext σ v; cases v <;> rfl
  rw [h]

#print axioms Formula.interp
#print axioms interp_eqAt
#print axioms Formula.interp_subst1

end HAomega
