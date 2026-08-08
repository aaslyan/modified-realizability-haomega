/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Formulas

/-!
# HA^ω, part 3: modified realizability and the rules

## `MR`, with no ambient level and no casts

    MR : Formula Γ a → Env Γ → a.interp → Prop

Two things are absent, and both were substantial machinery in the first-order
development.  There is no **ambient level**: `Core/Transport.lean` there is 330
lines of `liftR`/`dropR`/`famOf` whose only job is moving realizers between
levels, and there are no levels here.  And there is no **cast**: because
`Formula` is indexed by its realizer type, `φ.subst s` has the same index as
`φ` by construction, so `MR_subst` below is a statement about the *same* `x` on
both sides.

That second point is what unblocks soundness.  In the unindexed version the
corresponding lemma had to relate `cast` along an opaque proof of
`tyOf (φ.subst s) = tyOf φ` to casts on subformula components, and there was no
way to reach the equality's shape.  Here the induction is routine — the same
shape as `Formula.interp_subst`.

## Hypothesis contexts

`Ctx Γ as` is a list of formulas whose realizer types are `as`.  Carrying that
list as an index means the extracted term's context is literally `as ++ Γ`,
with no `map tyOf` and no lemma relating the two.

## The rules

**36 rules**, against the first-order development's 76, and **none carries a
side condition** — de Bruijn binders make `SubstOK` and `FreshIn` vacuous.  The
saving is the equational kit: one Leibniz rule (`eqSubst`) gives every
congruence, and the function symbols' defining equations are gone because the
functions are System T terms rather than axiomatized constants.  What remains
are System T's own computation rules, which are exactly HA^ω's equational
theory.

`tiEps0` is here: the elementary fragment plus transfinite induction to `ε₀`.
-/

namespace HAomega

/-! ## Hypothesis contexts -/

/-- A list of hypotheses, indexed by the list of their realizer types. -/
inductive Ctx (Γ : List Ty) : List Ty → Type where
  | nil : Ctx Γ []
  | cons {a : Ty} {as : List Ty} : Formula Γ a → Ctx Γ as → Ctx Γ (a :: as)

/-- Weaken every hypothesis into an extended context.  The realizer types are
unchanged by construction, which is why `allI` needs no lemma. -/
def Ctx.wk {Γ : List Ty} {σ : Ty} : {as : List Ty} → Ctx Γ as → Ctx (σ :: Γ) as
  | _, .nil => .nil
  | _, .cons φ Δ => .cons φ.wk Δ.wk

/-! ## Modified realizability -/

/-- **`MR φ e x`** — `x` realizes `φ` in environment `e`.

The `∨` clause is the tag convention: the realizer carries a number and both
components, and the number says which component is meaningful. -/
def MR : {Γ : List Ty} → {a : Ty} → Formula Γ a → Env Γ → a.interp → Prop
  | _, _, .bot, _, _ => False
  | _, _, .eq s t, e, _ => s.eval e = t.eval e
  | _, _, .and x y, e, p => MR x e p.1 ∧ MR y e p.2
  | _, _, .or x y, e, p => (p.1 = 0 → MR x e p.2.1) ∧ (p.1 ≠ 0 → MR y e p.2.2)
  | _, _, .imp x y, e, f => ∀ z, MR x e z → MR y e (f z)
  | _, _, .all _ x, e, f => ∀ v, MR x (Env.cons v e) (f v)
  | _, _, .ex _ x, e, p => MR x (Env.cons p.1 e) p.2

/-- **Realizability depends on the environment only pointwise.** -/
theorem MR_congrEnv : {Γ : List Ty} → {a : Ty} → (φ : Formula Γ a) →
    (e e' : Env Γ) → (∀ τ v, e τ v = e' τ v) → (x : a.interp) →
    MR φ e x → MR φ e' x := by
  intro Γ a φ
  induction φ with
  | bot => intro e e' _ x hx; exact hx
  | eq s t =>
      intro e e' h x hx
      have he : e = e' := by funext τ v; exact h τ v
      simpa [he] using hx
  | and _ _ iha ihb =>
      intro e e' h x hx; exact ⟨iha e e' h x.1 hx.1, ihb e e' h x.2 hx.2⟩
  | or _ _ iha ihb =>
      intro e e' h x hx
      exact ⟨fun k ↦ iha e e' h _ (hx.1 k), fun k ↦ ihb e e' h _ (hx.2 k)⟩
  | imp _ _ iha ihb =>
      intro e e' h x hx z hz
      exact ihb e e' h _ (hx z (iha e' e (fun τ v ↦ (h τ v).symm) z hz))
  | all τ _ ih =>
      intro e e' h x hx v
      exact ih _ _ (by intro σ w; cases w <;> simp [Env.cons, h]) _ (hx v)
  | ex τ _ ih =>
      intro e e' h x hx
      exact ih _ _ (by intro σ w; cases w <;> simp [Env.cons, h]) _ hx

/-- Renaming commutes with realizability. -/
theorem MR_rename {Γ : List Ty} {a : Ty} (φ : Formula Γ a) :
    ∀ {Δ : List Ty} (ρ : Ren Γ Δ) (e : Env Δ) (x : a.interp),
      MR (φ.rename ρ) e x ↔ MR φ (fun _ v ↦ e _ (ρ _ v)) x := by
  induction φ with
  | bot => intros; exact Iff.rfl
  | eq s t => intro Δ ρ e x; simp only [Formula.rename, MR, Tm.eval_rename]
  | and _ _ iha ihb =>
      intro Δ ρ e x; simp only [Formula.rename, MR]
      exact and_congr (iha ρ e x.1) (ihb ρ e x.2)
  | or _ _ iha ihb =>
      intro Δ ρ e x; simp only [Formula.rename, MR]
      exact and_congr (imp_congr Iff.rfl (iha ρ e x.2.1))
        (imp_congr Iff.rfl (ihb ρ e x.2.2))
  | imp _ _ iha ihb =>
      intro Δ ρ e x; simp only [Formula.rename, MR]
      exact forall_congr' fun z ↦ imp_congr (iha ρ e z) (ihb ρ e (x z))
  | all τ _ ih =>
      intro Δ ρ e x; simp only [Formula.rename, MR]
      refine forall_congr' fun v ↦ ?_
      refine (ih ρ.ext (Env.cons v e) (x v)).trans (Iff.of_eq ?_)
      congr 1; funext σ w; cases w <;> rfl
  | ex τ _ ih =>
      intro Δ ρ e x; simp only [Formula.rename, MR]
      refine (ih ρ.ext (Env.cons x.1 e) x.2).trans (Iff.of_eq ?_)
      congr 1; funext σ w; cases w <;> rfl

/-- Weakening a formula and realizing in an extended environment. -/
theorem MR_wk {Γ : List Ty} {σ a : Ty} (φ : Formula Γ a) (v : σ.interp)
    (e : Env Γ) (x : a.interp) :
    MR (φ.wk (σ := σ)) (Env.cons v e) x ↔ MR φ e x := by
  have h : (fun (τ' : Ty) (w : Var Γ τ') ↦ Env.cons v e τ' (Ren.wk σ τ' w))
      = e := by funext τ' w; rfl
  rw [Formula.wk, MR_rename, h]

/-- **Substitution commutes with realizability** — the lemma the whole redesign
exists to make statable without a cast. -/
theorem MR_subst {Γ : List Ty} {a : Ty} (φ : Formula Γ a) :
    ∀ {Δ : List Ty} (s : Sub Γ Δ) (e : Env Δ) (x : a.interp),
      MR (φ.subst s) e x ↔ MR φ (fun _ v ↦ (s _ v).eval e) x := by
  induction φ with
  | bot => intros; exact Iff.rfl
  | eq x y => intro Δ s e z; simp only [Formula.subst, MR, Tm.eval_subst]
  | and _ _ iha ihb =>
      intro Δ s e x; simp only [Formula.subst, MR]
      exact and_congr (iha s e x.1) (ihb s e x.2)
  | or _ _ iha ihb =>
      intro Δ s e x; simp only [Formula.subst, MR]
      exact and_congr (imp_congr Iff.rfl (iha s e x.2.1))
        (imp_congr Iff.rfl (ihb s e x.2.2))
  | imp _ _ iha ihb =>
      intro Δ s e x; simp only [Formula.subst, MR]
      exact forall_congr' fun z ↦ imp_congr (iha s e z) (ihb s e (x z))
  | all τ _ ih =>
      intro Δ s e x; simp only [Formula.subst, MR]
      refine forall_congr' fun v ↦ ?_
      refine (ih s.ext (Env.cons v e) (x v)).trans (Iff.of_eq ?_)
      congr 1; funext σ w
      cases w with
      | here => rfl
      | there w => exact Tm.eval_wk (s _ w) v e
  | ex τ _ ih =>
      intro Δ s e x; simp only [Formula.subst, MR]
      refine (ih s.ext (Env.cons x.1 e) x.2).trans (Iff.of_eq ?_)
      congr 1; funext σ w
      cases w with
      | here => rfl
      | there w => exact Tm.eval_wk (s _ w) x.1 e

/-- **Single substitution commutes with realizability.**  The shape `allE`,
`exI`, `ind` and `eqSubst` all need. -/
theorem MR_subst1 {Γ : List Ty} {c a : Ty} (φ : Formula (c :: Γ) a)
    (u : Tm Γ c) (e : Env Γ) (x : a.interp) :
    MR (φ.subst1 u) e x ↔ MR φ (Env.cons (u.eval e) e) x := by
  rw [Formula.subst1, MR_subst]
  have h : (fun (σ : Ty) (v : Var (c :: Γ) σ) ↦ (Sub.one u σ v).eval e)
      = Env.cons (u.eval e) e := by funext σ v; cases v <;> rfl
  rw [h]

/-! ## Canonical inhabitants -/

/-- A canonical closed term at every finite type, for `∨`-introduction's unused
branch and for `⊥`-elimination. -/
def Tm.dflt : {Γ : List Ty} → (τ : Ty) → Tm Γ τ
  | _, .unit => .star
  | _, .nat => .zero
  | _, .arrow _ b => .lam (Tm.dflt b)
  | _, .prod a b => .pair (Tm.dflt a) (Tm.dflt b)

/-! ## The rules -/

/-- **Natural deduction for HA^ω.**  28 rules, no side conditions. -/
inductive Deriv : {Γ : List Ty} → {as : List Ty} → Ctx Γ as →
    {a : Ty} → Formula Γ a → Type where
  | ax {Γ as a} {φ : Formula Γ a} {Δ : Ctx Γ as} : Deriv (.cons φ Δ) φ
  | wk {Γ as a b} {φ : Formula Γ a} {ψ : Formula Γ b} {Δ : Ctx Γ as} :
      Deriv Δ φ → Deriv (.cons ψ Δ) φ
  | andI {Γ as a b} {x : Formula Γ a} {y : Formula Γ b} {Δ : Ctx Γ as} :
      Deriv Δ x → Deriv Δ y → Deriv Δ (.and x y)
  | andE₁ {Γ as a b} {x : Formula Γ a} {y : Formula Γ b} {Δ : Ctx Γ as} :
      Deriv Δ (.and x y) → Deriv Δ x
  | andE₂ {Γ as a b} {x : Formula Γ a} {y : Formula Γ b} {Δ : Ctx Γ as} :
      Deriv Δ (.and x y) → Deriv Δ y
  | orI₁ {Γ as a b} {x : Formula Γ a} {y : Formula Γ b} {Δ : Ctx Γ as} :
      Deriv Δ x → Deriv Δ (.or x y)
  | orI₂ {Γ as a b} {x : Formula Γ a} {y : Formula Γ b} {Δ : Ctx Γ as} :
      Deriv Δ y → Deriv Δ (.or x y)
  | orE {Γ as a b c} {x : Formula Γ a} {y : Formula Γ b} {z : Formula Γ c}
      {Δ : Ctx Γ as} :
      Deriv Δ (.or x y) → Deriv (.cons x Δ) z → Deriv (.cons y Δ) z → Deriv Δ z
  | impI {Γ as a b} {x : Formula Γ a} {y : Formula Γ b} {Δ : Ctx Γ as} :
      Deriv (.cons x Δ) y → Deriv Δ (.imp x y)
  | impE {Γ as a b} {x : Formula Γ a} {y : Formula Γ b} {Δ : Ctx Γ as} :
      Deriv Δ (.imp x y) → Deriv Δ x → Deriv Δ y
  | botE {Γ as a} {φ : Formula Γ a} {Δ : Ctx Γ as} :
      Deriv Δ (Formula.bot (Γ := Γ)) → Deriv Δ φ
  | allI {Γ as a} {τ : Ty} {φ : Formula (τ :: Γ) a} {Δ : Ctx Γ as} :
      Deriv Δ.wk φ → Deriv Δ (.all τ φ)
  | allE {Γ as a} {τ : Ty} {φ : Formula (τ :: Γ) a} {Δ : Ctx Γ as}
      (u : Tm Γ τ) : Deriv Δ (.all τ φ) → Deriv Δ (φ.subst1 u)
  | exI {Γ as a} {τ : Ty} {φ : Formula (τ :: Γ) a} {Δ : Ctx Γ as}
      (u : Tm Γ τ) : Deriv Δ (φ.subst1 u) → Deriv Δ (.ex τ φ)
  | exE {Γ as a b} {τ : Ty} {φ : Formula (τ :: Γ) a} {ψ : Formula Γ b}
      {Δ : Ctx Γ as} :
      Deriv Δ (.ex τ φ) → Deriv (.cons φ Δ.wk) ψ.wk → Deriv Δ ψ
  | ind {Γ as a} {φ : Formula (.nat :: Γ) a} {Δ : Ctx Γ as} :
      Deriv Δ (φ.subst1 .zero) →
      Deriv Δ (.all .nat (.imp φ (φ.subst Sub.succHere))) →
      Deriv Δ (.all .nat φ)
  -- **Transfinite induction along `≺`** — the one rule that is not a
  -- consequence of the fragment's own resources.  Its order premise
  -- `prec y x = 1` is an *equation*, so its realizer is contentless: realizing
  -- it **is** the descent fact, and that is why `tiRec`'s step takes a `unit`
  -- argument it cannot inspect.
  | tiEps0 {Γ as a} {φ : Formula (.nat :: Γ) a} {Δ : Ctx Γ as} :
      Deriv Δ (.all .nat (.imp
        (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there .here))) (.succ .zero))
          φ.atInner))
        φ)) →
      Deriv Δ (.all .nat φ)
  -- The Goodstein layer: conversions for `pred`/`good`, and the three
  -- single-symbol imports of the first-order D5 design (`ordBump`,
  -- `ordPredLt`, `bumpNeZero`), each discharged in soundness by exactly one
  -- `OrdinalAssignment` theorem.  No congruence rules: Leibniz covers them.
  | convPredZero {Γ as} {Δ : Ctx Γ as} : Deriv Δ (.eq (.pred .zero) .zero)
  | convPredSucc {Γ as} {Δ : Ctx Γ as} (t : Tm Γ .nat) :
      Deriv Δ (.eq (.pred (.succ t)) t)
  | convGoodZero {Γ as} {Δ : Ctx Γ as} (s : Tm Γ .nat) :
      Deriv Δ (.eq (.good s .zero) s)
  | convGoodSucc {Γ as} {Δ : Ctx Γ as} (s t : Tm Γ .nat) :
      Deriv Δ (.eq (.good s (.succ t))
        (.pred (.bump (.succ (.succ t)) (.good s t))))
  | ordBump {Γ as} {Δ : Ctx Γ as} (b n : Tm Γ .nat) :
      Deriv Δ (.eq (.ord (.succ (.succ (.succ b))) (.bump (.succ (.succ b)) n))
        (.ord (.succ (.succ b)) n))
  | ordPredLt {Γ as} {Δ : Ctx Γ as} (b n : Tm Γ .nat) :
      Deriv Δ (.imp ((Formula.eq n .zero).neg)
        (.eq (.prec (.ord (.succ (.succ b)) (.pred n))
          (.ord (.succ (.succ b)) n)) (.succ .zero)))
  | bumpNeZero {Γ as} {Δ : Ctx Γ as} (b n : Tm Γ .nat) :
      Deriv Δ (.imp ((Formula.eq n .zero).neg)
        ((Formula.eq (.bump (.succ (.succ b)) n) .zero).neg))
  | eqRefl {Γ as} {Δ : Ctx Γ as} {τ : Ty} (t : Tm Γ τ) : Deriv Δ (.eq t t)
  -- **Leibniz, at every type.**  One rule; every congruence follows.
  | eqSubst {Γ as a c} {Δ : Ctx Γ as} {s t : Tm Γ c}
      (φ : Formula (c :: Γ) a) :
      Deriv Δ (.eq s t) → Deriv Δ (φ.subst1 s) → Deriv Δ (φ.subst1 t)
  -- **Conversion, at every type.**  These are System T's computation rules,
  -- and stating them at an arbitrary result type is what lets the theory
  -- unfold its own definitions: `recNat`'s step passes through `s n` at a
  -- function type, which equality-at-type-0 could not talk about.
  | convBeta {Γ as} {Δ : Ctx Γ as} {c d : Ty} (b : Tm (c :: Γ) d) (u : Tm Γ c) :
      Deriv Δ (.eq (.app (.lam b) u) (b.subst1 u))
  | convRecZero {Γ as} {Δ : Ctx Γ as} {τ : Ty} (z : Tm Γ τ)
      (s : Tm Γ (.arrow .nat (.arrow τ τ))) :
      Deriv Δ (.eq (.recNat z s .zero) z)
  | convRecSucc {Γ as} {Δ : Ctx Γ as} {τ : Ty} (z : Tm Γ τ)
      (s : Tm Γ (.arrow .nat (.arrow τ τ))) (n : Tm Γ .nat) :
      Deriv Δ (.eq (.recNat z s (.succ n)) (.app (.app s n) (.recNat z s n)))
  | convAddZero {Γ as} {Δ : Ctx Γ as} (x : Tm Γ .nat) :
      Deriv Δ (.eq (.add x .zero) x)
  | convAddSucc {Γ as} {Δ : Ctx Γ as} (x y : Tm Γ .nat) :
      Deriv Δ (.eq (.add x (.succ y)) (.succ (.add x y)))
  | convFst {Γ as} {Δ : Ctx Γ as} {c d : Ty} (x : Tm Γ c) (y : Tm Γ d) :
      Deriv Δ (.eq (.fst (.pair x y)) x)
  | convSnd {Γ as} {Δ : Ctx Γ as} {c d : Ty} (x : Tm Γ c) (y : Tm Γ d) :
      Deriv Δ (.eq (.snd (.pair x y)) y)
  | succNeZero {Γ as} {Δ : Ctx Γ as} (t : Tm Γ .nat) :
      Deriv Δ (Formula.eq (.succ t) .zero).neg
  | succInj {Γ as} {Δ : Ctx Γ as} (s t : Tm Γ .nat) :
      Deriv Δ ((Formula.eq (.succ s) (.succ t)).imp (.eq s t))
  | eqDec {Γ as} {Δ : Ctx Γ as} (s t : Tm Γ .nat) :
      Deriv Δ ((Formula.eq s t).or (Formula.eq s t).neg)

end HAomega
