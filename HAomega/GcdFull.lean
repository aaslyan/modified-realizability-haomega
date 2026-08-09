/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GcdStage2

/-!
# gcd stage 2, layers 2–3: cancellation, distributivity, trichotomy

The ∀-form lemmas of layer 1 cannot be *instantiated* at a use site without
running into the `Formula.subst1 ?φ u` inversion (the unifier cannot invert
substitution).  This file settles the pattern once: every lemma also gets a
**term form** — `plusAssocT x y z` instead of `allE`-chains — derived from the
∀-form by one `simp only` normalization with the substitution kit.  Use sites
then never mention `allE` on a lemma again, and everything elaborates
bottom-up at default heartbeats.

New mathematics here: `cancelAddD`/`cancelAddLT` (cancellation on either
side), `addEqZeroD`, `addLCommT` (the AC shuffle, a three-line chain of term
forms), **`distribLD`** — `d·(x+y) = d·x + d·y` — and **`trichotomyD`**:
`∀a∀b. (∃s. a+s=b) ∨ (∃s. b+S s=a)`, the comparison the Euclid recursion
branches on, proved by `ind` with the case-split device and two `eqSubst`
transports.

## The remaining gap to the full theorem, stated precisely

`dvdAddD`/`dvdSubD` and the fueled main induction remain.  The mathematics is
settled (the route is in the stage-1 header); what stops this session is an
*elaboration* pattern: inside nested `exE` chains the hypothesis context
arrives as unreduced `Ctx.wk`/`Formula.wk` applications, and unification
against a ground accessor (`ax1`/`ax2`) fails when the goal still carries
metavariables — whnf-directed unification gives up before reducing the
weakenings.  The demonstrated fix is a `show` restating the entire goal (context
index included) in reduced form after each elimination, which is bulletproof
but costs a hand-written context per elimination step.  A better fix — a small
normalization tactic for `Deriv` goals, or hypothesis access by position
rather than formula — is the right next step before writing `dvdSubD` and the
main induction, and none of it needs new machinery.
-/

namespace HAomega

/-- `mulT` ignores substitution (closed). -/
theorem mulT_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (mulT (Γ := Γ)).subst s = mulT := rfl


/-- `∀x ∀y ∀a. x + a = y + a → x = y` — right cancellation. -/
def cancelAddD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there (.there .here))) (.var .here))
                 (.add (.var (.there .here)) (.var .here)))
            (.eq (.var (.there (.there .here))) (.var (.there .here))))))) := by
  refine Deriv.allI (Deriv.allI ?_)
  refine Deriv.ind ?_ ?_
  · refine Deriv.impI ?_
    refine Deriv.transE (Deriv.symmE (Deriv.convAddZero _)) ?_
    refine Deriv.transE Deriv.ax ?_
    exact Deriv.transE (Deriv.convAddZero _) (Deriv.eqRefl _)
  · refine Deriv.allI (Deriv.impI (Deriv.impI ?_))
    -- ctx: hyp (x + S v = y + S v) :: IH (x+v=y+v → x=y) :: …
    have hS : Deriv (.cons (.eq (.add (.var (.there (.there .here))) (.succ (.var .here)))
        (.add (.var (.there .here)) (.succ (.var .here))))
        (.cons (.imp (.eq (.add (.var (.there (.there .here))) (.var .here))
            (.add (.var (.there .here)) (.var .here)))
          (.eq (.var (.there (.there .here))) (.var (.there .here))))
          (((Δ.wk).wk).wk)))
        (.eq (.succ (.add (.var (.there (.there .here))) (.var .here)))
          (.succ (.add (.var (.there .here)) (.var .here)))) := by
      refine Deriv.transE (Deriv.symmE (Deriv.convAddSucc _ _)) ?_
      refine Deriv.transE Deriv.ax ?_
      exact Deriv.transE (Deriv.convAddSucc _ _) (Deriv.eqRefl _)
    have hinj := Deriv.impE (Deriv.succInj _ _) hS
    exact Deriv.impE (Deriv.wk Deriv.ax) hinj

/-- `∀y ∀z. y + z = 0 → y = 0`. -/
def addEqZeroD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) .zero)
            (.eq (.var (.there .here)) .zero)))) := by
  refine Deriv.allI ?_
  refine Deriv.ind ?_ ?_
  · -- z = 0: y + 0 = 0 → y = 0
    refine Deriv.impI ?_
    refine Deriv.transE (Deriv.symmE (Deriv.convAddZero _)) ?_
    exact Deriv.transE Deriv.ax (Deriv.eqRefl _)
  · -- z = S v: y + S v = 0 is absurd
    refine Deriv.allI (Deriv.impI (Deriv.impI ?_))
    refine Deriv.botE ?_
    have hS : Deriv (.cons (.eq (.add (.var (.there .here)) (.succ (.var .here))) .zero)
        (.cons (.imp (.eq (.add (.var (.there .here)) (.var .here)) .zero)
          (.eq (.var (.there .here)) .zero)) (((Δ.wk).wk)))) 
        (.eq (.succ (.add (.var (.there .here)) (.var .here))) .zero) := by
      refine Deriv.transE (Deriv.symmE (Deriv.convAddSucc _ _)) ?_
      exact Deriv.transE Deriv.ax (Deriv.eqRefl _)
    exact Deriv.impE (Deriv.succNeZero _) hS



/-- `wk_subst_one`, rename-unfolded form (what simp-normalized goals show). -/
theorem subst_one_rename {Γ : List Ty} {σ τ : Ty} (t : Tm Γ τ) (u : Tm Γ σ) :
    Tm.subst (Sub.one u) (Tm.rename (Ren.wk σ) t) = t := Tm.subst1_wk t u

/-- `wk_subst_ext`, rename-unfolded form. -/
theorem subst_ext_rename {Γ Δ : List Ty} {σ τ : Ty} (t : Tm Γ τ) (s : Sub Γ Δ) :
    Tm.subst (Sub.ext (σ := σ) s) (Tm.rename (Ren.wk σ) t)
      = Tm.rename (Ren.wk σ) (Tm.subst s t) := Tm.wk_subst_ext t s

/-- Term form of `plusAssocD`. -/
def plusAssocT {Γ as : List Ty} {Δ : Ctx Γ as} (x y z : Tm Γ .nat) :
    Deriv Δ (.eq (.add (.add x y) z) (.add x (.add y z))) := by
  have h := Deriv.allE z (Deriv.allE y (Deriv.allE x (plusAssocD (Δ := Δ))))
  simp only [Formula.subst1, Formula.subst, Tm.subst, Sub.one,
    Sub.ext, Ren.wk, Tm.rename, 
    subst_one_rename, subst_ext_rename] at h
  exact h

/-- Term form of `plusCommD`. -/
def plusCommT {Γ as : List Ty} {Δ : Ctx Γ as} (x y : Tm Γ .nat) :
    Deriv Δ (.eq (.add x y) (.add y x)) := by
  have h := Deriv.allE y (Deriv.allE x (plusCommD (Δ := Δ)))
  simp only [Formula.subst1, Formula.subst, Tm.subst, Sub.one,
    Sub.ext, 
    subst_one_rename] at h
  exact h


/-- Term form of `zeroPlusD`. -/
def zeroPlusT {Γ as : List Ty} {Δ : Ctx Γ as} (x : Tm Γ .nat) :
    Deriv Δ (.eq (.add .zero x) x) := by
  have h := Deriv.allE x (zeroPlusD (Δ := Δ))
  simp only [Formula.subst1, Formula.subst, Tm.subst, Sub.one,
    
    ] at h
  exact h

/-- Term form of `succPlusD`. -/
def succPlusT {Γ as : List Ty} {Δ : Ctx Γ as} (x y : Tm Γ .nat) :
    Deriv Δ (.eq (.add (.succ x) y) (.succ (.add x y))) := by
  have h := Deriv.allE y (Deriv.allE x (succPlusD (Δ := Δ)))
  simp only [Formula.subst1, Formula.subst, Tm.subst, Sub.one,
    Sub.ext, 
    subst_one_rename] at h
  exact h

/-- Term form of `cancelAddD` (the implication, ready for `impE`). -/
def cancelAddT {Γ as : List Ty} {Δ : Ctx Γ as} (x y a : Tm Γ .nat) :
    Deriv Δ (.imp (.eq (.add x a) (.add y a)) (.eq x y)) := by
  have h := Deriv.allE a (Deriv.allE y (Deriv.allE x (cancelAddD (Δ := Δ))))
  simp only [Formula.subst1, Formula.subst, Tm.subst, Sub.one,
    Sub.ext, Ren.wk, Tm.rename, 
    subst_one_rename, subst_ext_rename] at h
  exact h

/-- Term form of `addEqZeroD`. -/
def addEqZeroT {Γ as : List Ty} {Δ : Ctx Γ as} (y z : Tm Γ .nat) :
    Deriv Δ (.imp (.eq (.add y z) .zero) (.eq y .zero)) := by
  have h := Deriv.allE z (Deriv.allE y (addEqZeroD (Δ := Δ)))
  simp only [Formula.subst1, Formula.subst, Tm.subst, Sub.one,
    Sub.ext, 
    subst_one_rename] at h
  exact h

/-- Term form of `caseNatD`. -/
def caseNatT {Γ as : List Ty} {Δ : Ctx Γ as} (v : Tm Γ .nat) :
    Deriv Δ (.or (.eq v .zero) (.ex .nat (.eq (v.wk) (.succ (.var .here))))) := by
  have h := Deriv.allE v (caseNatD (Δ := Δ))
  simp only [Formula.subst1, Formula.subst, Tm.subst, Sub.one,
    Sub.ext, 
    ] at h
  exact h

/-- `a + (p + q) = p + (a + q)` — now a three-line chain of term forms. -/
def addLCommT {Γ as : List Ty} {Δ : Ctx Γ as} (a p q : Tm Γ .nat) :
    Deriv Δ (.eq (.add a (.add p q)) (.add p (.add a q))) :=
  Deriv.transE (Deriv.symmE (plusAssocT a p q))
    (Deriv.transE (Deriv.congAddL q (plusCommT a p))
      (Deriv.transE (plusAssocT p a q) (Deriv.eqRefl _)))

/-- Left cancellation, from commutativity and `cancelAddT`. -/
def cancelAddLT {Γ as : List Ty} {Δ : Ctx Γ as} (a x y : Tm Γ .nat) :
    Deriv Δ (.imp (.eq (.add a x) (.add a y)) (.eq x y)) := by
  refine Deriv.impI ?_
  refine Deriv.impE (cancelAddT x y a) ?_
  refine Deriv.transE (plusCommT x a) ?_
  refine Deriv.transE Deriv.ax ?_
  exact Deriv.transE (plusCommT a y) (Deriv.eqRefl _)

/-- `∀d ∀x ∀y. d·(x+y) = d·x + d·y`, by `ind` on `y`; the shuffle is
`addLCommT` at the bound variables. -/
def distribLD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.all .nat
      (.eq (.app (.app mulT (.var (.there (.there .here))))
             (.add (.var (.there .here)) (.var .here)))
           (.add (.app (.app mulT (.var (.there (.there .here)))) (.var (.there .here)))
             (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))))) := by
  refine Deriv.allI (Deriv.allI ?_)
  refine Deriv.ind ?_ ?_
  · refine Deriv.transE (Deriv.congArg _ (Deriv.convAddZero _)) ?_
    refine Deriv.transE (Deriv.symmE (Deriv.convAddZero _)) ?_
    exact Deriv.transE (Deriv.symmE (Deriv.congAddR _ (mulZero _))) (Deriv.eqRefl _)
  · refine Deriv.allI (Deriv.impI ?_)
    refine Deriv.transE (Deriv.congArg _ (Deriv.convAddSucc _ _)) ?_
    refine Deriv.transE (mulSuccD _ _) ?_
    refine Deriv.transE (Deriv.congAddR _ Deriv.ax) ?_
    refine Deriv.transE (addLCommT (.var (.there (.there .here)))
      (.app (.app mulT (.var (.there (.there .here)))) (.var (.there .here)))
      (.app (.app mulT (.var (.there (.there .here)))) (.var .here))) ?_
    exact Deriv.transE (Deriv.symmE (Deriv.congAddR _ (mulSuccD _ _))) (Deriv.eqRefl _)

/-- Term form of `distribLD`. -/
def distribLT {Γ as : List Ty} {Δ : Ctx Γ as} (d x y : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app mulT d) (.add x y))
      (.add (.app (.app mulT d) x) (.app (.app mulT d) y))) := by
  have h := Deriv.allE y (Deriv.allE x (Deriv.allE d (distribLD (Δ := Δ))))
  simp only [Formula.subst1, Formula.subst, Tm.subst, Sub.one,
    Sub.ext, Ren.wk, Tm.rename, 
    subst_one_rename, subst_ext_rename, mulT_subst] at h
  exact h


/-- The trichotomy disjunction over context `Γ` (free vars: `a` then `b`
outermost-first, i.e. `a = var (there here)`, `b = var here` — inside each
`∃` they shift by one). -/
abbrev triOr (Γ : List Ty) : Formula (.nat :: .nat :: Γ)
    (.prod .nat (.prod (.prod .nat .unit) (.prod .nat .unit))) :=
  .or (.ex .nat (.eq (.add (.var (.there (.there .here))) (.var .here))
         (.var (.there .here))))
      (.ex .nat (.eq (.add (.var (.there .here)) (.succ (.var .here)))
         (.var (.there (.there .here)))))

/-- **Trichotomy**: `∀a ∀b. (∃s. a + s = b) ∨ (∃s. b + S s = a)`. -/
def trichotomyD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (triOr Γ))) := by
  refine Deriv.ind ?_ ?_
  · exact Deriv.allI (Deriv.orI₁ (Deriv.exI (.var .here) (zeroPlusT _)))
  · refine Deriv.allI (Deriv.impI (Deriv.allI ?_))
    refine Deriv.orE (Deriv.allE (τ := .nat) (.var .here)
      (Deriv.ax (φ := .all .nat (.or
        (.ex .nat (.eq (.add (.var (.there (.there (.there .here)))) (.var .here))
          (.var (.there .here))))
        (.ex .nat (.eq (.add (.var (.there .here)) (.succ (.var .here)))
          (.var (.there (.there (.there .here)))))))))) ?_ ?_
    · -- left IH branch: ∃s. v + s = b
      refine Deriv.exE Deriv.ax ?_
      refine Deriv.orE (caseNatT (.var .here)) ?_ ?_
      · -- witness s = 0 ⟹ v = b ⟹ right, difference 0
        refine Deriv.orI₂ (Deriv.exI .zero ?_)
        refine Deriv.transE (Deriv.convAddSucc _ _) ?_
        refine Deriv.transE (Deriv.congSucc (Deriv.convAddZero _)) ?_
        refine Deriv.transE (Deriv.congSucc (Deriv.symmE (Deriv.transE
          (Deriv.symmE (Deriv.convAddZero _)) (Deriv.transE
            (Deriv.eqSubst
              (.eq (.add (.var (.there (.there (.there .here)))) (.var .here))
                (.var (.there (.there .here))))
              (Deriv.ax (φ := .eq (.var .here) .zero))
              (Deriv.wk Deriv.ax))
            (Deriv.eqRefl _))))) ?_
        exact Deriv.eqRefl _
      · -- witness s = S w ⟹ left for S v, difference w
        refine Deriv.exE Deriv.ax ?_
        refine Deriv.orI₁ (Deriv.exI (.var .here) ?_)
        refine Deriv.transE (succPlusT _ _) ?_
        refine Deriv.transE (Deriv.symmE (Deriv.convAddSucc _ _)) ?_
        refine Deriv.transE
          (Deriv.eqSubst
            (.eq (.add (.var (.there (.there (.there (.there .here))))) (.var .here))
              (.var (.there (.there (.there .here)))))
            (Deriv.ax (φ := .eq (.var (.there .here)) (.succ (.var .here))))
            (Deriv.wk (Deriv.wk Deriv.ax))) ?_
        exact Deriv.eqRefl _
    · -- right IH branch: ∃s. b + S s = v ⟹ right for S v, difference S s
      refine Deriv.exE Deriv.ax ?_
      refine Deriv.orI₂ (Deriv.exI (.succ (.var .here)) ?_)
      refine Deriv.transE (Deriv.convAddSucc _ _) ?_
      exact Deriv.transE (Deriv.congSucc Deriv.ax) (Deriv.eqRefl _)


/-- Term form of `trichotomyD`. -/
def trichotomyT {Γ as : List Ty} {Δ : Ctx Γ as} (a b : Tm Γ .nat) :
    Deriv Δ (.or (.ex .nat (.eq (.add (a.wk) (.var .here)) (b.wk)))
                 (.ex .nat (.eq (.add (b.wk) (.succ (.var .here))) (a.wk)))) := by
  have h := Deriv.allE b (Deriv.allE a (trichotomyD (Δ := Δ)))
  simp only [Formula.subst1, Formula.subst, Tm.subst, Sub.one,
    Sub.ext, Ren.wk, Tm.rename, 
    subst_one_rename, subst_ext_rename] at h
  exact h

/-- Hypothesis at depth 1, everything explicit — the deterministic accessor
that sidesteps metavariable-order failures in nested eliminations. -/
def Deriv.ax1 {Γ as : List Ty} {a b : Ty} {Δ : Ctx Γ as}
    (ψ : Formula Γ b) (φ : Formula Γ a) :
    Deriv (.cons ψ (.cons φ Δ)) φ := Deriv.wk Deriv.ax

/-- Hypothesis at depth 2, everything explicit. -/
def Deriv.ax2 {Γ as : List Ty} {a b c : Ty} {Δ : Ctx Γ as}
    (ψ₂ : Formula Γ c) (ψ₁ : Formula Γ b) (φ : Formula Γ a) :
    Deriv (.cons ψ₂ (.cons ψ₁ (.cons φ Δ))) φ := Deriv.wk (Deriv.wk Deriv.ax)

end HAomega
