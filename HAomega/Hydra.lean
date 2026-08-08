/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Goodstein

/-!
# The Kirby–Paris Hydra theorem in HA^ω

    hydraD : ∀h. ∃t. hydra(h, t) = 0

Goodstein's derivation, mirrored — with a *shorter* descent: one `hordCutLt`
application and two rewrites, where Goodstein needs the `bump`/`pred` chain.
The single import is H4's: one property of one move symbol relative to one
ordinal symbol, discharged in `soundness` by `olt_ordOfHydraN_step`.

Independence from PA is **not** formalized and is not claimed.

With function variables, the strategy-quantified general theorem
(`hercules_wins`) is now *statable* in the object language — the first-order
development's hard boundary.  It is not derived here: formalizing legal plays
as object-level data is its own project, and only the one-battle theorem is
claimed, exactly as in the first-order H5.
-/

namespace HAomega

/-- The `tiEps0` invariant: `∀h ∀t. hord(hydra(h,t)) = x → ∃s. hydra(h,s) = 0`. -/
abbrev hydAux (Γ : List Ty) : Formula (.nat :: Γ)
    (.arrow .nat (.arrow .nat (.arrow .unit (.prod .nat .unit)))) :=
  .all .nat (.all .nat (.imp
    (.eq (.hord (.hydra (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.ex .nat (.eq (.hydra (.var (.there (.there .here))) (.var .here)) .zero))))

/-- The descent branch's context: `hneg :: hx :: IH` over `t::h::x::Γ`. -/
abbrev hydCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .nat :: Γ)
      ((.arrow .unit .unit) :: .unit ::
       (.arrow .nat (.arrow .unit
         (.arrow .nat (.arrow .nat (.arrow .unit (.prod .nat .unit)))))) :: as) :=
  .cons ((Formula.eq (.hydra (.var (.there .here)) (.var .here)) .zero).neg)
    (.cons (.eq (.hord (.hydra (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.cons (.all .nat (.imp
      (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
        (.succ .zero))
      (hydAux (.nat :: .nat :: .nat :: Γ))))
    (((Δ.wk).wk).wk)))

/-- **`∀x. AUX(x)`**, by transfinite induction along `≺`. -/
def hydAuxD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (hydAux Γ)) := by
  refine Deriv.tiEps0 ?_
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_))))
  deriv_norm
  refine Deriv.orE (Deriv.eqDec (.hydra (.var (.there .here)) (.var .here)) .zero) ?_ ?_
  · refine Deriv.exI (.var .here) ?_
    deriv_norm
    deriv_assumption
  · deriv_norm
    have hneg : Deriv (hydCtx Γ Δ)
        ((Formula.eq (.hydra (.var (.there .here)) (.var .here)) .zero).neg) :=
      Deriv.ax
    have hx1 : Deriv (hydCtx Γ Δ)
        (.eq (.hord (.hydra (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here)))) :=
      Deriv.wk Deriv.ax
    have hIHacc : Deriv (hydCtx Γ Δ)
        (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (hydAux (.nat :: .nat :: .nat :: Γ)))) :=
      Deriv.wk (Deriv.wk Deriv.ax)
    -- descent: one move strictly lowers the ordinal
    have h2 := Deriv.impE
      (Deriv.hordCutLt (.succ (.var .here))
        (.hydra (.var (.there .here)) (.var .here))) hneg
    -- rewrite hcut(t+1, hydra(h,t)) to hydra(h, t+1)
    have h3 := Deriv.eqSubst
      (φ := .eq (.prec (.hord (.var .here))
        (.hord (.hydra (.var (.there (.there .here))) (.var (.there .here)))))
        (.succ .zero))
      (Deriv.symmE (Deriv.convHydraSucc (.var (.there .here)) (.var .here))) h2
    -- rewrite hord(hydra(h,t)) to x
    have h4 := Deriv.eqSubst
      (φ := .eq (.prec (.hord (.hydra (.var (.there (.there .here)))
          (.succ (.var (.there .here))))) (.var .here))
        (.succ .zero))
      hx1 h3
    have hIH1 := Deriv.allE (τ := .nat)
      (.hord (.hydra (.var (.there .here)) (.succ (.var .here)))) hIHacc
    deriv_norm at hIH1
    have hIH2 := Deriv.impE hIH1 h4
    have hIH3 := Deriv.allE (τ := .nat) (.var (.there .here)) hIH2
    deriv_norm at hIH3
    have hIH4 := Deriv.allE (τ := .nat) (.succ (.var .here)) hIH3
    deriv_norm at hIH4
    exact Deriv.impE hIH4 (Deriv.eqRefl _)

/-- **The Kirby–Paris theorem**: every hydra dies. -/
def hydraD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.ex .nat
      (.eq (.hydra (.var (.there .here)) (.var .here)) .zero))) := by
  refine Deriv.allI ?_
  have h0 := Deriv.allE (τ := .nat) (.hord (.var .here))
    (hydAuxD (Γ := .nat :: Γ) (Δ := Ctx.wk Δ))
  deriv_norm at h0
  have h1 := Deriv.allE (τ := .nat) (.var .here) h0
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .nat) .zero h1
  deriv_norm at h2
  refine Deriv.impE h2 ?_
  refine Deriv.eqSubst
    (φ := .eq (.hord (.var .here)) (.hord (.var (.there .here))))
    (Deriv.symmE (Deriv.convHydraZero (.var .here))) ?_
  deriv_norm
  exact Deriv.eqRefl _

/-- **The extracted battle-length program.** -/
def hydraX (c : Nat) : Nat :=
  (((extractClosed (hydraD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) c).1

-- The published Kirby–Paris battle lengths at the small codes, and the
-- certificate that the extracted witness really ends each battle.  The
-- first-order extract cannot evaluate past code 1; this one runs.
#guard [hydraX 0, hydraX 1, hydraX 2] == [0, 1, 3]
#guard (List.range 3).all fun c ↦ Realizability.hydraSeqN c (hydraX c) == 0

#print axioms hydAuxD
#print axioms hydraD
#print axioms hydraX

end HAomega
