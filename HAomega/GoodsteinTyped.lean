/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Goodstein

/-!
# Goodstein again, over the typed ordinal layer

    goodsteinOD : ∀m. ∃t. good(m, t) = 0

**The same statement as `Goodstein.lean`'s `goodsteinD`, by a different
proof**: the induction is `tiEps0O` — transfinite induction on the *structural*
notations of `OrdCnf.lean` — and the invariant measures the state by `ordᵒ`,
which lands in the base type `.ord`, not in coded `ℕ`.  Nothing is coded
anywhere in this derivation or in the program it extracts to:

    ord(k, n) : ℕ      →      ordᵒ(k, n) : Eps0
    x ≺ y     : ℕ      →      x ≺ᵒ y     (structural comparison)
    tiRec on codes     →      tiRecᵒ on notations

The derivation is `Goodstein.lean`'s line for line with those three
replacements, which is the point: the machinery is indifferent to the
representation, so moving the ordinals into their own type costs the *proof*
nothing.  Nor does it import anything new — `ordEBump`/`ordEPredLt` are
discharged in `soundness` by `OrdCnf.lean`'s `ordE_bumpN`/`oltE_ordE_of_lt`,
which are themselves the first-order theorems read through `toCode`.

`#guard`s below check the two extracts agree: same stopping times, at every
input the build can evaluate.  Two proofs of one theorem, two programs, same
answers — the Sperner fingerprint experiment run with the *representation* as
the variable instead of the proof.
-/

namespace HAomega

/-- The `tiEps0O` invariant — `goodAux` with the ordinal slot at type `.ord`. -/
abbrev goodAuxO (Γ : List Ty) : Formula (.ord :: Γ)
    (.arrow .nat (.arrow .nat (.arrow .unit (.prod .nat .unit)))) :=
  .all .nat (.all .nat (.imp
    (.eq (.orde (.succ (.succ (.var .here)))
      (.good (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.ex .nat (.eq (.good (.var (.there (.there .here))) (.var .here)) .zero))))

/-- The descent branch's context: `hneg :: hx :: IH` over `t::m::x::Γ`, with
`x` and the induction hypothesis's bound `y` at type `.ord`. -/
abbrev goodCtxO (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .ord :: Γ)
      ((.arrow .unit .unit) :: .unit ::
       (.arrow .ord (.arrow .unit
         (.arrow .nat (.arrow .nat (.arrow .unit (.prod .nat .unit)))))) :: as) :=
  .cons ((Formula.eq (.good (.var (.there .here)) (.var .here)) .zero).neg)
    (.cons (.eq (.orde (.succ (.succ (.var .here)))
      (.good (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.cons (.all .ord (.imp
      (.eq (.olte (.var .here) (.var (.there (.there (.there .here)))))
        (.succ .zero))
      (goodAuxO (.nat :: .nat :: .ord :: Γ))))
    (((Δ.wk).wk).wk)))

/-- **`∀x^ord. AUX(x)`**, by transfinite induction along the structural `≺`. -/
def goodAuxOD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .ord (goodAuxO Γ)) := by
  refine Deriv.tiEps0O ?_
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_))))
  deriv_norm
  refine Deriv.orE (Deriv.eqDec (.good (.var (.there .here)) (.var .here)) .zero) ?_ ?_
  · -- hit zero: the current step is the witness
    refine Deriv.exI (.var .here) ?_
    deriv_norm
    deriv_assumption
  · -- not zero: descend, with the ordinal a structural notation throughout
    have hneg : Deriv (goodCtxO Γ Δ)
      ((Formula.eq (.good (.var (.there .here)) (.var .here)) .zero).neg) := Deriv.ax
    have hx1 : Deriv (goodCtxO Γ Δ) (.eq (.orde (.succ (.succ (.var .here)))
      (.good (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here)))) := Deriv.wk Deriv.ax
    have hIHacc : Deriv (goodCtxO Γ Δ) (.all .ord (.imp
      (.eq (.olte (.var .here) (.var (.there (.there (.there .here)))))
        (.succ .zero))
      (goodAuxO (.nat :: .nat :: .ord :: Γ)))) := Deriv.wk (Deriv.wk Deriv.ax)
    -- h1 : bump(t+2, g) ≠ 0
    have h1 := Deriv.impE
      (Deriv.bumpNeZero (.var .here)
        (.good (.var (.there .here)) (.var .here))) hneg
    -- h2 : ordᵒ(t+3, pred(bump(t+2,g))) ≺ᵒ ordᵒ(t+3, bump(t+2,g))
    have h2 := Deriv.impE
      (Deriv.ordEPredLt (.succ (.var .here))
        (.bump (.succ (.succ (.var .here)))
          (.good (.var (.there .here)) (.var .here)))) h1
    -- h3 : rewrite pred(bump(t+2,g)) to good(m, t+1)
    have h3 := Deriv.eqSubst
      (φ := .eq (.olte (.orde (.succ (.succ (.succ (.var (.there .here))))) (.var .here))
        (.orde (.succ (.succ (.succ (.var (.there .here)))))
          (.bump (.succ (.succ (.var (.there .here))))
            (.good (.var (.there (.there .here))) (.var (.there .here))))))
        (.succ .zero))
      (Deriv.symmE (Deriv.convGoodSucc (.var (.there .here)) (.var .here))) h2
    -- h4 : rewrite ordᵒ(t+3, bump(t+2,g)) to ordᵒ(t+2, g) — an `.ord`-typed rewrite
    have h4 := Deriv.eqSubst
      (φ := .eq (.olte (.orde (.succ (.succ (.succ (.var (.there .here)))))
          (.good (.var (.there (.there .here))) (.succ (.var (.there .here)))))
        (.var .here)) (.succ .zero))
      (Deriv.ordEBump (.var .here)
        (.good (.var (.there .here)) (.var .here))) h3
    -- h5 : rewrite ordᵒ(t+2, g) to x — the AUX hypothesis
    have h5 := Deriv.eqSubst
      (φ := .eq (.olte (.orde (.succ (.succ (.succ (.var (.there .here)))))
          (.good (.var (.there (.there .here))) (.succ (.var (.there .here)))))
        (.var .here)) (.succ .zero))
      hx1 h4
    -- instantiate the induction hypothesis at the descended **notation**
    have hIH1 := Deriv.allE (τ := .ord)
      (.orde (.succ (.succ (.succ (.var .here))))
        (.good (.var (.there .here)) (.succ (.var .here)))) hIHacc
    deriv_norm at hIH1
    have hIH2 := Deriv.impE hIH1 h5
    have hIH3 := Deriv.allE (τ := .nat) (.var (.there .here)) hIH2
    deriv_norm at hIH3
    have hIH4 := Deriv.allE (τ := .nat) (.succ (.var .here)) hIH3
    deriv_norm at hIH4
    exact Deriv.impE hIH4 (Deriv.eqRefl _)

/-- **Goodstein's theorem, over the typed ordinals.**  The conclusion is
`goodsteinD`'s, verbatim; only the proof's measure changed. -/
def goodsteinOD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.ex .nat
      (.eq (.good (.var (.there .here)) (.var .here)) .zero))) := by
  refine Deriv.allI ?_
  have h0 := Deriv.allE (τ := .ord)
    (.orde (.succ (.succ .zero)) (.var .here))
    (goodAuxOD (Γ := .nat :: Γ) (Δ := Ctx.wk Δ))
  deriv_norm at h0
  have h1 := Deriv.allE (τ := .nat) (.var .here) h0
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .nat) .zero h1
  deriv_norm at h2
  refine Deriv.impE h2 ?_
  refine Deriv.eqSubst
    (φ := .eq (.orde (.succ (.succ .zero)) (.var .here))
      (.orde (.succ (.succ .zero)) (.var (.there .here))))
    (Deriv.symmE (Deriv.convGoodZero (.var .here))) ?_
  deriv_norm
  exact Deriv.eqRefl _

/-- **The extracted stopping-time program, over typed ordinals.** -/
def goodsteinOX (m : Nat) : Nat :=
  (((extractClosed (goodsteinOD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) m).1

-- The published stopping times, from the structural recursion.
#guard [goodsteinOX 0, goodsteinOX 1, goodsteinOX 2, goodsteinOX 3] == [0, 1, 3, 5]
#guard (List.range 4).all fun m ↦ Realizability.goodN m (goodsteinOX m) == 0
-- **The two representations agree**: coded ordinals and structural notations
-- give the same extracted witness at every input the build can evaluate.
#guard (List.range 4).all fun m ↦ goodsteinOX m == goodsteinX m

#print axioms goodAuxOD
#print axioms goodsteinOD
#print axioms goodsteinOX

end HAomega
