/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GcdDvd

/-!
# Goodstein's theorem in HA^ω

    goodsteinD : ∀m. ∃t. good(m, t) = 0

by `tiEps0` — transfinite induction to `ε₀` — on the invariant

    AUX(x) := ∀m ∀t. ord(t+2, good(m,t)) = x → ∃s. good(m,s) = 0.

The derivation is the first-order `GoodsteinTheorem.lean` line for line,
**minus the naming dodge**: there, instantiating the induction hypothesis at
`ord(t+3, good(m, t+1))` — a term mentioning bound variables — was blocked by
naive substitution, and the derivation had to name the ordinal with a fresh
`∀z` first (`namedIHDeriv`).  Here substitution is capture-free, and the
instantiation is a single `allE` at exactly that term.

The three imports are D5's: `ordBump`, `ordPredLt`, `bumpNeZero` — one
property of one symbol each, none mentioning the Goodstein sequence, each
discharged in `soundness` by its `OrdinalAssignment` theorem.  The descent is
*derived* from them below, as in the first-order Phase D5.
-/

namespace HAomega

/-- The `tiEps0` invariant.  Note it mentions only its own binders and the
ordinal slot `x`, so `Formula.atInner` is textually the identity on it. -/
abbrev goodAux (Γ : List Ty) : Formula (.nat :: Γ)
    (.arrow .nat (.arrow .nat (.arrow .unit (.prod .nat .unit)))) :=
  .all .nat (.all .nat (.imp
    (.eq (.ord (.succ (.succ (.var .here)))
      (.good (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.ex .nat (.eq (.good (.var (.there (.there .here))) (.var .here)) .zero))))

/-- The descent branch's context: `hneg :: hx :: IH` over `t::m::x::Γ`. -/
abbrev goodCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .nat :: Γ)
      ((.arrow .unit .unit) :: .unit ::
       (.arrow .nat (.arrow .unit
         (.arrow .nat (.arrow .nat (.arrow .unit (.prod .nat .unit)))))) :: as) :=
  .cons ((Formula.eq (.good (.var (.there .here)) (.var .here)) .zero).neg)
    (.cons (.eq (.ord (.succ (.succ (.var .here)))
      (.good (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.cons (.all .nat (.imp
      (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
        (.succ .zero))
      (goodAux (.nat :: .nat :: .nat :: Γ))))
    (((Δ.wk).wk).wk)))

/-- **`∀x. AUX(x)`**, by transfinite induction along `≺`. -/
def goodAuxD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (goodAux Γ)) := by
  refine Deriv.tiEps0 ?_
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_))))
  deriv_norm
  -- terms t::m::x::Γ ; stack: hx :: IH ; branch on good(m,t) = 0
  refine Deriv.orE (Deriv.eqDec (.good (.var (.there .here)) (.var .here)) .zero) ?_ ?_
  · -- hit zero: the current step is the witness
    refine Deriv.exI (.var .here) ?_
    deriv_norm
    deriv_assumption
  · -- not zero: descend
    deriv_norm
    -- stack: hneg :: hx :: IH ; g := good m t
    have hneg : Deriv (goodCtx Γ Δ) ((Formula.eq (.good (.var (.there .here)) (.var .here)) .zero).neg) := Deriv.ax
    have hx1 : Deriv (goodCtx Γ Δ) (.eq (.ord (.succ (.succ (.var .here)))
      (.good (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here)))) := Deriv.wk Deriv.ax
    have hIHacc : Deriv (goodCtx Γ Δ) (.all .nat (.imp
      (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
        (.succ .zero))
      (goodAux (.nat :: .nat :: .nat :: Γ)))) := Deriv.wk (Deriv.wk Deriv.ax)
    -- h1 : bump(t+2, g) ≠ 0
    have h1 := Deriv.impE
      (Deriv.bumpNeZero (.var .here)
        (.good (.var (.there .here)) (.var .here))) hneg
    -- h2 : prec (ord(t+3, pred(bump(t+2,g)))) (ord(t+3, bump(t+2,g))) = 1
    have h2 := Deriv.impE
      (Deriv.ordPredLt (.succ (.var .here))
        (.bump (.succ (.succ (.var .here)))
          (.good (.var (.there .here)) (.var .here)))) h1
    -- h3 : rewrite pred(bump(t+2,g)) to good(m, t+1)
    have h3 := Deriv.eqSubst
      (φ := .eq (.prec (.ord (.succ (.succ (.succ (.var (.there .here))))) (.var .here))
        (.ord (.succ (.succ (.succ (.var (.there .here)))))
          (.bump (.succ (.succ (.var (.there .here))))
            (.good (.var (.there (.there .here))) (.var (.there .here))))))
        (.succ .zero))
      (Deriv.symmE (Deriv.convGoodSucc (.var (.there .here)) (.var .here))) h2
    -- h4 : rewrite ord(t+3, bump(t+2,g)) to ord(t+2, g)
    have h4 := Deriv.eqSubst
      (φ := .eq (.prec (.ord (.succ (.succ (.succ (.var (.there .here)))))
          (.good (.var (.there (.there .here))) (.succ (.var (.there .here)))))
        (.var .here)) (.succ .zero))
      (Deriv.ordBump (.var .here)
        (.good (.var (.there .here)) (.var .here))) h3
    -- h5 : rewrite ord(t+2, g) to x — the AUX hypothesis
    have h5 := Deriv.eqSubst
      (φ := .eq (.prec (.ord (.succ (.succ (.succ (.var (.there .here)))))
          (.good (.var (.there (.there .here))) (.succ (.var (.there .here)))))
        (.var .here)) (.succ .zero))
      hx1 h4
    -- instantiate the induction hypothesis at the descended ordinal
    have hIH1 := Deriv.allE (τ := .nat)
      (.ord (.succ (.succ (.succ (.var .here))))
        (.good (.var (.there .here)) (.succ (.var .here)))) hIHacc
    deriv_norm at hIH1
    have hIH2 := Deriv.impE hIH1 h5
    have hIH3 := Deriv.allE (τ := .nat) (.var (.there .here)) hIH2
    deriv_norm at hIH3
    have hIH4 := Deriv.allE (τ := .nat) (.succ (.var .here)) hIH3
    deriv_norm at hIH4
    exact Deriv.impE hIH4 (Deriv.eqRefl _)

/-- **Goodstein's theorem.** -/
def goodsteinD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.ex .nat
      (.eq (.good (.var (.there .here)) (.var .here)) .zero))) := by
  refine Deriv.allI ?_
  have h0 := Deriv.allE (τ := .nat)
    (.ord (.succ (.succ .zero)) (.var .here))
    (goodAuxD (Γ := .nat :: Γ) (Δ := Ctx.wk Δ))
  deriv_norm at h0
  have h1 := Deriv.allE (τ := .nat) (.var .here) h0
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .nat) .zero h1
  deriv_norm at h2
  refine Deriv.impE h2 ?_
  -- ord(2, good(m,0)) = ord(2, m): rewrite by good(m,0) = m
  refine Deriv.eqSubst
    (φ := .eq (.ord (.succ (.succ .zero)) (.var .here))
      (.ord (.succ (.succ .zero)) (.var (.there .here))))
    (Deriv.symmE (Deriv.convGoodZero (.var .here))) ?_
  deriv_norm
  exact Deriv.eqRefl _

/-- **The extracted Goodstein stopping-time program.** -/
def goodsteinX (m : Nat) : Nat :=
  (((extractClosed (goodsteinD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) m).1

-- The extracted witness really stops the sequence — and matches the published
-- stopping times.  The first-order extract walls at m = 2; this one runs.
#guard [goodsteinX 0, goodsteinX 1, goodsteinX 2, goodsteinX 3] == [0, 1, 3, 5]
#guard (List.range 4).all fun m ↦ Realizability.goodN m (goodsteinX m) == 0

#print axioms goodAuxD
#print axioms goodsteinD
#print axioms goodsteinX

end HAomega
