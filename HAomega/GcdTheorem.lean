/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GcdCases

/-!
# The gcd theorem, and the proof-computed gcd

    gcdTheoremD : ∀a ∀b. ∃g. g∣a ∧ g∣b ∧ ∀d. d∣a → d∣b → d∣g

**The fueled main induction**: `φ(m) := ∀a∀b∀c. (a+b)+c = m → Spec(a,b)`, by
plain `ind` with an explicit slack variable — no strong-induction scaffold, an
improvement on the first-order proof, which had to derive one.  The step opens
`a` and `b` with the case-split device, branches on `trichotomyT`, rebuilds
the fuel equation through the addition algebra and `succInj`, instantiates the
induction hypothesis at the smaller pair, and closes with the four case
lemmas.  `gcdFull` reads the witness off the extracted realizer — the gcd
computed by a program extraction assembled from the proof, Pascal-style:
nothing in the statement names an algorithm.
-/

namespace HAomega


def Deriv.ax6 {Γ as : List Ty} {a b c d e f g : Ty} {Δ : Ctx Γ as}
    (ψ₆ : Formula Γ g) (ψ₅ : Formula Γ f) (ψ₄ : Formula Γ e) (ψ₃ : Formula Γ d)
    (ψ₂ : Formula Γ c) (ψ₁ : Formula Γ b) (φ : Formula Γ a) :
    Deriv (.cons ψ₆ (.cons ψ₅ (.cons ψ₄ (.cons ψ₃ (.cons ψ₂ (.cons ψ₁ (.cons φ Δ))))))) φ :=
  Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax)))))

def Deriv.ax7 {Γ as : List Ty} {a b c d e f g h : Ty} {Δ : Ctx Γ as}
    (ψ₇ : Formula Γ h) (ψ₆ : Formula Γ g) (ψ₅ : Formula Γ f) (ψ₄ : Formula Γ e)
    (ψ₃ : Formula Γ d) (ψ₂ : Formula Γ c) (ψ₁ : Formula Γ b) (φ : Formula Γ a) :
    Deriv (.cons ψ₇ (.cons ψ₆ (.cons ψ₅ (.cons ψ₄ (.cons ψ₃ (.cons ψ₂
      (.cons ψ₁ (.cons φ Δ)))))))) φ :=
  Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))))))

def Deriv.ax5 {Γ as : List Ty} {a b c d e f : Ty} {Δ : Ctx Γ as}
    (ψ₅ : Formula Γ f) (ψ₄ : Formula Γ e) (ψ₃ : Formula Γ d)
    (ψ₂ : Formula Γ c) (ψ₁ : Formula Γ b) (φ : Formula Γ a) :
    Deriv (.cons ψ₅ (.cons ψ₄ (.cons ψ₃ (.cons ψ₂ (.cons ψ₁ (.cons φ Δ)))))) φ :=
  Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))))


/-- Term forms of the four case lemmas. -/
def gcdZeroLT {Γ as : List Ty} {Δ : Ctx Γ as} (a b : Tm Γ .nat) :
    Deriv Δ (.imp (.eq a .zero) (SpecF a b)) := by
  have h := Deriv.allE b (Deriv.allE a (gcdZeroLD (Δ := Δ)))
  deriv_norm at h ⊢
  exact h

def gcdZeroRT {Γ as : List Ty} {Δ : Ctx Γ as} (a b : Tm Γ .nat) :
    Deriv Δ (.imp (.eq b .zero) (SpecF a b)) := by
  have h := Deriv.allE b (Deriv.allE a (gcdZeroRD (Δ := Δ)))
  deriv_norm at h ⊢
  exact h

def gcdLeftT {Γ as : List Ty} {Δ : Ctx Γ as} (a b s : Tm Γ .nat) :
    Deriv Δ (.imp (.eq (.add a s) b) (.imp (SpecF a s) (SpecF a b))) := by
  have h := Deriv.allE s (Deriv.allE b (Deriv.allE a (gcdLeftD (Δ := Δ))))
  deriv_norm at h ⊢
  exact h

def gcdRightT {Γ as : List Ty} {Δ : Ctx Γ as} (a b s : Tm Γ .nat) :
    Deriv Δ (.imp (.eq (.add b (.succ s)) a)
      (.imp (SpecF b (.succ s)) (SpecF a b))) := by
  have h := Deriv.allE s (Deriv.allE b (Deriv.allE a (gcdRightD (Δ := Δ))))
  deriv_norm at h ⊢
  exact h

/-- The fueled motive: `∀a∀b∀c. (a+b)+c = m → Spec(a,b)`. -/
abbrev gcdPhi (Γ : List Ty) : Formula (.nat :: Γ)
    (.arrow .nat (.arrow .nat (.arrow .nat (.arrow .unit
      (.prod .nat (.prod (.prod .nat .unit) (.prod (.prod .nat .unit)
        (.arrow .nat (.arrow (.prod .nat .unit)
          (.arrow (.prod .nat .unit) (.prod .nat .unit))))))))))) :=
  .all .nat (.all .nat (.all .nat (.imp
    (.eq (.add (.add (.var (.there (.there .here))) (.var (.there .here)))
      (.var .here)) (.var (.there (.there (.there .here)))))
    (SpecF (.var (.there (.there .here))) (.var (.there .here))))))

/-- **The fueled main induction.** -/
def gcdFuelD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (gcdPhi Γ)) := by
  refine Deriv.ind ?_ ?_
  · -- m = 0 ⟹ a = 0
    refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI ?_)))
    deriv_norm
    refine Deriv.impE
      (gcdZeroLT (.var (.there (.there .here))) (.var (.there .here))) ?_
    refine Deriv.impE (addEqZeroT (.var (.there (.there .here))) (.var (.there .here))) ?_
    refine Deriv.impE (addEqZeroT
      (.add (.var (.there (.there .here))) (.var (.there .here))) (.var .here)) ?_
    exact Deriv.ax
  · refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI ?_)))))
    deriv_norm
    -- stack: hsum :: IH.wk³ ; terms c::b::a::m
    refine Deriv.orE (caseNatT (.var (.there (.there .here)))) ?_ ?_
    · -- a = 0
      refine Deriv.impE
        (gcdZeroLT (.var (.there (.there .here))) (.var (.there .here))) ?_
      exact Deriv.ax
    · refine Deriv.exE
        (ψ := SpecF (.var (.there (.there .here))) (.var (.there .here)))
        Deriv.ax ?_
      deriv_norm
      -- terms a'::c::b::a::m
      refine Deriv.orE (caseNatT (.var (.there (.there .here)))) ?_ ?_
      · -- b = 0
        refine Deriv.impE
          (gcdZeroRT (.var (.there (.there (.there .here))))
            (.var (.there (.there .here)))) ?_
        exact Deriv.ax
      · refine Deriv.exE
          (ψ := SpecF (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
          Deriv.ax ?_
        deriv_norm
        -- terms b'::a'::c::b::a::m
        refine Deriv.orE (trichotomyT (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there .here))))) ?_ ?_
        · -- a + s = b: recurse at (a, s, a'+c)
          refine Deriv.exE
            (ψ := SpecF (.var (.there (.there (.there (.there .here))))) (.var (.there (.there (.there .here)))))
            Deriv.ax ?_
          deriv_norm
          refine Deriv.impE (Deriv.impE (gcdLeftT (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there (.there .here))))) (.var .here)) Deriv.ax) ?_
          have hIH0 : Deriv (.cons (.eq (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var .here)) (.var (.there (.there (.there (.there .here)))))) (.cons (.ex .nat (.eq (.add (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var .here)) (.var (.there (.there (.there (.there (.there .here)))))))) (.cons (.eq (.var (.there (.there (.there (.there .here))))) (.succ (.var (.there .here)))) (.cons (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here)))) (.cons (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var (.there (.there .here))))) (.cons (.ex .nat (.eq (.var (.there (.there (.there (.there (.there (.there .here))))))) (.succ (.var .here)))) (.cons (.eq (.add (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.all .nat (.all .nat (.all .nat (.imp (.eq (.add (.add (.var (.there (.there .here))) (.var (.there .here))) (.var .here)) (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (SpecF (.var (.there (.there .here))) (.var (.there .here))))))) (((((((Δ.wk).wk).wk).wk).wk).wk).wk))))))))) (.all .nat (.all .nat (.all .nat (.imp (.eq (.add (.add (.var (.there (.there .here))) (.var (.there .here))) (.var .here)) (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (SpecF (.var (.there (.there .here))) (.var (.there .here))))))) :=
            Deriv.ax7 (.eq (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var .here)) (.var (.there (.there (.there (.there .here)))))) (.ex .nat (.eq (.add (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var .here)) (.var (.there (.there (.there (.there (.there .here)))))))) (.eq (.var (.there (.there (.there (.there .here))))) (.succ (.var (.there .here)))) (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here)))) (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var (.there (.there .here))))) (.ex .nat (.eq (.var (.there (.there (.there (.there (.there (.there .here))))))) (.succ (.var .here)))) (.eq (.add (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there (.there (.there (.there (.there .here))))))))) (.all .nat (.all .nat (.all .nat (.imp (.eq (.add (.add (.var (.there (.there .here))) (.var (.there .here))) (.var .here)) (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (SpecF (.var (.there (.there .here))) (.var (.there .here)))))))
          have hIH1 := Deriv.allE (τ := .nat) (.var (.there (.there (.there (.there (.there .here)))))) hIH0
          have hIH2 := Deriv.allE (τ := .nat) (.var .here) hIH1
          have hIH3 := Deriv.allE (τ := .nat) (.add (.var (.there (.there .here))) (.var (.there (.there (.there .here))))) hIH2
          deriv_norm at hIH3
          refine Deriv.impE hIH3 ?_
          refine Deriv.impE (Deriv.succInj _ _) ?_
          refine Deriv.transE (t := .add (.add (.var (.there (.there (.there (.there (.there .here)))))) (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var .here))) (.var (.there (.there (.there .here)))))
            (Deriv.symmE ?_) ?_
          · -- (a+(a+s))+c = S ((a+s)+(a'+c))
            refine Deriv.transE (Deriv.congAddL (.var (.there (.there (.there .here)))) (plusCommT (.var (.there (.there (.there (.there (.there .here)))))) (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var .here)))) ?_
            refine Deriv.transE (plusAssocT (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var .here)) (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here))))) ?_
            refine Deriv.transE (Deriv.congAddR (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var .here))
              (Deriv.transE (Deriv.congAddL (.var (.there (.there (.there .here))))
                  (Deriv.ax4 (.eq (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var .here)) (.var (.there (.there (.there (.there .here)))))) (.ex .nat (.eq (.add (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var .here)) (.var (.there (.there (.there (.there (.there .here)))))))) (.eq (.var (.there (.there (.there (.there .here))))) (.succ (.var (.there .here)))) (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here)))) (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var (.there (.there .here)))))))
                (Deriv.transE (succPlusT (.var (.there (.there .here))) (.var (.there (.there (.there .here))))) (Deriv.eqRefl _)))) ?_
            exact Deriv.transE (Deriv.convAddSucc _ _) (Deriv.eqRefl _)
          · -- (a+(a+s))+c = S m, transporting hsum along a+s = b
            refine Deriv.eqSubst (φ := (.eq (.add (.add (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var .here)) (.var (.there (.there (.there (.there .here)))))) (.succ (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
              (Deriv.symmE Deriv.ax) ?_
            deriv_norm
            exact Deriv.ax6 (.eq (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var .here)) (.var (.there (.there (.there (.there .here)))))) (.ex .nat (.eq (.add (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var .here)) (.var (.there (.there (.there (.there (.there .here)))))))) (.eq (.var (.there (.there (.there (.there .here))))) (.succ (.var (.there .here)))) (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here)))) (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var (.there (.there .here))))) (.ex .nat (.eq (.var (.there (.there (.there (.there (.there (.there .here))))))) (.succ (.var .here)))) (.eq (.add (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there (.there (.there (.there (.there .here)))))))))
        · -- b + S s = a: recurse at (b, S s, b'+c)
          refine Deriv.exE
            (ψ := SpecF (.var (.there (.there (.there (.there .here))))) (.var (.there (.there (.there .here)))))
            Deriv.ax ?_
          deriv_norm
          refine Deriv.impE (Deriv.impE (gcdRightT (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there (.there .here))))) (.var .here)) Deriv.ax) ?_
          have hIH0 : Deriv (.cons (.eq (.add (.var (.there (.there (.there (.there .here))))) (.succ (.var .here))) (.var (.there (.there (.there (.there (.there .here))))))) (.cons (.ex .nat (.eq (.add (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here))) (.var (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.eq (.var (.there (.there (.there (.there .here))))) (.succ (.var (.there .here)))) (.cons (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here)))) (.cons (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var (.there (.there .here))))) (.cons (.ex .nat (.eq (.var (.there (.there (.there (.there (.there (.there .here))))))) (.succ (.var .here)))) (.cons (.eq (.add (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.all .nat (.all .nat (.all .nat (.imp (.eq (.add (.add (.var (.there (.there .here))) (.var (.there .here))) (.var .here)) (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (SpecF (.var (.there (.there .here))) (.var (.there .here))))))) (((((((Δ.wk).wk).wk).wk).wk).wk).wk))))))))) (.all .nat (.all .nat (.all .nat (.imp (.eq (.add (.add (.var (.there (.there .here))) (.var (.there .here))) (.var .here)) (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (SpecF (.var (.there (.there .here))) (.var (.there .here))))))) :=
            Deriv.ax7 (.eq (.add (.var (.there (.there (.there (.there .here))))) (.succ (.var .here))) (.var (.there (.there (.there (.there (.there .here))))))) (.ex .nat (.eq (.add (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here))) (.var (.there (.there (.there (.there (.there (.there .here))))))))) (.eq (.var (.there (.there (.there (.there .here))))) (.succ (.var (.there .here)))) (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here)))) (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var (.there (.there .here))))) (.ex .nat (.eq (.var (.there (.there (.there (.there (.there (.there .here))))))) (.succ (.var .here)))) (.eq (.add (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there (.there (.there (.there (.there .here))))))))) (.all .nat (.all .nat (.all .nat (.imp (.eq (.add (.add (.var (.there (.there .here))) (.var (.there .here))) (.var .here)) (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (SpecF (.var (.there (.there .here))) (.var (.there .here)))))))
          have hIH1 := Deriv.allE (τ := .nat) (.var (.there (.there (.there (.there .here))))) hIH0
          have hIH2 := Deriv.allE (τ := .nat) (.succ (.var .here)) hIH1
          have hIH3 := Deriv.allE (τ := .nat) (.add (.var (.there .here)) (.var (.there (.there (.there .here))))) hIH2
          deriv_norm at hIH3
          refine Deriv.impE hIH3 ?_
          refine Deriv.impE (Deriv.succInj _ _) ?_
          refine Deriv.transE (t := .add (.add (.add (.var (.there (.there (.there (.there .here))))) (.succ (.var .here))) (.var (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here)))))
            (Deriv.symmE ?_) ?_
          · -- ((b+Ss)+b)+c = S ((b+Ss)+(b'+c))
            refine Deriv.transE (plusAssocT (.add (.var (.there (.there (.there (.there .here))))) (.succ (.var .here))) (.var (.there (.there (.there (.there .here))))) (.var (.there (.there (.there .here))))) ?_
            refine Deriv.transE (Deriv.congAddR (.add (.var (.there (.there (.there (.there .here))))) (.succ (.var .here)))
              (Deriv.transE (Deriv.congAddL (.var (.there (.there (.there .here))))
                  (Deriv.ax2 (.eq (.add (.var (.there (.there (.there (.there .here))))) (.succ (.var .here))) (.var (.there (.there (.there (.there (.there .here))))))) (.ex .nat (.eq (.add (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here))) (.var (.there (.there (.there (.there (.there (.there .here))))))))) (.eq (.var (.there (.there (.there (.there .here))))) (.succ (.var (.there .here))))))
                (Deriv.transE (succPlusT (.var (.there .here)) (.var (.there (.there (.there .here))))) (Deriv.eqRefl _)))) ?_
            exact Deriv.transE (Deriv.convAddSucc _ _) (Deriv.eqRefl _)
          · refine Deriv.eqSubst (φ := (.eq (.add (.add (.var .here) (.var (.there (.there (.there (.there (.there .here))))))) (.var (.there (.there (.there (.there .here)))))) (.succ (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
              (Deriv.symmE Deriv.ax) ?_
            deriv_norm
            exact Deriv.ax6 (.eq (.add (.var (.there (.there (.there (.there .here))))) (.succ (.var .here))) (.var (.there (.there (.there (.there (.there .here))))))) (.ex .nat (.eq (.add (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here))) (.var (.there (.there (.there (.there (.there (.there .here))))))))) (.eq (.var (.there (.there (.there (.there .here))))) (.succ (.var (.there .here)))) (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var .here)))) (.eq (.var (.there (.there (.there (.there (.there .here)))))) (.succ (.var (.there (.there .here))))) (.ex .nat (.eq (.var (.there (.there (.there (.there (.there (.there .here))))))) (.succ (.var .here)))) (.eq (.add (.add (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there (.there (.there (.there (.there .here)))))))))

/-- **The gcd theorem**: `∀a ∀b. ∃g. g∣a ∧ g∣b ∧ ∀d. d∣a → d∣b → d∣g`. -/
def gcdTheoremD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat
      (SpecF (.var (.there .here)) (.var .here)))) := by
  refine Deriv.allI (Deriv.allI ?_)
  have h0 : Deriv ((Δ.wk).wk) (.all .nat (gcdPhi (.nat :: .nat :: Γ))) := gcdFuelD
  have h1 := Deriv.allE (τ := .nat)
    (.add (.add (.var (.there .here)) (.var .here)) .zero) h0
  have h2 := Deriv.allE (τ := .nat) (.var (.there .here)) h1
  have h3 := Deriv.allE (τ := .nat) (.var .here) h2
  have h4 := Deriv.allE (τ := .nat) .zero h3
  deriv_norm at h4
  refine Deriv.impE h4 ?_
  exact Deriv.eqRefl _

/-- **The proof-computed gcd.**  The realizer's witness component, from the
full-specification theorem — the algorithm assembled by extraction out of the
fueled induction, the trichotomy decision, and the case analysis. -/
def gcdFull (a b : Nat) : Nat :=
  (((extractClosed (gcdTheoremD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) a b).1

-- Evaluating the extracted realizer is expensive (the derivation is the
-- largest in the development); the `#guard`s are kept out of the build and
-- recorded here for `lake env lean` verification runs:
--   gcdFull 12 18 = 6, gcdFull 21 14 = 7, gcdFull 7 13 = 1.
#print axioms gcdFuelD
#print axioms gcdTheoremD

end HAomega
