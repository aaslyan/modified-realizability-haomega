/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GcdCases

/-!
# gcd stage 2, layer 6: deep accessors and the case lemmas in term form

`ax5`–`ax7` extend the pinned hypothesis accessors to the depths the fueled
main induction reaches (its trichotomy branches carry an 8-deep stack), and
the four Euclid case lemmas get term forms (`gcdZeroLT`/`gcdZeroRT`/
`gcdLeftT`/`gcdRightT`) via the `deriv_norm` conversion, so the main induction
applies them at its bound variables with no `allE` inversion.

## Status of the main induction

The fueled induction (`φ(m) := ∀a∀b∀c. (a+b)+c = m → Spec(a,b)`, plain `ind`
with explicit slack — no strong-induction scaffold needed) is written and
elaborates through its skeleton: base case, both zero cases, both `exE`
openings and the trichotomy split all check.  Three applications inside the
trichotomy branches still mismatch on hypothesis-formula pins (the same
ground-index adjustments as every previous layer, against an 8-deep stack),
and the session ended there.  **`gcdTheoremD` is therefore not yet derived and
is not claimed.**  No new machinery is needed; the remaining work is pin
correction against the elaborator's printed expected contexts.
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


end HAomega
