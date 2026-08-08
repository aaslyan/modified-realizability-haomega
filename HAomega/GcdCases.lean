/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GcdDvd

/-!
# gcd stage 2, layer 5: the specification and the four Euclid cases

`SpecF a b` is the full gcd specification `∃g. g∣a ∧ g∣b ∧ ∀d. d∣a → d∣b → d∣g`
(an `abbrev`, so eliminations see through it), and the four case lemmas of
subtractive Euclid are derived:

* `gcdZeroLD` / `gcdZeroRD` — a zero argument: the other one is the gcd, and
  maximality is trivial;
* **`gcdLeftD`** — `a+s = b → Spec(a,s) → Spec(a,b)`: the recursive gcd also
  divides `b` by `dvdAddT`, and a common divisor of `a,b` divides `s` by
  `dvdSubT`, so maximality transports;
* **`gcdRightD`** — the mirror, recursing at `(b, S s)`.

These are the deepest derivations in the development (5-deep hypothesis
stacks, three nested eliminations); `deriv_norm` plus the explicit accessors
`ax1`–`ax4` is what makes them elaborate at default heartbeats.
-/

namespace HAomega


/-- The Spec body at witness `g = var here`. -/
abbrev SpecBody {Γ : List Ty} (a b : Tm Γ .nat) : Formula (.nat :: Γ)
    (.prod (.prod .nat .unit) (.prod (.prod .nat .unit)
      (.arrow .nat (.arrow (.prod .nat .unit)
        (.arrow (.prod .nat .unit) (.prod .nat .unit)))))) :=
  .and (Dvd (.var .here) (a.wk))
    (.and (Dvd (.var .here) (b.wk))
      (.all .nat (.imp (Dvd (.var .here) ((a.wk).wk))
        (.imp (Dvd (.var .here) ((b.wk).wk))
          (Dvd (.var .here) (.var (.there .here)))))))

/-- The gcd specification at `(a, b)`. -/
abbrev SpecF {Γ : List Ty} (a b : Tm Γ .nat) : Formula Γ
    (.prod .nat (.prod (.prod .nat .unit) (.prod (.prod .nat .unit)
      (.arrow .nat (.arrow (.prod .nat .unit)
        (.arrow (.prod .nat .unit) (.prod .nat .unit))))))) :=
  .ex .nat (SpecBody a b)

theorem SpecBody_def {Γ : List Ty} (a b : Tm Γ .nat) : SpecBody a b =
  .and (Dvd (.var .here) (a.wk))
    (.and (Dvd (.var .here) (b.wk))
      (.all .nat (.imp (Dvd (.var .here) ((a.wk).wk))
        (.imp (Dvd (.var .here) ((b.wk).wk))
          (Dvd (.var .here) (.var (.there .here))))))) := rfl

theorem SpecF_def {Γ : List Ty} (a b : Tm Γ .nat) :
    SpecF a b = .ex .nat (SpecBody a b) := rfl

/-- `∀a ∀b. a = 0 → Spec(a,b)` — the gcd is `b`. -/
def gcdZeroLD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.imp (.eq (.var (.there .here)) .zero)
      (SpecF (.var (.there .here)) (.var .here))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  refine Deriv.exI (.var .here) ?_
  deriv_norm
  refine Deriv.andI ?_ (Deriv.andI (dvdReflT (.var .here)) ?_)
  · refine Deriv.eqSubst
      (φ := .ex .nat (.eq (.var (.there .here))
        (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
      (Deriv.symmE Deriv.ax) ?_
    deriv_norm
    exact dvdZeroT (.var .here)
  · exact Deriv.allI (Deriv.impI (Deriv.impI Deriv.ax))

/-- `∀a ∀b. b = 0 → Spec(a,b)` — the gcd is `a`. -/
def gcdZeroRD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.imp (.eq (.var .here) .zero)
      (SpecF (.var (.there .here)) (.var .here))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  refine Deriv.exI (.var (.there .here)) ?_
  deriv_norm
  refine Deriv.andI (dvdReflT (.var (.there .here))) (Deriv.andI ?_ ?_)
  · refine Deriv.eqSubst
      (φ := .ex .nat (.eq (.var (.there .here))
        (.app (.app mulT (.var (.there (.there (.there .here))))) (.var .here))))
      (Deriv.symmE Deriv.ax) ?_
    deriv_norm
    exact dvdZeroT (.var (.there .here))
  · exact Deriv.allI (Deriv.impI (Deriv.impI (Deriv.wk Deriv.ax)))

/-- Hypothesis at depth 4, everything explicit. -/
def Deriv.ax4 {Γ as : List Ty} {a b c d e : Ty} {Δ : Ctx Γ as}
    (ψ₄ : Formula Γ e) (ψ₃ : Formula Γ d) (ψ₂ : Formula Γ c)
    (ψ₁ : Formula Γ b) (φ : Formula Γ a) :
    Deriv (.cons ψ₄ (.cons ψ₃ (.cons ψ₂ (.cons ψ₁ (.cons φ Δ))))) φ :=
  Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax)))

/-- `∀a∀b∀s. a+s = b → Spec(a,s) → Spec(a,b)` — the left Euclid step. -/
def gcdLeftD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there (.there .here))) (.var .here)) (.var (.there .here)))
        (.imp (SpecF (.var (.there (.there .here))) (.var .here))
          (SpecF (.var (.there (.there .here))) (.var (.there .here)))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_))))
  refine Deriv.exE
    (φ := SpecBody (.var (.there (.there .here))) (.var .here))
    (ψ := SpecF (.var (.there (.there .here))) (.var (.there .here)))
    Deriv.ax ?_
  refine Deriv.exI (.var .here) ?_
  deriv_norm
  refine Deriv.andI ?_ (Deriv.andI ?_ ?_)
  · exact Deriv.andE₁ Deriv.ax
  · refine Deriv.eqSubst
      (φ := .ex .nat (.eq (.var (.there .here))
        (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
      (Deriv.ax2
        (SpecBody (.var (.there (.there .here))) (.var .here))
        ((SpecF (.var (.there (.there .here))) (.var .here)).wk)
        (.eq (.add (.var (.there (.there (.there .here)))) (.var (.there .here)))
          (.var (.there (.there .here))))) ?_
    deriv_norm
    refine Deriv.impE (Deriv.impE
      (dvdAddT (.var .here) (.var (.there (.there (.there .here))))
        (.var (.there .here))) ?_) ?_
    · deriv_norm
      exact Deriv.andE₁ Deriv.ax
    · deriv_norm
      exact Deriv.andE₁ (Deriv.andE₂ Deriv.ax)
  · refine Deriv.allI (Deriv.impI (Deriv.impI ?_))
    deriv_norm
    refine Deriv.impE (Deriv.impE
      (Deriv.allE (τ := .nat) (.var .here) (Deriv.andE₂ (Deriv.andE₂ (Deriv.ax2
        (.ex .nat (.eq (.var (.there (.there (.there (.there .here)))))
          (.app (.app mulT (.var (.there .here))) (.var .here))))
        (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here))))))
          (.app (.app mulT (.var (.there .here))) (.var .here))))
        (.and (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here))))))
            (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
          (.and (.ex .nat (.eq (.var (.there (.there (.there .here))))
            (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
          (.all .nat (.imp
            (.ex .nat (.eq (.var (.there (.there (.there (.there (.there (.there .here)))))))
              (.app (.app mulT (.var (.there .here))) (.var .here))))
            (.imp (.ex .nat (.eq (.var (.there (.there (.there (.there .here)))))
              (.app (.app mulT (.var (.there .here))) (.var .here))))
            (.ex .nat (.eq (.var (.there (.there (.there .here))))
              (.app (.app mulT (.var (.there .here))) (.var .here)))))))))))))
      (Deriv.wk Deriv.ax)) ?_
    refine Deriv.impE (Deriv.impE
      (dvdSubT (.var .here) (.var (.there (.there (.there (.there .here)))))
        (.var (.there (.there .here)))) ?_) ?_
    · deriv_norm; exact Deriv.wk Deriv.ax
    · deriv_norm
      refine Deriv.eqSubst
        (φ := .ex .nat (.eq (.var (.there .here))
          (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
        (Deriv.symmE (Deriv.ax4
          (.ex .nat (.eq (.var (.there (.there (.there (.there .here)))))
            (.app (.app mulT (.var (.there .here))) (.var .here))))
          (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here))))))
            (.app (.app mulT (.var (.there .here))) (.var .here))))
          (.and (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here))))))
            (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
          (.and (.ex .nat (.eq (.var (.there (.there (.there .here))))
            (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
          (.all .nat (.imp
            (.ex .nat (.eq (.var (.there (.there (.there (.there (.there (.there .here)))))))
              (.app (.app mulT (.var (.there .here))) (.var .here))))
            (.imp (.ex .nat (.eq (.var (.there (.there (.there (.there .here)))))
              (.app (.app mulT (.var (.there .here))) (.var .here))))
            (.ex .nat (.eq (.var (.there (.there (.there .here))))
              (.app (.app mulT (.var (.there .here))) (.var .here)))))))))
          (((SpecF (.var (.there (.there .here))) (.var .here)).wk).wk)
          (.eq (.add (.var (.there (.there (.there (.there .here)))))
              (.var (.there (.there .here))))
            (.var (.there (.there (.there .here))))))) ?_
      deriv_norm
      exact Deriv.ax


/-- `∀a∀b∀s. b + S s = a → Spec(b, S s) → Spec(a,b)` — the right Euclid step. -/
def gcdRightD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
          (.var (.there (.there .here))))
        (.imp (SpecF (.var (.there .here)) (.succ (.var .here)))
          (SpecF (.var (.there (.there .here))) (.var (.there .here)))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_))))
  refine Deriv.exE
    (φ := SpecBody (.var (.there .here)) (.succ (.var .here)))
    (ψ := SpecF (.var (.there (.there .here))) (.var (.there .here)))
    Deriv.ax ?_
  refine Deriv.exI (.var .here) ?_
  deriv_norm
  refine Deriv.andI ?_ (Deriv.andI ?_ ?_)
  · -- g ∣ a  via dvdAdd g b (S s) and b + S s = a
    refine Deriv.eqSubst
      (φ := .ex .nat (.eq (.var (.there .here))
        (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
      (Deriv.ax2
        (SpecBody (.var (.there .here)) (.succ (.var .here)))
        ((SpecF (.var (.there .here)) (.succ (.var .here))).wk)
        (.eq (.add (.var (.there (.there .here))) (.succ (.var (.there .here))))
          (.var (.there (.there (.there .here)))))) ?_
    deriv_norm
    refine Deriv.impE (Deriv.impE
      (dvdAddT (.var .here) (.var (.there (.there .here)))
        (.succ (.var (.there .here)))) ?_) ?_
    · deriv_norm
      exact Deriv.andE₁ Deriv.ax
    · deriv_norm
      exact Deriv.andE₁ (Deriv.andE₂ Deriv.ax)
  · -- g ∣ b, directly
    exact Deriv.andE₁ Deriv.ax
  · -- maximality
    refine Deriv.allI (Deriv.impI (Deriv.impI ?_))
    deriv_norm
    refine Deriv.impE (Deriv.impE
      (Deriv.allE (τ := .nat) (.var .here) (Deriv.andE₂ (Deriv.andE₂ (Deriv.ax2
        (.ex .nat (.eq (.var (.there (.there (.there (.there .here)))))
          (.app (.app mulT (.var (.there .here))) (.var .here))))
        (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here))))))
          (.app (.app mulT (.var (.there .here))) (.var .here))))
        (.and (.ex .nat (.eq (.var (.there (.there (.there (.there .here)))))
            (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
          (.and (.ex .nat (.eq (.succ (.var (.there (.there (.there .here)))))
            (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
          (.all .nat (.imp
            (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here))))))
              (.app (.app mulT (.var (.there .here))) (.var .here))))
            (.imp (.ex .nat (.eq (.succ (.var (.there (.there (.there (.there .here))))))
              (.app (.app mulT (.var (.there .here))) (.var .here))))
            (.ex .nat (.eq (.var (.there (.there (.there .here))))
              (.app (.app mulT (.var (.there .here))) (.var .here)))))))))))))
      Deriv.ax) ?_
    -- remaining: d ∣ S s
    refine Deriv.impE (Deriv.impE
      (dvdSubT (.var .here) (.var (.there (.there (.there .here))))
        (.succ (.var (.there (.there .here))))) ?_) ?_
    · deriv_norm; exact Deriv.ax
    · deriv_norm
      refine Deriv.eqSubst
        (φ := .ex .nat (.eq (.var (.there .here))
          (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
        (Deriv.symmE (Deriv.ax4
          (.ex .nat (.eq (.var (.there (.there (.there (.there .here)))))
            (.app (.app mulT (.var (.there .here))) (.var .here))))
          (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here))))))
            (.app (.app mulT (.var (.there .here))) (.var .here))))
          (.and (.ex .nat (.eq (.var (.there (.there (.there (.there .here)))))
              (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
            (.and (.ex .nat (.eq (.succ (.var (.there (.there (.there .here)))))
              (.app (.app mulT (.var (.there (.there .here)))) (.var .here))))
            (.all .nat (.imp
              (.ex .nat (.eq (.var (.there (.there (.there (.there (.there .here))))))
                (.app (.app mulT (.var (.there .here))) (.var .here))))
              (.imp (.ex .nat (.eq (.succ (.var (.there (.there (.there (.there .here))))))
                (.app (.app mulT (.var (.there .here))) (.var .here))))
              (.ex .nat (.eq (.var (.there (.there (.there .here))))
                (.app (.app mulT (.var (.there .here))) (.var .here)))))))))
          (((SpecF (.var (.there .here)) (.succ (.var .here))).wk).wk)
          (.eq (.add (.var (.there (.there (.there .here))))
              (.succ (.var (.there (.there .here)))))
            (.var (.there (.there (.there (.there .here)))))))) ?_
      deriv_norm
      exact Deriv.wk Deriv.ax

#print axioms gcdZeroLD
#print axioms gcdZeroRD
#print axioms gcdLeftD
#print axioms gcdRightD

end HAomega
