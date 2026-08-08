/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GcdFull

/-!
# gcd stage 2, layer 4: `deriv_norm`, and the divisibility lemmas

**`deriv_norm`** is the normalization tactic the previous session's blocker
called for: one `simp only` set that reduces every `Ctx.wk`, `Formula.wk`,
substitution and weakening in a `Deriv` goal — context index included — to
ground normal form.  With it, nested `exE`/`orE` proofs elaborate at default
heartbeats, and the accessors (`ax1`–`ax3`) match structurally.

On top of it, the two recombination lemmas of subtractive Euclid, as
derivations:

* **`dvdAddD`** : `∀d∀x∀y. d∣x → d∣y → d∣(x+y)` — witnesses add, certificate
  by `distribLT`;
* **`dvdSubD`** : `∀d∀x∀y. d∣x → d∣(x+y) → d∣y` — by **trichotomy on the
  quotients**: if `q1 ≤ q2` the witness is the difference (certificate by
  distributivity and left cancellation); if `q2 < q1` the remainder is forced
  to `0` (certificate through `addEqZeroT`, cancellation, and `y = d·0`).

`dvdSubD` is the deepest derivation in the development so far — a 6-deep
hypothesis stack at its leaves, and precisely the proof the `Ctx.wk`
unification failures blocked before the tactic existed.
-/

namespace HAomega


/-! ## The normalization tactic -/

theorem Ctx.wk_cons {Γ : List Ty} {σ a : Ty} {as : List Ty}
    (φ : Formula Γ a) (Δ : Ctx Γ as) :
    (Ctx.cons φ Δ).wk (σ := σ) = .cons φ.wk Δ.wk := rfl
theorem Ctx.wk_nil {Γ : List Ty} {σ : Ty} :
    (Ctx.nil (Γ := Γ)).wk (σ := σ) = .nil := rfl
theorem mulT_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (mulT (Γ := Γ)).rename ρ = mulT := rfl

/-- Normalize a `Deriv` goal (or hypothesis): reduce every `Ctx.wk`,
`Formula.wk`/`rename`/`subst`, and `Tm`-level weakening to ground normal form,
so accessors and lemmas match structurally.  The fix for the
whnf-vs-metavariable unification failures in nested eliminations. -/
macro "deriv_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| try simp only [Ctx.wk_cons, Ctx.wk_nil, Dvd, Formula.wk,
      Formula.rename, Formula.subst1, Formula.subst, Tm.wk, Tm.rename,
      Tm.subst1, Tm.subst, Sub.one, Sub.ext, Ren.wk, Ren.ext,
      mulT_subst, mulT_rename, Tm.wk_subst_ext, Tm.wk_subst_one,
      subst_one_rename, subst_ext_rename] $(loc)?)

/-! ## Term forms of the stage-1 divisibility facts -/

def dvdZeroT {Γ as : List Ty} {Δ : Ctx Γ as} (d : Tm Γ .nat) :
    Deriv Δ (.ex .nat (.eq .zero (.app (.app mulT (d.wk)) (.var .here)))) := by
  have h := Deriv.allE d (dvdZeroDeriv (Δ := Δ))
  deriv_norm at h ⊢
  exact h

def dvdReflT {Γ as : List Ty} {Δ : Ctx Γ as} (d : Tm Γ .nat) :
    Deriv Δ (.ex .nat (.eq (d.wk) (.app (.app mulT (d.wk)) (.var .here)))) := by
  have h := Deriv.allE d (dvdReflDeriv (Δ := Δ))
  deriv_norm at h ⊢
  exact h

/-- Hypothesis at depth 3, everything explicit. -/
def Deriv.ax3 {Γ as : List Ty} {a b c d : Ty} {Δ : Ctx Γ as}
    (ψ₃ : Formula Γ d) (ψ₂ : Formula Γ c) (ψ₁ : Formula Γ b) (φ : Formula Γ a) :
    Deriv (.cons ψ₃ (.cons ψ₂ (.cons ψ₁ (.cons φ Δ)))) φ :=
  Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))

/-! ## dvdAdd, with the tactic -/

/-- `∀d ∀x ∀y. d∣x → d∣y → d∣(x+y)`. -/
def dvdAddD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.all .nat
      (.imp (Dvd (.var (.there (.there .here))) (.var (.there .here)))
        (.imp (Dvd (.var (.there (.there .here))) (.var .here))
          (Dvd (.var (.there (.there .here)))
            (.add (.var (.there .here)) (.var .here)))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_))))
  deriv_norm
  refine Deriv.exE
    (ψ := .ex .nat (.eq (.add (.var (.there (.there .here))) (.var (.there .here)))
      (.app (.app mulT (.var (.there (.there (.there .here))))) (.var .here))))
    (Deriv.ax1
      (.ex .nat (.eq (.var (.there .here))
        (.app (.app mulT (.var (.there (.there (.there .here))))) (.var .here))))
      (.ex .nat (.eq (.var (.there (.there .here)))
        (.app (.app mulT (.var (.there (.there (.there .here))))) (.var .here))))) ?_
  deriv_norm
  refine Deriv.exE
    (ψ := .ex .nat (.eq (.add (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
      (.app (.app mulT (.var (.there (.there (.there (.there .here)))))) (.var .here))))
    (Deriv.ax1
      (.eq (.var (.there (.there .here)))
        (.app (.app mulT (.var (.there (.there (.there .here))))) (.var .here)))
      (.ex .nat (.eq (.var (.there (.there .here)))
        (.app (.app mulT (.var (.there (.there (.there (.there .here)))))) (.var .here))))) ?_
  deriv_norm
  refine Deriv.exI (.add (.var (.there .here)) (.var .here)) ?_
  deriv_norm
  refine Deriv.transE (Deriv.congAddL (.var (.there (.there .here)))
    (Deriv.ax1
      (.eq (.var (.there (.there .here)))
        (.app (.app mulT (.var (.there (.there (.there (.there .here)))))) (.var .here)))
      (.eq (.var (.there (.there (.there .here))))
        (.app (.app mulT (.var (.there (.there (.there (.there .here))))))
          (.var (.there .here)))))) ?_
  refine Deriv.transE (Deriv.congAddR _ Deriv.ax) ?_
  exact Deriv.transE (Deriv.symmE (distribLT _ (.var (.there .here)) (.var .here)))
    (Deriv.eqRefl _)

/-- `∀d ∀x ∀y. d∣x → d∣(x+y) → d∣y`. -/
def dvdSubD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.all .nat
      (.imp (Dvd (.var (.there (.there .here))) (.var (.there .here)))
        (.imp (Dvd (.var (.there (.there .here)))
            (.add (.var (.there .here)) (.var .here)))
          (Dvd (.var (.there (.there .here))) (.var .here))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_))))
  deriv_norm
  refine Deriv.exE
    (ψ := .ex .nat (.eq (.var (.there .here))
      (.app (.app mulT (.var (.there (.there (.there .here))))) (.var .here))))
    (Deriv.ax1
      (.ex .nat (.eq (.add (.var (.there (.there .here))) (.var (.there .here)))
        (.app (.app mulT (.var (.there (.there (.there .here))))) (.var .here))))
      (.ex .nat (.eq (.var (.there (.there .here)))
        (.app (.app mulT (.var (.there (.there (.there .here))))) (.var .here))))) ?_
  deriv_norm
  refine Deriv.exE
    (ψ := .ex .nat (.eq (.var (.there (.there .here)))
      (.app (.app mulT (.var (.there (.there (.there (.there .here)))))) (.var .here))))
    (Deriv.ax1
      (.eq (.var (.there (.there .here)))
        (.app (.app mulT (.var (.there (.there (.there .here))))) (.var .here)))
      (.ex .nat (.eq (.add (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
        (.app (.app mulT (.var (.there (.there (.there (.there .here)))))) (.var .here))))) ?_
  deriv_norm
  -- ctx: hq2 : x+y = d·q2 :: hq1 : x = d·q1 ; term: q2::q1::y::x::d
  refine Deriv.orE (trichotomyT (.var (.there .here)) (.var .here)) ?_ ?_
  · -- ∃r. q1 + r = q2  ⟹  y = d·r
    deriv_norm
    refine Deriv.exE
      (ψ := .ex .nat (.eq (.var (.there (.there (.there .here))))
        (.app (.app mulT (.var (.there (.there (.there (.there (.there .here))))))) (.var .here))))
      Deriv.ax ?_
    deriv_norm
    refine Deriv.exI (.var .here) ?_
    deriv_norm
    -- stack: hr :: exhyp :: hq2 :: hq1 ; terms r::q2::q1::y::x::d
    refine Deriv.impE (cancelAddLT (.var (.there (.there (.there (.there .here)))))
      (.var (.there (.there (.there .here))))
      (.app (.app mulT (.var (.there (.there (.there (.there (.there .here)))))))
        (.var .here))) ?_
    refine Deriv.transE (Deriv.ax2 (.eq (.add (.var (.there (.there .here))) (.var .here)) (.var (.there .here)))
      (.ex .nat (.eq (.add (.var (.there (.there (.there .here)))) (.var .here))
        (.var (.there (.there .here)))))
      (.eq (.add (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there .here)))))
        (.app (.app mulT (.var (.there (.there (.there (.there (.there .here)))))))
          (.var (.there .here))))) ?_
    refine Deriv.transE (Deriv.congArg _ (Deriv.symmE Deriv.ax)) ?_
    refine Deriv.transE (distribLT _ (.var (.there (.there .here))) (.var .here)) ?_
    refine Deriv.transE (Deriv.congAddL _ (Deriv.symmE (Deriv.ax3 (.eq (.add (.var (.there (.there .here))) (.var .here)) (.var (.there .here)))
      (.ex .nat (.eq (.add (.var (.there (.there (.there .here)))) (.var .here))
        (.var (.there (.there .here)))))
      (.eq (.add (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there .here)))))
        (.app (.app mulT (.var (.there (.there (.there (.there (.there .here)))))))
          (.var (.there .here))))
      (.eq (.var (.there (.there (.there (.there .here)))))
        (.app (.app mulT (.var (.there (.there (.there (.there (.there .here)))))))
          (.var (.there (.there .here)))))))) ?_
    exact Deriv.eqRefl _
  · -- ∃r. q2 + S r = q1  ⟹  y = 0 = d·0
    deriv_norm
    refine Deriv.exE
      (ψ := .ex .nat (.eq (.var (.there (.there (.there .here))))
        (.app (.app mulT (.var (.there (.there (.there (.there (.there .here))))))) (.var .here))))
      Deriv.ax ?_
    deriv_norm
    refine Deriv.exI .zero ?_
    deriv_norm
    refine Deriv.transE (t := Tm.zero) ?_ (Deriv.symmE (mulZero _))
    -- goal: y = 0
    refine Deriv.impE (addEqZeroT (.var (.there (.there (.there .here))))
      (.app (.app mulT (.var (.there (.there (.there (.there (.there .here)))))))
        (.succ (.var .here)))) ?_
    refine Deriv.symmE ?_
    refine Deriv.impE (cancelAddLT (.var (.there (.there (.there (.there .here)))))
      .zero (.add (.var (.there (.there (.there .here))))
        (.app (.app mulT (.var (.there (.there (.there (.there (.there .here)))))))
          (.succ (.var .here))))) ?_
    refine Deriv.transE (Deriv.convAddZero _) ?_
    refine Deriv.transE (Deriv.ax3 (.eq (.add (.var (.there .here)) (.succ (.var .here)))
        (.var (.there (.there .here))))
      (.ex .nat (.eq (.add (.var (.there (.there .here))) (.succ (.var .here)))
        (.var (.there (.there (.there .here))))))
      (.eq (.add (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there .here)))))
        (.app (.app mulT (.var (.there (.there (.there (.there (.there .here)))))))
          (.var (.there .here))))
      (.eq (.var (.there (.there (.there (.there .here)))))
        (.app (.app mulT (.var (.there (.there (.there (.there (.there .here)))))))
          (.var (.there (.there .here)))))) ?_
    refine Deriv.transE (Deriv.congArg _ (Deriv.symmE Deriv.ax)) ?_
    refine Deriv.transE (distribLT _ (.var (.there .here)) (.succ (.var .here))) ?_
    refine Deriv.transE (Deriv.congAddL _ (Deriv.symmE (Deriv.ax2 (.eq (.add (.var (.there .here)) (.succ (.var .here)))
        (.var (.there (.there .here))))
      (.ex .nat (.eq (.add (.var (.there (.there .here))) (.succ (.var .here)))
        (.var (.there (.there (.there .here))))))
      (.eq (.add (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there .here)))))
        (.app (.app mulT (.var (.there (.there (.there (.there (.there .here)))))))
          (.var (.there .here))))))) ?_
    exact Deriv.transE (plusAssocT _ _ _) (Deriv.eqRefl _)


/-- Term form of `dvdAddD`. -/
def dvdAddT {Γ as : List Ty} {Δ : Ctx Γ as} (d x y : Tm Γ .nat) :
    Deriv Δ (.imp (.ex .nat (.eq (x.wk) (.app (.app mulT (d.wk)) (.var .here))))
      (.imp (.ex .nat (.eq (y.wk) (.app (.app mulT (d.wk)) (.var .here))))
        (.ex .nat (.eq (.add (x.wk) (y.wk))
          (.app (.app mulT (d.wk)) (.var .here)))))) := by
  have h := Deriv.allE y (Deriv.allE x (Deriv.allE d (dvdAddD (Δ := Δ))))
  simp only [Ctx.wk_cons, Ctx.wk_nil, Dvd, Formula.wk,
      Formula.rename, Formula.subst1, Formula.subst, Tm.wk, Tm.rename,
      Tm.subst1, Tm.subst, Sub.one, Sub.ext, Ren.wk, Ren.ext,
      mulT_subst, mulT_rename, Tm.wk_subst_ext, Tm.wk_subst_one,
      subst_one_rename, subst_ext_rename] at h
  exact h

/-- Term form of `dvdSubD`. -/
def dvdSubT {Γ as : List Ty} {Δ : Ctx Γ as} (d x y : Tm Γ .nat) :
    Deriv Δ (.imp (.ex .nat (.eq (x.wk) (.app (.app mulT (d.wk)) (.var .here))))
      (.imp (.ex .nat (.eq (.add (x.wk) (y.wk))
          (.app (.app mulT (d.wk)) (.var .here))))
        (.ex .nat (.eq (y.wk) (.app (.app mulT (d.wk)) (.var .here)))))) := by
  have h := Deriv.allE y (Deriv.allE x (Deriv.allE d (dvdSubD (Δ := Δ))))
  simp only [Ctx.wk_cons, Ctx.wk_nil, Dvd, Formula.wk,
      Formula.rename, Formula.subst1, Formula.subst, Tm.wk, Tm.rename,
      Tm.subst1, Tm.subst, Sub.one, Sub.ext, Ren.wk, Ren.ext,
      mulT_subst, mulT_rename, Tm.wk_subst_ext, Tm.wk_subst_one,
      subst_one_rename, subst_ext_rename] at h
  exact h

end HAomega
