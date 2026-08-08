/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Gcd

/-!
# gcd stage 2, layer 1: the arithmetic the full specification needs

The full gcd theorem — `∀a∀b. ∃g. g∣a ∧ g∣b ∧ ∀d.(d∣a → d∣b → d∣g)` by
induction on the fuel `a + b` — consumes an algebra layer the elementary
fragment does not ship with.  This file builds it as **derivations**:

* the missing congruences (`congSucc`, `congAddL` — `congAddR`/`congFun`/
  `congArg` already exist), each an instance of the one Leibniz rule;
* the four addition laws: `zeroPlusD`, `succPlusD` (the mirrors of the
  primitive conversions, by `ind`), `plusCommD`, `plusAssocD`;
* `mulSuccD` (`a·(x+1) = a + a·x`), completing `mulZero`/`mulOne`'s chain kit;
* `caseNatD` (`∀v. v = 0 ∨ ∃w. v = S w`) — the case-split device.

Compare `Realizability/Common/StrongInduction.lean` + `Euclid.lean` in the
first-order repo: the same facts there need the naive-substitution dodges and
per-symbol congruence schemas.  Here `plusCommD` is eleven lines.

## Still open for stage 2 (in dependency order)

`cancelAddD` (right cancellation, by `ind` + `succInj`) → `addEqZeroD` →
`distribLD` (`d·(x+y) = d·x + d·y`, by `ind` on `y` with the AC laws) →
trichotomy (`∀a∀b. (∃s. a+s=b) ∨ (∃s. b+S s=a)`) → `dvdAdd`/`dvdSub` → the
fueled main induction (`φ(m) := ∀a∀b∀c. (a+b)+c = m → ∃g. spec`).  The route
is fixed and nothing needs new machinery; it is assembly work at the scale of
`pasTotal`, and it is **not claimed** until done.

## Elaboration note

Instantiating a ∀-lemma against a computed goal (`allE` under `symmE`) makes
the unifier invert `Formula.subst1 ?φ u` — impossible.  Bind the
instantiation with `have` first (bottom-up elaboration, `φ` known), then
`exact`.  This is the formula-level twin of the explicit-chain discipline.
-/

namespace HAomega

section
variable {Γ as : List Ty} {Δ : Ctx Γ as}

/-- Congruence under `succ` — the Leibniz pattern. -/
def Deriv.congSucc {x y : Tm Γ .nat} (h : Deriv Δ (.eq x y)) :
    Deriv Δ (.eq (.succ x) (.succ y)) := by
  have hs : ∀ u : Tm Γ .nat,
      (Formula.eq (.succ (Tm.var .here)) ((Tm.succ x).wk)).subst1 u
        = Formula.eq (.succ u) (.succ x) := by
    intro u
    show Formula.eq (.succ u) (((Tm.succ x).wk).subst1 u) = _
    rw [Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.succ (Tm.var .here)) ((Tm.succ x).wk)) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

/-- Congruence in `add`'s left argument. -/
def Deriv.congAddL (a : Tm Γ .nat) {x y : Tm Γ .nat} (h : Deriv Δ (.eq x y)) :
    Deriv Δ (.eq (.add x a) (.add y a)) := by
  have hs : ∀ u : Tm Γ .nat,
      (Formula.eq (.add (Tm.var .here) (a.wk)) ((Tm.add x a).wk)).subst1 u
        = Formula.eq (.add u a) (.add x a) := by
    intro u
    show Formula.eq (.add u ((a.wk).subst1 u)) (((Tm.add x a).wk).subst1 u) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.add (Tm.var .here) (a.wk)) ((Tm.add x a).wk)) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

end

/-- `∀a. 0 + a = a` — the mirror of primitive `convAddZero`, by `ind`. -/
def zeroPlusD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.eq (.add .zero (.var .here)) (.var .here))) := by
  refine Deriv.ind (Deriv.convAddZero .zero) ?_
  refine Deriv.allI (Deriv.impI ?_)
  exact Deriv.transE (Deriv.convAddSucc _ _) (Deriv.congSucc Deriv.ax)

/-- `∀a ∀b. S a + b = S (a + b)`. -/
def succPlusD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat
      (.eq (.add (.succ (.var (.there .here))) (.var .here))
        (.succ (.add (.var (.there .here)) (.var .here)))))) := by
  refine Deriv.allI ?_
  refine Deriv.ind ?_ ?_
  · exact Deriv.transE (Deriv.convAddZero _)
      (Deriv.symmE (Deriv.congSucc (Deriv.convAddZero _)))
  · refine Deriv.allI (Deriv.impI ?_)
    exact Deriv.transE (Deriv.convAddSucc _ _)
      (Deriv.transE (Deriv.congSucc Deriv.ax)
        (Deriv.symmE (Deriv.congSucc (Deriv.convAddSucc _ _))))

/-- `∀a ∀b. a + b = b + a`. -/
def plusCommD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat
      (.eq (.add (.var (.there .here)) (.var .here))
        (.add (.var .here) (.var (.there .here)))))) := by
  refine Deriv.allI ?_
  refine Deriv.ind ?_ ?_
  · exact Deriv.transE (Deriv.convAddZero _)
      (Deriv.symmE (Deriv.allE (.var .here) zeroPlusD))
  · refine Deriv.allI (Deriv.impI ?_)
    refine Deriv.transE (Deriv.convAddSucc _ _) ?_
    refine Deriv.transE (Deriv.congSucc Deriv.ax) ?_
    have hsp := Deriv.allE (.var (.there .here))
      (Deriv.allE (.var .here) (succPlusD (Γ := .nat :: .nat :: Γ)
        (Δ := .cons (.eq (.add (.var (.there .here)) (.var .here))
          (.add (.var .here) (.var (.there .here)))) ((Ctx.wk Δ).wk))))
    exact Deriv.symmE hsp

/-- `∀a ∀b ∀c. (a + b) + c = a + (b + c)`. -/
def plusAssocD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.all .nat
      (.eq (.add (.add (.var (.there (.there .here))) (.var (.there .here)))
        (.var .here))
        (.add (.var (.there (.there .here)))
          (.add (.var (.there .here)) (.var .here))))))) := by
  refine Deriv.allI (Deriv.allI ?_)
  refine Deriv.ind ?_ ?_
  · exact Deriv.transE (Deriv.convAddZero _)
      (Deriv.symmE (Deriv.congAddR _ (Deriv.convAddZero _)))
  · refine Deriv.allI (Deriv.impI ?_)
    refine Deriv.transE (Deriv.convAddSucc _ _) ?_
    refine Deriv.transE (Deriv.congSucc Deriv.ax) ?_
    refine Deriv.symmE ?_
    exact Deriv.transE (Deriv.congAddR _ (Deriv.convAddSucc _ _))
      (Deriv.convAddSucc _ _)


/-- `∀a x. a · (x+1) = a + a · x` — completing the `mul` chain kit. -/
def mulSuccD {Γ as : List Ty} {Δ : Ctx Γ as} (a x : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app mulT a) (.succ x)) (.add a (.app (.app mulT a) x))) :=
  Deriv.transE (mulUnfold a (.succ x))
    (Deriv.transE (Deriv.convRecSucc _ _ _)
      (Deriv.transE (mulStepApp a x (.recNat .zero (mulStep a) x))
        (Deriv.congAddR a (Deriv.symmE (mulUnfold a x)))))

/-- `∀v. v = 0 ∨ ∃w. v = S w` — the case-split device, hypothesis discarded. -/
def caseNatD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.or (.eq (.var .here) .zero)
      (.ex .nat (.eq (.var (.there .here)) (.succ (.var .here)))))) := by
  refine Deriv.ind (Deriv.orI₁ (Deriv.eqRefl .zero)) ?_
  refine Deriv.allI (Deriv.impI ?_)
  exact Deriv.orI₂ (Deriv.exI (.var .here) (Deriv.eqRefl _))

#print axioms plusCommD
#print axioms plusAssocD
#print axioms mulSuccD
#print axioms caseNatD

end HAomega
