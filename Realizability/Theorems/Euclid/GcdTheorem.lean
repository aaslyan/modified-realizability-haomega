/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Euclid.Euclid

/-!
# Phase E2 (Euclid), the theorem: greatest common divisor as an existential

    ⊢ ∀a ∀b. ∃g. g ∣ a  ∧  g ∣ b  ∧  ∀d. (d ∣ a → d ∣ b → d ∣ g)

as a closed derivation of the fragment.  The extracted witness `g` **is**
the gcd — no `gcd` symbol, the same witness-carrying design as Goodstein
and Hanoi.

## The argument: subtractive Euclid, by strong induction on `a + b`

The subtractive Euclidean algorithm recurses `gcd(a,b) → gcd(a, b−a)`
when `0 < a ≤ b` and `gcd(a,b) → gcd(a−b, b)` when `0 < b < a`.  Neither
argument decreases every step, but the **sum** does: `a + (b−a) = b <
a + b` and `(a−b) + b = a < a + b`.  So the induction is course-of-values
on the sum, with predicate

    φ(m)  :=  ∀a ∀b. (a + b = m) → ∃g. spec(a, b, g).

Strong induction is not primitive here; it is **derived** from `ind`
(`StrongInduction.lean`), and this file inlines that scaffold at the
concrete φ — the `Aux(v) := ∀y. y < v → φ(y)` construction, run by `ind`,
with progressiveness applied at the point and `ltStepDown` closing the
descent.  Everything computes, so no generic strong-induction former and
no formula-substitution lemmas are needed.

## No positivity precondition

The roadmap's stated form carried a precondition `(a > 0 ∨ b > 0)`.  It
is **unnecessary**: `spec(0, 0, 0)` holds — `0 ∣ 0`, and `∀d. d ∣ 0 →
d ∣ 0 → d ∣ 0` is trivial because *everything* divides `0` — so the
convention `gcd(0,0) = 0` (Lean's own `Nat.gcd 0 0 = 0`) realizes the
predicate at the origin.  The delivered theorem is therefore the stronger
`∀a ∀b. ∃g. spec`, and the base case `a = 0` returns `g := b`
unconditionally.  (Recorded in docs/internal/QUESTIONS.md.)

## The two places naive substitution bites

The recursion instantiates the induction hypothesis at the sub-pair's
*sum*, a term mentioning the bound `a`, and then instantiates φ there at
the *sub-pair*, terms again mentioning `a`.  Both capture under the
fragment's naive substitution, and both are dodged exactly as the earlier
phases dodge them:

* the sub-sum is **named** by a fresh `∀w. (w = subsum) → …` (Goodstein's
  `namedIHDeriv` device), so the induction hypothesis is instantiated at a
  variable; and
* φ's inner `∀a ∀b` is **α-renamed** before the sub-pair is plugged in
  (Hanoi's `ihRenamed` device).

## Variable convention

Scaffold (fixed by `StrongInduction.lean`): `0 = v` (measure point),
`1 = y` (`Aux` binder), `2 = z` (progressiveness binder, doubling as
trichotomy's `≤`-difference `r`), `3` and `4` order-difference variables.
φ-internal: `8 = a`, `9 = b`, `10 = g`, `11 = d`, `12` the divisibility
quotient.  `13`/`14` the renamed `caseNat` predecessors `a'`/`b'`, `15`/`16`
the α-renamed inner binders, `17 = w` the naming variable.  The divisibility
lemmas of `Euclid.lean` emit quotient variables in `{1,3,4,5,6,7}`, all kept
clear of the term variables above; `dvdRename` bridges to the quotient `12`
this file uses.
-/

namespace Realizability

open ContinuousFunctionals

/-! ## Commutativity of `+`

`Arithmetic.lean` proved right-commutativity `(z+x)+y = (z+y)+x` but not
plain commutativity; the measure descent needs it (`b < a + b` from
`a = succ a'`).  One instantiation of `plusRightCommDeriv` at `z := 0`. -/

/-- **`∀x ∀y. x + y = y + x`**, from `plusRightCommDeriv` at `z = 0`
(`(0+x)+y = (0+y)+x`, then `zeroPlus` on both sides).  Binds `18`, `19` to
stay clear of every term variable this file instantiates it at. -/
def plusCommDeriv :
    Deriv [] (.all 18 (.all 19 (.eq (.plus (.var 18) (.var 19))
      (.plus (.var 19) (.var 18))))) := by
  refine Deriv.allI (Deriv.allI ?_ (freshIn_nil 19)) (freshIn_nil 18)
  have hrc : Deriv [] (.eq (.plus (.plus .zero (.var 18)) (.var 19))
      (.plus (.plus .zero (.var 19)) (.var 18))) :=
    Deriv.allE (.var 19) (Deriv.allE (.var 18) (Deriv.allE .zero plusRightCommDeriv
      (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
      (substOK_of_forall (by decide))
  have hl : Deriv [] (.eq (.plus (.plus .zero (.var 18)) (.var 19))
      (.plus (.var 18) (.var 19))) :=
    Deriv.congPlusL (.var 19) (Deriv.zeroPlus (.var 18))
  have hr : Deriv [] (.eq (.plus (.plus .zero (.var 19)) (.var 18))
      (.plus (.var 19) (.var 18))) :=
    Deriv.congPlusL (.var 18) (Deriv.zeroPlus (.var 19))
  exact (Deriv.symmE hl).transE (hrc.transE hr)

/-! ## The specification and the induction predicate -/

/-- `d ∣ a`, with the fixed quotient variable `12`; literally
`Euclid.dvdT 12`, so it interoperates with `dvdAddDeriv`/`dvdSubDeriv`
(whose quotient variables live in `{3,4,5,6,7}`). -/
abbrev dvdTm (d a : Term) : Formula := dvdT 12 d a

/-- `spec(a, b, g) := g ∣ a ∧ g ∣ b ∧ ∀d. (d ∣ a → d ∣ b → d ∣ g)`. -/
abbrev gcdSpecT (a b g : Term) : Formula :=
  (dvdTm g a).and ((dvdTm g b).and
    (.all 11 ((dvdTm (.var 11) a).imp ((dvdTm (.var 11) b).imp (dvdTm (.var 11) g)))))

/-- The induction predicate `φ(m) := ∀a ∀b. (a + b = m) → ∃g. spec(a,b,g)`,
with the measure the variable `m`. -/
abbrev phiG (m : ℕ) : Formula :=
  .all 8 (.all 9 ((Formula.eq (.plus (.var 8) (.var 9)) (.var m)).imp
    (.ex 10 (gcdSpecT (.var 8) (.var 9) (.var 10)))))

/-! ## The strong-induction scaffold, at the concrete φ

Mirrors `demoAux`/`demoProg`/`demoAuxDeriv`/`strongIndDemo` of
`StrongInduction.lean` line for line; the only φ-specific content is
`gcdProgDeriv` (progressiveness, i.e. the subtractive-Euclid step) and, in
the base of `gcdAuxDeriv`, the use of `ltZeroElim` where the demo could use
reflexivity. -/

/-- `Aux(v) := ∀y. y < v → φ(y)`. -/
abbrev gcdAux : Formula := .all 1 ((ltT 4 (.var 1) (.var 0)).imp (phiG 1))

/-- Progressiveness' antecedent `∀z. z < v → φ(z)`. -/
abbrev gcdProgAnt : Formula := .all 2 ((ltT 3 (.var 2) (.var 0)).imp (phiG 2))

/-- Progressiveness `∀v. ((∀z. z < v → φ(z)) → φ(v))`. -/
abbrev gcdProg : Formula := .all 0 (gcdProgAnt.imp (phiG 0))

/-- **Progressiveness of φ** — the subtractive-Euclid step.  Filled below. -/
def gcdProgDeriv : Deriv [] gcdProg := by
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_)
    (by decide +kernel)) (by decide +kernel))) (freshIn_nil 0)
  -- context: [ hsum : a + b = v , IH : gcdProgAnt ];  goal `∃g. spec(a,b,g)`
  -- (a = var 8, b = var 9, v = var 0)
  refine Deriv.orE (Deriv.allE (.var 8) (Deriv.wkNil _ caseNatDeriv)
    (substOK_of_forall (by decide))) ?a0 ?aS
  · -- a = 0 : the gcd is `b`
    -- context: [ ha : a = 0 , hsum , IH ];  witness g := b (= var 9)
    refine Deriv.exI (.var 9) ?_ (substOK_of_forall (by decide))
    -- goal: spec(a, b, b)
    have ha : Deriv [Formula.eq (.var 8) .zero, Formula.eq (.plus (.var 8) (.var 9)) (.var 0),
        gcdProgAnt] (Formula.eq (.var 8) .zero) := .ax
    refine Deriv.andI ?_ (Deriv.andI ?_ ?_)
    · -- b ∣ a : quotient 0, since a = 0 = b·0
      refine Deriv.exI .zero ?_ (substOK_of_forall (by decide))
      exact ha.transE (Deriv.symmE (Deriv.allE (.var 9) (Deriv.wkNil _ timesZeroDeriv)
        (substOK_of_forall (by decide))))
    · -- b ∣ b : quotient 1
      refine Deriv.exI (.succ .zero) ?_ (substOK_of_forall (by decide))
      have hbb : Deriv [Formula.eq (.var 8) .zero, Formula.eq (.plus (.var 8) (.var 9)) (.var 0),
          gcdProgAnt] (Formula.eq (.times (.var 9) (.succ .zero)) (.var 9)) :=
        ((Deriv.allE .zero (Deriv.allE (.var 9) (Deriv.wkNil _ timesSuccDeriv)
            (substOK_of_forall (by decide))) (substOK_of_forall (by decide))).transE
          (Deriv.congPlusL (.var 9) (Deriv.allE (.var 9) (Deriv.wkNil _ timesZeroDeriv)
            (substOK_of_forall (by decide))))).transE (Deriv.zeroPlus (.var 9))
      exact Deriv.symmE hbb
    · -- ∀d. d ∣ a → d ∣ b → d ∣ b
      exact Deriv.allI (Deriv.impI (Deriv.impI Deriv.ax)) (by decide +kernel)
  · -- a = succ a' : rename the predecessor witness 5 → 13, then split on b
    have haS : Deriv [.ex 5 (Formula.eq (.var 8) (.succ (.var 5))),
        Formula.eq (.plus (.var 8) (.var 9)) (.var 0), gcdProgAnt]
        (.ex 13 (Formula.eq (.var 8) (.succ (.var 13)))) :=
      Deriv.exE Deriv.ax (Deriv.exI (.var 5) Deriv.ax (substOK_of_forall (by decide)))
        (by decide +kernel) (by decide +kernel)
    refine Deriv.exE haS ?_ (by decide +kernel) (by decide +kernel)
    -- context: [ ha13 : a = succ a' , (∃13 …) , hsum , IH ]  (a' = var 13)
    refine Deriv.orE (Deriv.allE (.var 9) (Deriv.wkNil _ caseNatDeriv)
      (substOK_of_forall (by decide))) ?b0 ?bS
    · -- b = 0 : the gcd is `a` (= var 8)
      refine Deriv.exI (.var 8) ?_ (substOK_of_forall (by decide))
      refine Deriv.andI ?_ (Deriv.andI ?_ ?_)
      · -- a ∣ a : quotient 1
        refine Deriv.exI (.succ .zero) ?_ (substOK_of_forall (by decide))
        exact Deriv.symmE (((Deriv.allE .zero (Deriv.allE (.var 8)
          (Deriv.wkNil _ timesSuccDeriv) (substOK_of_forall (by decide)))
          (substOK_of_forall (by decide))).transE (Deriv.congPlusL (.var 8)
            (Deriv.allE (.var 8) (Deriv.wkNil _ timesZeroDeriv)
              (substOK_of_forall (by decide))))).transE (Deriv.zeroPlus (.var 8)))
      · -- a ∣ b : b = 0, quotient 0
        refine Deriv.exI .zero ?_ (substOK_of_forall (by decide))
        exact Deriv.ax.transE (Deriv.symmE (Deriv.allE (.var 8)
          (Deriv.wkNil _ timesZeroDeriv) (substOK_of_forall (by decide))))
      · -- ∀d. d ∣ a → d ∣ b → d ∣ a
        exact Deriv.allI (Deriv.impI (Deriv.impI (Deriv.wk Deriv.ax))) (by decide +kernel)
    · -- b = succ b' : both positive.  Rename predecessor 5 → 14, compare.
      have hbS : Deriv [.ex 5 (Formula.eq (.var 9) (.succ (.var 5))),
          Formula.eq (.var 8) (.succ (.var 13)),
          .ex 5 (Formula.eq (.var 8) (.succ (.var 5))),
          Formula.eq (.plus (.var 8) (.var 9)) (.var 0), gcdProgAnt]
          (.ex 14 (Formula.eq (.var 9) (.succ (.var 14)))) :=
        Deriv.exE Deriv.ax (Deriv.exI (.var 5) Deriv.ax (substOK_of_forall (by decide)))
          (by decide +kernel) (by decide +kernel)
      refine Deriv.exE hbS ?_ (by decide +kernel) (by decide +kernel)
      -- trichotomy on (a, b) = (var 8, var 9)
      refine Deriv.orE (Deriv.allE (.var 9) (Deriv.allE (.var 8)
        (Deriv.wkNil _ trichotomyDeriv) (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide))) ?le ?lt
      · -- a ≤ b : `b = a + r`, recurse on (a, r); sub-sum a + r = b < a + b
        refine Deriv.exE Deriv.ax ?_ (by decide +kernel) (by decide +kernel)
        set Δ : List Formula :=
          [Formula.eq (.plus (.var 8) (.var 2)) (.var 9),
           leT 2 (.var 8) (.var 9),
           Formula.eq (.var 9) (.succ (.var 14)),
           .ex 5 (Formula.eq (.var 9) (.succ (.var 5))),
           Formula.eq (.var 8) (.succ (.var 13)),
           .ex 5 (Formula.eq (.var 8) (.succ (.var 5))),
           Formula.eq (.plus (.var 8) (.var 9)) (.var 0), gcdProgAnt] with hΔ
        have hr : Deriv Δ (Formula.eq (.plus (.var 8) (.var 2)) (.var 9)) := Deriv.ax
        have ha13d : Deriv Δ (Formula.eq (.var 8) (.succ (.var 13))) :=
          Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax)))
        have hsumd : Deriv Δ (Formula.eq (.plus (.var 8) (.var 9)) (.var 0)) :=
          Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax)))))
        have IHd : Deriv Δ gcdProgAnt :=
          Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))))))
        -- descent: succ (a + r) + a' = a + b = v
        have hcomm : Deriv Δ (Formula.eq (.plus (.var 9) (.var 13))
            (.plus (.var 13) (.var 9))) :=
          Deriv.allE (.var 13) (Deriv.allE (.var 9) (Deriv.wkNil _ plusCommDeriv)
            (substOK_of_forall (by decide))) (substOK_of_forall (by decide))
        have Dlt : Deriv Δ (ltT 4 (.plus (.var 8) (.var 2)) (.var 0)) := by
          refine Deriv.exI (.var 13) ?_ (substOK_of_forall (by decide))
          exact ((((Deriv.congPlusL (.var 13) (Deriv.congSuccE hr)).transE
              (Deriv.succPlus (.var 9) (.var 13))).transE
              (Deriv.congSuccE hcomm)).transE
              (Deriv.symmE (Deriv.succPlus (.var 13) (.var 9)))).transE
              ((Deriv.congPlusL (.var 9) (Deriv.symmE ha13d)).transE hsumd)
        -- recurse: sub-pair (a, r) has a gcd (naming + α-rename)
        have hsub : Deriv Δ (.ex 10 (gcdSpecT (.var 8) (.var 2) (.var 10))) := by
          have hnamed : Deriv Δ (.all 17 ((Formula.eq (.var 17)
              (.plus (.var 8) (.var 2))).imp
              (.ex 10 (gcdSpecT (.var 8) (.var 2) (.var 10))))) := by
            refine Deriv.allI (Deriv.impI ?_) (by decide +kernel)
            set Δ2 : List Formula :=
              Formula.eq (.var 17) (.plus (.var 8) (.var 2)) :: Δ with hΔ2
            have hw : Deriv Δ2 (Formula.eq (.var 17) (.plus (.var 8) (.var 2))) := Deriv.ax
            have hIHat : Deriv Δ2 ((ltT 3 (.var 17) (.var 0)).imp (phiG 17)) :=
              Deriv.allE (.var 17) (Deriv.wk IHd) (substOK_of_forall (by decide))
            have hlt17 : Deriv Δ2 (ltT 3 (.var 17) (.var 0)) := by
              refine Deriv.exE (Deriv.wk Dlt) ?_ (by decide +kernel) (by decide +kernel)
              refine Deriv.exI (.var 4) ?_ (substOK_of_forall (by decide))
              exact (Deriv.congPlusL (.var 4) (Deriv.congSuccE (Deriv.wk hw))).transE
                Deriv.ax
            have hphi17 : Deriv Δ2 (phiG 17) := Deriv.impE hIHat hlt17
            have hren : Deriv Δ2 (.all 15 (.all 16 ((Formula.eq
                (.plus (.var 15) (.var 16)) (.var 17)).imp
                (.ex 10 (gcdSpecT (.var 15) (.var 16) (.var 10)))))) := by
              refine Deriv.allI (Deriv.allI ?_ (by decide +kernel)) (by decide +kernel)
              exact Deriv.allE (.var 16) (Deriv.allE (.var 15) hphi17
                (substOK_of_forall (by decide))) (substOK_of_forall (by decide))
            have hinst : Deriv Δ2 ((Formula.eq (.plus (.var 8) (.var 2)) (.var 17)).imp
                (.ex 10 (gcdSpecT (.var 8) (.var 2) (.var 10)))) :=
              Deriv.allE (.var 2) (Deriv.allE (.var 8) hren
                (substOK_of_forall (by decide))) (substOK_of_forall (by decide))
            exact Deriv.impE hinst (Deriv.symmE hw)
          exact Deriv.impE (Deriv.allE (.plus (.var 8) (.var 2)) hnamed
            (substOK_of_forall (by decide))) (Deriv.eqRefl (.plus (.var 8) (.var 2)))
        -- recombine spec(a, r, g) into spec(a, b, g), using r + a = b
        refine Deriv.exE hsub ?_ (by decide +kernel) (by decide +kernel)
        set Δ3 : List Formula := gcdSpecT (.var 8) (.var 2) (.var 10) :: Δ with hΔ3
        refine Deriv.exI (.var 10) ?_ (substOK_of_forall (by decide))
        have subspec : Deriv Δ3 (gcdSpecT (.var 8) (.var 2) (.var 10)) := Deriv.ax
        have hrd : Deriv Δ3 (Formula.eq (.plus (.var 8) (.var 2)) (.var 9)) := Deriv.wk hr
        have hga : Deriv Δ3 (dvdTm (.var 10) (.var 8)) := Deriv.andE₁ subspec
        have hgr : Deriv Δ3 (dvdTm (.var 10) (.var 2)) :=
          Deriv.andE₁ (Deriv.andE₂ subspec)
        have hgreat : Deriv Δ3 (.all 11 ((dvdTm (.var 11) (.var 8)).imp
            ((dvdTm (.var 11) (.var 2)).imp (dvdTm (.var 11) (.var 10))))) :=
          Deriv.andE₂ (Deriv.andE₂ subspec)
        refine Deriv.andI hga (Deriv.andI ?gb ?great)
        · -- g ∣ b : g ∣ a and g ∣ r give g ∣ (a + r) = b
          have hga3 : Deriv Δ3 (dvdT 3 (.var 10) (.var 8)) := by
            refine Deriv.exE hga ?_ (by decide +kernel) (by decide +kernel)
            exact Deriv.exI (.var 12) Deriv.ax (substOK_of_forall (by decide))
          have hgr4 : Deriv Δ3 (dvdT 4 (.var 10) (.var 2)) := by
            refine Deriv.exE hgr ?_ (by decide +kernel) (by decide +kernel)
            exact Deriv.exI (.var 12) Deriv.ax (substOK_of_forall (by decide))
          have hgadd : Deriv Δ3 (dvdT 5 (.var 10) (.plus (.var 8) (.var 2))) :=
            Deriv.impE (Deriv.impE (Deriv.allE (.var 2) (Deriv.allE (.var 8)
              (Deriv.allE (.var 10) (Deriv.wkNil _ dvdAddDeriv)
                (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
              (substOK_of_forall (by decide))) hga3) hgr4
          refine Deriv.exE hgadd ?_ (by decide +kernel) (by decide +kernel)
          refine Deriv.exI (.var 5) ?_ (substOK_of_forall (by decide))
          exact (Deriv.symmE (Deriv.wk hrd)).transE Deriv.ax
        · -- greatest: any common divisor of a, b divides g
          refine Deriv.allI (Deriv.impI (Deriv.impI ?_)) (by decide +kernel)
          set Δ4 : List Formula :=
            dvdTm (.var 11) (.var 9) :: dvdTm (.var 11) (.var 8) :: Δ3 with hΔ4
          have h1 : Deriv Δ4 (dvdTm (.var 11) (.var 8)) := Deriv.wk Deriv.ax
          have h2 : Deriv Δ4 (dvdTm (.var 11) (.var 9)) := Deriv.ax
          have hrd4 : Deriv Δ4 (Formula.eq (.plus (.var 8) (.var 2)) (.var 9)) :=
            Deriv.wk (Deriv.wk hrd)
          have hgreat4 : Deriv Δ4 (.all 11 ((dvdTm (.var 11) (.var 8)).imp
              ((dvdTm (.var 11) (.var 2)).imp (dvdTm (.var 11) (.var 10))))) :=
            Deriv.wk (Deriv.wk hgreat)
          have h1' : Deriv Δ4 (dvdT 5 (.var 11) (.var 8)) := by
            refine Deriv.exE h1 ?_ (by decide +kernel) (by decide +kernel)
            exact Deriv.exI (.var 12) Deriv.ax (substOK_of_forall (by decide))
          have hda : Deriv Δ4 (dvdT 6 (.var 11) (.plus (.var 8) (.var 2))) := by
            refine Deriv.exE h2 ?_ (by decide +kernel) (by decide +kernel)
            refine Deriv.exI (.var 12) ?_ (substOK_of_forall (by decide))
            exact (Deriv.wk hrd4).transE Deriv.ax
          have hdr : Deriv Δ4 (dvdT 7 (.var 11) (.var 2)) :=
            Deriv.impE (Deriv.impE (Deriv.allE (.var 2) (Deriv.allE (.var 8)
              (Deriv.allE (.var 11) (Deriv.wkNil _ dvdSubDeriv)
                (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
              (substOK_of_forall (by decide))) h1') hda
          have hdr12 : Deriv Δ4 (dvdTm (.var 11) (.var 2)) := by
            refine Deriv.exE hdr ?_ (by decide +kernel) (by decide +kernel)
            exact Deriv.exI (.var 7) Deriv.ax (substOK_of_forall (by decide))
          exact Deriv.impE (Deriv.impE (Deriv.allE (.var 11) hgreat4
            (substOK_of_forall (by decide))) h1) hdr12
      · -- b < a : `succ b + s = a`, i.e. `b + succ s = a`; recurse on (b, succ s).
        -- Rename the difference variable 3 → 2, so `succ s` avoids the
        -- divisibility lemmas' quotient variables `{3,4,5,6,7}`.
        have hlt2 : Deriv [ltT 3 (.var 9) (.var 8),
            Formula.eq (.var 9) (.succ (.var 14)),
            .ex 5 (Formula.eq (.var 9) (.succ (.var 5))),
            Formula.eq (.var 8) (.succ (.var 13)),
            .ex 5 (Formula.eq (.var 8) (.succ (.var 5))),
            Formula.eq (.plus (.var 8) (.var 9)) (.var 0), gcdProgAnt]
            (.ex 2 (Formula.eq (.plus (.succ (.var 9)) (.var 2)) (.var 8))) :=
          Deriv.exE Deriv.ax (Deriv.exI (.var 3) Deriv.ax (substOK_of_forall (by decide)))
            (by decide +kernel) (by decide +kernel)
        refine Deriv.exE hlt2 ?_ (by decide +kernel) (by decide +kernel)
        set Δ : List Formula :=
          [Formula.eq (.plus (.succ (.var 9)) (.var 2)) (.var 8),
           ltT 3 (.var 9) (.var 8),
           Formula.eq (.var 9) (.succ (.var 14)),
           .ex 5 (Formula.eq (.var 9) (.succ (.var 5))),
           Formula.eq (.var 8) (.succ (.var 13)),
           .ex 5 (Formula.eq (.var 8) (.succ (.var 5))),
           Formula.eq (.plus (.var 8) (.var 9)) (.var 0), gcdProgAnt] with hΔ
        have hs : Deriv Δ (Formula.eq (.plus (.succ (.var 9)) (.var 2)) (.var 8)) := Deriv.ax
        have hb14d : Deriv Δ (Formula.eq (.var 9) (.succ (.var 14))) :=
          Deriv.wk (Deriv.wk Deriv.ax)
        have hsumd : Deriv Δ (Formula.eq (.plus (.var 8) (.var 9)) (.var 0)) :=
          Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax)))))
        have IHd : Deriv Δ gcdProgAnt :=
          Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))))))
        -- `b + succ s = a`  (no commutativity: peel the `succ` on either side)
        have hab2 : Deriv Δ (Formula.eq (.plus (.var 9) (.succ (.var 2))) (.var 8)) :=
          (Deriv.allE (.var 2) (Deriv.allE (.var 9) (Deriv.wkNil _ plusSuccDeriv)
            (substOK_of_forall (by decide))) (substOK_of_forall (by decide))).transE
            ((Deriv.symmE (Deriv.succPlus (.var 9) (.var 2))).transE hs)
        -- descent: succ (b + succ s) + b' = a + b = v
        have Dlt : Deriv Δ (ltT 4 (.plus (.var 9) (.succ (.var 2))) (.var 0)) := by
          refine Deriv.exI (.var 14) ?_ (substOK_of_forall (by decide))
          exact ((((Deriv.succPlus (.plus (.var 9) (.succ (.var 2))) (.var 14)).transE
              (Deriv.congSuccE (Deriv.congPlusL (.var 14) hab2))).transE
              (Deriv.symmE (Deriv.allE (.var 14) (Deriv.allE (.var 8)
                (Deriv.wkNil _ plusSuccDeriv) (substOK_of_forall (by decide)))
                (substOK_of_forall (by decide))))).transE
              (Deriv.congPlusR (.var 8) (Deriv.symmE hb14d))).transE hsumd
        -- recurse: sub-pair (b, succ s) has a gcd (naming + α-rename)
        have hsub : Deriv Δ (.ex 10 (gcdSpecT (.var 9) (.succ (.var 2)) (.var 10))) := by
          have hnamed : Deriv Δ (.all 17 ((Formula.eq (.var 17)
              (.plus (.var 9) (.succ (.var 2)))).imp
              (.ex 10 (gcdSpecT (.var 9) (.succ (.var 2)) (.var 10))))) := by
            refine Deriv.allI (Deriv.impI ?_) (by decide +kernel)
            set Δ2 : List Formula :=
              Formula.eq (.var 17) (.plus (.var 9) (.succ (.var 2))) :: Δ with hΔ2
            have hw : Deriv Δ2 (Formula.eq (.var 17) (.plus (.var 9) (.succ (.var 2)))) :=
              Deriv.ax
            have hIHat : Deriv Δ2 ((ltT 3 (.var 17) (.var 0)).imp (phiG 17)) :=
              Deriv.allE (.var 17) (Deriv.wk IHd) (substOK_of_forall (by decide))
            have hlt17 : Deriv Δ2 (ltT 3 (.var 17) (.var 0)) := by
              refine Deriv.exE (Deriv.wk Dlt) ?_ (by decide +kernel) (by decide +kernel)
              refine Deriv.exI (.var 4) ?_ (substOK_of_forall (by decide))
              exact (Deriv.congPlusL (.var 4) (Deriv.congSuccE (Deriv.wk hw))).transE
                Deriv.ax
            have hphi17 : Deriv Δ2 (phiG 17) := Deriv.impE hIHat hlt17
            have hren : Deriv Δ2 (.all 15 (.all 16 ((Formula.eq
                (.plus (.var 15) (.var 16)) (.var 17)).imp
                (.ex 10 (gcdSpecT (.var 15) (.var 16) (.var 10)))))) := by
              refine Deriv.allI (Deriv.allI ?_ (by decide +kernel)) (by decide +kernel)
              exact Deriv.allE (.var 16) (Deriv.allE (.var 15) hphi17
                (substOK_of_forall (by decide))) (substOK_of_forall (by decide))
            have hinst : Deriv Δ2 ((Formula.eq (.plus (.var 9) (.succ (.var 2)))
                (.var 17)).imp
                (.ex 10 (gcdSpecT (.var 9) (.succ (.var 2)) (.var 10)))) :=
              Deriv.allE (.succ (.var 2)) (Deriv.allE (.var 9) hren
                (substOK_of_forall (by decide))) (substOK_of_forall (by decide))
            exact Deriv.impE hinst (Deriv.symmE hw)
          exact Deriv.impE (Deriv.allE (.plus (.var 9) (.succ (.var 2))) hnamed
            (substOK_of_forall (by decide))) (Deriv.eqRefl (.plus (.var 9) (.succ (.var 2))))
        -- recombine spec(b, succ s, g) into spec(a, b, g), using b + succ s = a
        refine Deriv.exE hsub ?_ (by decide +kernel) (by decide +kernel)
        set Δ3 : List Formula := gcdSpecT (.var 9) (.succ (.var 2)) (.var 10) :: Δ with hΔ3
        refine Deriv.exI (.var 10) ?_ (substOK_of_forall (by decide))
        have subspec : Deriv Δ3 (gcdSpecT (.var 9) (.succ (.var 2)) (.var 10)) := Deriv.ax
        have hab2d : Deriv Δ3 (Formula.eq (.plus (.var 9) (.succ (.var 2))) (.var 8)) :=
          Deriv.wk hab2
        have hgb : Deriv Δ3 (dvdTm (.var 10) (.var 9)) := Deriv.andE₁ subspec
        have hgs : Deriv Δ3 (dvdTm (.var 10) (.succ (.var 2))) :=
          Deriv.andE₁ (Deriv.andE₂ subspec)
        have hgreat_sub : Deriv Δ3 (.all 11 ((dvdTm (.var 11) (.var 9)).imp
            ((dvdTm (.var 11) (.succ (.var 2))).imp (dvdTm (.var 11) (.var 10))))) :=
          Deriv.andE₂ (Deriv.andE₂ subspec)
        refine Deriv.andI ?gaB (Deriv.andI hgb ?greatB)
        · -- g ∣ a : g ∣ b and g ∣ (succ s) give g ∣ (b + succ s) = a
          have hgb3 : Deriv Δ3 (dvdT 3 (.var 10) (.var 9)) := by
            refine Deriv.exE hgb ?_ (by decide +kernel) (by decide +kernel)
            exact Deriv.exI (.var 12) Deriv.ax (substOK_of_forall (by decide))
          have hgs4 : Deriv Δ3 (dvdT 4 (.var 10) (.succ (.var 2))) := by
            refine Deriv.exE hgs ?_ (by decide +kernel) (by decide +kernel)
            exact Deriv.exI (.var 12) Deriv.ax (substOK_of_forall (by decide))
          have hgadd : Deriv Δ3 (dvdT 5 (.var 10) (.plus (.var 9) (.succ (.var 2)))) :=
            Deriv.impE (Deriv.impE (Deriv.allE (.succ (.var 2)) (Deriv.allE (.var 9)
              (Deriv.allE (.var 10) (Deriv.wkNil _ dvdAddDeriv)
                (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
              (substOK_of_forall (by decide))) hgb3) hgs4
          refine Deriv.exE hgadd ?_ (by decide +kernel) (by decide +kernel)
          refine Deriv.exI (.var 5) ?_ (substOK_of_forall (by decide))
          exact (Deriv.symmE (Deriv.wk hab2d)).transE Deriv.ax
        · -- greatest: any common divisor of a, b divides g
          refine Deriv.allI (Deriv.impI (Deriv.impI ?_)) (by decide +kernel)
          set Δ4 : List Formula :=
            dvdTm (.var 11) (.var 9) :: dvdTm (.var 11) (.var 8) :: Δ3 with hΔ4
          have h1 : Deriv Δ4 (dvdTm (.var 11) (.var 8)) := Deriv.wk Deriv.ax
          have h2 : Deriv Δ4 (dvdTm (.var 11) (.var 9)) := Deriv.ax
          have hab2d4 : Deriv Δ4 (Formula.eq (.plus (.var 9) (.succ (.var 2))) (.var 8)) :=
            Deriv.wk (Deriv.wk (Deriv.wk hab2))
          have hgreat4 : Deriv Δ4 (.all 11 ((dvdTm (.var 11) (.var 9)).imp
              ((dvdTm (.var 11) (.succ (.var 2))).imp (dvdTm (.var 11) (.var 10))))) :=
            Deriv.wk (Deriv.wk hgreat_sub)
          have h2' : Deriv Δ4 (dvdT 5 (.var 11) (.var 9)) := by
            refine Deriv.exE h2 ?_ (by decide +kernel) (by decide +kernel)
            exact Deriv.exI (.var 12) Deriv.ax (substOK_of_forall (by decide))
          have hda : Deriv Δ4 (dvdT 6 (.var 11) (.plus (.var 9) (.succ (.var 2)))) := by
            refine Deriv.exE h1 ?_ (by decide +kernel) (by decide +kernel)
            refine Deriv.exI (.var 12) ?_ (substOK_of_forall (by decide))
            exact (Deriv.wk hab2d4).transE Deriv.ax
          have hds : Deriv Δ4 (dvdT 7 (.var 11) (.succ (.var 2))) :=
            Deriv.impE (Deriv.impE (Deriv.allE (.succ (.var 2)) (Deriv.allE (.var 9)
              (Deriv.allE (.var 11) (Deriv.wkNil _ dvdSubDeriv)
                (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
              (substOK_of_forall (by decide))) h2') hda
          have hds12 : Deriv Δ4 (dvdTm (.var 11) (.succ (.var 2))) := by
            refine Deriv.exE hds ?_ (by decide +kernel) (by decide +kernel)
            exact Deriv.exI (.var 7) Deriv.ax (substOK_of_forall (by decide))
          exact Deriv.impE (Deriv.impE (Deriv.allE (.var 11) hgreat4
            (substOK_of_forall (by decide))) h2) hds12

/-- **`∀v. Aux(v)`, by ordinary induction on `v`.** -/
def gcdAuxDeriv : Deriv [] (.all 0 gcdAux) := by
  refine Deriv.ind ?_ ?_ (substOK_of_forall (by decide))
  · -- base `Aux(0) = ∀y. y < 0 → φ(y)`: `y < 0` is impossible
    refine Deriv.allI (Deriv.impI ?_) (freshIn_nil 1)
    exact ltZeroElim 4 (.var 1) (phiG 1) (by decide) (by decide) Deriv.ax
  · -- step `∀v. Aux(v) → Aux(succ v)`
    refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.impI ?_) (by decide +kernel)))
      (freshIn_nil 0)
    -- context: [ h₁ : y < succ v , Aux(v) ];  goal `φ(y)`
    have hProgAt1 :
        Deriv [ltT 4 (.var 1) (.succ (.var 0)), gcdAux]
          ((gcdProgAnt.subst 0 (.var 1)).imp (phiG 1)) :=
      Deriv.allE (.var 1) (Deriv.wkNil _ gcdProgDeriv) (substOK_of_forall (by decide))
    refine Deriv.impE hProgAt1 ?_
    -- goal `∀z. z < y → φ(z)`
    refine Deriv.allI (Deriv.impI ?_) (by decide +kernel)
    -- context: [ h₂ : z < y , h₁ , Aux(v) ];  goal `φ(z)`
    have hzv : Deriv [ltT 3 (.var 2) (.var 1), ltT 4 (.var 1) (.succ (.var 0)), gcdAux]
        (ltT 4 (.var 2) (.var 0)) :=
      ltStepDown (by decide) (by decide) Deriv.ax (Deriv.wk Deriv.ax)
    have hAuxAt2 :
        Deriv [ltT 3 (.var 2) (.var 1), ltT 4 (.var 1) (.succ (.var 0)), gcdAux]
          ((ltT 4 (.var 2) (.var 0)).imp (phiG 2)) :=
      Deriv.allE (.var 2) (Deriv.wk (Deriv.wk Deriv.ax)) (substOK_of_forall (by decide))
    exact Deriv.impE hAuxAt2 hzv

/-- **`∀v. φ(v)`** — read `φ(v)` off `Aux(succ v)` at `y := v`. -/
def gcdAll : Deriv [] (.all 0 (phiG 0)) := by
  refine Deriv.allI ?_ (freshIn_nil 0)
  have hAuxSucc :
      Deriv [] (.all 1 ((ltT 4 (.var 1) (.succ (.var 0))).imp (phiG 1))) :=
    Deriv.allE (.succ (.var 0)) gcdAuxDeriv (substOK_of_forall (by decide))
  have hAt0 : Deriv [] ((ltT 4 (.var 0) (.succ (.var 0))).imp (phiG 0)) :=
    Deriv.allE (.var 0) hAuxSucc (substOK_of_forall (by decide))
  exact Deriv.impE hAt0 (ltSuccSelfV 4 0 (by decide))

/-- **The gcd existence theorem**:
`⊢ ∀a ∀b. ∃g. g ∣ a ∧ g ∣ b ∧ ∀d. (d ∣ a → d ∣ b → d ∣ g)`.

The extracted `g` is the greatest common divisor; every `∣` is the
fragment's own `∃`-over-`×`.  Proved by strong induction on `a + b`. -/
def gcdTheorem :
    Deriv [] (.all 6 (.all 7 (.ex 10 (gcdSpecT (.var 6) (.var 7) (.var 10))))) := by
  refine Deriv.allI (Deriv.allI ?_ (freshIn_nil 7)) (freshIn_nil 6)
  have hv : Deriv [] ((phiG 0).subst 0 (.plus (.var 6) (.var 7))) :=
    Deriv.allE (.plus (.var 6) (.var 7)) gcdAll (substOK_of_forall (by decide))
  have h8 : Deriv [] (.all 9 ((Formula.eq (.plus (.var 6) (.var 9))
      (.plus (.var 6) (.var 7))).imp (.ex 10 (gcdSpecT (.var 6) (.var 9) (.var 10))))) :=
    Deriv.allE (.var 6) hv (substOK_of_forall (by decide))
  have h9 : Deriv [] ((Formula.eq (.plus (.var 6) (.var 7))
      (.plus (.var 6) (.var 7))).imp (.ex 10 (gcdSpecT (.var 6) (.var 7) (.var 10)))) :=
    Deriv.allE (.var 7) h8 (substOK_of_forall (by decide))
  exact Deriv.impE h9 (Deriv.eqRefl (.plus (.var 6) (.var 7)))

/-! ## Certification

The same discipline as every headline derivation: the extracted realizer
realizes the theorem at every ambient above the derivation's bound
(`soundness` at the empty context), and its type-2 extract is continuous
(`extract_continuous`).  Realization reports `[propext, Classical.choice,
Quot.sound]`; continuity `[propext, Quot.sound]`. -/

/-- The extracted realizer of the gcd theorem realizes it — in particular
the `∃`-witness *is* a greatest common divisor of every `(a, b)`. -/
theorem gcd_realized (ρ : ℕ → ℕ) {n : ℕ} (hn : derivBound gcdTheorem ≤ n) :
    MR ρ (.all 6 (.all 7 (.ex 10 (gcdSpecT (.var 6) (.var 7) (.var 10))))) n
      (extract gcdTheorem ρ [] n) :=
  soundness gcdTheorem ρ [] trivial n hn

/-- Its type-2 extract is continuous — the whole subtractive-Euclid
recursion flows through generic continuity with no new per-derivation work. -/
theorem gcd_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract gcdTheorem ρ [] 1) :=
  extract_continuous gcdTheorem ρ

#print axioms gcd_realized
#print axioms gcd_extract_continuous

end Realizability
