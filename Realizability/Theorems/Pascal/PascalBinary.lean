/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Pascal.PascalTheorem

/-!
# Phase G2: the binary step identities, inside the fragment

Phase G proved Kummer/Lucas in the metatheory, and recorded why the
fragment cannot state it: the submask condition needs binary digits,
i.e. division, which the signature does not have.  What the fragment
*can* state and prove is the mathematical core — the four identities the
whole of Lucas runs on:

    pas(n+n,      k+k)      = pas(n,k)        pas(n+n,      succ (k+k)) = 0
    pas(succ(n+n), k+k)     = pas(n,k)        pas(succ(n+n), succ (k+k)) = pas(n,k)

all four by ordinary `ind`, from Pascal's recursion and Phase A's
arithmetic.  Only the final assembly — the induction down the bit
positions — has to stay outside, and docs/first-order/STATUS.md says why.

## Doubling is `n + n`, not `2 × n`

Deliberate.  The proofs need `2(n+1)` in the form `succ (succ (n+n))`,
because that is what the recursion schema `pasSuccSucc` can consume.
With `n + n` that is two rewrites — `succPlus` and Phase A's
`plusSuccDeriv'` — packaged once as `dblSuccDeriv`.  With `2 × n` it
would be `timesSucc` followed by unfolding `+ 2` into two successors,
strictly more work for the same result.

## The shape of the induction

The same alternation as the Lean proof, and it is what makes the phase
interesting: `oddFromEven` derives the two odd-row identities from the
two even-row ones **at the same `n`**, and the induction step then
derives the even-row identities at `n+1` from the odd-row ones at `n`.
So the fragment's induction on `n` alternates between the two rows of the
triangle, exactly as the gasket's self-similarity does.

Three places need a `0`/`succ` case split on the *column*, and the
fragment's only way to do that is `ind` with the hypothesis discarded —
the device Phase F3 introduced.
-/

namespace Realizability

open ContinuousFunctionals

/-! ## Doubling, and the one arithmetic lemma the phase needs -/

/-- An equation binds nothing, so any term may be substituted into it. -/
theorem substOK_eq {u s t : Term} : Formula.SubstOK u (.eq s t) := by
  intro y _ hb
  exact absurd hb List.not_mem_nil

/-- Doubling, as a term. -/
abbrev dbl (t : Term) : Term := .plus t t

/-- **`∀x. succ x + succ x = succ (succ (x + x))`** — the rewrite that
puts a doubled successor into the form `pasSuccSucc` consumes.  Two
steps: `succPlus` on the left, then Phase A's `plusSuccDeriv'` inside. -/
def dblSuccDeriv : Deriv []
    (.all 1 (.eq (dbl (.succ (.var 1))) (.succ (.succ (dbl (.var 1)))))) := by
  refine Deriv.allI ?_ (freshIn_nil 1)
  have h1 : Deriv [] (Formula.eq (.plus (.succ (.var 1)) (.succ (.var 1)))
      (.succ (.plus (.var 1) (.succ (.var 1))))) :=
    Deriv.succPlus (.var 1) (.succ (.var 1))
  have h2 : Deriv [] (Formula.eq (.plus (.var 1) (.succ (.var 1)))
      (.succ (.plus (.var 1) (.var 1)))) :=
    Deriv.allE (.var 1)
      (Deriv.allE (.var 1) plusSuccDeriv' (substOK_of_forall (by decide)))
      (substOK_of_forall (by decide))
  exact h1.transE (Deriv.congSuccE h2)

/-- `dblSuccDeriv` at an arbitrary term, in an arbitrary context. -/
def dblSucc {Γ : List Formula} (t : Term) :
    Deriv Γ (.eq (dbl (.succ t)) (.succ (.succ (dbl t)))) := by
  have h : Deriv Γ (.all 1 (.eq (dbl (.succ (.var 1)))
      (.succ (.succ (dbl (.var 1)))))) := by
    induction Γ with
    | nil => exact dblSuccDeriv
    | cons φ Γ ih => exact Deriv.wk ih
  exact Deriv.allE t h substOK_eq

/-- `0 + 0 = 0`. -/
def zeroDbl {Γ : List Formula} : Deriv Γ (.eq (dbl .zero) .zero) :=
  Deriv.zeroPlus .zero

/-! ## `xor` on bits, as derivation-formers

Each takes the totality disjunction for its argument and case-splits on
it — the fragment's `orE`, with the numeral graph closing each branch. -/

/-- `xor A 0 = A`, given `A` is a bit. -/
def xorZeroRight {Γ : List Formula} {A : Term}
    (D : Deriv Γ ((Formula.eq A (.succ .zero)).or (Formula.eq A .zero))) :
    Deriv Γ (.eq (.xor A .zero) A) := by
  refine Deriv.orE D ?_ ?_
  · exact ((Deriv.congXorE Deriv.ax (.eqRefl .zero)).transE
      (Deriv.xorNum 1 0)).transE (Deriv.symmE Deriv.ax)
  · exact ((Deriv.congXorE Deriv.ax (.eqRefl .zero)).transE
      (Deriv.xorNum 0 0)).transE (Deriv.symmE Deriv.ax)

/-- `xor 0 A = A`, given `A` is a bit. -/
def xorZeroLeft {Γ : List Formula} {A : Term}
    (D : Deriv Γ ((Formula.eq A (.succ .zero)).or (Formula.eq A .zero))) :
    Deriv Γ (.eq (.xor .zero A) A) := by
  refine Deriv.orE D ?_ ?_
  · exact ((Deriv.congXorE (.eqRefl .zero) Deriv.ax).transE
      (Deriv.xorNum 0 1)).transE (Deriv.symmE Deriv.ax)
  · exact ((Deriv.congXorE (.eqRefl .zero) Deriv.ax).transE
      (Deriv.xorNum 0 0)).transE (Deriv.symmE Deriv.ax)

/-- `xor A A = 0`, given `A` is a bit. -/
def xorSelf {Γ : List Formula} {A : Term}
    (D : Deriv Γ ((Formula.eq A (.succ .zero)).or (Formula.eq A .zero))) :
    Deriv Γ (.eq (.xor A A) .zero) := by
  refine Deriv.orE D ?_ ?_
  · exact (Deriv.congXorE Deriv.ax Deriv.ax).transE (Deriv.xorNum 1 1)
  · exact (Deriv.congXorE Deriv.ax Deriv.ax).transE (Deriv.xorNum 0 0)

/-- Totality of `pas` at arbitrary terms, in an arbitrary context. -/
def pasBitAt {Γ : List Formula} (c : Term) :
    Deriv Γ ((Formula.eq (.pas (.var 1) c) (.succ .zero)).or
      (Formula.eq (.pas (.var 1) c) .zero)) := by
  have h : Deriv Γ (.all 1 (.all 2 (pasBit (.var 1)))) := by
    induction Γ with
    | nil => exact pasTotal
    | cons φ Γ ih => exact Deriv.wk ih
  have h1 : Deriv Γ (.all 2 (pasBit (.var 1))) :=
    Deriv.allE (.var 1) h (by decide +kernel)
  exact Deriv.allE c h1 (by
    intro y _ hb
    exact absurd hb List.not_mem_nil)

/-- `pas(t, 0) = 1` at an arbitrary term. -/
def pasColZero {Γ : List Formula} (t : Term) :
    Deriv Γ (.eq (.pas t .zero) (.succ .zero)) := by
  have h : Deriv Γ (.all 1 (.eq (.pas (.var 1) .zero) (.succ .zero))) := by
    induction Γ with
    | nil => exact pasZeroCol
    | cons φ Γ ih => exact Deriv.wk ih
  exact Deriv.allE t h substOK_eq

/-! ## The two statements -/

/-- The even-row identities, at row `n` (variable `1`) and column `k`
(variable `2`). -/
abbrev binEvenBody : Formula :=
  (Formula.eq (.pas (dbl (.var 1)) (dbl (.var 2))) (.pas (.var 1) (.var 2))).and
    (Formula.eq (.pas (dbl (.var 1)) (.succ (dbl (.var 2)))) .zero)

/-- The even-row identities, quantified over the column. -/
abbrev binEven : Formula := .all 2 binEvenBody

/-- The odd-row identities. -/
abbrev binOddBody : Formula :=
  (Formula.eq (.pas (.succ (dbl (.var 1))) (dbl (.var 2)))
    (.pas (.var 1) (.var 2))).and
    (Formula.eq (.pas (.succ (dbl (.var 1))) (.succ (dbl (.var 2))))
      (.pas (.var 1) (.var 2)))

/-- The odd-row identities, quantified over the column. -/
abbrev binOdd : Formula := .all 2 binOddBody

/-! ## The odd rows, from the even rows at the same `n`

The first half of the alternation.  Both parts split on the column, by
`ind` with the hypothesis discarded. -/

/-- Derive the odd-row identities from the even ones at the same `n`. -/
def oddFromEven {Γ : List Formula} (hfresh : FreshIn 2 Γ)
    (hev : Deriv Γ binEven) : Deriv Γ binOdd := by
  refine .ind ?_ ?_ (substOK_of_forall (by decide))
  · -- column `0`
    have h0 : Deriv Γ ((Formula.eq (.pas (dbl (.var 1)) (dbl .zero))
          (.pas (.var 1) .zero)).and
        (Formula.eq (.pas (dbl (.var 1)) (.succ (dbl .zero))) .zero)) :=
      Deriv.allE .zero hev (by decide +kernel)
    refine Deriv.andI ?_ ?_
    · exact (Deriv.congPasE (.eqRefl _) zeroDbl).transE
        ((Deriv.pasSuccZero (dbl (.var 1))).transE
          (Deriv.symmE (pasColZero (.var 1))))
    · have e₁ : Deriv Γ (Formula.eq (.pas (dbl (.var 1)) .zero)
          (.pas (.var 1) .zero)) :=
        (Deriv.congPasE (.eqRefl _) (Deriv.symmE zeroDbl)).transE (Deriv.andE₁ h0)
      have e₂ : Deriv Γ (Formula.eq (.pas (dbl (.var 1)) (.succ .zero)) .zero) :=
        (Deriv.congPasE (.eqRefl _) (Deriv.congSuccE (Deriv.symmE zeroDbl))).transE
          (Deriv.andE₂ h0)
      exact (Deriv.congPasE (.eqRefl _) (Deriv.congSuccE zeroDbl)).transE
        ((Deriv.pasSuccSucc (dbl (.var 1)) .zero).transE
          ((Deriv.congXorE e₁ e₂).transE
            (xorZeroRight (pasBitAt .zero))))
  · -- column `succ k`; the induction hypothesis is discarded
    refine Deriv.allI (Deriv.impI ?_) hfresh
    have hev' : Deriv (binOddBody :: Γ) binEven := Deriv.wk hev
    have hk : Deriv (binOddBody :: Γ)
        ((Formula.eq (.pas (dbl (.var 1)) (dbl (.var 2)))
            (.pas (.var 1) (.var 2))).and
          (Formula.eq (.pas (dbl (.var 1)) (.succ (dbl (.var 2)))) .zero)) :=
      Deriv.allE (.var 2) hev' (by decide +kernel)
    have hsk : Deriv (binOddBody :: Γ)
        ((Formula.eq (.pas (dbl (.var 1)) (dbl (.succ (.var 2))))
            (.pas (.var 1) (.succ (.var 2)))).and
          (Formula.eq (.pas (dbl (.var 1)) (.succ (dbl (.succ (.var 2))))) .zero)) :=
      Deriv.allE (.succ (.var 2)) hev' (by decide +kernel)
    -- the shifted entry, used by both halves
    have p4 : Deriv (binOddBody :: Γ)
        (Formula.eq (.pas (dbl (.var 1)) (.succ (.succ (dbl (.var 2)))))
          (.pas (.var 1) (.succ (.var 2)))) :=
      (Deriv.congPasE (.eqRefl _) (Deriv.symmE (dblSucc (.var 2)))).transE
        (Deriv.andE₁ hsk)
    refine Deriv.andI ?_ ?_
    · exact (Deriv.congPasE (.eqRefl _) (dblSucc (.var 2))).transE
        ((Deriv.pasSuccSucc (dbl (.var 1)) (.succ (dbl (.var 2)))).transE
          ((Deriv.congXorE (Deriv.andE₂ hk) p4).transE
            (xorZeroLeft (pasBitAt (.succ (.var 2))))))
    · have q₂ : Deriv (binOddBody :: Γ)
          (Formula.eq (.pas (dbl (.var 1)) (.succ (.succ (.succ (dbl (.var 2))))))
            .zero) :=
        (Deriv.congPasE (.eqRefl _)
          (Deriv.congSuccE (Deriv.symmE (dblSucc (.var 2))))).transE
          (Deriv.andE₂ hsk)
      exact (Deriv.congPasE (.eqRefl _) (Deriv.congSuccE (dblSucc (.var 2)))).transE
        ((Deriv.pasSuccSucc (dbl (.var 1)) (.succ (.succ (dbl (.var 2))))).transE
          ((Deriv.congXorE p4 q₂).transE
            (xorZeroRight (pasBitAt (.succ (.var 2))))))

/-! ## The even rows, by induction on the row

The other half of the alternation: the step derives the odd identities at
`n` from the induction hypothesis, then the even identities at `n + 1`
from those. -/

/-- **The binary step identities inside the fragment**, by `ind` down the
rows (the even rows; the odd ones follow via `oddFromEven`). -/
def binEvenDeriv : Deriv [] (.all 1 binEven) := by
  refine .ind ?_ ?_ (substOK_of_forall (by decide))
  · -- row `0`
    refine .ind ?_ ?_ (substOK_of_forall (by decide))
    · refine Deriv.andI (Deriv.congPasE zeroDbl zeroDbl) ?_
      exact (Deriv.congPasE zeroDbl (Deriv.congSuccE zeroDbl)).transE
        (Deriv.pasZeroSucc .zero)
    · refine Deriv.allI (Deriv.impI ?_) (freshIn_nil 2)
      refine Deriv.andI ?_ ?_
      · exact ((Deriv.congPasE zeroDbl (dblSucc (.var 2))).transE
          (Deriv.pasZeroSucc (.succ (dbl (.var 2))))).transE
          (Deriv.symmE (Deriv.pasZeroSucc (.var 2)))
      · exact (Deriv.congPasE zeroDbl (.eqRefl _)).transE
          (Deriv.pasZeroSucc (dbl (.succ (.var 2))))
  · -- row `succ n`
    refine Deriv.allI (Deriv.impI ?_) (freshIn_nil 1)
    have hodd : Deriv [binEven] binOdd :=
      oddFromEven (by decide +kernel) Deriv.ax
    refine .ind ?_ ?_ (substOK_of_forall (by decide))
    · -- column `0`
      have o0 : Deriv [binEven]
          ((Formula.eq (.pas (.succ (dbl (.var 1))) (dbl .zero))
              (.pas (.var 1) .zero)).and
            (Formula.eq (.pas (.succ (dbl (.var 1))) (.succ (dbl .zero)))
              (.pas (.var 1) .zero))) :=
        Deriv.allE .zero hodd (by decide +kernel)
      refine Deriv.andI ?_ ?_
      · exact ((Deriv.congPasE (dblSucc (.var 1)) zeroDbl).transE
          (Deriv.pasSuccZero (.succ (dbl (.var 1))))).transE
          (Deriv.symmE (pasColZero (.succ (.var 1))))
      · have e₁ : Deriv [binEven]
            (Formula.eq (.pas (.succ (dbl (.var 1))) .zero) (.pas (.var 1) .zero)) :=
          (Deriv.congPasE (.eqRefl _) (Deriv.symmE zeroDbl)).transE (Deriv.andE₁ o0)
        have e₂ : Deriv [binEven]
            (Formula.eq (.pas (.succ (dbl (.var 1))) (.succ .zero))
              (.pas (.var 1) .zero)) :=
          (Deriv.congPasE (.eqRefl _) (Deriv.congSuccE (Deriv.symmE zeroDbl))).transE
            (Deriv.andE₂ o0)
        exact (Deriv.congPasE (dblSucc (.var 1)) (Deriv.congSuccE zeroDbl)).transE
          ((Deriv.pasSuccSucc (.succ (dbl (.var 1))) .zero).transE
            ((Deriv.congXorE e₁ e₂).transE
              (xorSelf (pasBitAt .zero))))
    · -- column `succ k`; the inner induction hypothesis is discarded
      refine Deriv.allI (Deriv.impI ?_) (by decide +kernel)
      refine Deriv.andI ?_ ?_
      · exact (Deriv.congPasE (dblSucc (.var 1)) (dblSucc (.var 2))).transE
          ((Deriv.pasSuccSucc (.succ (dbl (.var 1))) (.succ (dbl (.var 2)))).transE
            ((Deriv.congXorE
                (Deriv.andE₂ (Deriv.allE (.var 2) (Deriv.wk hodd) (by decide +kernel)))
                ((Deriv.congPasE (.eqRefl _)
                    (Deriv.symmE (dblSucc (.var 2)))).transE
                  (Deriv.andE₁ (Deriv.allE (.succ (.var 2)) (Deriv.wk hodd)
                    (by decide +kernel))))).transE
              (Deriv.symmE (Deriv.pasSuccSucc (.var 1) (.var 2)))))
      · exact (Deriv.congPasE (dblSucc (.var 1))
            (Deriv.congSuccE (dblSucc (.var 2)))).transE
          ((Deriv.pasSuccSucc (.succ (dbl (.var 1)))
              (.succ (.succ (dbl (.var 2))))).transE
            ((Deriv.congXorE
                ((Deriv.congPasE (.eqRefl _)
                    (Deriv.symmE (dblSucc (.var 2)))).transE
                  (Deriv.andE₁ (Deriv.allE (.succ (.var 2)) (Deriv.wk hodd)
                    (by decide +kernel))))
                ((Deriv.congPasE (.eqRefl _)
                    (Deriv.congSuccE (Deriv.symmE (dblSucc (.var 2))))).transE
                  (Deriv.andE₂ (Deriv.allE (.succ (.var 2)) (Deriv.wk hodd)
                    (by decide +kernel))))).transE
              (xorSelf (pasBitAt (.succ (.var 2))))))

/-- **The odd-row identities**, as a standalone theorem. -/
def binOddDeriv : Deriv [] (.all 1 binOdd) := by
  refine Deriv.allI ?_ (freshIn_nil 1)
  exact oddFromEven (freshIn_nil 2)
    (Deriv.allE (.var 1) binEvenDeriv (by decide +kernel))

/-! ## Certification, and the round trip

The identities are closed derivations, so `soundness` and generic
continuity apply with no new argument.  The round trip is the point: read
back through `soundness`, the fragment's derivations give exactly Phase
G's value-level `pasN_even` and `pasN_odd` — so what the fragment proved
is the same mathematics, not a weaker syntactic shadow of it. -/

theorem binEven_derivBound : derivBound binEvenDeriv = 18 := rfl

theorem binEven_realized (ρ : ℕ → ℕ) {m : ℕ} (hm : 18 ≤ m) :
    MR ρ (.all 1 binEven) m (extract binEvenDeriv ρ [] m) :=
  soundness binEvenDeriv ρ [] trivial m (by rw [binEven_derivBound]; exact hm)

theorem binEven_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract binEvenDeriv ρ [] 1) :=
  extract_continuous binEvenDeriv ρ

set_option maxRecDepth 8000 in
theorem binOdd_derivBound : derivBound binOddDeriv = 22 := rfl

theorem binOdd_realized (ρ : ℕ → ℕ) {m : ℕ} (hm : 22 ≤ m) :
    MR ρ (.all 1 binOdd) m (extract binOddDeriv ρ [] m) :=
  soundness binOddDeriv ρ [] trivial m (by rw [binOdd_derivBound]; exact hm)

theorem binOdd_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract binOddDeriv ρ [] 1) :=
  extract_continuous binOddDeriv ρ

/-- **The round trip for the even rows**: the fragment's derivation, read
through `soundness`, is Phase G's `pasN_even`. -/
theorem bin_even_via_fragment (n k : ℕ) :
    pasN (n + n) (k + k) = pasN n k ∧ pasN (n + n) (k + k + 1) = 0 := by
  have h := binEven_realized (fun _ ↦ 0) (m := 18) (Nat.le_refl 18) n k
  obtain ⟨h₁, h₂⟩ := h
  constructor
  · simpa [Term.eval, Function.update] using h₁
  · simpa [Term.eval, Function.update] using h₂

/-- **The round trip for the odd rows**: likewise Phase G's `pasN_odd`. -/
theorem bin_odd_via_fragment (n k : ℕ) :
    pasN (n + n + 1) (k + k) = pasN n k ∧ pasN (n + n + 1) (k + k + 1) = pasN n k := by
  have h := binOdd_realized (fun _ ↦ 0) (m := 22) (Nat.le_refl 22) n k
  obtain ⟨h₁, h₂⟩ := h
  constructor
  · simpa [Term.eval, Function.update] using h₁
  · simpa [Term.eval, Function.update] using h₂

#print axioms binEvenDeriv
#print axioms binOddDeriv
#print axioms binEven_realized
#print axioms bin_even_via_fragment
#print axioms bin_odd_via_fragment
#print axioms binEven_extract_continuous

end Realizability
