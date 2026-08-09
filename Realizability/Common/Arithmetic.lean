/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Core.Soundness
import Realizability.Core.GenericContinuity

/-!
# Phase A: `+` and `×`, their defining equations as `ind` theorems

The four briefed equations

* `∀x. x + 0 = x`
* `∀x ∀y. x + succ y = succ (x + y)`
* `∀x. x × 0 = 0`
* `∀x ∀y. x × succ y = (x × y) + x`

proved as closed derivations of the fragment — **every one of them by
the induction rule `ind`**, not cited as axioms.

## The design (Option 2 of the brief, "mirror recursion" form)

The axioms *defining* `+`/`×` (`Syntax.lean`) recurse on the **first**
argument: `0 + t = t`, `succ s + t = succ (s + t)`, `0 × t = 0`,
`succ s × t = (s × t) + t`.  The briefed equations recurse on the
*second* argument, so each is a genuine theorem, proved by `ind` on its
first argument — the exact mirror of how Lean's own `Nat.add` (which
recurses on the second argument) makes `0 + n = n` a theorem by
induction.  Had the defining axioms been the briefed equations
themselves, all four deliverables would have been one `allI` away from
an axiom and `ind` would never fire — Option 2 would have collapsed
into Option 1 with different labels.  See docs/first-order/STATUS.md.

The multiplication step case needs one auxiliary induction,
`plusRightCommDeriv` (`(z + x) + y = (z + y) + x`), itself an `ind`
theorem — five inductions in total.

## Bound variables and capture

`∀`-elimination's `SubstOK` side condition forbids instantiating
`∀x∀y. φ` at a term containing `y`.  Where an instance at such a term
is needed (inside `timesSuccDeriv`, at terms over variables `0`, `1`),
we use `plusSuccDeriv'`, the α-variant of `plusSuccDeriv` at bound
variables `2`, `3` — derived from it by instantiate-and-regeneralize,
not re-proved.  `plusRightCommDeriv` binds `2`, `3`, `4` for the same
reason.
-/

namespace Realizability

open ContinuousFunctionals

/-! ## Derivation-formers for the equational-logic schemas

Each wraps its schema's `impE` chain so the arithmetic proofs below
read as calculations. -/

/-- Symmetry, as a derivation-former. -/
def Deriv.symmE {Γ : List Formula} {s t : Term}
    (D : Deriv Γ (.eq s t)) : Deriv Γ (.eq t s) :=
  .impE (.eqSymm s t) D

/-- Transitivity, as a derivation-former. -/
def Deriv.transE {Γ : List Formula} {s t u : Term}
    (D₁ : Deriv Γ (.eq s t)) (D₂ : Deriv Γ (.eq t u)) :
    Deriv Γ (.eq s u) :=
  .impE (.impE (.eqTrans s t u) D₁) D₂

/-- Congruence of `succ`, as a derivation-former. -/
def Deriv.congSuccE {Γ : List Formula} {s t : Term}
    (D : Deriv Γ (.eq s t)) : Deriv Γ (.eq (.succ s) (.succ t)) :=
  .impE (.eqCongSucc s t) D

/-- Congruence of `+`, as a derivation-former. -/
def Deriv.congPlusE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.plus s₁ s₂) (.plus t₁ t₂)) :=
  .impE (.impE (.eqCongPlus s₁ t₁ s₂ t₂) D₁) D₂

/-- Congruence of `+` in the left argument alone. -/
def Deriv.congPlusL {Γ : List Formula} {s t : Term} (u : Term)
    (D : Deriv Γ (.eq s t)) : Deriv Γ (.eq (.plus s u) (.plus t u)) :=
  D.congPlusE (.eqRefl u)

/-- Congruence of `+` in the right argument alone. -/
def Deriv.congPlusR {Γ : List Formula} {s t : Term} (u : Term)
    (D : Deriv Γ (.eq s t)) : Deriv Γ (.eq (.plus u s) (.plus u t)) :=
  (Deriv.eqRefl u).congPlusE D

/-! ## Side-condition discharge -/

/-- Any variable is fresh for the empty context. -/
theorem freshIn_nil (x : ℕ) : FreshIn x [] :=
  fun _ h ↦ nomatch h

/-- A variable is fresh for the singleton context that binds it at the
head — the step-case context of every two-variable induction below. -/
theorem freshIn_singleton_all (x : ℕ) (ψ : Formula) :
    FreshIn x [.all x ψ] := by
  intro χ hχ
  rw [List.mem_singleton] at hχ
  subst hχ
  exact fun hf ↦ hf.1 rfl

/-- `SubstOK`, from its unfolded (decidable, for concrete data)
statement. -/
theorem substOK_of_forall {u : Term} {φ : Formula}
    (h : ∀ y ∈ u.vars, y ∉ φ.binders) : Formula.SubstOK u φ :=
  h

/-! ## `∀x. x + 0 = x` -/

/-- **`∀x. x + 0 = x`**, by `ind` on `x`: the base `0 + 0 = 0` is the
defining axiom `zeroPlus` at `0`; the step pushes `succ` out of the
left argument (`succPlus`) and closes with the hypothesis under
`succ`-congruence. -/
def plusZeroDeriv : Deriv [] (.all 0 (.eq (.plus (.var 0) .zero) (.var 0))) :=
  .ind
    (.zeroPlus .zero)
    (.allI
      (.impI
        ((Deriv.succPlus (.var 0) .zero).transE (Deriv.congSuccE .ax)))
      (freshIn_nil 0))
    (substOK_of_forall (by decide))

/-! ## `∀x ∀y. x + succ y = succ (x + y)` -/

/-- The equation `x + succ y = succ (x + y)`, free variables `0`, `1`. -/
private def plusSuccEq : Formula :=
  .eq (.plus (.var 0) (.succ (.var 1))) (.succ (.plus (.var 0) (.var 1)))

/-- **`∀x ∀y. x + succ y = succ (x + y)`**, by `ind` on `x` (the
recursion variable of the defining axioms), the quantifier on `y`
carried through the induction. -/
def plusSuccDeriv : Deriv [] (.all 0 (.all 1 plusSuccEq)) :=
  .ind
    -- Base, `∀y. 0 + succ y = succ (0 + y)`: both sides compute to
    -- `succ y` by `zeroPlus`.
    (.allI
      ((Deriv.zeroPlus (.succ (.var 1))).transE
        (Deriv.congSuccE (Deriv.symmE (.zeroPlus (.var 1)))))
      (freshIn_nil 1))
    -- Step: from `∀y. x + succ y = succ (x + y)` conclude the same for
    -- `succ x`, pushing `succ` out on both sides by `succPlus`.
    (.allI
      (.impI
        (.allI
          ((Deriv.succPlus (.var 0) (.succ (.var 1))).transE
            ((Deriv.congSuccE
              (.allE (.var 1) (.ax : Deriv [.all 1 plusSuccEq] _)
                (substOK_of_forall (by decide)))).transE
              (Deriv.symmE
                (Deriv.congSuccE (.succPlus (.var 0) (.var 1))))))
          (freshIn_singleton_all 1 plusSuccEq))
        )
      (freshIn_nil 0))
    (substOK_of_forall (by decide))

/-- The α-variant `∀x ∀y. x + succ y = succ (x + y)` at bound variables
`2`, `3`, for instantiation at terms whose variables include `0`, `1`
(the `SubstOK` no-capture condition forbids using `plusSuccDeriv`
there).  Derived by instantiate-and-regeneralize, not re-proved. -/
def plusSuccDeriv' :
    Deriv [] (.all 2 (.all 3 (.eq (.plus (.var 2) (.succ (.var 3)))
      (.succ (.plus (.var 2) (.var 3)))))) :=
  .allI
    (.allI
      (.allE (.var 3)
        (.allE (.var 2) plusSuccDeriv (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide)))
      (freshIn_nil 3))
    (freshIn_nil 2)

/-! ## The auxiliary induction: `(z + x) + y = (z + y) + x` -/

/-- The equation `(z + x) + y = (z + y) + x`, free variables `2`, `3`,
`4` (kept clear of `0`, `1` so `timesSuccDeriv` can instantiate it). -/
private def plusRightCommEq : Formula :=
  .eq (.plus (.plus (.var 2) (.var 3)) (.var 4))
    (.plus (.plus (.var 2) (.var 4)) (.var 3))

/-- **`∀z ∀x ∀y. (z + x) + y = (z + y) + x`** — the auxiliary lemma the
multiplication step needs, by `ind` on `y`: the base is `plusZeroDeriv`
twice; the step exchanges `succ` through both sides with
`plusSuccDeriv` (at bound variables clear of `2`, `3`, `4`), `succPlus`
and the hypothesis. -/
def plusRightCommDeriv : Deriv [] (.all 2 (.all 3 (.all 4 plusRightCommEq))) :=
  .allI
    (.allI
      (.ind
        -- Base: `(z + x) + 0 = z + x = (z + 0) + x`.
        ((Deriv.transE
          (.allE (.plus (.var 2) (.var 3)) plusZeroDeriv
            (substOK_of_forall (by decide)))
          (Deriv.congPlusL (.var 3)
            (Deriv.symmE
              (.allE (.var 2) plusZeroDeriv
                (substOK_of_forall (by decide)))))))
        -- Step: from `(z + x) + y = (z + y) + x` conclude the same at
        -- `succ y`, via `x + succ y = succ (x + y)` on both sides.
        (.allI
          (.impI
            (Deriv.transE
              (Deriv.transE
                (.wk (.allE (.var 4)
                  (.allE (.plus (.var 2) (.var 3)) plusSuccDeriv
                    (substOK_of_forall (by decide)))
                  (substOK_of_forall (by decide))))
                (Deriv.congSuccE (.ax : Deriv [plusRightCommEq] _)))
              (Deriv.symmE
                (Deriv.transE
                  (Deriv.congPlusL (.var 3)
                    (.wk (.allE (.var 4)
                      (.allE (.var 2) plusSuccDeriv
                        (substOK_of_forall (by decide)))
                      (substOK_of_forall (by decide)))))
                  (.succPlus (.plus (.var 2) (.var 4)) (.var 3))))))
          (freshIn_nil 4))
        (substOK_of_forall (by decide)))
      (freshIn_nil 3))
    (freshIn_nil 2)

/-! ## `∀x. x × 0 = 0` -/

/-- **`∀x. x × 0 = 0`**, by `ind` on `x`: the step unfolds
`succ x × 0 = (x × 0) + 0` (`succTimes`), strips the `+ 0` with the
already-proved `plusZeroDeriv` — the first theorem-to-theorem use in
the module — and closes with the hypothesis. -/
def timesZeroDeriv : Deriv [] (.all 0 (.eq (.times (.var 0) .zero) .zero)) :=
  .ind
    (.zeroTimes .zero)
    (.allI
      (.impI
        (Deriv.transE
          (Deriv.transE
            (.succTimes (.var 0) .zero)
            (.wk (.allE (.times (.var 0) .zero) plusZeroDeriv
              (substOK_of_forall (by decide)))))
          .ax))
      (freshIn_nil 0))
    (substOK_of_forall (by decide))

/-! ## `∀x ∀y. x × succ y = (x × y) + x` -/

/-- The equation `x × succ y = (x × y) + x`, free variables `0`, `1`. -/
private def timesSuccEq : Formula :=
  .eq (.times (.var 0) (.succ (.var 1)))
    (.plus (.times (.var 0) (.var 1)) (.var 0))

/-- **`∀x ∀y. x × succ y = (x × y) + x`**, by `ind` on `x`.  The base
computes both sides to `0`.  The step is the one genuine calculation of
the module: with `a := x × y`,

    succ x × succ y = (x × succ y) + succ y      (succTimes)
                    = ((a + x)) + succ y         (hypothesis)
                    = succ ((a + x) + y)         (plusSuccDeriv')
                    = succ ((a + y) + x)         (plusRightCommDeriv)
                    = (a + y) + succ x           (plusSuccDeriv', back)
                    = (succ x × y) + succ x      (succTimes, back)

— the two α-variant instantiations are exactly why `plusSuccDeriv'`
and `plusRightCommDeriv` bind variables clear of `0`, `1`. -/
def timesSuccDeriv : Deriv [] (.all 0 (.all 1 timesSuccEq)) :=
  .ind
    -- Base, `∀y. 0 × succ y = (0 × y) + 0`: both sides are `0`.
    (.allI
      (Deriv.transE
        (Deriv.transE
          (.zeroTimes (.succ (.var 1)))
          (Deriv.symmE (.zeroTimes (.var 1))))
        (Deriv.symmE
          (.allE (.times .zero (.var 1)) plusZeroDeriv
            (substOK_of_forall (by decide)))))
      (freshIn_nil 1))
    -- Step: the six-line calculation above.
    (.allI
      (.impI
        (.allI
          (Deriv.transE
            (Deriv.transE
              (Deriv.transE
                (Deriv.transE
                  ((Deriv.succTimes (.var 0) (.succ (.var 1))).transE
                    (Deriv.congPlusL (.succ (.var 1))
                      (.allE (.var 1) (.ax : Deriv [.all 1 timesSuccEq] _)
                        (substOK_of_forall (by decide)))))
                  (.wk (.allE (.var 1)
                    (.allE (.plus (.times (.var 0) (.var 1)) (.var 0))
                      plusSuccDeriv' (substOK_of_forall (by decide)))
                    (substOK_of_forall (by decide)))))
                (Deriv.congSuccE
                  (.wk (.allE (.var 1)
                    (.allE (.var 0)
                      (.allE (.times (.var 0) (.var 1)) plusRightCommDeriv
                        (substOK_of_forall (by decide)))
                      (substOK_of_forall (by decide)))
                    (substOK_of_forall (by decide))))))
              (Deriv.symmE
                (.wk (.allE (.var 0)
                  (.allE (.plus (.times (.var 0) (.var 1)) (.var 1))
                    plusSuccDeriv' (substOK_of_forall (by decide)))
                  (substOK_of_forall (by decide))))))
            (Deriv.symmE
              (Deriv.congPlusL (.succ (.var 0))
                (.succTimes (.var 0) (.var 1)))))
          (freshIn_singleton_all 1 timesSuccEq)))
      (freshIn_nil 0))
    (substOK_of_forall (by decide))

/-! ## Extraction and certification

The same discipline as every headline theorem of the repository: each
equation's extracted realizer family realizes it at every ambient above
the derivation's bound (`soundness` at the empty context), and each
type-2 extract is continuous (`extract_continuous`).  `#print axioms`
on all of them at the end of the file — checked at every build. -/

/-- The extracted realizer of `∀x. x + 0 = x` realizes it. -/
theorem plus_zero_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound plusZeroDeriv ≤ n) :
    MR ρ (.all 0 (.eq (.plus (.var 0) .zero) (.var 0))) n
      (extract plusZeroDeriv ρ [] n) :=
  soundness plusZeroDeriv ρ [] trivial n hn

/-- The extracted realizer of `∀x ∀y. x + succ y = succ (x + y)`
realizes it. -/
theorem plus_succ_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound plusSuccDeriv ≤ n) :
    MR ρ (.all 0 (.all 1 plusSuccEq)) n (extract plusSuccDeriv ρ [] n) :=
  soundness plusSuccDeriv ρ [] trivial n hn

/-- The extracted realizer of `∀x. x × 0 = 0` realizes it. -/
theorem times_zero_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound timesZeroDeriv ≤ n) :
    MR ρ (.all 0 (.eq (.times (.var 0) .zero) .zero)) n
      (extract timesZeroDeriv ρ [] n) :=
  soundness timesZeroDeriv ρ [] trivial n hn

/-- The extracted realizer of `∀x ∀y. x × succ y = (x × y) + x`
realizes it. -/
theorem times_succ_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound timesSuccDeriv ≤ n) :
    MR ρ (.all 0 (.all 1 timesSuccEq)) n (extract timesSuccDeriv ρ [] n) :=
  soundness timesSuccDeriv ρ [] trivial n hn

/-- Continuity of the type-2 extract of `∀x. x + 0 = x` — a one-line
corollary of `extract_continuous`, new `ind`-heavy content flowing
through the generic theorem with no new per-derivation work. -/
theorem plus_zero_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract plusZeroDeriv ρ [] 1) :=
  extract_continuous plusZeroDeriv ρ

/-- Continuity of the type-2 extract of `∀x ∀y. x + succ y = succ (x + y)`. -/
theorem plus_succ_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract plusSuccDeriv ρ [] 1) :=
  extract_continuous plusSuccDeriv ρ

/-- Continuity of the type-2 extract of `∀x. x × 0 = 0`. -/
theorem times_zero_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract timesZeroDeriv ρ [] 1) :=
  extract_continuous timesZeroDeriv ρ

/-- Continuity of the type-2 extract of `∀x ∀y. x × succ y = (x × y) + x`. -/
theorem times_succ_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract timesSuccDeriv ρ [] 1) :=
  extract_continuous timesSuccDeriv ρ

#print axioms plus_zero_realized
#print axioms plus_succ_realized
#print axioms times_zero_realized
#print axioms times_succ_realized
#print axioms plus_zero_extract_continuous
#print axioms plus_succ_extract_continuous
#print axioms times_zero_extract_continuous
#print axioms times_succ_extract_continuous

end Realizability
