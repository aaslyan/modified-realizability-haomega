/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Hanoi

/-!
# gcd in HA^ω — stage 1: the layer the first-order version could never run

The first-order `gcdTheorem` is that repository's deepest derivation
(`derivBound = 41`), and its certified extract `gcdWitness` **evaluates at no
input whatsoever** — the ambient tower walls it off.  This file's headline is
the converse: the extracted gcd here **runs** (`#guard`ed against `Nat.gcd`
below), because there is no tower.

What stage 1 contains:

* `mulT` — multiplication, *definable* (`rec 0 (λ_ ih. a + ih) b`), where the
  first-order signature needed `×` as a primitive with axiom schemas;
* `gcdT` — subtractive Euclid, **fueled by `a + b`**, on a state pair; agrees
  with `Nat.gcd` on all 900 pairs below 30 and the classical examples;
* the divisibility former `Dvd d a := ∃q. a = d·q` and the first
  **proof-computed** divisibility facts: `dvdZeroDeriv` (`∀d. d ∣ 0`, witness
  `0`, certificate `mulZero`) and `dvdReflDeriv` (`∀d. d ∣ d`, witness `1`,
  certificate `mulOne` — a five-link conversion chain in the explicit
  discipline);
* `gcdSpecDeriv : ∀a ∀b. ∃g. g = gcd a b`, and `gcdProgram`, its extracted
  witness — **the running extracted gcd**.

## Not claimed (stage 2)

The full first-order specification — `g ∣ a ∧ g ∣ b ∧ ∀d. d∣a → d∣b → d∣g` —
needs the order/trichotomy layer and strong induction on `a + b`, ported as
derivations.  Nothing blocks it (no `SubstOK` dodges exist here, and the
explicit-chain discipline handles the conversions), but it is real work and it
is not done.  `gcdSpecDeriv` names the algorithm in its statement, so its
extract is the solver — Fibonacci-style, not Pascal-style.
-/

namespace HAomega


/-- Multiplication, definable: `mul a b = rec 0 (λ_ ih. a + ih) b`. -/
def mulT {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.lam (.recNat .zero
    (.lam (.lam (.add (.var (.there (.there (.there .here)))) (.var .here))))
    (.var .here)))

#guard (mulT (Γ := [])).eval Env.nil 3 4 == 12
#guard (mulT (Γ := [])).eval Env.nil 0 5 == 0
#guard (mulT (Γ := [])).eval Env.nil 7 1 == 7

/-- One subtractive-Euclid step on the state `(a, b)`:
if `a ∸ b = 0` (i.e. `a ≤ b`) then `(a, b ∸ a)` else `(a ∸ b, b)`.
Fixpoints are exactly the states with a zero component. -/
def gcdStepT {Γ : List Ty} : Tm Γ (.arrow (.prod .nat .nat) (.prod .nat .nat)) :=
  .lam (.recNat
    (.pair (.fst (.var .here))
      (.app (.app Tm.subT (.snd (.var .here))) (.fst (.var .here))))
    (.lam (.lam (.pair
      (.app (.app Tm.subT (.fst (.var (.there (.there .here)))))
        (.snd (.var (.there (.there .here)))))
      (.snd (.var (.there (.there .here)))))))
    (.app Tm.isPos (.app (.app Tm.subT (.fst (.var .here))) (.snd (.var .here)))))

/-- **Subtractive Euclid, fueled by `a + b`**: iterate the step, then read the
answer as the sum of the (one-zero) final state. -/
def gcdT {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.lam
    (.app (.lam (.add (.fst (.var .here)) (.snd (.var .here))))
      (.recNat (.pair (.var (.there .here)) (.var .here))
        (.lam (.lam (.app gcdStepT (.var .here))))
        (.add (.var (.there .here)) (.var .here)))))

def gcdVal (a b : Nat) : Nat := (gcdT (Γ := [])).eval Env.nil a b

#guard [gcdVal 12 18, gcdVal 7 13, gcdVal 0 0, gcdVal 48 180, gcdVal 100 75,
        gcdVal 1071 462, gcdVal 270 192, gcdVal 5 0, gcdVal 0 5]
  == [6, 1, 0, 12, 25, 21, 6, 5, 5]
#guard (List.range 30).all fun a ↦ (List.range 30).all fun b ↦
  gcdVal a b == Nat.gcd a b


/-- Congruence in `add`'s right argument — from Leibniz, like `congFun`. -/
def Deriv.congAddR {Γ as : List Ty} {Δ : Ctx Γ as} (a : Tm Γ .nat)
    {x y : Tm Γ .nat} (h : Deriv Δ (.eq x y)) :
    Deriv Δ (.eq (.add a x) (.add a y)) := by
  have hs : ∀ u : Tm Γ .nat,
      (Formula.eq (.add (a.wk) (Tm.var .here)) ((Tm.add a x).wk)).subst1 u
        = Formula.eq (.add a u) (.add a x) := by
    intro u
    show Formula.eq (.add ((a.wk).subst1 u) u) (((Tm.add a x).wk).subst1 u) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.add (a.wk) (Tm.var .here)) ((Tm.add a x).wk)) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

/-- `mulT` applied to its first argument, named. -/
def mulApp {Γ : List Ty} (a : Tm Γ .nat) : Tm Γ (.arrow .nat .nat) :=
  .lam (.recNat .zero
    (.lam (.lam (.add (((a.wk).wk).wk) (.var .here))))
    (.var .here))

/-- The step of `mulApp a`, argument consumed. -/
def mulStep {Γ : List Ty} (a : Tm Γ .nat) :
    Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.lam (.add ((a.wk).wk) (.var .here)))

theorem linkMul1 {Γ : List Ty} (a : Tm Γ .nat) :
    Tm.subst1 (.lam (.recNat .zero
      (.lam (.lam (.add (.var (.there (.there (.there .here)))) (.var .here))))
      (.var .here))) a = mulApp a := rfl

theorem linkMul2 {Γ : List Ty} (a u : Tm Γ .nat) :
    Tm.subst1 (.recNat .zero
      (.lam (.lam (.add (((a.wk).wk).wk) (.var .here))))
      (.var .here)) u = .recNat .zero (mulStep a) u := by
  simp only [Tm.subst1, Tm.subst, Sub.ext, Sub.one, mulStep,
    Tm.wk_subst_ext, Tm.wk_subst_one]

theorem linkMul3 {Γ : List Ty} (a k I : Tm Γ .nat) :
    Tm.subst1 (Tm.subst1 (.add (((a.wk).wk)) (.var .here)) (I.wk)) k
      = .add a I := by
  simp only [Tm.subst1, Tm.subst, Sub.one, 
    Tm.wk_subst_one]

/-- `mul a u` unfolds to its recursor. -/
def mulUnfold {Γ as : List Ty} {Δ : Ctx Γ as} (a u : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app mulT a) u) (.recNat .zero (mulStep a) u)) := by
  have h1 : Deriv Δ (.eq (.app mulT a) (mulApp a)) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat) (.lam (.recNat .zero
      (.lam (.lam (.add (.var (.there (.there (.there .here)))) (.var .here))))
      (.var .here))) a
    rwa [linkMul1] at h
  have h2 : Deriv Δ (.eq (.app (mulApp a) u)
      (.recNat .zero (mulStep a) u)) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat) ((.recNat .zero
      (.lam (.lam (.add (((a.wk (σ := .nat)).wk).wk) (.var .here))))
      (.var .here) : Tm (.nat :: Γ) .nat)) u
    rwa [linkMul2] at h
  exact Deriv.transE (Deriv.congFun h1 u) h2

theorem linkStep1 {Γ : List Ty} (a z : Tm Γ .nat) :
    Tm.subst1 ((.lam (.add (((a.wk (σ := .nat)).wk)) (.var .here))
      : Tm (.nat :: Γ) (.arrow .nat .nat))) z
      = .lam (.add (a.wk) (.var .here)) := by
  simp only [Tm.subst1, Tm.subst, Sub.ext, 
    Tm.wk_subst_ext, Tm.wk_subst_one]

theorem linkStep2 {Γ : List Ty} (a I : Tm Γ .nat) :
    Tm.subst1 ((.add ((a.wk (σ := .nat))) (.var .here) : Tm (.nat :: Γ) .nat)) I
      = .add a I := by
  simp only [Tm.subst1, Tm.subst, Sub.one, 
    Tm.wk_subst_one]

/-- `mulStep a` applied twice is `add a ·`. -/
def mulStepApp {Γ as : List Ty} {Δ : Ctx Γ as} (a k I : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (mulStep a) k) I) (.add a I)) := by
  have h1 : Deriv Δ (.eq (.app (mulStep a) k)
      (.lam (.add (a.wk) (.var .here)))) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat)
      ((.lam (.add (((a.wk (σ := .nat)).wk)) (.var .here))
        : Tm (.nat :: Γ) (.arrow .nat .nat))) k
    rwa [linkStep1] at h
  have h2 : Deriv Δ (.eq (.app (.lam (.add (a.wk) (.var .here))) I)
      (.add a I)) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat)
      ((.add ((a.wk (σ := .nat))) (.var .here) : Tm (.nat :: Γ) .nat)) I
    rwa [linkStep2] at h
  exact Deriv.transE (Deriv.congFun h1 I) h2

/-- `mul a 0 = 0`. -/
def mulZero {Γ as : List Ty} {Δ : Ctx Γ as} (a : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app mulT a) .zero) .zero) :=
  Deriv.transE (mulUnfold a .zero) (Deriv.convRecZero _ _)

/-- **`mul a 1 = a`** — unfold, one step, then `a + 0 = a`. -/
def mulOne {Γ as : List Ty} {Δ : Ctx Γ as} (a : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app mulT a) (.succ .zero)) a) :=
  Deriv.transE (mulUnfold a (.succ .zero))
    (Deriv.transE (Deriv.convRecSucc _ _ _)
      (Deriv.transE (mulStepApp a .zero (.recNat .zero (mulStep a) .zero))
        (Deriv.transE (Deriv.congAddR a (Deriv.convRecZero _ _))
          (Deriv.convAddZero a))))


/-! ## Divisibility -/

/-- `d ∣ a := ∃q. a = d · q`. -/
def Dvd {Γ : List Ty} (d a : Tm Γ .nat) : Formula Γ (.prod .nat .unit) :=
  .ex .nat (.eq (a.wk) (.app (.app mulT (d.wk)) (.var .here)))

/-- **`∀d. d ∣ 0`** — witness `0`, certificate `mulZero`. -/
def dvdZeroDeriv {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (Dvd (.var .here) .zero)) := by
  refine Deriv.allI ?_
  refine Deriv.exI .zero ?_
  exact (mulZero (.var .here)).symmE

/-- **`∀d. d ∣ d`** — witness `1`, certificate the `mulOne` chain. -/
def dvdReflDeriv {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (Dvd (.var .here) (.var .here))) := by
  refine Deriv.allI ?_
  refine Deriv.exI (.succ .zero) ?_
  exact (mulOne (.var .here)).symmE

/-! ## The existence theorem, and the running extract -/

/-- `∀a ∀b. ∃g. g = gcd a b`. -/
def gcdSpec : Formula []
    (.arrow .nat (.arrow .nat (.prod .nat .unit))) :=
  .all .nat (.all .nat (.ex .nat
    (.eq (.var .here)
      (.app (.app gcdT (.var (.there (.there .here)))) (.var (.there .here))))))

def gcdSpecDeriv : Deriv Ctx.nil gcdSpec := by
  refine Deriv.allI (Deriv.allI ?_)
  refine Deriv.exI
    (.app (.app gcdT (.var (.there .here))) (.var .here)) ?_
  exact Deriv.eqRefl _

/-- **The extracted gcd — and it runs.**  The first-order `gcdWitness` is
certified at every input and evaluable at none; this one is both. -/
def gcdProgram (a b : Nat) : Nat :=
  (((extractClosed gcdSpecDeriv).eval Env.nil) a b).1

#guard [gcdProgram 12 18, gcdProgram 7 13, gcdProgram 0 0, gcdProgram 48 180,
        gcdProgram 1071 462] == [6, 1, 0, 12, 21]
#guard (List.range 20).all fun a ↦ (List.range 20).all fun b ↦
  gcdProgram a b == Nat.gcd a b

#print axioms mulOne
#print axioms dvdReflDeriv
#print axioms gcdSpecDeriv
#print axioms gcdProgram

end HAomega
