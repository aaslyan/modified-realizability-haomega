/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.Picard
import HAomega.GaloisAdequacy
import HAomega.FixedPoint
import HAomega.AnalysisDeriv
import HAomega.SquareRoot

/-!
# Executable ODE Extraction Demo: Solving $y' = y, y(0) = 1$ via Picard Iteration

This module demonstrates the end-to-end constructive execution of our
Newton–Leibniz + Banach fixed point synthesis:

1. The initial value problem $y' = y, y(0) = 1$ on $[0, 1/2]$ corresponds to the
   Picard integral operator:
   $$\mathcal{T}(P)(x) = 1 + \int_0^x P(t)\,dt$$

2. Starting from initial approximation $P_0(x) = 1$, exact Picard integration
   computes the sequence of Taylor polynomials:
   $$P_n(x) = \sum_{j=0}^n \frac{x^j}{j!}$$

3. At $x = 1/2$, this converges to $\sqrt{e} \approx 1.64872127...$ with verified
   exact rational values:
   - $P_1(1/2) = 3/2 = 1.5$
   - $P_2(1/2) = 13/8 = 1.625$
   - $P_3(1/2) = 79/48 \approx 1.64583$
   - $P_4(1/2) = 211/128 \approx 1.6484375$
   - $P_5(1/2) = 6331/3840 \approx 1.6486979$
   - $P_6(1/2) = 75973 / 46080 \approx 1.6487196$ (error $< 2 \cdot 10^{-6}$)
-/

namespace HAomega

open Rat

/-- Factorial for Taylor polynomial coefficients. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Power of a rational number $x^n$. -/
def qpow (x : Q) : Nat → Q
  | 0 => Q.ofNat 1
  | n + 1 => Q.mul x (qpow x n)

/-- $n$-th Taylor term $x^j / j!$. -/
def taylorTerm (x : Q) (j : Nat) : Q :=
  Q.div (qpow x j) (Q.ofNat (fact j))

/-- Direct Taylor partial sum $P_n(x) = \sum_{j=0}^n \frac{x^j}{j!}$. -/
def expTaylor (n : Nat) (x : Q) : Q :=
  (List.range (n + 1)).foldl (fun acc j ↦ Q.add acc (taylorTerm x j)) Q.zero

/-- Taylor step recurrence: $P_{n+1}(x) = P_n(x) + \frac{x^{n+1}}{(n+1)!}$. -/
theorem expTaylor_succ (n : Nat) (x : Q) :
    expTaylor (n + 1) x = Q.add (expTaylor n x) (taylorTerm x (n + 1)) := by
  dsimp [expTaylor]
  rw [List.range_succ, List.foldl_append]
  rfl

/-- Integrate polynomial $P(t) = \sum c_j t^j$: $\int_0^x P(t)\,dt = \sum \frac{c_j}{j+1} x^{j+1}$. -/
def polyIntegrate (p : List Q) : List Q :=
  Q.zero :: (((List.range p.length).zip p).map (fun ⟨j, c⟩ ↦ Q.div c (Q.ofNat (j + 1))))

/-- 1D Picard step for $y' = y, y(0) = 1$: $P_{n+1}(x) = 1 + \int_0^x P_n(t)\,dt$. -/
def expPicardStep (p : List Q) : List Q :=
  Q.ofNat 1 :: (((List.range p.length).zip p).map (fun ⟨j, c⟩ ↦ Q.div c (Q.ofNat (j + 1))))

/-- $n$-th Picard polynomial iterate for $y' = y, y(0) = 1$, starting from $P_0 = [1]$. -/
def expPicardPoly : Nat → List Q
  | 0 => [Q.ofNat 1]
  | n + 1 => expPicardStep (expPicardPoly n)

/-- Evaluate a polynomial at $x$. -/
def evalRealPoly (p : List Q) (x : Q) : Q :=
  ((List.range p.length).zip p).foldl (fun acc ⟨j, c⟩ ↦
    let term := Q.mul c (qpow x j)
    Q.add acc term) Q.zero

/-- Executable Picard iterate $P_n(x)$ computed via genuine polynomial Picard integration. -/
def expPicard (n : Nat) (x : Q) : Q :=
  evalRealPoly (expPicardPoly n) x

/-! ### Verified Concrete Calculations in Lean -/

-- P₀(1/2) = 1
#guard expPicard 0 (Q.of 1 2) == Q.of 1 1
#guard expTaylor 0 (Q.of 1 2) == Q.of 1 1

-- P₁(1/2) = 1 + 1/2 = 3/2
#guard expPicard 1 (Q.of 1 2) == Q.of 3 2
#guard expTaylor 1 (Q.of 1 2) == Q.of 3 2

-- P₂(1/2) = 1 + 1/2 + 1/8 = 13/8
#guard expPicard 2 (Q.of 1 2) == Q.of 13 8
#guard expTaylor 2 (Q.of 1 2) == Q.of 13 8

-- P₃(1/2) = 1 + 1/2 + 1/8 + 1/48 = 79/48
#guard expPicard 3 (Q.of 1 2) == Q.of 79 48
#guard expTaylor 3 (Q.of 1 2) == Q.of 79 48

-- P₄(1/2) = 79/48 + 1/384 = 633/384 = 211/128
#guard expPicard 4 (Q.of 1 2) == Q.of 211 128
#guard expTaylor 4 (Q.of 1 2) == Q.of 211 128

-- P₅(1/2) = 211/128 + 1/3840 = 6331/3840
#guard expPicard 5 (Q.of 1 2) == Q.of 6331 3840
#guard expTaylor 5 (Q.of 1 2) == Q.of 6331 3840

-- P₆(1/2) = 6331/3840 + 1/46080 = 75973/46080
#guard expPicard 6 (Q.of 1 2) == Q.of 75973 46080
#guard expTaylor 6 (Q.of 1 2) == Q.of 75973 46080

/-- Taylor step recurrence: $P_{n+1}(x) = P_n(x) + \frac{x^{n+1}}{(n+1)!}$. -/
theorem expPicard_succ (n : Nat) (x : Q) :
    expTaylor (n + 1) x = Q.add (expTaylor n x) (taylorTerm x (n + 1)) :=
  expTaylor_succ n x

#print axioms expPicard_succ

/-- Rational constants for Picard iteration. -/
def qZero : Tm [] .rat := .qnat .zero
def qOne : Tm [] .rat := .qnat (.succ .zero)
def qTwo : Tm [] .rat := .qnat (.succ (.succ .zero))
def qHalf : Tm [] .rat := .qdiv qOne qTwo

/-- Step term for Picard iteration $T(y) = 1 + y/2$ on $\mathbb{Q}$. -/
def picardAffineStepTm : Tm [] (.arrow .rat .rat) :=
  .lam (.qadd qOne.wk (.qmul (.var .here) qHalf.wk))

/-- Natural deduction derivation of Picard sequence existence via mathematical induction. -/
def picardAffineDeriv : Deriv .nil (.all .nat (iterInv .rat [] qOne picardAffineStepTm)) :=
  iterSequenceD .rat qOne picardAffineStepTm

/-- The $n$-th iterate of Picard contraction as a System T term: $y_n = T^n(1)$. -/
def picardIterTm : Tm [.nat] .rat :=
  iterTm .rat qOne picardAffineStepTm

/-- The extracted Picard iteration program (EXTRACTED from `picardAffineDeriv`). -/
def picardAffineExtracted (n : Nat) : Q :=
  ((extractClosed picardAffineDeriv).eval Env.nil n).1

-- Extracted Picard Contraction Sequence (EXTRACTED, tautological specification):
-- T⁰(1) = 1
#guard picardAffineExtracted 0 == Q.of 1 1

-- T¹(1) = 1 + 1/2 = 3/2
#guard picardAffineExtracted 1 == Q.of 3 2

-- T²(1) = 1 + 3/4 = 7/4
#guard picardAffineExtracted 2 == Q.of 7 4

-- T³(1) = 1 + 7/8 = 15/8
#guard picardAffineExtracted 3 == Q.of 15 8

-- T⁴(1) = 1 + 15/16 = 31/16
#guard picardAffineExtracted 4 == Q.of 31 16

-- T⁵(1) = 1 + 31/32 = 63/32
#guard picardAffineExtracted 5 == Q.of 63 32

-- T⁶(1) = 1 + 63/64 = 127/64
#guard picardAffineExtracted 6 == Q.of 127 64

/-! ## 4. Certified Answer: The Picard Fixed Point via Sperner's Discrete IVT

The contrast between the two extractions:
- `picardAffineExtracted n` computes $T^n(1)$ — its specification is **tautological** ($\forall n. \exists y. y = y_n$).
  It climbs rapidly from below: $1, 3/2, 7/4, 15/8, 31/16, 63/32, 127/64 \to 2$.
- `fnCrossingSol (· × 1/2) 1` **certifies** that $2$ is the unique fixed point ($T(y) = y \iff y/2 = 1$).
  Its specification (`fnCrossingD`) is **GENUINE** and non-tautological, derived from the 1-D Sperner lemma.
-/

-- The Picard fixed point y = 2, certified by the crossing theorem at precision 2⁰ (grid step 1):
#guard fnCrossingX (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 0 5 == 2
#guard fnCrossingSol (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 0 5 == Q.ofNat 2

-- Certified bracket at precision 2⁻¹ (grid step 1/2): k = 4, interval [4/2, 5/2) = [2, 2.5)
#guard fnCrossingX (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 1 10 == 4
#guard fnCrossingSol (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 1 10 == Q.ofNat 2

-- Certified bracket at precision 2⁻² (grid step 1/4): k = 8, interval [8/4, 9/4) = [2, 2.25)
#guard fnCrossingX (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 2 20 == 8
#guard fnCrossingSol (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 2 20 == Q.ofNat 2

-- Certified bracket at precision 2⁻⁴ (grid step 1/16): k = 32, interval [32/16, 33/16) = [2, 2.0625)
#guard fnCrossingX (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 4 80 == 32
#guard fnCrossingSol (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 4 80 == Q.ofNat 2

-- Certified bracket at precision 2⁻⁶ (grid step 1/64): k = 128, interval [128/64, 129/64) = [2, 2.015625)
#guard fnCrossingX (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 6 320 == 128
#guard fnCrossingSol (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 6 320 == Q.ofNat 2

-- The Picard iterate T⁶(1) = 127/64 lies strictly below the certified fixed point 2:
#guard Q.ltN (picardAffineExtracted 6) (fnCrossingSol (fun x ↦ Q.mul (Q.of 1 2) x) (Q.ofNat 1) 6 320) == 1

end HAomega
