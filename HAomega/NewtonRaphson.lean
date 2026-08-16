/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.Picard
import HAomega.GaloisAdequacy
import HAomega.FixedPoint
import HAomega.IVT
import HAomega.ModulusClosure
import HAomega.ODEDemo
import HAomega.Taylor
import HAomega.HarmonicODE
import HAomega.AnalysisDeriv
import HAomega.SquareRoot

/-!
# Newton–Raphson Method and Quadratic Error Contraction

This module formalizes the **Newton–Raphson root extraction method** on $\mathbb{Q}$:

1. **Newton Iteration Operator (`newtonSqrtStep`)**:
   For $\sqrt{a}$, the Babylonian/Newton step is:
   $$x_{n+1} = \frac{1}{2}\left(x_n + \frac{a}{x_n}\right)$$

2. **Quadratic Error Contraction Theorem (`newton_sqrt_quadratic_error`)**:
   For any positive rational approximation $x > 0$ and target $a > 0$:
   $$x_{n+1}^2 - a = \frac{(x_n^2 - a)^2}{4 x_n^2}$$
   proving that the residual error squares at every single iteration, doubling the
   number of correct digits of precision.

3. **Newton Step Recurrence in System T (`tmNewtonSqrtStep`)**:
   Formalized as a closed executable recursor term in $\mathrm{Tm}$.

4. **Kernel-Verified High-Precision Computations**:
   Verified `#guard` calculations in the Lean 4 kernel:
   - $x_0 = 1$
   - $x_1 = 3/2 = 1.5$
   - $x_2 = 17/12 \approx 1.4166667$
   - $x_3 = 577/408 \approx 1.414215686$ (error $\approx 2 \cdot 10^{-6}$)
   - $x_4 = 665857/470832 \approx 1.41421356237469$ (error $< 2 \cdot 10^{-12}$).
-/

namespace HAomega

open Rat

/-! ## 1. Newton Sqrt Iteration Operator -/

/-- Single Newton step for computing $\sqrt{a}$: $x \mapsto \frac{1}{2}(x + a/x)$. -/
def newtonSqrtStep (a : Q) (x : Q) : Q :=
  Q.div (Q.add x (Q.div a x)) (Q.ofNat 2)

/-- $n$-th Newton iterate for $\sqrt{a}$ starting at $x_0$. -/
def newtonSqrtIter (a : Q) (x0 : Q) : Nat → Q
  | 0 => x0
  | n + 1 => newtonSqrtStep a (newtonSqrtIter a x0 n)

/-! ## 2. The Quadratic Error Contraction Theorem -/

/-- **Theorem (Exact Quadratic Contraction for Newton Square Root)**:
    The residual $x_{next}^2 - a$ equals exactly $\frac{(x^2 - a)^2}{4 x^2}$.
    This proves that the residual error squares at every iteration! -/
theorem newton_sqrt_quadratic_error (a x : Rat) (hx : x ≠ 0) :
    ((1 / 2 : Rat) * (x + a / x)) ^ 2 - a = (x ^ 2 - a) ^ 2 / (4 * x ^ 2) := by
  have _h4x2 : 4 * x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

#print axioms newton_sqrt_quadratic_error

/-- **Theorem (Positivity of Sqrt Iterates)**:
    For any $a > 0$ and $x > 0$, the next iterate is strictly positive. -/
theorem newton_step_pos (a x : Rat) (ha : 0 < a) (hx : 0 < x) :
    0 < (1 / 2 : Rat) * (x + a / x) := by
  have : 0 < a / x := div_pos ha hx
  have : 0 < x + a / x := add_pos hx this
  linarith

#print axioms newton_step_pos

/-! ## 3. Object-Level Newton Operator in System T and Realizer Extraction -/

/-- Closed step term for √2: `(x + 2/x)/2`. -/
def newtonSqrt2StepTm : Tm [] (.arrow .rat .rat) :=
  .lam (
    let x_val : Tm (.rat :: []) .rat := Tm.var .here
    let two : Tm (.rat :: []) .rat := Tm.qnat (Tm.succ (Tm.succ Tm.zero))
    let two_div_x := Tm.qdiv two x_val
    let sum := Tm.qadd x_val two_div_x
    Tm.qdiv sum two
  )

/-- Closed step term for √3: `(x + 3/x)/2`. -/
def newtonSqrt3StepTm : Tm [] (.arrow .rat .rat) :=
  .lam (
    let x_val : Tm (.rat :: []) .rat := Tm.var .here
    let three : Tm (.rat :: []) .rat := Tm.qnat (Tm.succ (Tm.succ (Tm.succ Tm.zero)))
    let two : Tm (.rat :: []) .rat := Tm.qnat (Tm.succ (Tm.succ Tm.zero))
    let three_div_x := Tm.qdiv three x_val
    let sum := Tm.qadd x_val three_div_x
    Tm.qdiv sum two
  )

/-- Natural deduction derivation of the Newton sequence for √2 from initial guess x₀ = 1. -/
def newtonSqrt2Deriv : Deriv .nil (.all .nat (iterInv .rat [] (.qnat (.succ .zero)) newtonSqrt2StepTm)) :=
  iterSequenceD .rat (.qnat (.succ .zero)) newtonSqrt2StepTm

/-- Natural deduction derivation of the Newton sequence for √3 from initial guess x₀ = 1. -/
def newtonSqrt3Deriv : Deriv .nil (.all .nat (iterInv .rat [] (.qnat (.succ .zero)) newtonSqrt3StepTm)) :=
  iterSequenceD .rat (.qnat (.succ .zero)) newtonSqrt3StepTm

/-- The extracted **program** for √2 Newton iteration (EXTRACTED from `newtonSqrt2Deriv`). -/
def newtonSqrt2Extracted (n : Nat) : Q :=
  ((extractClosed newtonSqrt2Deriv).eval Env.nil n).1

/-- The extracted **program** for √3 Newton iteration (EXTRACTED from `newtonSqrt3Deriv`). -/
def newtonSqrt3Extracted (n : Nat) : Q :=
  ((extractClosed newtonSqrt3Deriv).eval Env.nil n).1

/-- Closed Newton step term in System T: `fun a x ↦ (x + a / x) / 2`. -/
def tmNewtonSqrtStep {Γ : List Ty} :
    Tm Γ (.arrow .rat (.arrow .rat .rat)) :=
  .lam -- a : rat
    (.lam -- x : rat
      (let a_val : Tm (.rat :: .rat :: Γ) .rat := Tm.var (.there .here)
       let x_val : Tm (.rat :: .rat :: Γ) .rat := Tm.var .here
       let a_div_x := Tm.qdiv a_val x_val
       let sum := Tm.qadd x_val a_div_x
       let two := Tm.qnat (Tm.succ (Tm.succ Tm.zero))
       Tm.qdiv sum two))

/-- Step term for Newton recursion in context `[acc, k, N, x0, a, Γ...]`. -/
def tmNewtonSqrtRecStep {Γ : List Ty} :
    Tm (.rat :: .nat :: .nat :: .rat :: .rat :: Γ) .rat :=
  let acc_val : Tm (.rat :: .nat :: .nat :: .rat :: .rat :: Γ) .rat := Tm.var .here
  let a_val : Tm (.rat :: .nat :: .nat :: .rat :: .rat :: Γ) .rat := Tm.var (.there (.there (.there (.there .here))))
  let a_div_acc := Tm.qdiv a_val acc_val
  let sum := Tm.qadd acc_val a_div_acc
  let two := Tm.qnat (Tm.succ (Tm.succ Tm.zero))
  Tm.qdiv sum two

/-- Closed Newton sqrt iterator in System T (OBJECT-RUN):
    `fun a x0 N ↦ recNat x0 (fun k acc ↦ (acc + a / acc) / 2) N`. -/
def tmNewtonSqrtIter {Γ : List Ty} :
    Tm Γ (.arrow .rat (.arrow .rat (.arrow .nat .rat))) :=
  .lam -- a
    (.lam -- x0
      (.lam -- N
        (.recNat (.var (.there .here)) (.lam (.lam tmNewtonSqrtRecStep)) (.var .here))))

/-- Direct System T evaluation of the Newton sqrt iterator term (OBJECT-RUN). -/
def runNewtonSqrtIter (a : Q) (x0 : Q) (N : Nat) : Q :=
  (tmNewtonSqrtIter (Γ := [])).eval Env.nil a x0 N

/-! ## 4. Verified High-Precision Computations in Lean 4 Kernel -/

-- Approximating √2 with x₀ = 1 via EXTRACTED realizer from newtonSqrt2Deriv:
-- Iteration 0: x₀ = 1
#guard newtonSqrt2Extracted 0 == Q.ofNat 1

-- Iteration 1: x₁ = 3/2 = 1.5 (x₁² - 2 = 9/4 - 2 = 1/4 = 0.25)
#guard newtonSqrt2Extracted 1 == Q.of 3 2

-- Iteration 2: x₂ = 17/12 ≈ 1.416667 (x₂² - 2 = 289/144 - 2 = 1/144 ≈ 0.00694)
#guard newtonSqrt2Extracted 2 == Q.of 17 12

-- Iteration 3: x₃ = 577/408 ≈ 1.414215686 (x₃² - 2 = 1/166464 ≈ 0.0000060)
#guard newtonSqrt2Extracted 3 == Q.of 577 408

-- Iteration 4: x₄ = 665857/470832 ≈ 1.41421356237469 (x₄² - 2 = 1/221682772224 ≈ 4.5 * 10⁻¹²)
#guard newtonSqrt2Extracted 4 == Q.of 665857 470832

-- Approximating √3 with x₀ = 1 via EXTRACTED realizer from newtonSqrt3Deriv:
-- Iteration 1: (1 + 3/1)/2 = 2
#guard newtonSqrt3Extracted 1 == Q.ofNat 2

-- Iteration 2: (2 + 3/2)/2 = 7/4 = 1.75
#guard newtonSqrt3Extracted 2 == Q.of 7 4

-- Iteration 3: (7/4 + 12/7)/2 = 97/56 ≈ 1.73214 (x₃² - 3 = 1/3136 ≈ 0.000318)
#guard newtonSqrt3Extracted 3 == Q.of 97 56

-- Iteration 4: 18817/10864 ≈ 1.73205081 (x₄² - 3 = 1/118026496 ≈ 8.4 * 10⁻⁹)
#guard newtonSqrt3Extracted 4 == Q.of 18817 10864

/-! ## 5. Certified Answers: Newton Convergence Checked Against Non-Tautological Brackets

The pairing between fast iteration and genuine certification:
- `newtonSqrt2Extracted` and `newtonSqrt3Extracted` compute quadratically fast:
  - $x_4(\sqrt{2}) = 665857/470832 \approx 1.41421356237469$ (12 correct digits).
  - $x_4(\sqrt{3}) = 18817/10864 \approx 1.73205081$ (8 correct digits).
  Their formal specification (`newtonSqrt2Deriv`, `newtonSqrt3Deriv`) is **tautological** ($\forall n. \exists y. y = x_n$).
- `sqrtApproxD` and `fnCrossingD` **certify** the root brackets through Sperner's discrete IVT — a **GENUINE**, non-tautological higher-type derivation.

Below, kernel `#guard`s verify that the fast, uncertified Newton answers land strictly inside the certified intervals at matching precisions.
-/

-- √2: Newton's 4th iterate lands inside the certified interval [362/256, 363/256) at precision 2⁻⁸:
#guard sqrtApprox (Q.ofNat 2) 8 512 == Q.of 181 128
#guard Q.ltN (sqrtApprox (Q.ofNat 2) 8 512) (newtonSqrt2Extracted 4) == 1
#guard Q.ltN (newtonSqrt2Extracted 4) (Q.add (sqrtApprox (Q.ofNat 2) 8 512) (D.toQ (D.pow2neg 8))) == 1

-- √3: Newton's 4th iterate lands inside the certified interval [443/256, 444/256) at precision 2⁻⁸:
#guard fnCrossingSol (fun x ↦ Q.mul x x) (Q.ofNat 3) 8 1024 == Q.of 443 256
#guard Q.ltN (fnCrossingSol (fun x ↦ Q.mul x x) (Q.ofNat 3) 8 1024) (newtonSqrt3Extracted 4) == 1
#guard Q.ltN (newtonSqrt3Extracted 4) (Q.add (fnCrossingSol (fun x ↦ Q.mul x x) (Q.ofNat 3) 8 1024) (D.toQ (D.pow2neg 8))) == 1

end HAomega
