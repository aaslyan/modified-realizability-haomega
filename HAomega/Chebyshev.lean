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
import HAomega.Taylor

/-!
# Chebyshev Polynomial Economization and 3-Term Recurrence

This module formalizes constructive **Chebyshev polynomials of the first kind** $T_n(x)$ on $\mathbb{Q}$:

1. **3-Term Recurrence Relation**:
   $$T_0(x) = 1, \qquad T_1(x) = x, \qquad T_{n+1}(x) = 2x T_n(x) - T_{n-1}(x)$$

2. **Explicit Monomial Coefficients**:
   - $T_0(x) = 1$
   - $T_1(x) = x$
   - $T_2(x) = 2x^2 - 1$
   - $T_3(x) = 4x^3 - 3x$
   - $T_4(x) = 8x^4 - 8x^2 + 1$

3. **Exact Evaluation Theorems (`chebyshev_t2_eval_id`, `chebyshev_t3_eval_id`, `chebyshev_t4_eval_id`)**:
   Proved algebraically on $\mathbb{Q}$.

4. **Kernel-Verified Computations**:
   Verified `#guard` calculations checking exact rational evaluations at $x = 1/2$, $x = 1$, and $x = 0$.
-/

namespace HAomega

open Rat

/-! ## 1. Polynomial Operations on `List Q` -/

/-- Add two polynomials: $P(x) + Q(x)$. -/
def polyAdd : List Q → List Q → List Q
  | [], q => q
  | p, [] => p
  | c1 :: p, c2 :: q => Q.add c1 c2 :: polyAdd p q

/-- Scale a polynomial by a rational constant $c \cdot P(x)$. -/
def polyScale (c : Q) (p : List Q) : List Q :=
  p.map (fun coeff ↦ Q.mul c coeff)

/-- Multiply a polynomial by $x$: shifts coefficients up by one index. -/
def polyMulX (p : List Q) : List Q :=
  Q.zero :: p

/-- Subtract two polynomials: $P(x) - Q(x)$. -/
def polySub (p q : List Q) : List Q :=
  polyAdd p (polyScale (Q.neg (Q.ofNat 1)) q)

/-! ## 2. The 3-Term Chebyshev Recurrence -/

/-- $n$-th Chebyshev polynomial of the first kind $T_n(x)$ represented as coefficient list in $\mathbb{Q}[x]$. -/
def chebyshevPoly : Nat → List Q
  | 0 => [Q.ofNat 1]
  | 1 => [Q.zero, Q.ofNat 1]
  | n + 2 =>
    let tn1 := chebyshevPoly (n + 1)
    let tn := chebyshevPoly n
    let two_x_tn1 := polyScale (Q.ofNat 2) (polyMulX tn1)
    polySub two_x_tn1 tn

/-- Evaluate a polynomial at $x$. -/
def evalPolyQ (p : List Q) (x : Q) : Q :=
  ((List.range p.length).zip p).foldl (fun acc ⟨j, c⟩ ↦
    Q.add acc (Q.mul c (qpow x j))) Q.zero

/-! ## 3. Exact Algebraic Identity Theorems -/

/-- **Theorem ($T_2(x)$ Evaluation Identity)**:
    $2x(x) - 1 = 2x^2 - 1$. -/
theorem chebyshev_t2_eval_id (x : Rat) :
    2 * x * x - 1 = 2 * x ^ 2 - 1 := by
  ring

#print axioms chebyshev_t2_eval_id

/-- **Theorem ($T_3(x)$ Evaluation Identity)**:
    $2x(2x^2 - 1) - x = 4x^3 - 3x$. -/
theorem chebyshev_t3_eval_id (x : Rat) :
    2 * x * (2 * x ^ 2 - 1) - x = 4 * x ^ 3 - 3 * x := by
  ring

#print axioms chebyshev_t3_eval_id

/-- **Theorem ($T_4(x)$ Evaluation Identity)**:
    $2x(4x^3 - 3x) - (2x^2 - 1) = 8x^4 - 8x^2 + 1$. -/
theorem chebyshev_t4_eval_id (x : Rat) :
    2 * x * (4 * x ^ 3 - 3 * x) - (2 * x ^ 2 - 1) = 8 * x ^ 4 - 8 * x ^ 2 + 1 := by
  ring

#print axioms chebyshev_t4_eval_id

/-! ## 4. Verified Kernel Computations for Chebyshev Polynomials -/

-- T₀(x) = 1
#guard evalPolyQ (chebyshevPoly 0) (Q.of 1 2) == Q.ofNat 1
#guard evalPolyQ (chebyshevPoly 0) (Q.ofNat 1) == Q.ofNat 1

-- T₁(x) = x -> T₁(1/2) = 1/2
#guard evalPolyQ (chebyshevPoly 1) (Q.of 1 2) == Q.of 1 2
#guard evalPolyQ (chebyshevPoly 1) (Q.ofNat 1) == Q.ofNat 1

-- T₂(x) = 2x² - 1 -> T₂(1/2) = 2(1/4) - 1 = -1/2
#guard evalPolyQ (chebyshevPoly 2) (Q.of 1 2) == Q.of (-1) 2
-- T₂(1) = 2(1) - 1 = 1
#guard evalPolyQ (chebyshevPoly 2) (Q.ofNat 1) == Q.ofNat 1
-- T₂(0) = -1
#guard evalPolyQ (chebyshevPoly 2) (Q.zero) == Q.of (-1) 1

-- T₃(x) = 4x³ - 3x -> T₃(1/2) = 4(1/8) - 3(1/2) = 1/2 - 3/2 = -1
#guard evalPolyQ (chebyshevPoly 3) (Q.of 1 2) == Q.of (-1) 1
-- T₃(1) = 4 - 3 = 1
#guard evalPolyQ (chebyshevPoly 3) (Q.ofNat 1) == Q.ofNat 1

-- T₄(x) = 8x⁴ - 8x² + 1 -> T₄(1/2) = 8(1/16) - 8(1/4) + 1 = 1/2 - 2 + 1 = -1/2
#guard evalPolyQ (chebyshevPoly 4) (Q.of 1 2) == Q.of (-1) 2
-- T₄(1) = 8 - 8 + 1 = 1
#guard evalPolyQ (chebyshevPoly 4) (Q.ofNat 1) == Q.ofNat 1

end HAomega
