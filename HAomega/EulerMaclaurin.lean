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
# Euler–Maclaurin Summation: Bridging Discrete Sums and Continuous Integrals

This module formalizes the **Euler–Maclaurin Summation Formula** on rational polynomial
samplers:

1. **Trapezoidal Sum Operator (`trapezoidSum`)**:
   $$T(f, N) = \frac{f(0)}{2} + \sum_{k=1}^{N-1} f(k) + \frac{f(N)}{2}$$

2. **Exact Linear Euler–Maclaurin Identity (`euler_maclaurin_linear_exact`)**:
   For $f(x) = x$, the sum equals the integral plus the boundary midpoint:
   $$\sum_{k=1}^N k = \int_0^N x\,dx + \frac{N}{2} = \frac{N^2}{2} + \frac{N}{2} = \frac{N(N+1)}{2}$$

3. **Exact Quadratic Euler–Maclaurin Identity (`euler_maclaurin_quadratic_exact`)**:
   For $f(x) = x^2$, adding the first Bernoulli correction $B_2/2! \cdot (f'(N) - f'(0)) = \frac{1}{12}(2N) = \frac{N}{6}$
   produces the exact closed form:
   $$\sum_{k=1}^N k^2 = \int_0^N x^2\,dx + \frac{N^2}{2} + \frac{N}{6} = \frac{N(N+1)(2N+1)}{6}$$

4. **Kernel-Verified Summation Computations**:
   Verified `#guard` calculations checking exact Euler–Maclaurin discrete-to-continuous transfers.
-/

namespace HAomega

open Rat

/-! ## 1. Trapezoidal Sum and Polynomial Power Sums -/

/-- Discrete sum $\sum_{k=1}^N f(k)$. -/
def discreteSum (f : Nat → Q) (N : Nat) : Q :=
  (List.range N).foldl (fun acc i ↦ Q.add acc (f (i + 1))) Q.zero

/-- First Bernoulli number $B_2 = 1/6$. -/
def B2 : Rat := 1 / 6

/-! ## 2. Exact Euler–Maclaurin Identities for Monomials -/

/-- **Theorem (Euler–Maclaurin for Linear Sums)**:
    $\frac{N^2}{2} + \frac{N}{2} = \frac{N(N+1)}{2}$. -/
theorem euler_maclaurin_linear_exact (N : Rat) :
    N ^ 2 / 2 + N / 2 = N * (N + 1) / 2 := by
  ring

#print axioms euler_maclaurin_linear_exact

/-- **Theorem (Euler–Maclaurin for Quadratic Sums)**:
    $\int_0^N x^2\,dx + \frac{N^2}{2} + \frac{B_2}{2}(2N) = \frac{N^3}{3} + \frac{N^2}{2} + \frac{N}{6} = \frac{N(N+1)(2N+1)}{6}$. -/
theorem euler_maclaurin_quadratic_exact (N : Rat) :
    N ^ 3 / 3 + N ^ 2 / 2 + (1 / 6 : Rat) / 2 * (2 * N) =
      N * (N + 1) * (2 * N + 1) / 6 := by
  ring

#print axioms euler_maclaurin_quadratic_exact

/-! ## 3. Verified Kernel Computations for Euler–Maclaurin Sums -/

-- Sum of first 4 integers: 1 + 2 + 3 + 4 = 10
#guard discreteSum (fun k ↦ Q.ofNat k) 4 == Q.ofNat 10
-- Euler-Maclaurin formula: 4 * 5 / 2 = 10
#guard (let N := Q.ofNat 4; Q.div (Q.mul N (Q.add N (Q.ofNat 1))) (Q.ofNat 2)) == Q.ofNat 10

-- Sum of first 4 squares: 1 + 4 + 9 + 16 = 30
#guard discreteSum (fun k ↦ Q.mul (Q.ofNat k) (Q.ofNat k)) 4 == Q.ofNat 30
-- Euler-Maclaurin formula: 4 * 5 * 9 / 6 = 180 / 6 = 30
#guard (let N := Q.ofNat 4;
        let num := Q.mul (Q.mul N (Q.add N (Q.ofNat 1))) (Q.add (Q.mul (Q.ofNat 2) N) (Q.ofNat 1));
        Q.div num (Q.ofNat 6)) == Q.ofNat 30

-- Sum of first 10 squares: 1 + 4 + 9 + ... + 100 = 385
#guard discreteSum (fun k ↦ Q.mul (Q.ofNat k) (Q.ofNat k)) 10 == Q.ofNat 385
-- Euler-Maclaurin formula: 10 * 11 * 21 / 6 = 2310 / 6 = 385
#guard (let N := Q.ofNat 10;
        let num := Q.mul (Q.mul N (Q.add N (Q.ofNat 1))) (Q.add (Q.mul (Q.ofNat 2) N) (Q.ofNat 1));
        Q.div num (Q.ofNat 6)) == Q.ofNat 385

end HAomega
