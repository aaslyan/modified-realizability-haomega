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
# Euler–Maclaurin Summation: Power Sums and Bernoulli Correction Values

This module formalizes discrete power sums and Euler–Maclaurin algebraic identities:

1. **Discrete Power Sum Operator (`discreteSum`)**:
   $$S(f, N) = \sum_{k=1}^N f(k)$$

2. **Linear Sum Formula Identity (`linear_sum_formula_id`)**:
   $$\frac{N^2}{2} + \frac{N}{2} = \frac{N(N+1)}{2}$$

3. **Quadratic Sum Formula with $B_2 = 1/6$ (`quadratic_sum_formula_id`)**:
   $$\frac{N^3}{3} + \frac{N^2}{2} + \frac{1/6}{2}(2N) = \frac{N(N+1)(2N+1)}{6}$$

4. **Kernel-Verified Summation Computations**:
   Verified `#guard` calculations checking exact discrete power sums for integers and squares.
-/

namespace HAomega

open Rat

/-! ## 1. Discrete Sum and Bernoulli Constant -/

/-- Discrete sum $\sum_{k=1}^N f(k)$. -/
def discreteSum (f : Nat → Q) (N : Nat) : Q :=
  (List.range N).foldl (fun acc i ↦ Q.add acc (f (i + 1))) Q.zero

/-- First Bernoulli number $B_2 = 1/6$. -/
def B2 : Rat := 1 / 6

/-! ## 2. Exact Algebraic Identities for Monomial Sums -/

/-- **Theorem (Linear Sum Algebraic Identity)**:
    $\frac{N^2}{2} + \frac{N}{2} = \frac{N(N+1)}{2}$. -/
theorem linear_sum_formula_id (N : Rat) :
    N ^ 2 / 2 + N / 2 = N * (N + 1) / 2 := by
  ring

#print axioms linear_sum_formula_id

/-- **Theorem (Quadratic Sum Algebraic Identity with $B_2 = 1/6$)**:
    $\frac{N^3}{3} + \frac{N^2}{2} + \frac{1/6}{2}(2N) = \frac{N(N+1)(2N+1)}{6}$. -/
theorem quadratic_sum_formula_id (N : Rat) :
    N ^ 3 / 3 + N ^ 2 / 2 + (1 / 6 : Rat) / 2 * (2 * N) =
      N * (N + 1) * (2 * N + 1) / 6 := by
  ring

#print axioms quadratic_sum_formula_id

/-! ## 3. Verified Kernel Computations for Discrete Sums -/

-- Sum of first 4 integers: 1 + 2 + 3 + 4 = 10
#guard discreteSum (fun k ↦ Q.ofNat k) 4 == Q.ofNat 10
-- Formula: 4 * 5 / 2 = 10
#guard (let N := Q.ofNat 4; Q.div (Q.mul N (Q.add N (Q.ofNat 1))) (Q.ofNat 2)) == Q.ofNat 10

-- Sum of first 4 squares: 1 + 4 + 9 + 16 = 30
#guard discreteSum (fun k ↦ Q.mul (Q.ofNat k) (Q.ofNat k)) 4 == Q.ofNat 30
-- Formula: 4 * 5 * 9 / 6 = 180 / 6 = 30
#guard (let N := Q.ofNat 4;
        let num := Q.mul (Q.mul N (Q.add N (Q.ofNat 1))) (Q.add (Q.mul (Q.ofNat 2) N) (Q.ofNat 1));
        Q.div num (Q.ofNat 6)) == Q.ofNat 30

-- Sum of first 10 squares: 1 + 4 + 9 + ... + 100 = 385
#guard discreteSum (fun k ↦ Q.mul (Q.ofNat k) (Q.ofNat k)) 10 == Q.ofNat 385
-- Formula: 10 * 11 * 21 / 6 = 2310 / 6 = 385
#guard (let N := Q.ofNat 10;
        let num := Q.mul (Q.mul N (Q.add N (Q.ofNat 1))) (Q.add (Q.mul (Q.ofNat 2) N) (Q.ofNat 1));
        Q.div num (Q.ofNat 6)) == Q.ofNat 385

end HAomega
