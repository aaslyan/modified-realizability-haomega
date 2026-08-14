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
import HAomega.ComplexAnalysis

/-!
# Polynomial Root Calculus: Horner Scheme, Cauchy Radius, and Linear Roots in $\mathbb{Q}(i)$

This module formalizes polynomial operations and root calculus over Gaussian rationals $\mathbb{Q}(i)$:

1. **Complex Polynomials $\mathbb{Q}(i)[z]$ (`evalPoly`)**:
   Polynomials $P(z) = \sum_{j=0}^n c_j z^j$ with Gaussian rational coefficients
   $c_j \in \mathbb{Q}(i)$, evaluated via Horner's scheme.

2. **Cauchy Root Radius (`cauchy_bound_dominance`)**:
   For any polynomial with leading coefficient $c_n \neq 0$, the Cauchy radius bound:
   $$R = 1 + \frac{\sum_{j=0}^{n-1} \|c_j\|_1}{\|c_n\|_1}$$
   satisfies $R \ge 1$, bounding the search region for roots.

3. **Exact Linear Root Evaluation (`linear_root_val`)**:
   For any monic linear polynomial $P(z) = z - z_0$, evaluating at $z_0$ yields $0 \in \mathbb{Q}(i)$.

4. **Kernel-Verified Computations**:
   Verified `#guard` assertions evaluating quadratic and linear roots in the Lean 4 kernel:
   - $P(z) = z^2 + 1 \implies P(\pm i) = 0$
   - $P(z) = z^2 - 2 \implies P(99/70) = 1/4900 \approx 0.000204 < 2^{-12}$.
-/

namespace HAomega

open Rat

/-! ## 1. Polynomials over Gaussian Rationals $\mathbb{Q}(i)$ -/

/-- Polynomial with coefficients in $\mathbb{Q}(i)$ in ascending order:
    $[c_0, c_1, \dots, c_n]$ represents $\sum_{j=0}^n c_j z^j$. -/
def PolyQC := List QC

/-- Horner's polynomial evaluation: $P(z) = c_0 + z(c_1 + z(\dots))$. -/
def evalPoly (p : PolyQC) (z : QC) : QC :=
  p.foldr (fun c acc ↦ QC.add c (QC.mul z acc)) QC.zero

/-- Degree of a polynomial (length minus 1). -/
def polyDeg (p : PolyQC) : Nat :=
  p.length - 1

/-! ## 2. Cauchy Root Radius Bound -/

/-- Sum of $L_1$ norms of lower coefficients $\sum_{j=0}^{n-1} \|c_j\|_1$. -/
def lowerCoeffNormSum (p : PolyQC) : Rat :=
  (p.dropLast.map QC.norm1).foldl (· + ·) 0

/-- Cauchy root bound: for leading coefficient norm $L > 0$,
    $R = 1 + \frac{\sum_{j < n} \|c_j\|_1}{L}$. -/
def cauchyRadius (p : PolyQC) (leadNorm : Rat) : Rat :=
  1 + lowerCoeffNormSum p / leadNorm

/-- **Theorem (Cauchy Root Bound Property)**:
    For any leading coefficient norm $L > 0$, the Cauchy radius satisfies $R \ge 1$. -/
theorem cauchy_bound_dominance (p : PolyQC) (leadNorm : Rat) (hL : 0 < leadNorm)
    (h_sum : 0 ≤ lowerCoeffNormSum p) :
    1 ≤ cauchyRadius p leadNorm := by
  dsimp [cauchyRadius]
  have : 0 ≤ lowerCoeffNormSum p / leadNorm := div_nonneg h_sum (le_of_lt hL)
  linarith

#print axioms cauchy_bound_dominance

/-! ## 3. Linear Root Extraction -/

/-- Exact root value of a monic linear polynomial $P(z) = z - z_0$: evaluates to $0 \in \mathbb{Q}(i)$. -/
theorem linear_root_val (z0 : QC) :
    (evalPoly [QC.neg z0, QC.one] z0).re.val = 0 ∧
    (evalPoly [QC.neg z0, QC.one] z0).im.val = 0 := by
  dsimp [evalPoly, QC.mul, QC.add, QC.neg, QC.one, QC.zero]
  constructor
  · simp only [Q.val_add, Q.val_sub, Q.val_mul, Q.val_neg, Q.val_ofNat, Q.val_zero]
    ring
  · simp only [Q.val_add, Q.val_sub, Q.val_mul, Q.val_neg, Q.val_ofNat, Q.val_zero]
    ring

#print axioms linear_root_val

/-! ## 4. Verified Kernel Computations for Polynomial Roots -/

-- P(z) = z - (1 + 2i) has root z = 1 + 2i
#guard evalPoly [QC.neg ⟨Q.ofNat 1, Q.ofNat 2⟩, QC.one] ⟨Q.ofNat 1, Q.ofNat 2⟩ == QC.zero

-- P(z) = z² + 1 has root z = i = (0 + 1i)
-- [1 + 0i, 0, 1 + 0i] evaluated at i is 0
#guard evalPoly [QC.one, QC.zero, QC.one] QC.I == QC.zero

-- P(z) = z² + 1 evaluated at -i is 0
#guard evalPoly [QC.one, QC.zero, QC.one] (QC.neg QC.I) == QC.zero

-- P(z) = z² - 2 has roots z ≈ ±1.41421...
-- Evaluated at rational approximation 7/5 = 1.4:
-- P(7/5) = 49/25 - 2 = -1/25 = -0.04
#guard evalPoly [⟨Q.of (-2) 1, Q.zero⟩, QC.zero, QC.one] ⟨Q.of 7 5, Q.zero⟩
  == ⟨Q.of (-1) 25, Q.zero⟩

-- Evaluated at rational approximation 99/70 ≈ 1.4142857:
-- P(99/70) = 9801/4900 - 2 = 1/4900 ≈ 0.000204 (< 2⁻¹²)
#guard evalPoly [⟨Q.of (-2) 1, Q.zero⟩, QC.zero, QC.one] ⟨Q.of 99 70, Q.zero⟩
  == ⟨Q.of 1 4900, Q.zero⟩

end HAomega
