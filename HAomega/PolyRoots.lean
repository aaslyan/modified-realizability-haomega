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

/-- Reverse triangle inequality for the $L_1$ norm on $\mathbb{Q}(i)$:
    $|a + b|_1 \ge |b|_1 - |a|_1$. -/
theorem QC.norm1_add_ge_sub (a b : QC) :
    QC.norm1 b - QC.norm1 a ≤ QC.norm1 (QC.add a b) := by
  have h := QC.norm1_add_le (QC.neg a) (QC.add a b)
  have h_neg : QC.norm1 (QC.neg a) = QC.norm1 a := by
    dsimp [QC.norm1, QC.neg]
    rw [Q.val_neg, Q.val_neg, abs_neg, abs_neg]
  have h_cancel : QC.norm1 (QC.add (QC.neg a) (QC.add a b)) = QC.norm1 b := by
    dsimp [QC.norm1, QC.add, QC.neg]
    simp only [Q.val_add, Q.val_neg]
    have h1 : -a.re.val + (a.re.val + b.re.val) = b.re.val := by ring
    have h2 : -a.im.val + (a.im.val + b.im.val) = b.im.val := by ring
    rw [h1, h2]
  linarith

/-- Non-vanishing criterion: if $|w|_1 > 0$, then $w$ cannot have both real and imaginary parts $0$. -/
theorem QC.ne_zero_of_norm1_pos (w : QC) (h : 0 < QC.norm1 w) :
    w.re.val ≠ 0 ∨ w.im.val ≠ 0 := by
  by_contra hc
  push_neg at hc
  dsimp [QC.norm1] at h
  rw [hc.1, hc.2, abs_zero, add_zero] at h
  exact lt_irrefl 0 h

/-- **Theorem (Monic Linear Cauchy Root Exclusion)**:
    For any monic linear polynomial $P(z) = c_0 + z$, if $|z|_1 > |c_0|_1$
    (in particular if $|z|_1 \ge \mathrm{cauchyRadius}\ [c_0, 1]\ 1 = 1 + |c_0|_1$),
    then $|P(z)|_1 \ge |z|_1 - |c_0|_1 > 0$, so $P(z) \ne 0$. -/
theorem monic_linear_root_exclusion (c0 z : QC)
    (hz : QC.norm1 c0 < QC.norm1 z) :
    0 < QC.norm1 (evalPoly [c0, QC.one] z) ∧
    ((evalPoly [c0, QC.one] z).re.val ≠ 0 ∨ (evalPoly [c0, QC.one] z).im.val ≠ 0) := by
  have h_eval : QC.norm1 (evalPoly [c0, QC.one] z) = QC.norm1 (QC.add c0 z) := by
    dsimp [evalPoly, QC.norm1, QC.add, QC.mul, QC.one, QC.zero]
    simp only [Q.val_add, Q.val_sub, Q.val_mul, Q.val_ofNat, Q.val_zero]
    push_cast
    have h1 : c0.re.val + (z.re.val * (1 + (z.re.val * 0 - z.im.val * 0))
        - z.im.val * (0 + (z.re.val * 0 + z.im.val * 0))) = c0.re.val + z.re.val := by ring
    have h2 : c0.im.val + (z.re.val * (0 + (z.re.val * 0 + z.im.val * 0))
        + z.im.val * (1 + (z.re.val * 0 - z.im.val * 0))) = c0.im.val + z.im.val := by ring
    rw [h1, h2]
  have h_rev := QC.norm1_add_ge_sub c0 z
  have h_pos : 0 < QC.norm1 (evalPoly [c0, QC.one] z) := by linarith
  exact ⟨h_pos, QC.ne_zero_of_norm1_pos _ h_pos⟩

/-- Real scalar multiplication in $\mathbb{Q}(i)$ scales the $L_1$ norm exactly by $|r|$:
    $|\langle r, 0 \rangle \cdot w|_1 = |r.\mathrm{val}| \cdot |w|_1$. -/
theorem QC.norm1_mul_real (r : Q) (w : QC) :
    QC.norm1 (QC.mul ⟨r, Q.zero⟩ w) = |r.val| * QC.norm1 w := by
  dsimp [QC.norm1, QC.mul]
  simp only [Q.val_sub, Q.val_add, Q.val_mul, Q.val_zero]
  have h1 : r.val * w.re.val - 0 * w.im.val = r.val * w.re.val := by ring
  have h2 : r.val * w.im.val + 0 * w.re.val = r.val * w.im.val := by ring
  rw [h1, h2, abs_mul, abs_mul, ← mul_add]

/-- **Theorem (Real-Line Cauchy Root Exclusion for Monic Quadratics)**:
    For any monic quadratic $P(z) = c_0 + c_1 z + z^2$ evaluated at $z = \langle r, 0 \rangle$
    with $|r.\mathrm{val}| \ge \mathrm{cauchyRadius}\ [c_0, c_1, 1]\ 1 = 1 + |c_0|_1 + |c_1|_1$,
    we have $|P(r)|_1 \ge 1 > 0$, hence $P(r) \ne 0$. -/
theorem monic_quadratic_cauchy_exclusion (c0 c1 : QC) (r : Q)
    (hr : cauchyRadius [c0, c1, QC.one] 1 ≤ |r.val|) :
    1 ≤ QC.norm1 (evalPoly [c0, c1, QC.one] ⟨r, Q.zero⟩) ∧
    ((evalPoly [c0, c1, QC.one] ⟨r, Q.zero⟩).re.val ≠ 0 ∨
     (evalPoly [c0, c1, QC.one] ⟨r, Q.zero⟩).im.val ≠ 0) := by
  have h_rad : cauchyRadius [c0, c1, QC.one] 1 = 1 + (QC.norm1 c0 + QC.norm1 c1) := by
    dsimp [cauchyRadius, lowerCoeffNormSum, List.dropLast]
    ring
  rw [h_rad] at hr
  have hc0_nn : 0 ≤ QC.norm1 c0 := by dsimp [QC.norm1]; positivity
  have hc1_nn : 0 ≤ QC.norm1 c1 := by dsimp [QC.norm1]; positivity
  have hr_ge1 : 1 ≤ |r.val| := by linarith
  set z : QC := ⟨r, Q.zero⟩
  have h_step2 : QC.norm1 (QC.add QC.one (QC.mul z QC.zero)) = 1 := by
    dsimp [QC.norm1, QC.add, QC.mul, QC.one, QC.zero]
    simp only [Q.val_add, Q.val_sub, Q.val_mul, Q.val_ofNat, Q.val_zero]
    norm_num
  have h_step1_mul : QC.norm1 (QC.mul z (QC.add QC.one (QC.mul z QC.zero))) = |r.val| := by
    rw [QC.norm1_mul_real, h_step2, mul_one]
  set q1 := QC.add c1 (QC.mul z (QC.add QC.one (QC.mul z QC.zero)))
  have h_q1 : |r.val| - QC.norm1 c1 ≤ QC.norm1 q1 := by
    have := QC.norm1_add_ge_sub c1 (QC.mul z (QC.add QC.one (QC.mul z QC.zero)))
    linarith
  have h_step0_mul : QC.norm1 (QC.mul z q1) = |r.val| * QC.norm1 q1 :=
    QC.norm1_mul_real r q1
  have h_q0 : |r.val| * QC.norm1 q1 - QC.norm1 c0 ≤ QC.norm1 (evalPoly [c0, c1, QC.one] z) := by
    dsimp [evalPoly]
    have := QC.norm1_add_ge_sub c0 (QC.mul z q1)
    linarith
  have h_q1_ge : 1 + QC.norm1 c0 ≤ QC.norm1 q1 := by linarith
  have h_prod : 1 + QC.norm1 c0 ≤ |r.val| * QC.norm1 q1 := by
    calc 1 + QC.norm1 c0
      _ = 1 * (1 + QC.norm1 c0) := by ring
      _ ≤ |r.val| * QC.norm1 q1 := mul_le_mul hr_ge1 h_q1_ge (by linarith) (by linarith)
  have h_ge1 : 1 ≤ QC.norm1 (evalPoly [c0, c1, QC.one] z) := by linarith
  exact ⟨h_ge1, QC.ne_zero_of_norm1_pos _ (by linarith)⟩

#print axioms monic_linear_root_exclusion
#print axioms monic_quadratic_cauchy_exclusion

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
