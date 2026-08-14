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
import HAomega.Transcendental
import HAomega.PolyRoots

/-!
# Leibniz Product Rule and Monomial Integration by Parts

This module formalizes the algebraic core of the Leibniz product rule and monomial
integration by parts:

1. **Leibniz Product Difference Quotient Decomposition (`leibniz_diff_quot_split`)**:
   Algebraic decomposition of a product difference quotient:
   $$\frac{u(x+h)v(x+h) - u(x)v(x)}{h} = \frac{u(x+h) - u(x)}{h} v(x+h) + u(x) \frac{v(x+h) - v(x)}{h}$$

2. **Leibniz Error 3-Term Split (`leibniz_error_split`)**:
   Decomposition of the difference quotient error into $u$-derivative error, $v$-continuity jump,
   and $v$-derivative error.

3. **Monomial Duality Theorem (`monomial_ibp_sq_val`)**:
   Exact evaluation of $\int_0^1 x^2\,dx = [x \cdot (x^2/2)]_0^1 - \int_0^1 (x^2/2)\,dx = 1/2 - 1/6 = 1/3$.

4. **Kernel-Verified Computations**:
   Verified `#guard` calculations evaluating monomial IBP boundary and integral terms.
-/

namespace HAomega

open Rat

/-! ## 1. The Leibniz Product Difference Quotient Identity -/

/-- **Theorem (Leibniz Difference Quotient Identity)**:
    The difference quotient of a product splits algebraically into:
    $\frac{u(x+h)v(x+h) - u(x)v(x)}{h} = \frac{u(x+h) - u(x)}{h} v(x+h) + u(x) \frac{v(x+h) - v(x)}{h}$. -/
theorem leibniz_diff_quot_split (ux uxh vx vxh h : Rat) (_hh : h ≠ 0) :
    (uxh * vxh - ux * vx) / h =
      ((uxh - ux) / h) * vxh + ux * ((vxh - vx) / h) := by
  have : ((uxh - ux) / h) * vxh + ux * ((vxh - vx) / h) =
      ((uxh - ux) * vxh + ux * (vxh - vx)) / h := by ring
  rw [this]
  have h_num : (uxh - ux) * vxh + ux * (vxh - vx) = uxh * vxh - ux * vx := by ring
  rw [h_num]

#print axioms leibniz_diff_quot_split

/-- **Theorem (Leibniz Error 3-Term Decomposition)**:
    The residual between the product difference quotient and $u' v + u v'$ splits into
    $u$-derivative error, $v$-continuity jump, and $v$-derivative error. -/
theorem leibniz_error_split (ux uxh vx vxh u' v' h : Rat) (hh : h ≠ 0) :
    (uxh * vxh - ux * vx) / h - (u' * vx + ux * v') =
      ((uxh - ux) / h - u') * vxh +
      u' * (vxh - vx) +
      ux * ((vxh - vx) / h - v') := by
  rw [leibniz_diff_quot_split ux uxh vx vxh h hh]
  ring

#print axioms leibniz_error_split

/-! ## 2. Monomial Integration by Parts Duality -/

/-- **Theorem (Monomial Duality for Squaring)**:
    For $u(x) = x$ and $v(x) = x^2/2$, the boundary term $1/2$ minus the complementary
    integral $1/6$ evaluates identically to $1/3$. -/
theorem monomial_ibp_sq_val :
    (1 : Rat) / 2 - 1 / 6 = 1 / 3 := by
  norm_num

#print axioms monomial_ibp_sq_val

/-! ## 3. Verified Kernel Computations for Integration by Parts -/

-- Boundary term for u(x) = x, v(x) = x²/2 on [0, 1]:
-- u(1)v(1) - u(0)v(0) = 1 * (1/2) - 0 = 1/2
#guard (let u1 := Q.ofNat 1; let v1 := Q.of 1 2;
        let u0 := Q.ofNat 0; let v0 := Q.ofNat 0;
        Q.sub (Q.mul u1 v1) (Q.mul u0 v0)) == Q.of 1 2

-- Complementary integral: ∫₀¹ u'(t) v(t) dt = ∫₀¹ 1 * (t²/2) dt = 1/6
-- Result: ∫₀¹ t² dt = 1/2 - 1/6 = 1/3
#guard Q.sub (Q.of 1 2) (Q.of 1 6) == Q.of 1 3

-- Monomial integral ∫₀¹ x³ dx via IBP:
-- u(x) = x, v(x) = x³/3 on [0, 1]
-- Boundary: 1 * (1/3) = 1/3
-- Complementary: ∫₀¹ 1 * (t³/3) dt = 1/12
-- Result: 1/3 - 1/12 = 3/12 = 1/4
#guard Q.sub (Q.of 1 3) (Q.of 1 12) == Q.of 1 4

end HAomega
