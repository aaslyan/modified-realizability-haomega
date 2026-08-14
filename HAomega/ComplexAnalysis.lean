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

/-!
# Gaussian Rationals $\mathbb{Q}(i)$ and Cauchy–Riemann Algebra

This module formalizes Gaussian rationals and Cauchy–Riemann differential algebra:

1. **Gaussian Rationals $\mathbb{Q}(i)$**:
   Complex numbers $z = x + i y$ with rational parts $x, y \in \mathbb{Q}$, equipped with
   the rational $L_1$ norm $|z|_1 = |x| + |y|$ and verified triangle inequality (`norm1_add_le`).

2. **Cauchy–Riemann Differential Data**:
   The partial derivative data satisfying $u_x = v_y$ and $u_y = -v_x$.
   Instantiated on explicit holomorphic maps:
   - Identity map $f(z) = z$ (`idCR`)
   - Monomial squaring $f(z) = z^2$ (`sqCR`)

3. **Jacobian Action as Complex Multiplication (`cr_jacobian_eq_complex_mul`)**:
   The action of the 2D Jacobian matrix $\begin{pmatrix} u_x & u_y \\ v_x & v_y \end{pmatrix}$
   on a displacement vector $(\Delta x, \Delta y)$ is identically equal to complex multiplication
   by $f'(z) = u_x + i v_x$.

4. **Curvature Residual Vanishing (`goursat_rect_zero`)**:
   The rectangular divergence/curl integrand residual $(u_x - v_y)\Delta x \Delta y + i(v_x + u_y)\Delta x \Delta y$
   vanishes algebraically under the Cauchy–Riemann equations.
-/

namespace HAomega

open Rat

/-! ## 1. Gaussian Rationals $\mathbb{Q}(i)$ -/

/-- Gaussian rational number $z = x + i y$ with $x, y \in \mathbb{Q}$. -/
structure QC where
  re : Q
  im : Q
deriving DecidableEq, Repr

namespace QC

/-- Zero in $\mathbb{Q}(i)$: $0 + 0i$. -/
def zero : QC := ⟨Q.zero, Q.zero⟩

/-- One in $\mathbb{Q}(i)$: $1 + 0i$. -/
def one : QC := ⟨Q.ofNat 1, Q.zero⟩

/-- Imaginary unit $i$: $0 + 1i$. -/
def I : QC := ⟨Q.zero, Q.ofNat 1⟩

/-- Addition in $\mathbb{Q}(i)$: $(x_1 + i y_1) + (x_2 + i y_2) = (x_1 + x_2) + i (y_1 + y_2)$. -/
def add (z1 z2 : QC) : QC :=
  ⟨Q.add z1.re z2.re, Q.add z1.im z2.im⟩

/-- Negation in $\mathbb{Q}(i)$: $-(x + i y) = -x - i y$. -/
def neg (z : QC) : QC :=
  ⟨Q.neg z.re, Q.neg z.im⟩

/-- Subtraction in $\mathbb{Q}(i)$. -/
def sub (z1 z2 : QC) : QC :=
  add z1 (neg z2)

/-- Multiplication in $\mathbb{Q}(i)$: $(x_1 + i y_1)(x_2 + i y_2) = (x_1 x_2 - y_1 y_2) + i (x_1 y_2 + x_2 y_1)$. -/
def mul (z1 z2 : QC) : QC :=
  ⟨Q.sub (Q.mul z1.re z2.re) (Q.mul z1.im z2.im),
   Q.add (Q.mul z1.re z2.im) (Q.mul z1.im z2.re)⟩

/-- Rational-valued $L_1$ norm: $|z|_1 = |x| + |y|$. -/
def norm1 (z : QC) : Rat :=
  |z.re.val| + |z.im.val|

/-- Triangle inequality for the complex $L_1$ norm: $|z_1 + z_2|_1 \le |z_1|_1 + |z_2|_1$. -/
theorem norm1_add_le (z1 z2 : QC) :
    norm1 (add z1 z2) ≤ norm1 z1 + norm1 z2 := by
  dsimp [norm1, add]
  rw [Q.val_add, Q.val_add]
  have h1 := abs_add_le z1.re.val z2.re.val
  have h2 := abs_add_le z1.im.val z2.im.val
  linarith

#print axioms norm1_add_le

end QC

/-! ## 2. Cauchy–Riemann Differentiability -/

/-- Data for Cauchy–Riemann partial derivatives of $f = u + i v$. -/
structure CauchyRiemannData where
  ux : Rat
  uy : Rat
  vx : Rat
  vy : Rat
  /-- First Cauchy–Riemann equation: $u_x = v_y$. -/
  cr1 : ux = vy
  /-- Second Cauchy–Riemann equation: $u_y = -v_x$. -/
  cr2 : uy = -vx

/-- Non-trivial instance: Identity map $f(z) = z$ with $u_x = 1, u_y = 0, v_x = 0, v_y = 1$. -/
def idCR : CauchyRiemannData :=
  { ux := 1, uy := 0, vx := 0, vy := 1, cr1 := rfl, cr2 := rfl }

/-- Non-trivial instance: Squaring map $f(z) = z^2$ with $u_x = 2x, u_y = -2y, v_x = 2y, v_y = 2x$. -/
def sqCR (x y : Rat) : CauchyRiemannData :=
  { ux := 2 * x, uy := -2 * y, vx := 2 * y, vy := 2 * x,
    cr1 := rfl,
    cr2 := by ring }

/-- **Theorem (Jacobian Action as Complex Multiplication)**:
    Applying the real 2D Jacobian matrix $\begin{pmatrix} u_x & u_y \\ v_x & v_y \end{pmatrix}$
    to a displacement $(\Delta x, \Delta y)$ is identical to complex multiplication
    by $f'(z) = u_x + i v_x$. -/
theorem cr_jacobian_eq_complex_mul (CR : CauchyRiemannData) (dx dy : Rat) :
    CR.ux * dx + CR.uy * dy = CR.ux * dx - CR.vx * dy ∧
    CR.vx * dx + CR.vy * dy = CR.vx * dx + CR.ux * dy := by
  constructor
  · rw [CR.cr2]
    ring
  · rw [CR.cr1]

#print axioms cr_jacobian_eq_complex_mul

/-! ## 3. Integrand Residual for Rectangular Loops -/

/-- Exact rectangular divergence/curl residual vanishes identically for Cauchy–Riemann fields. -/
theorem goursat_rect_zero (CR : CauchyRiemannData) (hx hy : Rat) :
    (CR.ux - CR.vy) * hx * hy = 0 ∧ (CR.vx + CR.uy) * hx * hy = 0 := by
  constructor
  · rw [CR.cr1]
    ring
  · rw [CR.cr2]
    ring

#print axioms goursat_rect_zero

/-! ## 4. Verified Kernel Computations in $\mathbb{Q}(i)$ -/

-- (1 + 2i) + (3 + 4i) = 4 + 6i
#guard QC.add ⟨Q.ofNat 1, Q.ofNat 2⟩ ⟨Q.ofNat 3, Q.ofNat 4⟩ == ⟨Q.ofNat 4, Q.ofNat 6⟩

-- i * i = (0 + 1i)(0 + 1i) = -1 + 0i
#guard QC.mul QC.I QC.I == ⟨Q.of (-1) 1, Q.zero⟩

-- (1 + i)(1 - i) = 1 - (-1) = 2 + 0i
#guard QC.mul ⟨Q.ofNat 1, Q.ofNat 1⟩ ⟨Q.ofNat 1, Q.of (-1) 1⟩ == ⟨Q.ofNat 2, Q.zero⟩

-- (2 + 3i)(4 + 5i) = (8 - 15) + (10 + 12)i = -7 + 22i
#guard QC.mul ⟨Q.ofNat 2, Q.ofNat 3⟩ ⟨Q.ofNat 4, Q.ofNat 5⟩ == ⟨Q.of (-7) 1, Q.ofNat 22⟩

end HAomega
