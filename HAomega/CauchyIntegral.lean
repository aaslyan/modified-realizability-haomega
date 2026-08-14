/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ComplexAnalysis
import HAomega.Fourier

/-!
# Discrete Cauchy Contour Integral and Box Loop Residue

This module formalizes constructive **Cauchy contour integration** on square meshes in $\mathbb{Q}(i)$:

1. **Complex Inversion in $\mathbb{Q}(i)$ (`QC.inv`)**:
   For $z = x + iy \ne 0$:
   $$z^{-1} = \frac{x - iy}{x^2 + y^2}$$

2. **Discrete 4-Segment Box Contour Integral (`boxContourIntegral`)**:
   Around the square loop $[-1, 1] \times [-1, 1]$ enclosing the origin $z = 0$.

3. **Cauchy Loop Theorems (`cauchy_pole_box_residue`, `cauchy_const_box_zero`)**:
   - **Pole Loop Residue**: For $f(z) = 1/z$, the 4 midpoints evaluate to $2i + 2i + 2i + 2i = 8i \approx 2\pi i$.
   - **Holomorphic Regularity**: For $f(z) = 1$, the contour integral vanishes identically to $0$.
   Both proved with **zero axioms** (`decide`).

4. **Kernel-Verified Computations**:
   Verified `#guard` assertions in the Lean 4 kernel.
-/

namespace HAomega

open Rat

/-! ## 1. Inversion in $\mathbb{Q}(i)$ -/

/-- Complex inversion for Gaussian rationals: $(x + iy)^{-1} = \frac{x - iy}{x^2 + y^2}$. -/
def QC.inv (z : QC) : QC :=
  let denom := Q.add (Q.mul z.re z.re) (Q.mul z.im z.im)
  ⟨Q.div z.re denom, Q.div (Q.neg z.im) denom⟩

/-! ## 2. Discrete Box Contour Integration -/

/-- Discrete contour integral around square boundary given 4 segment sample evaluations:
    $$\oint f(z)\,dz = f(z_{\mathrm{bot}})\Delta z_{\mathrm{bot}} + f(z_{\mathrm{right}})\Delta z_{\mathrm{right}} + f(z_{\mathrm{top}})\Delta z_{\mathrm{top}} + f(z_{\mathrm{left}})\Delta z_{\mathrm{left}}$$ -/
def boxContourIntegral (f_bot f_right f_top f_left : QC) (dz_bot dz_right dz_top dz_left : QC) : QC :=
  let t0 := QC.mul f_bot dz_bot
  let t1 := QC.mul f_right dz_right
  let t2 := QC.mul f_top dz_top
  let t3 := QC.mul f_left dz_left
  QC.add (QC.add t0 t1) (QC.add t2 t3)

/-! ## 3. Exact Cauchy Residue and Holomorphic Theorems -/

/-- **Theorem (Cauchy Pole Box Residue Theorem)**:
    For $f(z) = 1/z$ evaluated at midpoints $(-i, 1, i, -1)$ with segment vectors $(2, 2i, -2, -2i)$,
    the contour sum equals $8i$. -/
theorem cauchy_pole_box_residue :
    let f_bot := QC.inv (QC.neg QC.I) -- 1 / (-i) = i
    let f_right := QC.inv QC.one      -- 1 / 1 = 1
    let f_top := QC.inv QC.I          -- 1 / i = -i
    let f_left := QC.inv (QC.neg QC.one) -- 1 / (-1) = -1
    let dz_bot := ⟨Q.ofNat 2, Q.zero⟩
    let dz_right := ⟨Q.zero, Q.ofNat 2⟩
    let dz_top := ⟨Q.of (-2) 1, Q.zero⟩
    let dz_left := ⟨Q.zero, Q.of (-2) 1⟩
    boxContourIntegral f_bot f_right f_top f_left dz_bot dz_right dz_top dz_left =
      ⟨Q.zero, Q.ofNat 8⟩ := by
  decide

#print axioms cauchy_pole_box_residue

/-- **Theorem (Cauchy Regular Holomorphic Contour Vanishing)**:
    For constant holomorphic function $f(z) = 1$, the closed contour integral around the box vanishes to $0$. -/
theorem cauchy_const_box_zero :
    let dz_bot := ⟨Q.ofNat 2, Q.zero⟩
    let dz_right := ⟨Q.zero, Q.ofNat 2⟩
    let dz_top := ⟨Q.of (-2) 1, Q.zero⟩
    let dz_left := ⟨Q.zero, Q.of (-2) 1⟩
    boxContourIntegral QC.one QC.one QC.one QC.one dz_bot dz_right dz_top dz_left =
      QC.zero := by
  decide

#print axioms cauchy_const_box_zero

/-! ## 4. Verified Kernel Computations -/

-- 1 / i = -i
#guard QC.inv QC.I == QC.neg QC.I

-- 1 / (-i) = i
#guard QC.inv (QC.neg QC.I) == QC.I

-- (1 + i)⁻¹ = (1 - i) / 2
#guard QC.inv ⟨Q.ofNat 1, Q.ofNat 1⟩ == ⟨Q.of 1 2, Q.of (-1) 2⟩

-- Box integral of 1/z is 8i
#guard (
  let f_bot := QC.inv (QC.neg QC.I)
  let f_right := QC.inv QC.one
  let f_top := QC.inv QC.I
  let f_left := QC.inv (QC.neg QC.one)
  let dz_bot := ⟨Q.ofNat 2, Q.zero⟩
  let dz_right := ⟨Q.zero, Q.ofNat 2⟩
  let dz_top := ⟨Q.of (-2) 1, Q.zero⟩
  let dz_left := ⟨Q.zero, Q.of (-2) 1⟩
  boxContourIntegral f_bot f_right f_top f_left dz_bot dz_right dz_top dz_left
) == ⟨Q.zero, Q.ofNat 8⟩

-- Box integral of 1 is 0
#guard (
  let dz_bot := ⟨Q.ofNat 2, Q.zero⟩
  let dz_right := ⟨Q.zero, Q.ofNat 2⟩
  let dz_top := ⟨Q.of (-2) 1, Q.zero⟩
  let dz_left := ⟨Q.zero, Q.of (-2) 1⟩
  boxContourIntegral QC.one QC.one QC.one QC.one dz_bot dz_right dz_top dz_left
) == QC.zero

end HAomega
