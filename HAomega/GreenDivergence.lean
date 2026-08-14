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
# 2D Green's Circulation and Divergence Theorem on Rational Grids

This module formalizes the **2D Green's Theorem / Divergence Theorem** on rational
rectangular meshes:

1. **Discrete Circulation Operator (`cellCirculation`)**:
   Line integral around the boundary of a single cell $[x_1, x_2] \times [y_1, y_2]$:
   $$\oint_{\partial C} (F_1\,dx + F_2\,dy) = F_1(x_1, y_1)\Delta x + F_2(x_2, y_1)\Delta y - F_1(x_1, y_2)\Delta x - F_2(x_1, y_1)\Delta y$$

2. **Adjacent Cell Edge Cancellation Theorem (`green_horiz_cell_cancel`)**:
   For horizontally adjacent cells sharing a vertical boundary, the internal edge terms
   cancel with opposite orientation:
   $$\oint_{\partial C_L} \mathbf{F} + \oint_{\partial C_R} \mathbf{F} = \oint_{\partial (C_L \cup C_R)} \mathbf{F}$$

3. **$2 \times 2$ Grid Telescoping Green Identity (`green_2x2_exact_cancellation`)**:
   Summing the circulation over all 4 interior cells algebraically cancels all internal
   edges, leaving strictly the outer boundary loop.

4. **Kernel-Verified Vector Field Circulation**:
   Verified `#guard` calculations checking rotational and irrotational vector fields.
-/

namespace HAomega

open Rat

/-! ## 1. 2D Cell Circulation Definition -/

/-- Discrete line integral around a single rectangular cell $[x_1, x_2] \times [y_1, y_2]$:
    Bottom + Right - Top - Left. -/
def cellCirculation (F1_bot F2_right F1_top F2_left : Rat) (dx dy : Rat) : Rat :=
  F1_bot * dx + F2_right * dy - F1_top * dx - F2_left * dy

/-! ## 2. Horizontal and Vertical Edge Cancellation Theorems -/

/-- **Theorem (Horizontal Cell Edge Cancellation)**:
    When two cells share the vertical edge at $x_2$ (with field value $F_{2,\mathrm{mid}}$),
    the internal edge $+F_{2,\mathrm{mid}} \Delta y - F_{2,\mathrm{mid}} \Delta y = 0$ cancels identically! -/
theorem green_horiz_cell_cancel
    (F1_L_bot F2_mid F1_L_top F2_L_left : Rat)
    (F1_R_bot F2_R_right F1_R_top : Rat)
    (dxL dxR dy : Rat) :
    cellCirculation F1_L_bot F2_mid F1_L_top F2_L_left dxL dy +
    cellCirculation F1_R_bot F2_R_right F1_R_top F2_mid dxR dy =
      (F1_L_bot * dxL + F1_R_bot * dxR) + F2_R_right * dy -
      (F1_L_top * dxL + F1_R_top * dxR) - F2_L_left * dy := by
  dsimp [cellCirculation]
  ring

#print axioms green_horiz_cell_cancel

/-! ## 3. The $2 \times 2$ Mesh Telescoping Green Theorem -/

/-- **Theorem ($2 \times 2$ Grid Green Telescoping Identity)**:
    Summing 4 cell circulations on a $2 \times 2$ mesh cancels all 4 interior edges,
    yielding identically the global outer boundary circulation loop. -/
theorem green_2x2_exact_cancellation
    (F1_00 F1_10 F1_01 F1_11 F1_02 F1_12 : Rat)
    (F2_00 F2_10 F2_20 F2_01 F2_11 F2_21 : Rat)
    (dx dy : Rat) :
    -- Cell (0,0)
    cellCirculation F1_00 F2_10 F1_01 F2_00 dx dy +
    -- Cell (1,0)
    cellCirculation F1_10 F2_20 F1_11 F2_10 dx dy +
    -- Cell (0,1)
    cellCirculation F1_01 F2_11 F1_02 F2_01 dx dy +
    -- Cell (1,1)
    cellCirculation F1_11 F2_21 F1_12 F2_11 dx dy =
      -- Global Bottom Boundary
      (F1_00 * dx + F1_10 * dx) +
      -- Global Right Boundary
      (F2_20 * dy + F2_21 * dy) -
      -- Global Top Boundary
      (F1_02 * dx + F1_12 * dx) -
      -- Global Left Boundary
      (F2_00 * dy + F2_01 * dy) := by
  dsimp [cellCirculation]
  ring

#print axioms green_2x2_exact_cancellation

/-! ## 4. Verified Kernel Computations for 2D Circulation -/

-- Irrotational field: F(x, y) = (y, x)
-- F1(x, y) = y, F2(x, y) = x
-- Cell [0, 1] x [0, 1] with dx = 1, dy = 1:
-- F1_bot = 0, F2_right = 1, F1_top = 1, F2_left = 0
-- Circulation: 0*1 + 1*1 - 1*1 - 0*1 = 0
#guard cellCirculation (0 : Rat) 1 1 0 1 1 == 0

-- Rotational vortex field: F(x, y) = (-y, x)
-- F1(x, y) = -y, F2(x, y) = x
-- Cell [0, 1] x [0, 1] with dx = 1, dy = 1:
-- F1_bot = 0, F2_right = 1, F1_top = -1, F2_left = 0
-- Circulation: 0*1 + 1*1 - (-1)*1 - 0*1 = 2 (exact curl area = 2 * 1 = 2)
#guard cellCirculation (0 : Rat) 1 (-1) 0 1 1 == 2

-- Scaled vortex on cell with dx = 1/2, dy = 1/2:
-- F1_bot = 0, F2_right = 1/2, F1_top = -1/2, F2_left = 0
-- Circulation: 0*(1/2) + (1/2)*(1/2) - (-1/2)*(1/2) - 0*(1/2) = 1/4 + 1/4 = 1/2 (curl * area = 2 * (1/4) = 1/2)
#guard cellCirculation (0 : Rat) (1/2) (-1/2) 0 (1/2) (1/2) == (1/2 : Rat)

end HAomega
