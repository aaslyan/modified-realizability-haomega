/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.DynamicalSystems.VanDerPol

/-!
# Dynamical Systems Suite: Duffing Oscillator and Double-Well Separatrix

This module formalizes the nonlinear **Duffing Oscillator**:
$$\ddot{x} + \delta \dot{x} - x + x^3 = 0 \iff \begin{cases} \dot{x}_1 = x_2 \\ \dot{x}_2 = x_1 - x_1^3 - \delta x_2 \end{cases}$$

1. **Nonlinear Picard Iteration (`duffingPicard`)**:
   Iterates cubic restoring force $x - x^3$ and damping $-\delta v$.

2. **Hamiltonian Energy Dissipation Identity (`duffing_energy_dissipation_id`)**:
   Proves algebraic identity $\frac{dE}{dt} = -\delta x_2^2 \le 0$.

3. **Kernel-Verified Computations**:
   Verified `#guard` calculations generating cubic Picard trajectory segments.
-/

namespace HAomega

open Rat

/-! ## 1. Duffing Picard Step -/

/-- One Picard integration step for Duffing oscillator with damping $\delta = 1/2$ and double well $x - x^3$:
    $$\dot{x}_1 = x_2, \qquad \dot{x}_2 = x_1 - x_1^3 - \frac{1}{2} x_2$$ -/
def duffingPicardStep (x0 v0 : Q) (pair : List Q × List Q) : List Q × List Q :=
  let ⟨x1, x2⟩ := pair
  let x1_sq := polyMul x1 x1
  let x1_cube := polyMul x1 x1_sq
  -- Linear restoring + cubic hardening: x1 - x1³
  let restoring := polySub x1 x1_cube
  -- Damping: - 1/2 * x2
  let damping := polyScale (Q.of (-1) 2) x2
  let accel := polyAdd restoring damping
  let x1_next := x0 :: (polyIntegrate x2).tail
  let x2_next := v0 :: (polyIntegrate accel).tail
  ⟨x1_next, x2_next⟩

/-- $n$-th Picard iterate for Duffing oscillator starting at $(x_0, v_0)$. -/
def duffingPicard (x0 v0 : Q) : Nat → List Q × List Q
  | 0 => ⟨[x0], [v0]⟩
  | n + 1 => duffingPicardStep x0 v0 (duffingPicard x0 v0 n)

/-! ## 2. Hamiltonian Energy Dissipation Theorem -/

/-- **Theorem (Duffing Energy Dissipation Rate)**:
    The derivative of the double-well energy $E(x_1, x_2) = \frac{1}{2} x_2^2 - \frac{1}{2} x_1^2 + \frac{1}{4} x_1^4$
    along the trajectory is strictly dissipative:
    $x_2 (x_1 - x_1^3 - \delta x_2) + (-x_1 + x_1^3) x_2 = -\delta x_2^2$. -/
theorem duffing_energy_dissipation_id (delta x1 x2 : Rat) :
    x2 * (x1 - x1 ^ 3 - delta * x2) + (-x1 + x1 ^ 3) * x2 = -delta * (x2 ^ 2) := by
  ring

#print axioms duffing_energy_dissipation_id

/-! ## 3. Verified Kernel Computations -/

-- Initial state at right well disturbance: x0 = 1, v0 = 1/2
-- Iteration 0: x(t) = 1, v(t) = 1/2
#guard evalPolyQ (duffingPicard (Q.ofNat 1) (Q.of 1 2) 0).1 (Q.of 1 2) == Q.ofNat 1
#guard evalPolyQ (duffingPicard (Q.ofNat 1) (Q.of 1 2) 0).2 (Q.of 1 2) == Q.of 1 2

-- Iteration 1:
-- x_dot = 1/2 -> x(t) = 1 + t/2 -> x(1/2) = 1 + 1/4 = 5/4
-- v_dot = (1 - 1) - (1/2)*(1/2) = -1/4 -> v(t) = 1/2 - t/4 -> v(1/2) = 1/2 - 1/8 = 3/8
#guard evalPolyQ (duffingPicard (Q.ofNat 1) (Q.of 1 2) 1).1 (Q.of 1 2) == Q.of 5 4
#guard evalPolyQ (duffingPicard (Q.ofNat 1) (Q.of 1 2) 1).2 (Q.of 1 2) == Q.of 3 8

end HAomega
