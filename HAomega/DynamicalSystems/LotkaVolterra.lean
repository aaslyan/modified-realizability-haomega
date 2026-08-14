/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.DynamicalSystems.VanDerPol

/-!
# Dynamical Systems Suite: Lotka–Volterra Predator–Prey Dynamics

This module formalizes the nonlinear **Lotka–Volterra Ecosystem**:
$$\begin{cases} \dot{x} = \alpha x - \beta x y \\ \dot{y} = \delta x y - \gamma y \end{cases}$$

1. **Nonlinear Picard Iteration (`lotkaPicard`)**:
   Synthesizes exact polynomial trajectories for coupled predator and prey populations.

2. **First Integral Invariant Conservation (`lotka_volterra_invariant_cancel`)**:
   Proves exact algebraic vanishing of the Hamiltonian derivative along vector field flows.

3. **Kernel-Verified Computations**:
   Verified `#guard` calculations generating initial population responses.
-/

namespace HAomega

open Rat

/-! ## 1. Lotka–Volterra Picard Step -/

/-- One Picard integration step for normalized Lotka–Volterra with $\alpha=\beta=\delta=\gamma=1$:
    $$\dot{x} = x - x y, \qquad \dot{y} = x y - y$$ -/
def lotkaPicardStep (x0 y0 : Q) (pair : List Q × List Q) : List Q × List Q :=
  let ⟨x, y⟩ := pair
  let xy := polyMul x y
  -- x_dot = x - xy
  let x_dot := polySub x xy
  let x_next := x0 :: (polyIntegrate x_dot).tail
  -- y_dot = xy - y
  let y_dot := polySub xy y
  let y_next := y0 :: (polyIntegrate y_dot).tail
  ⟨x_next, y_next⟩

/-- $n$-th Picard iterate for Lotka–Volterra starting at $(x_0, y_0)$. -/
def lotkaPicard (x0 y0 : Q) : Nat → List Q × List Q
  | 0 => ⟨[x0], [y0]⟩
  | n + 1 => lotkaPicardStep x0 y0 (lotkaPicard x0 y0 n)

/-! ## 2. Conserved First Integral Derivative Cancellation -/

/-- **Theorem (Lotka–Volterra Invariant Flow Conservation)**:
    The rate of change of the invariant $H(x, y) = (x - \ln x) + (y - \ln y)$ along the flow
    $(x(1-y), y(x-1))$ vanishes identically:
    $(x - 1)(1 - y) + (y - 1)(x - 1) = 0$. -/
theorem lotka_volterra_invariant_cancel (x y : Rat) :
    (x - 1) * (1 - y) + (y - 1) * (x - 1) = 0 := by
  ring

#print axioms lotka_volterra_invariant_cancel

/-! ## 3. Verified Kernel Computations -/

-- Initial populations: Prey x0 = 2, Predator y0 = 1/2
-- Iteration 0: x(t) = 2, y(t) = 1/2
#guard evalPolyQ (lotkaPicard (Q.ofNat 2) (Q.of 1 2) 0).1 (Q.of 1 2) == Q.ofNat 2
#guard evalPolyQ (lotkaPicard (Q.ofNat 2) (Q.of 1 2) 0).2 (Q.of 1 2) == Q.of 1 2

-- Iteration 1:
-- x_dot = 2 - 2*(1/2) = 1 -> x(t) = 2 + t -> x(1/2) = 2.5 = 5/2
-- y_dot = 2*(1/2) - 1/2 = 1/2 -> y(t) = 1/2 + t/2 -> y(1/2) = 3/4
#guard evalPolyQ (lotkaPicard (Q.ofNat 2) (Q.of 1 2) 1).1 (Q.of 1 2) == Q.of 5 2
#guard evalPolyQ (lotkaPicard (Q.ofNat 2) (Q.of 1 2) 1).2 (Q.of 1 2) == Q.of 3 4

end HAomega
