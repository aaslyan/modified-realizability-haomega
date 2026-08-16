/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.Picard
import HAomega.GaloisAdequacy
import HAomega.IVT
import HAomega.ModulusClosure

/-!
# Object-Level Riemann Integration and Realizer Execution in $\mathrm{HA}^\omega$

This module formalizes the **Riemann integration operator** as an object-level term
in Gödel's System T ($\mathrm{Tm}$):

1. **Object-Level Riemann Sum Operator (`tmRiemannSum`)**:
   Constructed via `recNat` in `Tm`:
   $$S(0) = 0, \qquad S(n+1) = S(n) + f(n \cdot h) \cdot h$$

2. **Running the Object-Language Integrator (`runRiemannSum`)**:
   Directly executes the closed System T term `tmRiemannSum` through `Tm.eval`.

3. **Kernel-Verified Computations**:
   Verified execution of the System T integrator computing rational Riemann sums for monomials.
-/

namespace HAomega

open Rat

/-! ## 1. Object-Level Riemann Sum in System T -/

/-- The step term for Riemann sum recursion:
    `acc + f(i · h) · h` in context `[acc, i, N, h, f, Γ...]`. -/
def tmRiemannStep {Γ : List Ty} :
    Tm (.rat :: .nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ) .rat :=
  let acc : Tm (.rat :: .nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ) .rat :=
    Tm.var .here
  let i_val : Tm (.rat :: .nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ) .rat :=
    Tm.qnat (Tm.var (.there .here))
  let h_val : Tm (.rat :: .nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ) .rat :=
    Tm.var (.there (.there (.there .here)))
  let f_val : Tm (.rat :: .nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ) (.arrow .rat .rat) :=
    Tm.var (.there (.there (.there (.there .here))))
  let xi := Tm.qmul i_val h_val
  let f_xi := Tm.app f_val xi
  let term := Tm.qmul f_xi h_val
  Tm.qadd acc term

/-- The closed Riemann sum operator in System T:
    `fun f h N ↦ recNat 0 (fun i acc ↦ acc + f(i · h) · h) N`. -/
def tmRiemannSum {Γ : List Ty} :
    Tm Γ (.arrow (.arrow .rat .rat) (.arrow .rat (.arrow .nat .rat))) :=
  .lam (.lam (.lam (.recNat (.qnat .zero) (.lam (.lam tmRiemannStep)) (.var .here))))

/-! ## 2. Running the Object-Language Integrator -/

/-- **The object term itself, evaluated.**  Not a re-implementation:
`tmRiemannSum` is applied to its three arguments through `Tm.eval`, so the
guards below execute the System T operator rather than a parallel Lean
function that happens to compute the same sums. -/
def runRiemannSum (f : Q → Q) (h : Q) (N : Nat) : Q :=
  (tmRiemannSum (Γ := [])).eval Env.nil f h N

/-! ## 3. Kernel-Verified Computations for System T Integrator -/

-- Integrating f(x) = 1 on [0, 1] with N = 4 (h = 1/4):
-- S_4 = 4 * (1 * 1/4) = 1
#guard runRiemannSum (fun _ ↦ Q.ofNat 1) (Q.of 1 4) 4 == Q.ofNat 1

-- Integrating f(x) = x on [0, 1] with N = 4 (h = 1/4):
-- S_4 = (1/4) * (0 + 1/4 + 2/4 + 3/4) = (1/4) * (6/4) = 6/16 = 3/8 = 0.375
#guard runRiemannSum (fun x ↦ x) (Q.of 1 4) 4 == Q.of 3 8

-- Integrating f(x) = x on [0, 1] with N = 8 (h = 1/8):
-- S_8 = (1/8) * (28/8) = 28/64 = 7/16 = 0.4375 (approaching 1/2)
#guard runRiemannSum (fun x ↦ x) (Q.of 1 8) 8 == Q.of 7 16

-- Integrating f(x) = x² on [0, 1] with N = 4 (h = 1/4):
-- S_4 = (1/4) * (0 + 1/16 + 4/16 + 9/16) = (1/4) * (14/16) = 14/64 = 7/32 = 0.21875 (approaching 1/3)
#guard runRiemannSum (fun x ↦ Q.mul x x) (Q.of 1 4) 4 == Q.of 7 32

end HAomega
