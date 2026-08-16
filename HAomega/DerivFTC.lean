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
import HAomega.AnalysisDeriv

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

/-! ## 2. Natural Deduction Derivation & Realizer Extraction for Riemann Integrator -/

/-- Step term for Riemann sum integration: `λ (i : nat) (acc : rat). acc + f(i · h) · h`. -/
def riemannStepTm (f : Tm [] (.arrow .rat .rat)) (h : Tm [] .rat) :
    Tm [] (.arrow .nat (.arrow .rat .rat)) :=
  .lam (.lam (.qadd (.var .here) (.qmul (.app f.wk.wk (.qmul (.qnat (.var (.there .here))) h.wk.wk)) h.wk.wk)))

/-- Natural deduction derivation of the Riemann sum integration sequence. -/
def riemannSequenceD (f : Tm [] (.arrow .rat .rat)) (h : Tm [] .rat) :
    Deriv Ctx.nil (.all .nat (indexedIterInv .rat [] (.qnat .zero) (riemannStepTm f h))) :=
  indexedIterSequenceD .rat (.qnat .zero) (riemannStepTm f h)

/-- The extracted Riemann sum integrator (EXTRACTED from `riemannSequenceD`). -/
def riemannExtracted (f : Tm [] (.arrow .rat .rat)) (h : Tm [] .rat) (N : Nat) : Q :=
  ((extractClosed (riemannSequenceD f h)).eval Env.nil N).1

/-- Constant function 1 in System T. -/
def tmConstOne : Tm [] (.arrow .rat .rat) := .lam (.qnat (.succ .zero))

/-- Identity function in System T. -/
def tmId : Tm [] (.arrow .rat .rat) := .lam (.var .here)

/-- Square function in System T. -/
def tmSqr : Tm [] (.arrow .rat .rat) := .lam (.qmul (.var .here) (.var .here))

/-- Quarter step size h = 1/4 in System T. -/
def tmQuarter : Tm [] .rat := .qdiv (.qnat (.succ .zero)) (.qnat (.succ (.succ (.succ (.succ .zero)))))

/-- Eighth step size h = 1/8 in System T. -/
def tmEighth : Tm [] .rat := .qdiv (.qnat (.succ .zero)) (.qnat (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))

/-- **The object term itself, evaluated via extraction.** -/
def runRiemannSum (f : Q → Q) (h : Q) (N : Nat) : Q :=
  (tmRiemannSum (Γ := [])).eval Env.nil f h N

/-! ## 3. Kernel-Verified Computations for System T Integrator -/

-- Integrating f(x) = 1 on [0, 1] with N = 4 (h = 1/4):
#guard riemannExtracted tmConstOne tmQuarter 4 == Q.ofNat 1
#guard runRiemannSum (fun _ ↦ Q.ofNat 1) (Q.of 1 4) 4 == Q.ofNat 1

-- Integrating f(x) = x on [0, 1] with N = 4 (h = 1/4):
#guard riemannExtracted tmId tmQuarter 4 == Q.of 3 8
#guard runRiemannSum (fun x ↦ x) (Q.of 1 4) 4 == Q.of 3 8

-- Integrating f(x) = x on [0, 1] with N = 8 (h = 1/8):
#guard riemannExtracted tmId tmEighth 8 == Q.of 7 16
#guard runRiemannSum (fun x ↦ x) (Q.of 1 8) 8 == Q.of 7 16

-- Integrating f(x) = x² on [0, 1] with N = 4 (h = 1/4):
#guard riemannExtracted tmSqr tmQuarter 4 == Q.of 7 32
#guard runRiemannSum (fun x ↦ Q.mul x x) (Q.of 1 4) 4 == Q.of 7 32

end HAomega
