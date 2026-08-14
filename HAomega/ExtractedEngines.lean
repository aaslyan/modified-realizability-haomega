/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Syntax
import HAomega.EmitHaskell
import HAomega.CauchyKowalevski
import HAomega.InverseFunction
import HAomega.SymplecticKepler

/-!
# Extracted System T Lambda Terms & Haskell Source for Breakthrough Engines

This module formalizes the closed Gödel System T $\lambda$-terms (`Tm`) and emits
the exact, standalone Haskell programs for:

1. **The Cauchy–Kowalevski Analytic PDE Engine** (Bivariate Taylor Recursor)
2. **The Newton–Raphson Double-Exponential Root Inverter**
3. **The Symplectic Kepler Orbit & Angular Momentum Integrator**
-/

namespace HAomega

open Rat

/-! ## 1. Cauchy–Kowalevski Analytic PDE System T Term -/

/-- The closed System T functional for the Cauchy–Kowalevski PDE recurrence:
    Type: `(Nat → Q) → Nat → Nat → Q`
    Given initial spatial series $a(k)$, computes the bivariate coefficient $c_{j, k} = a(j + k)$. -/
def tmCKAdvection {Γ : List Ty} :
    Tm Γ (.arrow (.arrow .nat .rat) (.arrow .nat (.arrow .nat .rat))) :=
  -- λ a. λ j. λ k. a (j + k)
  .lam (.lam (.lam (
    .app (.var (.there (.there .here)))
         (.add (.var (.there .here)) (.var .here))
  )))

/-! ## 2. Newton–Raphson Double-Exponential Inversion System T Term -/

/-- Step term for Newton–Raphson in recNat step context `[acc, k, N, x0, y, df, f, Γ...]`:
    acc at 0, y at 4, df at 5, f at 6. -/
def tmNewtonStep {Γ : List Ty} :
    Tm (.rat :: .nat :: .nat :: .rat :: .rat :: (.arrow .rat .rat) :: (.arrow .rat .rat) :: Γ) .rat :=
  let x_acc : Tm _ .rat := .var .here
  let y_val : Tm _ .rat := .var (.there (.there (.there (.there .here))))
  let df_op : Tm _ (.arrow .rat .rat) := .var (.there (.there (.there (.there (.there .here)))))
  let f_op  : Tm _ (.arrow .rat .rat) := .var (.there (.there (.there (.there (.there (.there .here))))))
  -- x_acc - (f(x_acc) - y_val) / df(x_acc)
  .qsub x_acc (.qdiv (.qsub (.app f_op x_acc) y_val) (.app df_op x_acc))

/-- The closed Newton–Raphson Inversion functional in System T:
    Type: `(Q → Q) → (Q → Q) → Q → Q → Nat → Q`
    `λ f. λ df. λ y. λ x0. λ N. recNat x0 (λ k acc. acc - (f(acc) - y) / df(acc)) N`. -/
def tmNewtonIter {Γ : List Ty} :
    Tm Γ (.arrow (.arrow .rat .rat) (.arrow (.arrow .rat .rat) (.arrow .rat (.arrow .rat (.arrow .nat .rat))))) :=
  .lam (.lam (.lam (.lam (.lam (
    .recNat (.var (.there .here)) (.lam (.lam tmNewtonStep)) (.var .here)
  )))))

/-! ## 3. Symplectic Kepler Orbit Integrator System T Term -/

/-- The closed Symplectic Orbit step functional in System T:
    Type: `(Q × Q) → (Q × Q) → Q → Q → ((Q × Q) × (Q × Q))`
    Given pos $\mathbf{r}$, vel $\mathbf{v}$, step $dt$, and field $\kappa$, computes $(\mathbf{r}_{n+1}, \mathbf{v}_{n+1})$. -/
def tmSymplecticStep {Γ : List Ty} :
    Tm Γ (.arrow (.prod .rat .rat) (.arrow (.prod .rat .rat) (.arrow .rat (.arrow .rat (.prod (.prod .rat .rat) (.prod .rat .rat)))))) :=
  .lam (.lam (.lam (.lam (
    let r : Tm _ (.prod .rat .rat) := .var (.there (.there (.there .here)))
    let v : Tm _ (.prod .rat .rat) := .var (.there (.there .here))
    let dt : Tm _ .rat := .var (.there .here)
    let kappa : Tm _ .rat := .var .here
    let rx : Tm _ .rat := .fst r
    let ry : Tm _ .rat := .snd r
    let vx : Tm _ .rat := .fst v
    let vy : Tm _ .rat := .snd v
    -- ax = kappa * rx, ay = kappa * ry
    let ax := .qmul kappa rx
    let ay := .qmul kappa ry
    -- vx_next = vx + dt * ax, vy_next = vy + dt * ay
    let vx_next := .qadd vx (.qmul dt ax)
    let vy_next := .qadd vy (.qmul dt ay)
    -- rx_next = rx + dt * vx_next, ry_next = ry + dt * vy_next
    let rx_next := .qadd rx (.qmul dt vx_next)
    let ry_next := .qadd ry (.qmul dt vy_next)
    .pair (.pair rx_next ry_next) (.pair vx_next vy_next)
  ))))

/-! ## 4. Renderings of the Extracted Terms -/

def ckRawLambda : String := tmCKAdvection (Γ := []).pretty 0
def ckCollapsedLambda : String := tmCKAdvection (Γ := []).pretty' 0
def ckHaskellSource : String := EmitHaskell.hsTm (tmCKAdvection (Γ := [])) 0

def newtonRawLambda : String := tmNewtonIter (Γ := []).pretty 0
def newtonCollapsedLambda : String := tmNewtonIter (Γ := []).pretty' 0
def newtonHaskellSource : String := EmitHaskell.hsTm (tmNewtonIter (Γ := [])) 0

def symplecticRawLambda : String := tmSymplecticStep (Γ := []).pretty 0
def symplecticCollapsedLambda : String := tmSymplecticStep (Γ := []).pretty' 0
def symplecticHaskellSource : String := EmitHaskell.hsTm (tmSymplecticStep (Γ := [])) 0

end HAomega
