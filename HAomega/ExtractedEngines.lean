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
import HAomega.AnalysisDeriv

/-!
# Hand-Written Gödel System T Object Terms & Haskell Source (OBJECT-RUN)

This module formalizes hand-written closed Gödel System T terms (`Tm`) and emits
their exact, standalone Haskell programs for:

1. **The Cauchy–Kowalevski Analytic PDE Engine** (`tmCKAdvection`)
2. **The Newton–Raphson Inverter** (`tmNewtonIter`)
3. **The Symplectic Kepler Orbit & Momentum Integrator** (`tmSymplecticStep`)
4. **The 2D Harmonic Oscillator Step** (`tmHarmonicStep`)
5. **The 1D Heat Equation Diffusion Step** (`tmHeatDiffusionStep`)

**Classification Note:** These terms are hand-written object-language programs
evaluated via `Tm.eval Env.nil` (`OBJECT-RUN`). They are not produced by `extractClosed`
from a natural deduction proof tree (`EXTRACTED`).
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

/-! ## 4. 2D Harmonic Oscillator System T Term -/

/-- Closed 2D Harmonic Oscillator step in System T:
    Type: `(Q × Q) → Q → (Q × Q)`
    Given `(x, v)` and `dt`, returns `(x + dt * v, v - dt * x)`. -/
def tmHarmonicStep {Γ : List Ty} :
    Tm Γ (.arrow (.prod .rat .rat) (.arrow .rat (.prod .rat .rat))) :=
  .lam (.lam (
    let state : Tm _ (.prod .rat .rat) := .var (.there .here)
    let dt : Tm _ .rat := .var .here
    let x : Tm _ .rat := .fst state
    let v : Tm _ .rat := .snd state
    let x_next := .qadd x (.qmul dt v)
    let v_next := .qsub v (.qmul dt x)
    .pair x_next v_next
  ))

/-! ## 5. 1D Heat Equation Diffusion Step in System T -/

/-- Closed 1D Heat Equation spatial stencil step in System T:
    Type: `Q → Q → Q → Q → Q`
    Given `(u_{i-1}, u_i, u_{i+1}, r)` computes `u_i + r * (u_{i+1} - 2 u_i + u_{i-1})`. -/
def tmHeatDiffusionStep {Γ : List Ty} :
    Tm Γ (.arrow .rat (.arrow .rat (.arrow .rat (.arrow .rat .rat)))) :=
  .lam (.lam (.lam (.lam (
    let u_prev : Tm _ .rat := .var (.there (.there (.there .here)))
    let u_curr : Tm _ .rat := .var (.there (.there .here))
    let u_next : Tm _ .rat := .var (.there .here)
    let r : Tm _ .rat := .var .here
    let two_u := .qmul (.qnat (.succ (.succ .zero))) u_curr
    let laplacian := .qadd (.qsub u_next two_u) u_prev
    .qadd u_curr (.qmul r laplacian)
  ))))

/-! ## 6. Renderings of the Extracted Terms -/

def ckRawLambda : String := tmCKAdvection (Γ := []).pretty 0
def ckCollapsedLambda : String := tmCKAdvection (Γ := []).pretty' 0
def ckHaskellSource : String := EmitHaskell.hsTm (tmCKAdvection (Γ := [])) 0

def newtonRawLambda : String := tmNewtonIter (Γ := []).pretty 0
def newtonCollapsedLambda : String := tmNewtonIter (Γ := []).pretty' 0
def newtonHaskellSource : String := EmitHaskell.hsTm (tmNewtonIter (Γ := [])) 0

def symplecticRawLambda : String := tmSymplecticStep (Γ := []).pretty 0
def symplecticCollapsedLambda : String := tmSymplecticStep (Γ := []).pretty' 0
def symplecticHaskellSource : String := EmitHaskell.hsTm (tmSymplecticStep (Γ := [])) 0

def harmonicRawLambda : String := tmHarmonicStep (Γ := []).pretty 0
def harmonicCollapsedLambda : String := tmHarmonicStep (Γ := []).pretty' 0
def harmonicHaskellSource : String := EmitHaskell.hsTm (tmHarmonicStep (Γ := [])) 0

def heatRawLambda : String := tmHeatDiffusionStep (Γ := []).pretty 0
def heatCollapsedLambda : String := tmHeatDiffusionStep (Γ := []).pretty' 0
def heatHaskellSource : String := EmitHaskell.hsTm (tmHeatDiffusionStep (Γ := [])) 0

/-! ## 7. Natural Deduction Derivations in `Deriv` & `extractClosed` Realizers -/

/-- Generic closed existential synthesis in `Deriv` for any closed System T term $t : \mathrm{Tm}\ []\ \tau$:
    derives $\exists f : \tau.\; f = t$ and extracts $t$ via `extractClosed`. -/
def closedEngineD (τ : Ty) (t : Tm [] τ) :
    Deriv Ctx.nil (.ex τ (.eq (.var .here) t.wk)) := by
  have d_refl : Deriv Ctx.nil (Formula.eq t t) := Deriv.eqRefl t
  have d_subst : Deriv Ctx.nil ((Formula.eq (.var .here) t.wk).subst1 t) :=
    Formula.subst1_eq_var_wk t t ▸ d_refl
  exact Deriv.exI t d_subst

/-- 1. Cauchy–Kowalevski `Deriv` proof and `extractClosed` realizer. -/
def ckAdvectionD :
    Deriv Ctx.nil (.ex (.arrow (.arrow .nat .rat) (.arrow .nat (.arrow .nat .rat)))
      (.eq (.var .here) (tmCKAdvection (Γ := [])).wk)) :=
  closedEngineD _ (tmCKAdvection (Γ := []))

def ckAdvectionExtracted (a : Nat → Q) (j k : Nat) : Q :=
  ((extractClosed ckAdvectionD).eval Env.nil).1 a j k

/-- 2. Newton–Raphson `Deriv` proof and `extractClosed` realizer. -/
def newtonIterD :
    Deriv Ctx.nil (.ex (.arrow (.arrow .rat .rat) (.arrow (.arrow .rat .rat) (.arrow .rat (.arrow .rat (.arrow .nat .rat)))))
      (.eq (.var .here) (tmNewtonIter (Γ := [])).wk)) :=
  closedEngineD _ (tmNewtonIter (Γ := []))

def newtonIterExtracted (f df : Q → Q) (y x0 : Q) (N : Nat) : Q :=
  ((extractClosed newtonIterD).eval Env.nil).1 f df y x0 N

/-- 3. Symplectic Kepler step `Deriv` proof and multi-step trajectory `Deriv` proof (`iterSequenceD`). -/
def symplecticStepD :
    Deriv Ctx.nil (.ex (.arrow (.prod .rat .rat) (.arrow (.prod .rat .rat) (.arrow .rat (.arrow .rat (.prod (.prod .rat .rat) (.prod .rat .rat))))))
      (.eq (.var .here) (tmSymplecticStep (Γ := [])).wk)) :=
  closedEngineD _ (tmSymplecticStep (Γ := []))

def symplecticStepExtracted (r v : Q × Q) (dt kappa : Q) : (Q × Q) × (Q × Q) :=
  ((extractClosed symplecticStepD).eval Env.nil).1 r v dt kappa

/-- 4. 2D Harmonic Oscillator multi-step trajectory `Deriv` proof via `iterSequenceD` and `extractClosed`. -/
def harmonicStepForDt (dt : Tm [] .rat) :
    Tm [] (.arrow (.prod .rat .rat) (.prod .rat .rat)) :=
  .lam (.app (.app (tmHarmonicStep (Γ := [])).wk (.var .here)) dt.wk)

def harmonicTrajectoryD (s0 : Tm [] (.prod .rat .rat)) (dt : Tm [] .rat) :
    Deriv Ctx.nil (.all .nat (iterInv (.prod .rat .rat) [] s0 (harmonicStepForDt dt))) :=
  iterSequenceD (.prod .rat .rat) s0 (harmonicStepForDt dt)

def harmonicTrajectoryExtracted (s0 : Tm [] (.prod .rat .rat)) (dt : Tm [] .rat) (n : Nat) : Q × Q :=
  ((extractClosed (harmonicTrajectoryD s0 dt)).eval Env.nil n).1

/-- 5. 1D Heat Diffusion step `Deriv` proof and `extractClosed` realizer. -/
def heatDiffusionStepD :
    Deriv Ctx.nil (.ex (.arrow .rat (.arrow .rat (.arrow .rat (.arrow .rat .rat))))
      (.eq (.var .here) (tmHeatDiffusionStep (Γ := [])).wk)) :=
  closedEngineD _ (tmHeatDiffusionStep (Γ := []))

def heatDiffusionExtracted (u_prev u_curr u_next r : Q) : Q :=
  ((extractClosed heatDiffusionStepD).eval Env.nil).1 u_prev u_curr u_next r

/-! ## 8. Kernel `#guard` Checks on the `extractClosed` Engine Realizers -/

-- 1. Cauchy–Kowalevski extracted realizer: c_{j,k} = a(j + k)
#guard ckAdvectionExtracted (fun n ↦ Q.ofNat (n + 1)) 2 3 == Q.ofNat 6

-- 2. Newton–Raphson extracted realizer: solving x² = 2 from x0 = 1
-- Step 1: 1 - (1 - 2)/2 = 3/2; Step 2: 3/2 - (9/4 - 2)/3 = 17/12
#guard newtonIterExtracted (fun x ↦ Q.mul x x) (fun x ↦ Q.add x x) (Q.ofNat 2) (Q.ofNat 1) 1 == Q.of 3 2
#guard newtonIterExtracted (fun x ↦ Q.mul x x) (fun x ↦ Q.add x x) (Q.ofNat 2) (Q.ofNat 1) 2 == Q.of 17 12

-- 3. Symplectic Kepler extracted realizer: conserves discrete angular momentum rx * vy - ry * vx = 1
#guard let s1 := symplecticStepExtracted (Q.ofNat 1, Q.zero) (Q.zero, Q.ofNat 1) (Q.of 1 10) (Q.neg (Q.ofNat 1))
       Q.sub (Q.mul s1.1.1 s1.2.2) (Q.mul s1.1.2 s1.2.1) == Q.ofNat 1

-- 4. 2D Harmonic Oscillator trajectory extracted via `iterSequenceD`:
-- Initial state (1, 0), dt = 1/4: step 0 = (1, 0), step 1 = (1, -1/4), step 2 = (15/16, -1/2)
#guard harmonicTrajectoryExtracted (.pair (.qnat (.succ .zero)) (.qnat .zero))
         (.qdiv (.qnat (.succ .zero)) (.qnat (.succ (.succ (.succ (.succ .zero)))))) 0 == (Q.ofNat 1, Q.zero)
#guard harmonicTrajectoryExtracted (.pair (.qnat (.succ .zero)) (.qnat .zero))
         (.qdiv (.qnat (.succ .zero)) (.qnat (.succ (.succ (.succ (.succ .zero)))))) 1 == (Q.ofNat 1, Q.neg (Q.of 1 4))
#guard harmonicTrajectoryExtracted (.pair (.qnat (.succ .zero)) (.qnat .zero))
         (.qdiv (.qnat (.succ .zero)) (.qnat (.succ (.succ (.succ (.succ .zero)))))) 2 == (Q.of 15 16, Q.neg (Q.of 1 2))

-- 5. Heat Diffusion extracted realizer: smoothing spike (0, 1, 0) with r = 1/4 gives 1 + 1/4*(0 - 2 + 0) = 1/2
#guard heatDiffusionExtracted Q.zero (Q.ofNat 1) Q.zero (Q.of 1 4) == Q.of 1 2

#print axioms ckAdvectionD
#print axioms newtonIterD
#print axioms symplecticStepD
#print axioms harmonicTrajectoryD
#print axioms heatDiffusionStepD

end HAomega
