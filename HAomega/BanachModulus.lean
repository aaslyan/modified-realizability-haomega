/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniformContinuity
import HAomega.AnalysisDeriv
import HAomega.GcdStage2
import HAomega.Kit

/-!
# Banach Fixed Point: Extracting Stopping Criteria and Convergence Moduli

Classically, the Banach fixed-point theorem asserts the *existence* of a unique
limit point $x^*$ for any contraction $T$, leaving the rate of convergence implicit.
Constructively, the computational content of contraction mapping theorems is the
**modulus of convergence** — a computable stopping function:
$$N : \mathbb{N} \to \mathbb{N}$$
which maps any requested precision $2^{-n}$ to the certified number of iterations $N(n)$
guaranteeing that all subsequent iterates satisfy the precision tolerance:
$$\forall d \in \mathbb{N}. \; |x_{N(n)+d} - x_{N(n)+d+1}| < 2^{-(n + d + k_0)} \le 2^{-n}$$

## Mathematical Architecture

1. **Operator as a Function Variable**:
   $T : \mathbb{Q} \to \mathbb{Q}$ is quantified as a higher-type variable in HA^ω.
2. **Contraction Premise (Premise A)**:
   $$\forall u, v \in \mathbb{Q}, \forall m \in \mathbb{N}. \; |u - v| < 2^{-m} \implies |T(u) - T(v)| < 2^{-(m+1)}$$
3. **Seed Step Premise (Premise B)**:
   $$|x_0 - T(x_0)| < 2^{-k_0}$$
4. **Inductive Orbit Decay**:
   By induction on the iteration index $m$, the distance between consecutive iterates
   contracts geometrically: $|x_m - x_{m+1}| < 2^{-(m + k_0)}$.
5. **Extracted Program as Stopping Rule**:
   The realizer extracted from `banachContractionD` takes $(T, x_0, k_0)$ and precision $n$,
   returning the exact stopping iteration count $N(n) = n$.
-/

namespace HAomega

/-- Step term for recursor: `λ k acc. T acc`. -/
def banachStep {Γ : List Ty} (T : Tm Γ (.arrow .rat .rat)) :
    Tm Γ (.arrow .nat (.arrow .rat .rat)) :=
  .lam (.lam (.app ((T.wk (σ := .nat)).wk (σ := .rat)) (.var .here)))

/-- The $m$-th iterate $T^m(x_0)$ as an object term. -/
def iterAt {Γ : List Ty} (T : Tm Γ (.arrow .rat .rat)) (x0 : Tm Γ .rat) (m : Tm Γ .nat) : Tm Γ .rat :=
  .recNat x0 (banachStep T) m

theorem linkBanachStep1 {Γ : List Ty} (T : Tm Γ (.arrow .rat .rat)) (m : Tm Γ .nat) :
    Tm.subst1 (.lam (.app (((T.wk (σ := .nat)).wk (σ := .rat))) (.var .here)) : Tm (.nat :: Γ) (.arrow .rat .rat)) m
      = .lam (.app (T.wk (σ := .rat)) (.var .here)) := by
  simp only [Tm.subst1, Tm.subst, Sub.ext, Tm.wk_subst_ext, Tm.wk_subst_one]

theorem linkBanachStep2 {Γ : List Ty} (T : Tm Γ (.arrow .rat .rat)) (acc : Tm Γ .rat) :
    Tm.subst1 (.app (T.wk (σ := .rat)) (.var .here) : Tm (.rat :: Γ) .rat) acc
      = .app T acc := by
  simp only [Tm.subst1, Tm.subst, Sub.one, Tm.wk_subst_one]

/-- Step application unfolds to `T acc`. -/
def banachStepApp {Γ as : List Ty} {Δ : Ctx Γ as} (T : Tm Γ (.arrow .rat .rat)) (m : Tm Γ .nat) (acc : Tm Γ .rat) :
    Deriv Δ (.eq (.app (.app (banachStep T) m) acc) (.app T acc)) := by
  have h1 : Deriv Δ (.eq (.app (banachStep T) m) (.lam (.app (T.wk (σ := .rat)) (.var .here)))) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.lam (.app (((T.wk (σ := .nat)).wk (σ := .rat))) (.var .here)) : Tm (.nat :: Γ) (.arrow .rat .rat)) m
    rwa [linkBanachStep1] at h
  have h2 : Deriv Δ (.eq (.app (.lam (.app (T.wk (σ := .rat)) (.var .here))) acc) (.app T acc)) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .rat)
      (.app (T.wk (σ := .rat)) (.var .here) : Tm (.rat :: Γ) .rat) acc
    rwa [linkBanachStep2] at h
  exact Deriv.transE (Deriv.congFun h1 acc) h2

/-- `iterAt T x0 0 = x0`. -/
def iterAtZero {Γ as : List Ty} {Δ : Ctx Γ as} (T : Tm Γ (.arrow .rat .rat)) (x0 : Tm Γ .rat) :
    Deriv Δ (.eq (iterAt T x0 .zero) x0) :=
  Deriv.convRecZero x0 (banachStep T)

/-- `iterAt T x0 (succ m) = T (iterAt T x0 m)`. -/
def iterAtSucc {Γ as : List Ty} {Δ : Ctx Γ as} (T : Tm Γ (.arrow .rat .rat)) (x0 : Tm Γ .rat) (m : Tm Γ .nat) :
    Deriv Δ (.eq (iterAt T x0 (.succ m)) (.app T (iterAt T x0 m))) :=
  Deriv.transE (Deriv.convRecSucc x0 (banachStep T) m)
    (banachStepApp T m (iterAt T x0 m))

/-- Congruence for the dyadic closeness predicate `qclose`. -/
def qcloseCong {Γ as : List Ty} {Δ : Ctx Γ as}
    {s s' : Tm Γ .nat} {u u' v v' : Tm Γ .rat}
    (hs : Deriv Δ (.eq s s')) (hu : Deriv Δ (.eq u u')) (hv : Deriv Δ (.eq v v')) :
    Deriv Δ (.eq (.app (.app (.app qclose s) u) v)
                 (.app (.app (.app qclose s') u') v')) := by
  have h1 : Deriv Δ (.eq (.app (.app (.app qclose s) u) v) (.app (.app (.app qclose s) u) v')) :=
    Deriv.congArg (.app (.app qclose s) u) hv
  have h2 : Deriv Δ (.eq (.app (.app (.app qclose s) u) v') (.app (.app (.app qclose s) u') v')) :=
    Deriv.congFun (Deriv.congArg (.app qclose s) hu) v'
  have h3 : Deriv Δ (.eq (.app (.app (.app qclose s) u') v') (.app (.app (.app qclose s') u') v')) :=
    Deriv.congFun (Deriv.congFun (Deriv.congArg qclose hs) u') v'
  exact Deriv.transE h1 (Deriv.transE h2 h3)

/-- Transport a `close` evaluation across argument equalities. -/
def qcloseTransport {Γ as : List Ty} {Δ : Ctx Γ as}
    {s s' : Tm Γ .nat} {u u' v v' : Tm Γ .rat}
    (hs : Deriv Δ (.eq s s')) (hu : Deriv Δ (.eq u u')) (hv : Deriv Δ (.eq v v'))
    (hclose : Deriv Δ (.eq (.app (.app (.app qclose s) u) v) (.succ .zero))) :
    Deriv Δ (.eq (.app (.app (.app qclose s') u') v') (.succ .zero)) :=
  Deriv.transE (Deriv.symmE (qcloseCong hs hu hv)) hclose

/-- `(m + k0) + 1 = (m + 1) + k0` in System T. -/
def scaleSuccStep {Γ as : List Ty} {Δ : Ctx Γ as} (m k0 : Tm Γ .nat) :
    Deriv Δ (.eq (.succ (.add m k0)) (.add (.succ m) k0)) := by
  have h1 : Deriv Δ (.eq (.add (.succ m) k0) (.succ (.add m k0))) := by
    have h := succPlusD (Δ := Δ)
    have h' := Deriv.allE k0 (Deriv.allE m h)
    deriv_norm at h'
    exact h'
  exact Deriv.symmE h1

/-- Premise A: $T$ is a dyadic contraction. -/
abbrev banachContractPremise (Γ : List Ty) :
    Formula (.nat :: .rat :: (.arrow .rat .rat) :: Γ)
      (.arrow .rat (.arrow .rat (.arrow .nat (.arrow .unit .unit)))) :=
  let ctxTy : List Ty := .nat :: .rat :: (.arrow .rat .rat) :: Γ
  let T_var : Tm ctxTy (.arrow .rat .rat) := .var (.there (.there .here))
  .all .rat (.all .rat (.all .nat
    (.imp (.eq (.app (.app (.app qclose (.var .here)) (.var (.there (.there .here)))) (.var (.there .here))) (.succ .zero))
      (.eq (.app (.app (.app qclose (.succ (.var .here)))
        (.app (T_var.wk.wk.wk) (.var (.there (.there .here)))))
        (.app (T_var.wk.wk.wk) (.var (.there .here)))) (.succ .zero)))))

/-- Premise B: seed condition $\text{close}(k_0, x_0, T(x_0)) = 1$. -/
abbrev banachSeedPremise (Γ : List Ty) :
    Formula (.nat :: .rat :: (.arrow .rat .rat) :: Γ) .unit :=
  let ctxTy : List Ty := .nat :: .rat :: (.arrow .rat .rat) :: Γ
  let k0_var : Tm ctxTy .nat := .var .here
  let x0_var : Tm ctxTy .rat := .var (.there .here)
  let T_var : Tm ctxTy (.arrow .rat .rat) := .var (.there (.there .here))
  .eq (.app (.app (.app qclose k0_var) x0_var) (.app T_var x0_var)) (.succ .zero)

/-- Realizer type of the stopping criterion: `Nat → Nat × (Nat → Unit)`. -/
abbrev banachRealizerTy : Ty :=
  .arrow .nat (.prod .nat (.arrow .nat .unit))

/-- Formula for the Banach convergence modulus conclusion:
    $\forall n, \exists N, \forall d. \; \text{close}(n, x_{N+d}, x_{N+d+1}) = 1$. -/
abbrev banachContractionConcl (Γ : List Ty) :
    Formula (.nat :: .rat :: (.arrow .rat .rat) :: Γ) banachRealizerTy :=
  let ctxTy : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ
  let T_var : Tm ctxTy (.arrow .rat .rat) := .var (.there (.there (.there (.there (.there .here)))))
  let x0_var : Tm ctxTy .rat := .var (.there (.there (.there (.there .here))))
  let n_var : Tm ctxTy .nat := .var (.there (.there .here))
  let N_var : Tm ctxTy .nat := .var (.there .here)
  let d_var : Tm ctxTy .nat := .var .here
  let m_var : Tm ctxTy .nat := .add N_var d_var
  let xm : Tm ctxTy .rat := iterAt T_var x0_var m_var
  let xm1 : Tm ctxTy .rat := iterAt T_var x0_var (.succ m_var)
  .all .nat (.ex .nat (.all .nat
    (.eq (.app (.app (.app qclose n_var) xm) xm1) (.succ .zero))))

/-- Context at the innermost point of `banachContractionD`. -/
abbrev banachInnerCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ)
      (.unit :: (.arrow .rat (.arrow .rat (.arrow .nat (.arrow .unit .unit)))) :: as) :=
  .cons (((banachSeedPremise Γ).wk (σ := .nat)).wk (σ := .nat))
    (.cons (((banachContractPremise Γ).wk (σ := .nat)).wk (σ := .nat))
      (((((Δ.wk).wk).wk).wk).wk))

/-- **Theorem (Banach Contraction Convergence Modulus)**:
    For EVERY contraction $T : \mathbb{Q} \to \mathbb{Q}$ with seed $x_0 \in \mathbb{Q}$
    and initial scale $k_0 \in \mathbb{N}$, derives by mathematical induction (`Deriv.ind`)
    on the iteration count $m$ that the stopping criterion $N(n) = n$ guarantees consecutive
    iterate gaps drop below $2^{-n}$ for all future iterations $N + d$. -/
def banachContractionD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all (.arrow .rat .rat) (.all .rat (.all .nat
      (.imp (banachContractPremise Γ)
        (.imp (banachSeedPremise Γ)
          (banachContractionConcl Γ)))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_))))
  -- Target precision n
  refine Deriv.allI ?_
  -- Witness for stopping iteration count: N = n
  refine Deriv.exI (τ := .nat) (.var .here) ?_
  deriv_norm
  -- For all offset indices d
  refine Deriv.allI ?_
  let ctxTy : List Ty := .nat :: .nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ
  let d : Tm ctxTy .nat := .var .here
  let n : Tm ctxTy .nat := .var (.there .here)
  let k0 : Tm ctxTy .nat := .var (.there (.there .here))
  let x0 : Tm ctxTy .rat := .var (.there (.there (.there .here)))
  let T : Tm ctxTy (.arrow .rat .rat) := .var (.there (.there (.there (.there .here))))
  let innerCtx := banachInnerCtx Γ Δ
  let xm : Tm ctxTy .rat := iterAt T x0 (.add n d)
  let xm1 : Tm ctxTy .rat := iterAt T x0 (.succ (.add n d))
  -- Orbit invariant for general m in this context:
  let orbitInv : Formula (.nat :: ctxTy) .unit :=
    let m_var : Tm (.nat :: ctxTy) .nat := .var .here
    let k0_var : Tm (.nat :: ctxTy) .nat := .var (.there (.there (.there .here)))
    let x0_var : Tm (.nat :: ctxTy) .rat := .var (.there (.there (.there (.there .here))))
    let T_var : Tm (.nat :: ctxTy) (.arrow .rat .rat) := .var (.there (.there (.there (.there (.there .here)))))
    let scale : Tm (.nat :: ctxTy) .nat := .add m_var k0_var
    let xm_m : Tm (.nat :: ctxTy) .rat := iterAt T_var x0_var m_var
    let xm1_m : Tm (.nat :: ctxTy) .rat := iterAt T_var x0_var (.succ m_var)
    .eq (.app (.app (.app qclose scale) xm_m) xm1_m) (.succ .zero)
  have hOrbit : Deriv innerCtx (.all .nat orbitInv) := by
    refine Deriv.ind ?_ ?_
    · -- Base case: m = 0
      deriv_norm
      have heq_scale : Deriv innerCtx (.eq (.add .zero k0) k0) := by
        have h := zeroPlusD (Δ := innerCtx)
        have h' := Deriv.allE k0 h
        deriv_norm at h'
        exact h'
      have heq_xm : Deriv innerCtx (.eq (iterAt T x0 .zero) x0) := iterAtZero T x0
      have heq_xm1 : Deriv innerCtx (.eq (iterAt T x0 (.succ .zero)) (.app T x0)) := by
        have hsucc := iterAtSucc (Δ := innerCtx) T x0 .zero
        have hcong := Deriv.congArg T (iterAtZero (Δ := innerCtx) T x0)
        exact Deriv.transE hsucc hcong
      have hSeed : Deriv innerCtx (.eq (.app (.app (.app qclose k0) x0) (.app T x0)) (.succ .zero)) := Deriv.ax
      exact qcloseTransport heq_scale.symmE heq_xm.symmE heq_xm1.symmE hSeed
    · -- Step case: m -> m + 1
      refine Deriv.allI (Deriv.impI ?_)
      let stepCtxTy : List Ty := .nat :: ctxTy
      let m_s : Tm stepCtxTy .nat := .var .here
      let k0_s : Tm stepCtxTy .nat := .var (.there (.there (.there .here)))
      let x0_s : Tm stepCtxTy .rat := .var (.there (.there (.there (.there .here))))
      let T_s : Tm stepCtxTy (.arrow .rat .rat) := .var (.there (.there (.there (.there (.there .here)))))
      let u : Tm stepCtxTy .rat := iterAt T_s x0_s m_s
      let v : Tm stepCtxTy .rat := iterAt T_s x0_s (.succ m_s)
      let scale : Tm stepCtxTy .nat := .add m_s k0_s
      have hContr : Deriv (.cons orbitInv innerCtx.wk) (((banachContractPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk := by
        deriv_assumption
      have h1 := Deriv.allE u hContr
      deriv_norm at h1
      have h2 := Deriv.allE v h1
      deriv_norm at h2
      have h3 := Deriv.allE scale h2
      deriv_norm at h3
      have hIH : Deriv (.cons orbitInv innerCtx.wk) orbitInv := Deriv.ax
      have hStepClose := Deriv.impE h3 hIH
      have heq_scale : Deriv (.cons orbitInv innerCtx.wk) (.eq (.succ (.add m_s k0_s)) (.add (.succ m_s) k0_s)) :=
        scaleSuccStep m_s k0_s
      have heq_u : Deriv (.cons orbitInv innerCtx.wk) (.eq (.app T_s (iterAt T_s x0_s m_s)) (iterAt T_s x0_s (.succ m_s))) :=
        Deriv.symmE (iterAtSucc T_s x0_s m_s)
      have heq_v : Deriv (.cons orbitInv innerCtx.wk) (.eq (.app T_s (iterAt T_s x0_s (.succ m_s))) (iterAt T_s x0_s (.succ (.succ m_s)))) :=
        Deriv.symmE (iterAtSucc T_s x0_s (.succ m_s))
      exact qcloseTransport heq_scale heq_u heq_v hStepClose
  have hInst := Deriv.allE (.add n d) hOrbit
  -- hInst : close((n + d) + k0, xm, xm1) = 1
  have heq_assoc : Deriv innerCtx (.eq (.add (.add n d) k0) (.add n (.add d k0))) := by
    have h := plusAssocD (Δ := innerCtx)
    have h' := Deriv.allE k0 (Deriv.allE d (Deriv.allE n h))
    deriv_norm at h'
    exact h'
  have hReassoc : Deriv innerCtx (.eq (.app (.app (.app qclose (.add n (.add d k0))) xm) xm1) (.succ .zero)) :=
    qcloseTransport heq_assoc (Deriv.eqRefl xm) (Deriv.eqRefl xm1) hInst
  exact Deriv.convQCloseMono n (.add d k0) xm xm1 hReassoc

-- MUTATION (does not build): Replacing witness `N = n` (`.var .here`) with a false witness like `N = 0` (`.zero`)
-- fails to build because the orbit step count `0 + d` gives scale tolerance `(0 + d) + k0`,
-- which cannot be reduced to target precision `n` via scale monotonicity when `n > d + k0`.

/-- Backward-compatibility alias for `banachContractionD`. -/
abbrev banachModulusD {Γ as : List Ty} {Δ : Ctx Γ as} := @banachContractionD Γ as Δ

/-- **The extracted Banach stopping criterion program.**
    Feed it operator `T`, initial point `x0`, initial scale `k0`, and requested precision `n`;
    returns the certified iteration count `N`. -/
def banachStoppingN (T : Q → Q) (x0 : Q) (k0 : Nat) (n : Nat) : Nat :=
  let realizer := (((((extractClosed (banachContractionD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    T x0 k0) (fun _ _ _ _ ↦ ())) ())
  (realizer n).1

/-! ## Kernel-Verified Stopping Tables and Boundary Checks -/

-- Picard operator T(y) = 1 + y/2 on Q with x0 = 1, fixed point y* = 2:
def picardT (y : Q) : Q := Q.add (Q.ofNat 1) (Q.div y (Q.ofNat 2))

-- Consecutive iterate gaps |T^(m+1)(x0) - T^m(x0)|:
def picardIterGap (T : Q → Q) (x0 : Q) (m : Nat) : Q :=
  let ym := (List.range m).foldl (fun acc _ ↦ T acc) x0
  let ym1 := T ym
  let diff := Q.sub ym1 ym
  if diff.num < 0 then Q.sub (Q.ofNat 0) diff else diff

-- Premise B verified at value level: closeVal k0 x0 (T x0) == 1
#guard closeVal 0 (Q.ofNat 1) (picardT (Q.ofNat 1)) == 1

-- 1. Concrete Stopping Table for Picard Iteration across precisions n = 0 ... 8:
#guard (List.range 9).map (banachStoppingN picardT (Q.ofNat 1) 0)
  == [0, 1, 2, 3, 4, 5, 6, 7, 8]

-- 2. Exact Boundary Soundness Checks for Picard Iteration (k0 = 0):
-- At m = N(n) = n: the gap is strictly below 2⁻ⁿ:
#guard Q.ltN (picardIterGap picardT (Q.ofNat 1) (banachStoppingN picardT (Q.ofNat 1) 0 1)) (D.toQ (D.pow2neg 1)) == 1
#guard Q.ltN (picardIterGap picardT (Q.ofNat 1) (banachStoppingN picardT (Q.ofNat 1) 0 2)) (D.toQ (D.pow2neg 2)) == 1
#guard Q.ltN (picardIterGap picardT (Q.ofNat 1) (banachStoppingN picardT (Q.ofNat 1) 0 4)) (D.toQ (D.pow2neg 4)) == 1
#guard Q.ltN (picardIterGap picardT (Q.ofNat 1) (banachStoppingN picardT (Q.ofNat 1) 0 6)) (D.toQ (D.pow2neg 6)) == 1

-- At m = N(n) - 1: the gap is NOT strictly below 2⁻ⁿ (exactness of the stopping rule):
-- For n = 1: N = 1, at m = 0 gap is 1/2 = 2⁻¹, not < 2⁻¹:
#guard Q.ltN (picardIterGap picardT (Q.ofNat 1) 0) (D.toQ (D.pow2neg 1)) == 0
-- For n = 4: N = 4, at m = 3 gap is 1/16 = 2⁻⁴, not < 2⁻⁴:
#guard Q.ltN (picardIterGap picardT (Q.ofNat 1) 3) (D.toQ (D.pow2neg 4)) == 0

-- 3. Second Contraction: T₂(y) = 3 + y/2 with x₀ = 5, fixed point y* = 6:
def picardT2 (y : Q) : Q := Q.add (Q.ofNat 3) (Q.div y (Q.ofNat 2))

-- Seed premise check: |5 - 5.5| = 0.5 < 2⁻⁰ = 1 (k0 = 0)
#guard closeVal 0 (Q.ofNat 5) (picardT2 (Q.ofNat 5)) == 1

#guard (List.range 7).map (banachStoppingN picardT2 (Q.ofNat 5) 0)
  == [0, 1, 2, 3, 4, 5, 6]

-- 4. Third Contraction: T₃(y) = y/2 with x₀ = 1, fixed point y* = 0:
def picardT3 (y : Q) : Q := Q.div y (Q.ofNat 2)

-- Seed premise check: |1 - 0.5| = 0.5 < 2⁻⁰ = 1 (k0 = 0)
#guard closeVal 0 (Q.ofNat 1) (picardT3 (Q.ofNat 1)) == 1

#guard (List.range 6).map (banachStoppingN picardT3 (Q.ofNat 1) 0)
  == [0, 1, 2, 3, 4, 5]

#print axioms banachContractionD
#print axioms banachStoppingN

end HAomega
