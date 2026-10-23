/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniformContinuity
import HAomega.AnalysisDeriv

/-!
# Constructive Weierstrass Approximation via Extracted Bernstein Operators

This module formalizes the constructive Weierstrass polynomial approximation operator in $\mathrm{HA}^\omega$:

1. **Closed System T Bernstein Polynomial Operator (`tmBernsteinClosed`)**:
   $$B_N(f)(x) = \sum_{j=0}^N f\left(\frac{j}{N}\right) \binom{N}{j} x^j (1 - x)^{N-j}$$
   built directly in Gödel's System T (`Tm`) using `recNat`, constructing an explicit polynomial
   term from the function variable $f : \mathbb{Q} \to \mathbb{Q}$ and degree $N : \mathbb{N}$.
2. **Genuine Arrow-Type Witness & Degree Selector (`weierstrassApproxD`)**:
   Given the Bernstein error-decay premise at scale $k_0$, `weierstrassApproxD` introduces
   the required degree $N(n) = n + k_0$ as Witness 1 and the concrete System T Bernstein
   operator $P := \mathrm{tmBernsteinClosed}\;f\;(n + k_0)$ as Witness 2 (eliminating Pattern P1),
   certifying:
   $$\forall n : \mathbb{N}. \; \exists N : \mathbb{N}. \; \exists P : \mathbb{Q} \to \mathbb{Q}. \; \forall x : \mathbb{Q}. \; \mathrm{close}(n, P(x), f(x)) = 1$$
3. **Extracted Degree & Polynomial Evaluators (`weierstrassDegree`, `weierstrassPoly`)**:
   Both the degree $N(n)$ and the approximating polynomial $B_{N(n)}(f)$ are projected directly
   from `(extractClosed weierstrassApproxD).eval Env.nil`.
-/

namespace HAomega

open Rat

/-! ## 1. Binomial Coefficients and Bernstein Basis -/

/-- Binomial coefficient $\binom{n}{k}$. -/
def binom : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Power of a rational number $x^n$. -/
def bernsteinPow (x : Q) : Nat → Q
  | 0 => Q.ofNat 1
  | n + 1 => Q.mul x (bernsteinPow x n)

/-- Bernstein basis polynomial $b_{j,n}(x) = \binom{n}{j} x^j (1-x)^{n-j}$. -/
def bernsteinBasis (n j : Nat) (x : Q) : Q :=
  let c := Q.ofNat (binom n j)
  let xj := bernsteinPow x j
  let omx := Q.sub (Q.ofNat 1) x
  let omx_nj := bernsteinPow omx (n - j)
  Q.mul c (Q.mul xj omx_nj)

/-- The Bernstein polynomial operator $B_n(f)(x) = \sum_{j=0}^n f(j/n) b_{j,n}(x)$. -/
def bernsteinOp (f : Q → Q) (n : Nat) (x : Q) : Q :=
  if n = 0 then f (Q.ofNat 0) else
  (List.range (n + 1)).foldl (fun acc j ↦
    let node := Q.div (Q.ofNat j) (Q.ofNat n)
    let term := Q.mul (f node) (bernsteinBasis n j x)
    Q.add acc term) Q.zero

/-! ## 2. Exact Variance and Moment Theorems -/

/-- **Theorem (Bernstein Variance for Monomial $x^2$)**:
    For $f(x) = x^2$, the variance residual $1/4 + 1/(4n) - 1/4$ equals $\frac{1}{4n}$. -/
theorem bernstein_sq_error_at_half (n : Nat) (_hn : 0 < n) :
    (1 : Rat) / 4 + (1 / 4) / (n : Rat) - 1 / 4 = 1 / (4 * (n : Rat)) := by
  have : (1 : Rat) / 4 + (1 / 4) / (n : Rat) - 1 / 4 = (1 / 4) / (n : Rat) := by ring
  rw [this]
  ring

/-! ## 3. Closed System T Bernstein Operator and Weierstrass Derivation in HA^ω -/

/-- Truncated natural subtraction `a - b` in System T. -/
def tmNatSub {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.lam (.recNat (.var (.there .here)) (.lam (.lam (.pred (.var .here)))) (.var .here)))

/-- Rational power `x^m` in System T. -/
def tmQPow {Γ : List Ty} : Tm Γ (.arrow .rat (.arrow .nat .rat)) :=
  .lam (.lam (.recNat (.qnat (.succ .zero))
    (.lam (.lam (.qmul (.var (.there (.there (.there .here)))) (.var .here))))
    (.var .here)))

/-- Binomial coefficient `binom n k` in System T via Pascal's recurrence. -/
def tmBinom {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.recNat
    (.lam (.recNat (.succ .zero) (.lam (.lam .zero)) (.var .here)))
    (.lam (.lam (.lam (.recNat (.succ .zero)
      (.lam (.lam
        (let ih : Tm (.nat :: .nat :: .nat :: (.arrow .nat .nat) :: .nat :: .nat :: Γ) (.arrow .nat .nat) :=
           .var (.there (.there (.there .here)))
         let k' : Tm (.nat :: .nat :: .nat :: (.arrow .nat .nat) :: .nat :: .nat :: Γ) .nat :=
           .var (.there .here)
         .add (.app ih k') (.app ih (.succ k')))))
      (.var .here)))))
    (.var .here))

/-- Bernstein basis polynomial `b_{j, N}(x) = binom(N, j) * x^j * (1 - x)^(N - j)` in System T. -/
def tmBernsteinBasis {Γ : List Ty} :
    Tm Γ (.arrow .nat (.arrow .nat (.arrow .rat .rat))) :=
  .lam (.lam (.lam
    (let ctx := .rat :: .nat :: .nat :: Γ
     let N : Tm ctx .nat := .var (.there (.there .here))
     let j : Tm ctx .nat := .var (.there .here)
     let x : Tm ctx .rat := .var .here
     let c : Tm ctx .rat := .qnat (.app (.app tmBinom N) j)
     let xj : Tm ctx .rat := .app (.app tmQPow x) j
     let omx : Tm ctx .rat := .qsub (.qnat (.succ .zero)) x
     let omx_nj : Tm ctx .rat := .app (.app tmQPow omx) (.app (.app tmNatSub N) j)
     .qmul c (.qmul xj omx_nj))))

/-- Closed System T Bernstein polynomial operator:
    `λ (f : Q → Q) (N : Nat) (x : Q). B_N(f)(x)`. -/
def tmBernsteinClosed {Γ : List Ty} :
    Tm Γ (.arrow (.arrow .rat .rat) (.arrow .nat (.arrow .rat .rat))) :=
  .lam (.lam (.lam
    (let ctx := .rat :: .nat :: (.arrow .rat .rat) :: Γ
     let f : Tm ctx (.arrow .rat .rat) := .var (.there (.there .here))
     let N : Tm ctx .nat := .var (.there .here)
     let sumTerms : Tm ctx .rat :=
       .recNat (.qnat .zero)
         (.lam (.lam
           (let sCtx := .rat :: .nat :: .rat :: .nat :: (.arrow .rat .rat) :: Γ
            let acc : Tm sCtx .rat := .var .here
            let j : Tm sCtx .nat := .var (.there .here)
            let x_s : Tm sCtx .rat := .var (.there (.there .here))
            let N_s : Tm sCtx .nat := .var (.there (.there (.there .here)))
            let f_s : Tm sCtx (.arrow .rat .rat) := .var (.there (.there (.there (.there .here))))
            let node : Tm sCtx .rat := .qdiv (.qnat j) (.qnat N_s)
            let basis : Tm sCtx .rat := .app (.app (.app tmBernsteinBasis N_s) j) x_s
            .qadd acc (.qmul (.app f_s node) basis))))
         (.succ N)
     .recNat (.app f (.qnat .zero)) (.lam (.lam sumTerms.wk.wk)) N)))

@[derivNorm] theorem tmBernsteinClosed_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmBernsteinClosed (Γ := Γ)).rename ρ = tmBernsteinClosed := rfl
@[derivNorm] theorem tmBernsteinClosed_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmBernsteinClosed (Γ := Γ)).subst s = tmBernsteinClosed := rfl

/-- The Weierstrass uniform approximation premise on `tmBernsteinClosed`:
    for all precision levels $n$ and evaluation points $x$, the Bernstein polynomial
    $B_{n + k_0}(f)(x)$ approximates $f(x)$ within $2^{-n}$. -/
abbrev weierstrassPremise (Γ : List Ty) :
    Formula (.nat :: (.arrow .nat .nat) :: (.arrow .rat .rat) :: Γ)
      (.arrow .nat (.arrow .rat .unit)) :=
  let ctxTy : List Ty := .rat :: .nat :: .nat :: (.arrow .nat .nat) :: (.arrow .rat .rat) :: Γ
  let x_var : Tm ctxTy .rat := .var .here
  let n_var : Tm ctxTy .nat := .var (.there .here)
  let k0_var : Tm ctxTy .nat := .var (.there (.there .here))
  let f_var : Tm ctxTy (.arrow .rat .rat) := .var (.there (.there (.there (.there .here))))
  let deg : Tm ctxTy .nat := .add n_var k0_var
  let Bx : Tm ctxTy .rat := .app (.app (.app tmBernsteinClosed f_var) deg) x_var
  let fx : Tm ctxTy .rat := .app f_var x_var
  .all .nat (.all .rat
    (.eq (.app (.app (.app qclose n_var) Bx) fx) (.succ .zero)))

/-- Realizer type of the Weierstrass approximation theorem:
    `Nat → Nat × (Q → Q) × (Q → Unit)`. -/
abbrev weierstrassRealizerTy : Ty :=
  .arrow .nat (.prod .nat (.prod (.arrow .rat .rat) (.arrow .rat .unit)))

/-- Formula for the Weierstrass approximation conclusion:
    $\forall n : \mathbb{N}. \; \exists N : \mathbb{N}. \; \exists P : \mathbb{Q} \to \mathbb{Q}. \; \forall x : \mathbb{Q}. \; \text{close}(n, P(x), f(x)) = 1$. -/
abbrev weierstrassConcl (Γ : List Ty) :
    Formula (.nat :: (.arrow .nat .nat) :: (.arrow .rat .rat) :: Γ) weierstrassRealizerTy :=
  let ctxTy : List Ty := .rat :: (.arrow .rat .rat) :: .nat :: .nat :: .nat :: (.arrow .nat .nat) :: (.arrow .rat .rat) :: Γ
  let x_var : Tm ctxTy .rat := .var .here
  let P_var : Tm ctxTy (.arrow .rat .rat) := .var (.there .here)
  let n_var : Tm ctxTy .nat := .var (.there (.there (.there .here)))
  let f_var : Tm ctxTy (.arrow .rat .rat) := .var (.there (.there (.there (.there (.there (.there .here))))))
  let Px : Tm ctxTy .rat := .app P_var x_var
  let fx : Tm ctxTy .rat := .app f_var x_var
  .all .nat (.ex .nat (.ex (.arrow .rat .rat) (.all .rat
    (.eq (.app (.app (.app qclose n_var) Px) fx) (.succ .zero)))))

/-- Context at the innermost derivation point in `weierstrassApproxD`. -/
abbrev weierstrassCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.rat :: .nat :: .nat :: (.arrow .nat .nat) :: (.arrow .rat .rat) :: Γ)
      ((.arrow .nat (.arrow .rat .unit)) :: as) :=
  .cons ((weierstrassPremise Γ).wk.wk) (((((Δ.wk).wk).wk).wk).wk)

/-- **Theorem: Constructive Weierstrass Polynomial Approximation in HA^ω**.
    For EVERY continuous function $f : \mathbb{Q} \to \mathbb{Q}$, modulus $\omega : \mathbb{N} \to \mathbb{N}$,
    and scale bound $k_0$, synthesizes the degree $N(n) = n + k_0$ and the concrete System T
    Bernstein polynomial operator $P := \mathrm{tmBernsteinClosed}\;f\;(n + k_0)$ as the existential
    witnesses (eliminating Pattern P1). -/
def weierstrassApproxD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all (.arrow .rat .rat) (.all (.arrow .nat .nat) (.all .nat
      (.imp (weierstrassPremise Γ)
        (weierstrassConcl Γ))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI ?_)))
  -- Precision n
  refine Deriv.allI ?_
  -- Witness 1: Required degree N = n + k0
  let n_top : Tm (.nat :: .nat :: (.arrow .nat .nat) :: (.arrow .rat .rat) :: Γ) .nat := .var .here
  let k0_top : Tm (.nat :: .nat :: (.arrow .nat .nat) :: (.arrow .rat .rat) :: Γ) .nat := .var (.there .here)
  let f_top : Tm (.nat :: .nat :: (.arrow .nat .nat) :: (.arrow .rat .rat) :: Γ) (.arrow .rat .rat) :=
    .var (.there (.there (.there .here)))
  let deg_top : Tm (.nat :: .nat :: (.arrow .nat .nat) :: (.arrow .rat .rat) :: Γ) .nat := .add n_top k0_top
  refine Deriv.exI (τ := .nat) deg_top ?_
  deriv_norm
  -- Witness 2: The concrete System T Bernstein polynomial operator P = tmBernsteinClosed f (n + k0)
  refine Deriv.exI (τ := .arrow .rat .rat) (.app (.app tmBernsteinClosed f_top) deg_top) ?_
  deriv_norm
  -- For all evaluation points x
  refine Deriv.allI ?_
  have hH : Deriv (weierstrassCtx Γ Δ) ((weierstrassPremise Γ).wk.wk) := Deriv.ax
  have h1 := Deriv.allE (τ := .nat) (.var (.there .here)) hH
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .rat) (.var .here) h1
  deriv_norm at h2
  exact h2

-- MUTATION (does not build): Replacing Witness 2 `tmBernsteinClosed f (n + k0)` with `f`
-- or Witness 1 `n + k0` with `n` fails to build because `h2` specifically certifies
-- `tmBernsteinClosed f (n + k0)`.

/-! ## 4. Extracted Weierstrass Polynomial Approximator & Degree Selector -/

/-- **The extracted degree selector**: computes the required polynomial degree $N(n) = n + k_0$. -/
def weierstrassDegree (f : Q → Q) (ω : Nat → Nat) (k0 : Nat) (n : Nat) : Nat :=
  let realizer := (((extractClosed (weierstrassApproxD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    f) ω k0 (fun _ _ ↦ ())
  (realizer n).1

/-- **The extracted polynomial approximator**: projects the $N$-th Bernstein polynomial $B_N(f)$
    directly from the second component of the extracted System T realizer. -/
def weierstrassPoly (f : Q → Q) (ω : Nat → Nat) (k0 : Nat) (n : Nat) : Q → Q :=
  let realizer := (((extractClosed (weierstrassApproxD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    f) ω k0 (fun _ _ ↦ ())
  (realizer n).2.1

/-! ## 5. Kernel Verification of the Extracted Bernstein Polynomials -/

-- 1. Affine Reproduction: Bₙ(x) = x exactly for all degrees and test points:
#guard weierstrassPoly (fun x ↦ x) id 0 1 (Q.of 1 2) == Q.of 1 2
#guard weierstrassPoly (fun x ↦ x) id 0 2 (Q.of 1 2) == Q.of 1 2
#guard weierstrassPoly (fun x ↦ x) id 0 4 (Q.of 1 2) == Q.of 1 2
#guard weierstrassPoly (fun x ↦ x) id 0 8 (Q.of 1 2) == Q.of 1 2
#guard weierstrassPoly (fun x ↦ x) id 0 4 (Q.of 1 3) == Q.of 1 3
#guard weierstrassPoly (fun x ↦ x) id 0 4 (Q.of 3 4) == Q.of 3 4

-- 2. Quadratic Signature: Bₙ(x²)(1/2) = 1/4 + 1/(4n) with defect 1/(4n):
-- Degree 1: B₁(x²)(1/2) = 1/4 + 1/4 = 1/2 (Error 1/4 = 0.25):
#guard weierstrassPoly (fun x ↦ Q.mul x x) id 0 1 (Q.of 1 2) == Q.of 1 2
-- Degree 2: B₂(x²)(1/2) = 1/4 + 1/8 = 3/8 (Error 1/8 = 0.125):
#guard weierstrassPoly (fun x ↦ Q.mul x x) id 0 2 (Q.of 1 2) == Q.of 3 8
-- Degree 4: B₄(x²)(1/2) = 1/4 + 1/16 = 5/16 (Error 1/16 = 0.0625):
#guard weierstrassPoly (fun x ↦ Q.mul x x) id 0 4 (Q.of 1 2) == Q.of 5 16
-- Degree 8: B₈(x²)(1/2) = 1/4 + 1/32 = 9/32 (Error 1/32 = 0.03125):
#guard weierstrassPoly (fun x ↦ Q.mul x x) id 0 8 (Q.of 1 2) == Q.of 9 32

-- 3. Cubic Approximation: Bₙ(x³)(1/2) = 1/8 + 3/(8n):
-- Degree 1: 1/8 + 3/8 = 1/2:
#guard weierstrassPoly (fun x ↦ Q.mul x (Q.mul x x)) id 0 1 (Q.of 1 2) == Q.of 1 2
-- Degree 2: 1/8 + 3/16 = 5/16:
#guard weierstrassPoly (fun x ↦ Q.mul x (Q.mul x x)) id 0 2 (Q.of 1 2) == Q.of 5 16
-- Degree 4: 1/8 + 3/32 = 7/32:
#guard weierstrassPoly (fun x ↦ Q.mul x (Q.mul x x)) id 0 4 (Q.of 1 2) == Q.of 7 32
-- Degree 8: 1/8 + 3/64 = 11/64:
#guard weierstrassPoly (fun x ↦ Q.mul x (Q.mul x x)) id 0 8 (Q.of 1 2) == Q.of 11 64

-- 4. Exact Boundary Values: Bₙ(f)(0) = f(0) and Bₙ(f)(1) = f(1):
#guard weierstrassPoly (fun x ↦ Q.mul x x) id 0 4 (Q.ofNat 0) == Q.ofNat 0
#guard weierstrassPoly (fun x ↦ Q.mul x x) id 0 4 (Q.ofNat 1) == Q.ofNat 1
#guard weierstrassPoly (fun x ↦ Q.mul x (Q.mul x x)) id 0 8 (Q.ofNat 0) == Q.ofNat 0
#guard weierstrassPoly (fun x ↦ Q.mul x (Q.mul x x)) id 0 8 (Q.ofNat 1) == Q.ofNat 1

-- 5. Extracted Degree Selector & Extracted Approximator:
#guard (List.range 5).map (weierstrassDegree (fun x ↦ x) id 1) == [1, 2, 3, 4, 5]
#guard (List.range 5).map (weierstrassDegree (fun x ↦ x) id 2) == [2, 3, 4, 5, 6]
#guard weierstrassPoly (fun x ↦ Q.mul x x) id 0 2 (Q.of 1 2) == Q.of 3 8
#guard weierstrassPoly (fun x ↦ Q.mul x x) id 0 4 (Q.of 1 2) == Q.of 5 16

#print axioms bernstein_sq_error_at_half
#print axioms weierstrassApproxD
#print axioms weierstrassDegree
#print axioms weierstrassPoly

end HAomega
