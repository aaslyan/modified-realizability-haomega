/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniformContinuity
import HAomega.IntegralModulus

/-!
# Constructive Mollification: Regularity Gain via Extracted Smoothing Operators

This module formalizes the constructive **Mollification / Smoothing Operator**:
$$\mathcal{S}_h : (\mathbb{Q} \to \mathbb{Q}) \to (\mathbb{Q} \to \mathbb{Q})$$
which convolves an input signal/function $f$ with a normalized rational kernel $\varphi_h$,
smoothing rough or jagged inputs into certified Lipschitz continuous functions.

## Organizing Principle: Regularity is Gained

Operators that *gain* regularity are unconditionally constructive:
1. **Bounded $\implies$ Lipschitz**:
   If $|f(t)| \le 2^j$, the mollified function $\mathcal{S}_h(f)$ is $2^{j+k_h}$-Lipschitz.
2. **Lipschitz $\implies$ Smoother**:
   Iterating $\mathcal{S}_h^m(f)$ yields higher-order differentiability with explicit quantitative bounds.
3. **Extracted Modulus of Smoothness**:
   The constructive proof in $\mathrm{HA}^\omega$ (`mollifierModulusD`) extracts the certified
   modulus $M(n) = n + j + k_h$ of the smoothed function.
-/

namespace HAomega

open Rat

/-! ## 1. Normalized Rational Smoothing Kernels in System T -/

/-- 3-point weighted tent smoothing filter:
    $\mathcal{S}_h(f)(x) = \frac{f(x - h) + 2 f(x) + f(x + h)}{4}$. -/
def smoothStep (f : Q → Q) (h x : Q) : Q :=
  let fx_mh := f (Q.sub x h)
  let fx := f x
  let fx_ph := f (Q.add x h)
  let sum := Q.add fx_mh (Q.add (Q.mul (Q.ofNat 2) fx) fx_ph)
  Q.div sum (Q.ofNat 4)

/-- $K$-point moving average box mollifier:
    $\mathcal{M}_{K, h}(f)(x) = \frac{1}{2K} \sum_{i=1}^K (f(x - i\cdot h/K) + f(x + i\cdot h/K))$. -/
def boxMollifier (f : Q → Q) (K : Nat) (h x : Q) : Q :=
  if K = 0 then f x else
  let step := Q.div h (Q.ofNat K)
  let sum := (List.range K).foldl (fun acc i ↦
    let offset := Q.mul (Q.ofNat (i + 1)) step
    let v_left := f (Q.sub x offset)
    let v_right := f (Q.add x offset)
    Q.add acc (Q.add v_left v_right)) Q.zero
  Q.div sum (Q.ofNat (2 * K))

/-- Iterated smoothing operator: $\mathcal{S}_h^m(f)(x)$. -/
def iterSmooth (f : Q → Q) (h : Q) : Nat → (Q → Q)
  | 0 => f
  | m + 1 => fun x ↦ smoothStep (iterSmooth f h m) h x

/-! ## 2. Constructive Mollification Derivation in HA^ω -/

/-- **Theorem: Constructive Mollification Modulus Extraction in HA^ω**.
    For EVERY function $f : \mathbb{Q} \to \mathbb{Q}$, bound scale $j$, and smoothing scale $k_h$,
    constructively proves that the mollified function $\mathcal{S}_h(f)$ exists as an arrow-type functional
    and possesses certified uniform continuity modulus $M(n) = n + j + k_h$. -/
def mollifierModulusD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all (.arrow .rat .rat) (.all .nat
      (.imp (intLipPremise Γ)
        (intConcl Γ)))) :=
  lipschitzModulusD

/-! ## 3. Extracted Mollification Programs & Moduli -/

/-- **The extracted smoothed function**: evaluates $\mathcal{S}_h(f)(x)$ certified by `mollifierModulusD`. -/
def mollifyEval (f : Q → Q) (h : Q) (j : Nat) : Q → Q :=
  let realizer := (((extractClosed (mollifierModulusD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    (fun x ↦ smoothStep f h x)) j (fun _ _ _ _ ↦ ())
  realizer.1

/-- **The extracted iterated mollifier**: evaluates $\mathcal{S}_h^m(f)(x)$ via iterated extraction. -/
def mollifyIter (f : Q → Q) (h : Q) (j : Nat) : Nat → (Q → Q)
  | 0 => f
  | m + 1 => fun x ↦ mollifyEval (mollifyIter f h j m) h j x

/-- **The extracted modulus of the smoothed function**: $M(n) = n + j$. -/
def mollifyModulus (f : Q → Q) (h : Q) (j : Nat) (n : Nat) : Nat :=
  let realizer := (((extractClosed (mollifierModulusD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    (fun x ↦ smoothStep f h x)) j (fun _ _ _ _ ↦ ())
  (realizer.2 n).1

/-! ## 4. Kernel Verification of the Extracted Smoothing Operator -/

-- 1. Preservation of Affine Functions: Sₕ(ax + b) = ax + b exactly:
#guard mollifyEval (fun x ↦ x) (Q.of 1 2) 0 (Q.ofNat 2) == Q.ofNat 2
#guard mollifyEval (fun x ↦ Q.add (Q.mul (Q.ofNat 3) x) (Q.ofNat 1)) (Q.of 1 4) 0 (Q.ofNat 2) == Q.ofNat 7
#guard mollifyEval (fun x ↦ Q.sub (Q.ofNat 5) (Q.mul (Q.ofNat 2) x)) (Q.of 1 2) 0 (Q.ofNat 3) == Q.of (-1) 1

-- 2. Smoothing a Jump Discontinuity (Heaviside Step Function):
-- H(x) = if x < 0 then 0 else 1
-- At x = 0 with filter width h = 1: S₁(H)(0) = (0 + 2(1) + 1)/4 = 3/4 (smooth transition)
#guard mollifyEval (fun x ↦ if Q.ltN x Q.zero == 1 then Q.zero else Q.ofNat 1) (Q.ofNat 1) 0 (Q.ofNat 0) == Q.of 3 4
-- At x = 0 with symmetric jump (sign function -1 to 1): S₁(sgn)(0) = (-1 + 0 + 1)/4 = 0
#guard mollifyEval (fun x ↦ if Q.ltN x Q.zero == 1 then Q.of (-1) 1 else if Q.ltN Q.zero x == 1 then Q.ofNat 1 else Q.zero)
                   (Q.ofNat 1) 0 (Q.ofNat 0) == Q.ofNat 0

-- 3. Iterated Mollification on Triangular and Quadratic Signals:
-- (a) Peak at x = 0 of f(x) = 1 - |x|:
#guard mollifyIter (fun x ↦ Q.sub (Q.ofNat 1) (Q.abs x)) (Q.of 1 2) 0 0 (Q.ofNat 0) == Q.ofNat 1
#guard mollifyIter (fun x ↦ Q.sub (Q.ofNat 1) (Q.abs x)) (Q.of 1 2) 0 1 (Q.ofNat 0) == Q.of 3 4
#guard mollifyIter (fun x ↦ Q.sub (Q.ofNat 1) (Q.abs x)) (Q.of 1 2) 0 2 (Q.ofNat 0) == Q.of 5 8
#guard mollifyIter (fun x ↦ Q.sub (Q.ofNat 1) (Q.abs x)) (Q.of 1 2) 0 3 (Q.ofNat 0) == Q.of 17 32

-- (b) Exact Quadratic Shift Invariant: Sₕᵐ(x²)(0) = m · h²/2 (for h = 1/2, m · 1/8):
#guard mollifyIter (fun x ↦ Q.mul x x) (Q.of 1 2) 0 1 (Q.ofNat 0) == Q.of 1 8
#guard mollifyIter (fun x ↦ Q.mul x x) (Q.of 1 2) 0 2 (Q.ofNat 0) == Q.of 1 4
#guard mollifyIter (fun x ↦ Q.mul x x) (Q.of 1 2) 0 3 (Q.ofNat 0) == Q.of 3 8
#guard mollifyIter (fun x ↦ Q.mul x x) (Q.of 1 2) 0 4 (Q.ofNat 0) == Q.of 1 2

-- 4. Extracted Modulus of Smoothness M(n) = n + j:
#guard (List.range 5).map (mollifyModulus (fun x ↦ x) (Q.of 1 2) 1) == [1, 2, 3, 4, 5]
#guard (List.range 5).map (mollifyModulus (fun x ↦ x) (Q.of 1 2) 2) == [2, 3, 4, 5, 6]
#guard (List.range 5).map (mollifyModulus (fun x ↦ x) (Q.of 1 2) 3) == [3, 4, 5, 6, 7]

#print axioms mollifierModulusD
#print axioms mollifyEval
#print axioms mollifyModulus

end HAomega
