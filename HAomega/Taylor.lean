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
import HAomega.ODEDemo

/-!
# Taylor's Expansion and Remainder Positivity Scaling

This module formalizes constructive **Taylor polynomial expansions** and their
scaling properties:

1. **Taylor Polynomial Operator (`taylorEval`)**:
   For derivatives $f^{(0)}(a), f^{(1)}(a), \dots, f^{(n)}(a)$, the $n$-th Taylor polynomial is:
   $$T_n(x) = \sum_{j=0}^n \frac{f^{(j)}(a)}{j!} (x - a)^j$$

2. **The Positivity Scaling Lemma (`taylor_remainder_pos_scale`)**:
   For non-negative bound $M \ge 0$ and displacement $\Delta x \ge 0$, the product
   $\frac{M}{(n+1)!} \Delta x^{n+1}$ is non-negative.

3. **Kernel-Verified Computations**:
   Verified `#guard` calculations computing Taylor expansions of $e^x$ at $a = 0$
   evaluated at $x = 1/2$.
-/

namespace HAomega

open Rat

/-! ## 1. Factorial Positivity and Taylor Polynomial Evaluator -/

/-- Factorial is strictly positive for all $n$. -/
theorem fact_pos : ∀ n : Nat, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- $n$-th Taylor polynomial: $T_n(x) = \sum_{j=0}^n \frac{c_j}{j!} (x - a)^j$. -/
def taylorEval (derivs : List Q) (a x : Q) : Q :=
  let dx := Q.sub x a
  ((List.range derivs.length).zip derivs).foldl (fun acc ⟨j, fj⟩ ↦
    let coeff := Q.div fj (Q.ofNat (fact j))
    let term := Q.mul coeff (qpow dx j)
    Q.add acc term) Q.zero

/-! ## 2. The Positivity Scaling Lemma -/

/-- **Lemma (Taylor Remainder Factor Positivity)**:
    For non-negative derivative bound $M \ge 0$ and non-negative displacement $\Delta x \ge 0$,
    the expression $\frac{M}{(n+1)!} \Delta x^{n+1}$ is non-negative. -/
theorem taylor_remainder_pos_scale (M : Rat) (dx : Rat) (n : Nat)
    (hM : 0 ≤ M) (hdx : 0 ≤ dx) :
    0 ≤ (M / (fact (n + 1) : Rat)) * (dx ^ (n + 1)) := by
  have h_fact : (0 : Rat) < (fact (n + 1) : Rat) := by
    exact_mod_cast (fact_pos (n + 1))
  have h_frac : 0 ≤ M / (fact (n + 1) : Rat) := div_nonneg hM (le_of_lt h_fact)
  have h_pow : 0 ≤ dx ^ (n + 1) := by positivity
  exact mul_nonneg h_frac h_pow

#print axioms taylor_remainder_pos_scale

/-! ## 3. Verified Kernel Computations for Taylor Expansions -/

-- Taylor polynomial of exp(x) at a = 0: derivatives are all 1
-- Order 0: T₀(1/2) = 1
#guard taylorEval [Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.ofNat 1

-- Order 1: T₁(1/2) = 1 + 1/2 = 3/2 = 1.5
#guard taylorEval [Q.ofNat 1, Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.of 3 2

-- Order 2: T₂(1/2) = 1 + 1/2 + 1/8 = 13/8 = 1.625
#guard taylorEval [Q.ofNat 1, Q.ofNat 1, Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.of 13 8

-- Order 3: T₃(1/2) = 1 + 1/2 + 1/8 + 1/48 = 79/48 ≈ 1.64583
#guard taylorEval [Q.ofNat 1, Q.ofNat 1, Q.ofNat 1, Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.of 79 48

-- Order 4: T₄(1/2) = 79/48 + 1/384 = 633/384 = 211/128 ≈ 1.6484375
#guard taylorEval [Q.ofNat 1, Q.ofNat 1, Q.ofNat 1, Q.ofNat 1, Q.ofNat 1] (Q.ofNat 0) (Q.of 1 2) == Q.of 211 128

end HAomega
