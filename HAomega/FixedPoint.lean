/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.Picard
import HAomega.GaloisAdequacy

/-!
# Non-Expansive Maps and Krasnoselskii–Mann Iteration

This module formalizes the data structures for **non-expansive mappings** ($L = 1$,
$|T(x) - T(y)| \le |x - y|$) and their averaged iterations:

1. **Non-Expansive Maps (`NonExpansiveMap`)**:
   Self-maps $T : [a, b] \to [a, b]$ with Lipschitz constant $L = 1$.

2. **Krasnoselskii–Mann Averaged Operator (`NonExpansiveMap.avg`)**:
   $$T_{1/2}(x) = \frac{1}{2} x + \frac{1}{2} T(x)$$
   We prove the identity $(T_{1/2}(x)).\mathrm{val} - x.\mathrm{val} = \frac{1}{2}((T(x)).\mathrm{val} - x.\mathrm{val})$
   (`step_eq_half_residual`).

3. **Krasnoselskii–Mann Sequence (`NonExpansiveMap.kmIter`)**:
   The sequence $x_n = T_{1/2}^n(x_0)$.
-/

namespace HAomega

open Rat

/-- Data of a non-expansive self-map $T : [a, b] \to [a, b]$. -/
structure NonExpansiveMap (a b : Q) where
  T : Q → Q
  /-- Non-expansiveness: $|T(x) - T(y)| \le |x - y|$. -/
  nonexp : ∀ x y : Q, Qle a x = true → Qle x b = true →
    Qle a y = true → Qle y b = true →
    |(T x).val - (T y).val| ≤ |x.val - y.val|
  /-- Maps $[a, b]$ to itself. -/
  maps_to : ∀ x : Q, Qle a x = true → Qle x b = true →
    Qle a (T x) = true ∧ Qle (T x) b = true

/-- The Krasnoselskii–Mann averaged operator $T_{1/2}(x) = \frac{1}{2} x + \frac{1}{2} T(x)$. -/
def NonExpansiveMap.avg {a b : Q} (N : NonExpansiveMap a b) (x : Q) : Q :=
  Q.div (Q.add x (N.T x)) (Q.ofNat 2)

/-- Krasnoselskii–Mann iteration sequence $x_n = T_{1/2}^n(x_0)$. -/
def NonExpansiveMap.kmIter {a b : Q} (N : NonExpansiveMap a b) (x0 : Q) : Nat → Q
  | 0 => x0
  | n + 1 => N.avg (N.kmIter x0 n)

/-- **Theorem (Averaged Step Equals Half Fixed-Point Residual)**:
    $x_{n+1} - x_n = \frac{1}{2}(T(x_n) - x_n)$. -/
theorem NonExpansiveMap.step_eq_half_residual {a b : Q} (N : NonExpansiveMap a b)
    (x : Q) :
    (N.avg x).val - x.val = (1 / 2 : Rat) * ((N.T x).val - x.val) := by
  dsimp [avg]
  rw [Q.val_div _ _ (by decide)]
  rw [Q.val_add, Q.val_ofNat]
  push_cast
  ring

#print axioms NonExpansiveMap.step_eq_half_residual

/-- Explicit rate of asymptotic regularity bound: $\Phi(k) = 4 (D + 1)^2 \cdot 4^k$. -/
def kmRate (diamSq : Nat) (k : Nat) : Nat :=
  4 * (diamSq + 1) * 4 ^ k

/-- Dividing a summed residual bound by $n$. -/
theorem residual_div_bound (diam : Rat) (k n : Nat) (hn : 0 < n)
    (h_sum : (n : Rat) * (1 / 2 ^ (2 * k + 2)) ≤ diam ^ 2) :
    1 / 2 ^ (2 * k + 2) ≤ diam ^ 2 / (n : Rat) := by
  have hn_pos : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  rw [le_div_iff₀ hn_pos, mul_comm]
  exact h_sum

#print axioms residual_div_bound

end HAomega
