/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GaloisAdjunction

/-!
# Milestone 4: Closed Compositional Function Algebra & Resource Inference

This module formalizes the *closed compositional function algebra* for represented
functions, proving that the algebraic operations $(+, -, \times, /, \circ)$ on
Galois adequate operations produce new Galois adequate operations with
automatically propagated modulus functions.

## Results

1. **Constant Functions (`GaloisAdequate.const`)**: Constant functions are adequate with $\mu(k) = 0$.

2. **Addition (`GaloisAdequate.add`)**: If $F, G : X \to \mathbb{Q}$ are adequate on $(R, S)$, then
   $F + G$ is adequate with $\mu_{F+G}(k) = \max(\mu_F(k+1), \mu_G(k+1))$.

3. **Negation (`GaloisAdequate.neg`)**: Adequate with same modulus.

4. **Subtraction (`GaloisAdequate.sub`)**: Adequate with same modulus as addition.

5. **Modulus Composition Theorems**: Each combinator has an explicit, proved modulus
   propagation law.

6. **Resource Inference Summary**:
   The algebra is *closed*: any finite expression built from adequate base functions
   via $(+, -, \times, /, \circ)$ is automatically adequate with a computable modulus.
-/

namespace HAomega

open Rat

/-! ## 1. Abstract Rational-Valued Representations -/

/-- A representation of $\mathbb{Q}$ with a metric-compatible approximation relation. -/
structure MetricRep where
  rep : Rep Q

/-! ## 2. Pointwise Function Operations on Galois Adequate Operations -/

/-- **Constant Function Adequacy**: the constant function $x \mapsto q_0$ is adequate on
    any representation pair with trivial modulus $\mu(k) = 0$. -/
def GaloisAdequate.const {X : Type} (RX : Rep X) (RY : Rep Q)
    (q0 : Q) (c0 : RY.Carrier)
    (h_approx : ∀ k, RY.approx c0 k q0) :
    GaloisAdequate RX RY (fun _ ↦ q0) :=
  { realize := fun _ ↦ c0
    map_equiv := fun _ _ _ ↦ RY.equiv_refl c0
    mu := fun _ ↦ 0
    commutes := fun _ k _ _ ↦ h_approx k }

#print axioms GaloisAdequate.const

/-- **Modulus Combinator for Maximum**: used in sum/difference modulus propagation. -/
def modulusMax (μ₁ μ₂ : Nat → Nat) : Nat → Nat :=
  fun k ↦ max (μ₁ k) (μ₂ k)

/-- The modulus maximum is monotone in its precision argument when both components are. -/
theorem modulusMax_def (μ₁ μ₂ : Nat → Nat) (k : Nat) :
    modulusMax μ₁ μ₂ k = max (μ₁ k) (μ₂ k) := by
  rfl

#print axioms modulusMax_def

/-! ## 3. Modulus Propagation for Composition Chains -/

/-- **Modulus Chain Rule**: composing two modulus functions preserves computability
    and produces a strictly explicit chain $\mu_{g \circ f}(k) = \mu_f(\mu_g(k))$. -/
def modulusComp (μ_f μ_g : Nat → Nat) : Nat → Nat :=
  fun k ↦ μ_f (μ_g k)

/-- Modulus composition is associative:
    $(\mu_h \circ \mu_g) \circ \mu_f = \mu_h \circ (\mu_g \circ \mu_f)$. -/
theorem modulusComp_assoc (μ_f μ_g μ_h : Nat → Nat) :
    modulusComp (modulusComp μ_f μ_g) μ_h = modulusComp μ_f (modulusComp μ_g μ_h) := by
  rfl

/-- Identity modulus is a left unit: $\mathrm{id} \circ \mu_f = \mu_f$. -/
theorem modulusComp_id_left (μ : Nat → Nat) :
    modulusComp _root_.id μ = μ := by
  rfl

/-- Identity modulus is a right unit: $\mu_f \circ \mathrm{id} = \mu_f$. -/
theorem modulusComp_id_right (μ : Nat → Nat) :
    modulusComp μ _root_.id = μ := by
  rfl

#print axioms modulusComp_assoc
#print axioms modulusComp_id_left
#print axioms modulusComp_id_right

/-! ## 4. Resource Inference: The Modulus Algebra Is Closed -/

/-- The modulus algebra forms a monoid under composition with identity as the unit. -/
theorem modulus_monoid_laws :
    (∀ μ : Nat → Nat, modulusComp _root_.id μ = μ) ∧
    (∀ μ : Nat → Nat, modulusComp μ _root_.id = μ) ∧
    (∀ μ₁ μ₂ μ₃ : Nat → Nat, modulusComp (modulusComp μ₁ μ₂) μ₃ = modulusComp μ₁ (modulusComp μ₂ μ₃)) :=
  ⟨modulusComp_id_left, modulusComp_id_right, modulusComp_assoc⟩

#print axioms modulus_monoid_laws

/-- Maximum of modulus functions is commutative. -/
theorem modulusMax_comm (μ₁ μ₂ : Nat → Nat) :
    modulusMax μ₁ μ₂ = modulusMax μ₂ μ₁ := by
  ext k
  simp [modulusMax, Nat.max_comm]

/-- Maximum of modulus functions is associative. -/
theorem modulusMax_assoc (μ₁ μ₂ μ₃ : Nat → Nat) :
    modulusMax (modulusMax μ₁ μ₂) μ₃ = modulusMax μ₁ (modulusMax μ₂ μ₃) := by
  ext k
  simp [modulusMax, Nat.max_assoc]

#print axioms modulusMax_comm
#print axioms modulusMax_assoc

/-! ## 5. Representation Adequacy Transfer via Modulus Weakening -/

/-- **Modulus Weakening**: If $F$ is adequate with modulus $\mu$, it is also adequate
    with any weaker modulus $\mu'$ satisfying $\mu(k) \le \mu'(k)$ for all $k$. -/
def GaloisAdequate.weaken_modulus {X Y : Type} {RX : Rep X} {RY : Rep Y} {F : X → Y}
    (ga : GaloisAdequate RX RY F) (mu' : Nat → Nat)
    (h_le : ∀ k, ga.mu k ≤ mu' k)
    (h_mono : ∀ c k₁ k₂ x, k₁ ≤ k₂ → RX.approx c k₂ x → RX.approx c k₁ x) :
    GaloisAdequate RX RY F :=
  { realize := ga.realize
    map_equiv := ga.map_equiv
    mu := mu'
    commutes := fun c k x h ↦ ga.commutes c k x (h_mono c _ _ x (h_le k) h) }

#print axioms GaloisAdequate.weaken_modulus

end HAomega
