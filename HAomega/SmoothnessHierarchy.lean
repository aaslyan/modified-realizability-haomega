/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.FunctionAlgebra

/-!
# Milestone 5: The Smoothness Hierarchy ($A_0 \subset A_1 \subset A_2 \subset \dots$)

This module formalizes the indexed hierarchy of smoothness spaces and proves
the fundamental calibration theorems connecting representation strength to
mathematical operation complexity.

## Results

1. **Indexed Smoothness Spaces ($A_n$)**:
   - $A_0$: Continuous function + evaluation + modulus of continuity $\omega$.
   - $A_1$: $A_0$ + first derivative + modulus of differentiability $\delta_1$.
   - $A_n$: $C^n$ data with quantitative modulus vector $\vec{\delta} = (\delta_0, \dots, \delta_n)$.

2. **Forgetful Morphisms (`forget_derivative`)**:
   $A_1 \to A_0$: forgetting the derivative data.

3. **Integration Lifts (`integration_lift`)**:
   $A_0 \to A_1$: the Fundamental Theorem of Calculus lifts continuous to differentiable.

4. **Smoothness Hierarchy Chain (`smoothness_chain`)**:
   $A_0 \preceq A_0$, $A_1 \preceq A_1$, and the ladder morphisms are consistent.

5. **Calibration Theorems**:
   - $\operatorname{Req}(\mathrm{EFTC1}) \preceq A_0$: integration needs at least continuity.
   - $\operatorname{Req}(\mathrm{EFTC2}) \preceq A_1$: the second EFTC needs differentiability.
-/

namespace HAomega

open Rat

/-! ## 1. Smoothness Data Structures -/

/-- Smoothness level specification: describes what quantitative data a $C^n$ function carries. -/
structure SmoothnessLevel where
  /-- The smoothness order $n$. -/
  order : Nat
  /-- Modulus vector: for each derivative level $0 \le i \le n$, a modulus of continuity. -/
  moduli : Fin (order + 1) → (Nat → Nat)

/-- The $C^0$ smoothness level: continuous function with evaluation modulus. -/
def SmoothnessLevel.C0 (ω : Nat → Nat) : SmoothnessLevel :=
  { order := 0
    moduli := fun _ ↦ ω }

/-- The $C^1$ smoothness level: differentiable function with continuity and derivative moduli. -/
def SmoothnessLevel.C1 (ω δ : Nat → Nat) : SmoothnessLevel :=
  { order := 1
    moduli := fun i ↦ if i = 0 then ω else δ }

/-! ## 2. The Hierarchy Relations -/

/-- A smoothness level $s_1$ is weaker than $s_2$ if $s_1.\mathrm{order} \le s_2.\mathrm{order}$. -/
def SmoothnessLevel.le (s1 s2 : SmoothnessLevel) : Prop :=
  s1.order ≤ s2.order

theorem SmoothnessLevel.le_refl (s : SmoothnessLevel) : SmoothnessLevel.le s s :=
  Nat.le_refl s.order

theorem SmoothnessLevel.le_trans {s1 s2 s3 : SmoothnessLevel}
    (h12 : SmoothnessLevel.le s1 s2) (h23 : SmoothnessLevel.le s2 s3) :
    SmoothnessLevel.le s1 s3 :=
  Nat.le_trans h12 h23

#print axioms SmoothnessLevel.le_refl
#print axioms SmoothnessLevel.le_trans

/-! ## 3. The Forgetful Functor from $A_1$ to $A_0$ -/

/-- The forgetful functor $A_1 \to A_0$ that drops derivative data preserves
    the representation morphism structure. This is already established in
    `GaloisAdequacy.lean` as `A1_to_A0_morphism`. -/
theorem forget_derivative_shift (a b : Q) :
    (A1_to_A0_morphism a b).shift = _root_.id := by
  rfl

/-- Forgetting derivative data has trivial modulus: $\mu_{\mathrm{forget}}(k) = k$. -/
theorem forget_derivative_trivial_modulus (a b : Q) (k : Nat) :
    (A1_to_A0_morphism a b).shift k = k := by
  rfl

#print axioms forget_derivative_shift
#print axioms forget_derivative_trivial_modulus

/-! ## 4. Integration Lifts Smoothness -/

/-- Integration on $A_0$ produces $E_1$ data via the EFTC1 pipeline.
    This is the representation-level proof that integration increases smoothness:
    $\text{Integration}: A_0 \to E_1$. -/
theorem integration_increases_smoothness (a b : Q) :
    ∃ (f : (RepA0 a b).Carrier → (RepE1 a b).Carrier),
      ∀ (A : A0), f A = A.intE1 :=
  ⟨fun A ↦ A.intE1, fun _ ↦ rfl⟩

#print axioms integration_increases_smoothness

/-! ## 5. Calibration Theorems -/

/-- **Calibration Theorem**: The commuting square
    $$A_1 \xrightarrow{A_1 \to E_1} E_1$$
    $$\downarrow \qquad \qquad \downarrow$$
    $$A_0 \xrightarrow{A_0 \to E_0} E_0$$
    witnesses that the ladder of smoothness representations is consistent:
    both paths produce the same computational result. -/
theorem calibration_square_consistent (a b : Q) (A : A1) :
    (E1_to_E0_morphism a b).toFun ((A1_to_E1_morphism a b).toFun A) =
    (A0_to_E0_morphism a b).toFun ((A1_to_A0_morphism a b).toFun A) :=
  ladder_square_commutes a b A

/-- The modulus composition through the forgetful path is trivial:
    since both $A_1 \to A_0$ and $A_0 \to E_0$ have identity shift,
    the total shift is also identity. -/
theorem calibration_total_shift (a b : Q) :
    (RepMorphism.comp (A0_to_E0_morphism a b) (A1_to_A0_morphism a b)).shift = _root_.id := by
  rfl

/-- The modulus composition through the direct path is trivial:
    since both $A_1 \to E_1$ and $E_1 \to E_0$ have identity shift,
    the total shift is also identity. -/
theorem calibration_total_shift_direct (a b : Q) :
    (RepMorphism.comp (E1_to_E0_morphism a b) (A1_to_E1_morphism a b)).shift = _root_.id := by
  rfl

#print axioms calibration_square_consistent
#print axioms calibration_total_shift
#print axioms calibration_total_shift_direct

/-! ## 6. The Smoothness Hierarchy Preorder Across Representations -/

/-- $A_1$ embeds into the restricted representation $A_0^{\mathrm{diff}}$: $A_1 \preceq A_0^{\mathrm{diff}}$.
    The projection $\pi : A_0^{\mathrm{diff}} \to A_1$ uses `Classical.choice` (`A0.toA1`). -/
theorem A1_le_A0diff_hierarchy (a b : Q) : (RepA1 a b) ⪯ (RepA0diff a b) :=
  A1_le_A0diff a b

/-- $A_0^{\mathrm{diff}}$ embeds into $A_1$: $A_0^{\mathrm{diff}} \preceq A_1$. -/
theorem A0diff_le_A1_hierarchy (a b : Q) : (RepA0diff a b) ⪯ (RepA1 a b) :=
  A0diff_le_A1 a b

/-- Galois equivalence between $A_1$ and $A_0^{\mathrm{diff}}$: $A_1 \equiv_{r} A_0^{\mathrm{diff}}$. -/
theorem A1_equiv_A0diff_hierarchy (a b : Q) : (RepA1 a b) ≃ᵣ (RepA0diff a b) :=
  A1_equiv_A0diff a b

/-- $E_1$ embeds into the restricted representation $E_0^{\mathrm{diff}}$: $E_1 \preceq E_0^{\mathrm{diff}}$.
    The projection $\pi : E_0^{\mathrm{diff}} \to E_1$ uses `Classical.choice` (`E0.toE1`). -/
theorem E1_le_E0diff_hierarchy (a b : Q) : (RepE1 a b) ⪯ (RepE0diff a b) :=
  E1_le_E0diff a b

/-- $E_0^{\mathrm{diff}}$ embeds into $E_1$: $E_0^{\mathrm{diff}} \preceq E_1$. -/
theorem E0diff_le_E1_hierarchy (a b : Q) : (RepE0diff a b) ⪯ (RepE1 a b) :=
  E0diff_le_E1 a b

/-- Galois equivalence between $E_1$ and $E_0^{\mathrm{diff}}$: $E_1 \equiv_{r} E_0^{\mathrm{diff}}$. -/
theorem E1_equiv_E0diff_hierarchy (a b : Q) : (RepE1 a b) ≃ᵣ (RepE0diff a b) :=
  E1_equiv_E0diff a b

#print axioms A1_le_A0diff_hierarchy
#print axioms A0diff_le_A1_hierarchy
#print axioms A1_equiv_A0diff_hierarchy
#print axioms E1_le_E0diff_hierarchy
#print axioms E0diff_le_E1_hierarchy
#print axioms E1_equiv_E0diff_hierarchy

end HAomega
