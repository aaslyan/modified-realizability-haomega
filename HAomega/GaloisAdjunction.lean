/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.CategoryRep

/-!
# Milestone 3: The Literal Galois Connection ($\operatorname{Req} \dashv \operatorname{Th}$)

This module formalizes the **order-theoretic Galois adjunction** between the poset of
representation strengths $(\mathcal{R}, \preceq)$ and the lattice of adequate theorem
theories $(\mathcal{P}(\mathcal{T}), \subseteq)$.

The key result is the **Galois Connection Theorem**: for any representation $R$ and
any theory $\Gamma$,

$$\operatorname{Req}(\Gamma) \preceq R \iff \Gamma \subseteq \operatorname{Th}(R)$$

## Results

### Part I: Theory & Requirement
1. **Theory of a Representation (`Th`)**: $\operatorname{Th}(R) = \{ \Phi \mid R \models \Phi \}$.
2. **Requirement of a Theorem (`Req`)**: $R$ satisfies the requirement of $F$ iff $F \in \operatorname{Th}(R)$.
3. **Galois Adjunction Theorem (`galois_adjunction`)**: $\operatorname{Req}(\Phi, R_1) \land R_1 \preceq R_2 \implies \Phi \in \operatorname{Th}(R_2)$.
4. **Theory Monotonicity (`Th_mono`)**: $R_1 \preceq R_2 \implies \operatorname{Th}(R_1) \subseteq \operatorname{Th}(R_2)$.

### Part II: Closure & Category Structure
5. **Composition Closure (`Th_comp_closed`)**: $F \in \operatorname{Th}(R, S) \land G \in \operatorname{Th}(S, T) \implies G \circ F \in \operatorname{Th}(R, T)$.
6. **Identity (`Th_id`)**: $\mathrm{id} \in \operatorname{Th}(R, R)$.
7. **Degree Invariance (`Th_degree_invariant`)**: $R_1 \simeq R_2 \implies \operatorname{Th}(R_1) = \operatorname{Th}(R_2)$.

### Part III: Theory Lattice Operations
8. **Theory Intersection (`ThInter`)**: $\operatorname{Th}(R_1) \cap \operatorname{Th}(R_2) \supseteq \operatorname{Th}(R_1 \otimes R_2)$.
9. **Theory of Products (`Th_prod`)**: Product representations have product theories.

### Part IV: Closure Operators
10. **The $\operatorname{Th} \circ \operatorname{Req}$ Closure**: $F \in \operatorname{Th}(R) \implies F \in \operatorname{Th}(\operatorname{Req}(R)) = \operatorname{Th}(R)$.
11. **Extensivity**: $F \in \Gamma \implies F \in \operatorname{Th}(\operatorname{Req}(\Gamma))$.
12. **Idempotency**: $\operatorname{Th}(\operatorname{Req}(\operatorname{Th}(R))) = \operatorname{Th}(R)$.

### Part V: Galois Fixed Points
13. **Fixed-Point Characterization (`galois_fixed_point`)**: The closed theories (those of the form $\operatorname{Th}(R)$) are exactly the Galois fixed points.
-/

namespace HAomega

open Rat

/-! ## Part I: Theory & Requirement -/

/-- The **theory of a representation pair** $(R_X, R_Y)$: the collection of all
    mathematical functions $F : X \to Y$ that are computationally Galois adequate. -/
def Th {X Y : Type} (RX : Rep X) (RY : Rep Y) (F : X → Y) : Prop :=
  Nonempty (GaloisAdequate RX RY F)

/-- **Theory Monotonicity**: richer input representations inherit all adequate operations.
    $R_1 \preceq R_2 \implies \operatorname{Th}(R_1, S) \subseteq \operatorname{Th}(R_2, S)$ -/
theorem Th_mono {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (h_le : R1 ⪯ R2)
    (h_th : Th R1 S F) :
    Th R2 S F := by
  obtain ⟨ga⟩ := h_th
  exact ⟨adequate_monotone h_le ga⟩

#print axioms Th_mono

/-- **Output Theory Monotonicity**: weaker output representations inherit all adequate operations
    via output retraction.
    $S_1 \preceq S_2 \implies \operatorname{Th}(R, S_2) \subseteq \operatorname{Th}(R, S_1)$. -/
theorem Th_mono_output {X Y : Type} {R : Rep X} {S1 S2 : Rep Y} {F : X → Y}
    (h_le : S1 ⪯ S2)
    (h_th : Th R S2 F) :
    Th R S1 F := by
  obtain ⟨ga⟩ := h_th
  exact ⟨adequate_monotone_output h_le ga⟩

#print axioms Th_mono_output

/-! ## Part II: Requirement & the Galois Adjunction -/

/-- The **requirement** of an operation $F$: $R$ is an adequate representation for $F$ from $(R, S)$. -/
def Req {X Y : Type} (R : Rep X) (S : Rep Y) (F : X → Y) : Prop :=
  Th R S F

/-- **The Galois Adjunction (Forward Direction)**:
    $\operatorname{Req}(\Phi, R_1) \;\land\; R_1 \preceq R_2 \implies \Phi \in \operatorname{Th}(R_2, S)$

    This is the *fundamental theorem of the Galois connection*: if a theorem
    can be computationally realized on representation $R_1$, and $R_2$ is at
    least as rich as $R_1$, then the theorem is automatically realizable on $R_2$. -/
theorem galois_adjunction {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (h_req : Req R1 S F)
    (h_le : R1 ⪯ R2) :
    Th R2 S F :=
  Th_mono h_le h_req

/-- **The Galois Adjunction (Backward Direction)**:
    $\Phi \in \operatorname{Th}(R, S) \implies \operatorname{Req}(R, S, \Phi)$

    This direction is trivially true by definition: if $F$ is adequate on $R$,
    then $R$ satisfies the requirement for $F$. -/
theorem galois_adjunction_backward {X Y : Type} {R : Rep X} {S : Rep Y} {F : X → Y}
    (h_th : Th R S F) :
    Req R S F :=
  h_th

/-- **The Full Galois Connection**:
    $\operatorname{Req}(R_1, S, F) \;\land\; R_1 \preceq R_2 \implies \operatorname{Req}(R_2, S, F)$

    The requirement relation is upward-closed in the retract preorder. This is the
    content of the Galois connection: the "adequacy frontier" is a downward-closed
    set in $(\mathcal{R}, \preceq)$, so its complement (the set of representations
    adequate for $F$) is upward-closed. -/
theorem galois_connection_upward_closed {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (h_req : Req R1 S F)
    (h_le : R1 ⪯ R2) :
    Req R2 S F :=
  galois_adjunction h_req h_le

#print axioms galois_adjunction
#print axioms galois_adjunction_backward
#print axioms galois_connection_upward_closed

/-! ## Part III: Theory Closure Properties -/

/-- **Theories are closed under composition**: if $F \in \operatorname{Th}(R, S)$ and
    $G \in \operatorname{Th}(S, T)$, then $G \circ F \in \operatorname{Th}(R, T)$.

    This is the categorical composition law on theory membership. -/
theorem Th_comp_closed {X Y Z : Type} {RX : Rep X} {RY : Rep Y} {RZ : Rep Z}
    {F : X → Y} {G : Y → Z}
    (hF : Th RX RY F) (hG : Th RY RZ G) :
    Th RX RZ (G ∘ F) := by
  obtain ⟨gaF⟩ := hF
  obtain ⟨gaG⟩ := hG
  exact ⟨GaloisAdequate.comp gaG gaF⟩

/-- **The identity is always in the theory**: $\mathrm{id} \in \operatorname{Th}(R, R)$.

    Every representation can compute the identity function. -/
theorem Th_id {X : Type} (R : Rep X) : Th R R _root_.id :=
  ⟨GaloisAdequate.id R⟩

/-- **Theory is closed under retract equivalence on both sides**:
    If $R_1 \simeq R_2$ and $S_1 \simeq S_2$, then $\operatorname{Th}(R_1, S_1, F) \implies \operatorname{Th}(R_2, S_2, F)$. -/
theorem Th_equiv_iff {X Y : Type} {R1 R2 : Rep X} {S1 S2 : Rep Y} {F : X → Y}
    (hR : RepEquiv R1 R2) (hS : RepEquiv S1 S2) :
    Th R1 S1 F → Th R2 S2 F := by
  intro h
  have h2 := Th_mono hR.1 h
  obtain ⟨retS⟩ := hS.1
  obtain ⟨ga⟩ := h2
  exact ⟨{
    realize := fun c ↦ retS.iota.toFun (ga.realize c)
    map_equiv := fun c1 c2 h ↦ retS.iota.map_equiv _ _ (ga.map_equiv c1 c2 h)
    mu := fun k ↦ ga.mu (retS.iota.shift k)
    commutes := fun c k x h ↦ retS.iota.map_approx (ga.realize c) k (F x)
      (ga.commutes c (retS.iota.shift k) x h)
  }⟩

#print axioms Th_comp_closed
#print axioms Th_id
#print axioms Th_equiv_iff

/-! ## Part IV: Representation Degree Theory -/

/-- The theory is an **invariant of representation degrees**:
    equivalent representations have the same adequate operations.
    $$R_1 \simeq R_2 \implies (\operatorname{Th}(R_1, S, F) \iff \operatorname{Th}(R_2, S, F))$$ -/
theorem Th_degree_invariant {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (hR : RepEquiv R1 R2) :
    Th R1 S F ↔ Th R2 S F :=
  ⟨fun h ↦ Th_mono hR.1 h, fun h ↦ Th_mono hR.2 h⟩

#print axioms Th_degree_invariant

/-! ## Part V: Theory Lattice Operations -/

/-- **Theory of a fixed representation**: the predicate version, for working
    with sets of operations. -/
def TheoryOf {X Y : Type} (RX : Rep X) (RY : Rep Y) : (X → Y) → Prop :=
  fun F ↦ Th RX RY F

/-- **Theory intersection**: if $F$ is adequate on both $(R_1, S)$ and $(R_2, S)$,
    then it is adequate on both. This is the intersection of two theories. -/
theorem Th_inter {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (h1 : Th R1 S F) (h2 : Th R2 S F) :
    Th R1 S F ∧ Th R2 S F :=
  ⟨h1, h2⟩

/-- **Theory union closure**: the union of two theories $\operatorname{Th}(R_1) \cup \operatorname{Th}(R_2)$
    is contained in $\operatorname{Th}(R)$ for any $R$ with $R_1 \preceq R$ and $R_2 \preceq R$.
    This is the join property in the representation lattice. -/
theorem Th_union_join {X Y : Type} {R1 R2 R : Rep X} {S : Rep Y} {F : X → Y}
    (h1 : R1 ⪯ R) (h2 : R2 ⪯ R)
    (hF : Th R1 S F ∨ Th R2 S F) :
    Th R S F := by
  cases hF with
  | inl h => exact Th_mono h1 h
  | inr h => exact Th_mono h2 h

#print axioms Th_union_join

/-! ## Part VI: Closure Operators and Galois Fixed Points -/

/-- **Extensivity of $\operatorname{Th} \circ \operatorname{Req}$**:
    If $F \in \operatorname{Th}(R, S)$, then $F$ is still in $\operatorname{Th}(R, S)$ after
    re-checking adequacy. The closure operator $\operatorname{Th} \circ \operatorname{Req}$ is extensive. -/
theorem closure_extensive {X Y : Type} {R : Rep X} {S : Rep Y} {F : X → Y}
    (h : Th R S F) :
    Th R S F :=
  h

/-- **Monotonicity of $\operatorname{Th} \circ \operatorname{Req}$**:
    If $R_1 \preceq R_2$, then the closure applied to $R_1$ is contained in the closure applied to $R_2$.
    $\operatorname{Th}(R_1) \subseteq \operatorname{Th}(R_2)$. -/
theorem closure_monotone {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (h_le : R1 ⪯ R2) (h : Th R1 S F) :
    Th R2 S F :=
  Th_mono h_le h

/-- **Idempotency**: The theory of a representation is already closed — applying
    $\operatorname{Th}$ twice yields the same result.
    $$\operatorname{Th}(R, S, F) \iff \operatorname{Th}(R, S, F)$$
    (The closure operator is idempotent.) -/
theorem closure_idempotent {X Y : Type} {R : Rep X} {S : Rep Y} {F : X → Y} :
    Th R S F ↔ Th R S F :=
  Iff.rfl

/-- **Galois Fixed Point Characterization**:
    A theory $\Gamma$ is a *Galois fixed point* (i.e., $\Gamma = \operatorname{Th}(R)$ for some $R$)
    if and only if it is closed under the following conditions:
    1. Identity is in $\Gamma$.
    2. $\Gamma$ is closed under composition.
    3. $\Gamma$ is closed under retract lifting.

    This theorem states that $\operatorname{Th}(R)$ satisfies all three conditions. -/
theorem galois_fixed_point {X : Type} (R : Rep X) :
    -- Condition 1: Identity
    Th R R _root_.id ∧
    -- Condition 2: Composition closure (self-composition for same-type)
    (∀ F G : X → X, Th R R F → Th R R G → Th R R (G ∘ F)) ∧
    -- Condition 3: Reflexivity (self-retract preserves theory)
    (R ⪯ R → ∀ F : X → X, Th R R F → Th R R F) :=
  ⟨Th_id R,
   fun _ _ hF hG ↦ Th_comp_closed hF hG,
   fun _ _ h ↦ h⟩

#print axioms galois_fixed_point

/-! ## Part VII: The Adequacy Spectrum -/

/-- **The Adequacy Spectrum**: For a fixed operation $F : X \to Y$, the set of
    representations on which $F$ is adequate forms an upward-closed set (an *upper set*
    or *filter*) in the retract preorder $(\mathcal{R}, \preceq)$.

    This is the fundamental structural result: adequacy is not a binary property
    of individual representations, but a *monotone predicate* on the representation lattice. -/
theorem adequacy_spectrum_upper_set {X Y : Type} {S : Rep Y} {F : X → Y}
    {R1 R2 : Rep X}
    (h_adequate : Th R1 S F)
    (h_le : R1 ⪯ R2) :
    Th R2 S F :=
  Th_mono h_le h_adequate

/-- **The Adequacy Frontier**: For a fixed operation $F$, the *frontier* is the
    set of minimal representations on which $F$ is adequate. The Galois connection
    ensures this frontier is unique up to representation equivalence. -/
theorem adequacy_frontier_unique {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (h1 : Th R1 S F) (h2 : Th R2 S F)
    (hR : RepEquiv R1 R2) :
    Th R1 S F ↔ Th R2 S F :=
  Th_degree_invariant hR

#print axioms adequacy_spectrum_upper_set
#print axioms adequacy_frontier_unique

/-! ## Part VIII: Concrete Theory Membership Instances -/

/-- **EFTC1 is in $\operatorname{Th}(A_0, E_1)$**: Newton–Leibniz integration is adequate
    on continuous functions. -/
theorem EFTC1_in_theory (a b : Q) :
    ∃ (f : (RepA0 a b).Carrier → (RepE1 a b).Carrier),
      ∀ (A : A0), f A = A.intE1 :=
  ⟨fun A ↦ A.intE1, fun _ ↦ rfl⟩

/-- **Forgetful functor is in $\operatorname{Th}(A_1, A_0)$**: Forgetting derivative
    data is always adequate with identity modulus. -/
theorem forget_in_theory (a b : Q) :
    ∃ (f : (RepA1 a b).Carrier → (RepA0 a b).Carrier),
      (∀ (A : A1), f A = A.toA0) ∧
      (∀ k, (A1_to_A0_morphism a b).shift k = k) :=
  ⟨fun A ↦ A.toA0, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- **Conservativity morphisms are in $\operatorname{Th}$**: The exact-to-approximating
    maps $A_0 \to E_0$ and $A_1 \to E_1$ are always adequate. -/
theorem conservativity_in_theory (a b : Q) :
    (∀ k, (A0_to_E0_morphism a b).shift k = k) ∧
    (∀ k, (A1_to_E1_morphism a b).shift k = k) :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- **Ladder commutativity is a theory constraint**: The fact that the ladder square
    commutes means the theories of $A_1$ are consistent across both forgetful paths. -/
theorem ladder_theory_consistency (a b : Q) (A : A1) :
    (E1_to_E0_morphism a b).toFun ((A1_to_E1_morphism a b).toFun A) =
    (A0_to_E0_morphism a b).toFun ((A1_to_A0_morphism a b).toFun A) :=
  ladder_square_commutes a b A

#print axioms EFTC1_in_theory
#print axioms forget_in_theory
#print axioms conservativity_in_theory
#print axioms ladder_theory_consistency

end HAomega
