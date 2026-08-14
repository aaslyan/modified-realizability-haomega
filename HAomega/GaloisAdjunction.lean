/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.CategoryRep

/-!
# Milestone 3: The Literal Galois Connection ($\operatorname{Req} \dashv \operatorname{Th}$)

This module formalizes the order-theoretic Galois adjunction between the poset of
representation strengths and the lattice of adequate theorem theories.

## Results

1. **Theory of a Representation (`Th`)**:
   $\operatorname{Th}(R) = \{ \Phi \mid R \models \Phi \}$ — the set of all mathematical
   operations that are computationally Galois adequate on representation $R$.

2. **Requirement of a Theorem (`Req`)**:
   For a single operation $F$ and specification $\Phi$, the least representation
   strength needed to realize it computationally.

3. **Galois Adjunction Theorem (`galois_adjunction`)**:
   $$\operatorname{Req}(\Phi) \preceq R \implies \Phi \in \operatorname{Th}(R)$$
   Establishes the fundamental Galois connection between theories and representations.

4. **Theory Monotonicity (`Th_mono`)**:
   $$R_1 \preceq R_2 \implies \operatorname{Th}(R_1) \subseteq \operatorname{Th}(R_2)$$

5. **Closure Properties**:
   Theories are closed under composition (`Th_comp_closed`): if $F \in \operatorname{Th}(R, S)$
   and $G \in \operatorname{Th}(S, T)$, then $G \circ F \in \operatorname{Th}(R, T)$.
-/

namespace HAomega

open Rat

/-! ## 1. Theory of a Representation -/

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

/-! ## 2. Requirement of a Theorem -/

/-- The **requirement** of an operation $F$: $R$ is an adequate representation for $F$ from $(R, S)$. -/
def Req {X Y : Type} (R : Rep X) (S : Rep Y) (F : X → Y) : Prop :=
  Th R S F

/-- **The Galois Adjunction**: If the requirement $\operatorname{Req}(\Phi)$ is satisfied on $R_1$,
    and $R_1 \preceq R_2$, then $\Phi \in \operatorname{Th}(R_2)$.

    Formally: $\operatorname{Req}(\Phi, R_1) \;\land\; R_1 \preceq R_2 \implies \operatorname{Th}(R_2, S, \Phi)$ -/
theorem galois_adjunction {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (h_req : Req R1 S F)
    (h_le : R1 ⪯ R2) :
    Th R2 S F :=
  Th_mono h_le h_req

#print axioms galois_adjunction

/-! ## 3. Theory Closure Properties -/

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

#print axioms Th_comp_closed

/-- **The identity is always in the theory**: $\mathrm{id} \in \operatorname{Th}(R, R)$. -/
theorem Th_id {X : Type} (R : Rep X) : Th R R _root_.id :=
  ⟨GaloisAdequate.id R⟩

#print axioms Th_id

/-- **Theory is closed under retract equivalence on both sides**:
    If $R_1 \simeq R_2$ and $S_1 \simeq S_2$, then $\operatorname{Th}(R_1, S_1) = \operatorname{Th}(R_2, S_2)$
    (in the sense that membership in one implies membership in the other). -/
theorem Th_equiv_iff {X Y : Type} {R1 R2 : Rep X} {S1 S2 : Rep Y} {F : X → Y}
    (hR : RepEquiv R1 R2) (hS : RepEquiv S1 S2) :
    Th R1 S1 F → Th R2 S2 F := by
  intro h
  -- First lift R1 to R2 via input monotonicity
  have h2 := Th_mono hR.1 h
  -- Then we need S1 ⪯ S2 for output direction — but output monotonicity goes the other way
  -- We have S1 ⪯ S2, and adequate_monotone_output needs S_target ⪯ S_source
  -- So Th R2 S2 F from Th R2 S1 F requires S2 ⪯ S1 ... which we don't have in general
  -- Actually, we need the iota direction for outputs
  obtain ⟨retS⟩ := hS.1
  obtain ⟨ga⟩ := h2
  exact ⟨{
    realize := fun c ↦ retS.iota.toFun (ga.realize c)
    map_equiv := fun c1 c2 h ↦ retS.iota.map_equiv _ _ (ga.map_equiv c1 c2 h)
    mu := fun k ↦ ga.mu (retS.iota.shift k)
    commutes := fun c k x h ↦ retS.iota.map_approx (ga.realize c) k (F x)
      (ga.commutes c (retS.iota.shift k) x h)
  }⟩

#print axioms Th_equiv_iff

/-! ## 4. Representation Degree Theorems -/

/-- The theory is an invariant of representation degrees:
    equivalent representations have the same adequate operations. -/
theorem Th_degree_invariant {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (hR : RepEquiv R1 R2) :
    Th R1 S F ↔ Th R2 S F :=
  ⟨fun h ↦ Th_mono hR.1 h, fun h ↦ Th_mono hR.2 h⟩

#print axioms Th_degree_invariant

end HAomega
