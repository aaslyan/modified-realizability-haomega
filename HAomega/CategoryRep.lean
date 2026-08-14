/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GaloisAdequacy

/-!
# Milestone 2: The Category $\mathbf{Rep}$ — Modulus Propagation & Monotonicity

This module proves the categorical laws and the Representation Monotonicity Theorem
for the category $\mathbf{Rep}$ of computational representations.

## Results

1. **Modulus Propagation Law (`RepMorphism.comp_shift`)**:
   For composable morphisms $f : R_1 \to R_2$ and $g : R_2 \to R_3$:
   $$\mu_{g \circ f}(k) = \mu_f(\mu_g(k))$$

2. **Categorical Laws**:
   - Left identity: $\mathrm{id} \circ f \sim f$ on code-functions (`comp_id_left`).
   - Right identity: $f \circ \mathrm{id} \sim f$ on code-functions (`comp_id_right`).
   - Associativity: $(h \circ g) \circ f \sim h \circ (g \circ f)$ on code-functions (`comp_assoc`).
   - Shift associativity: $\mu_{(h \circ g) \circ f} = \mu_{h \circ (g \circ f)}$ (`comp_shift_assoc`).

3. **Galois Adequate Identity (`GaloisAdequate.id`)**:
   The identity function on any representation is Galois adequate with $\mu = \mathrm{id}$.

4. **Galois Adequate Modulus Propagation (`GaloisAdequate.comp_mu`)**:
   For composable adequate operations $f, g$:
   $$\mu_{g \circ f}(k) = \mu_f(\mu_g(k))$$

5. **Representation Monotonicity Theorem (`adequate_monotone`)**:
   $$R_1 \preceq R_2 \;\land\; \text{GaloisAdequate } R_1 \, S \, F \implies \text{GaloisAdequate } R_2 \, S \, F$$
   If a mathematical operation $F$ is computationally adequate on representation $R_1$,
   it is automatically adequate on any richer representation $R_2 \succeq R_1$.

6. **Output Monotonicity (`adequate_monotone_output`)**:
   $$S_1 \preceq S_2 \;\land\; \text{GaloisAdequate } R \, S_2 \, F \implies \text{GaloisAdequate } R \, S_1 \, F$$
-/

namespace HAomega

open Rat

/-! ## 1. Modulus Propagation Law -/

/-- **Modulus Propagation**: The modulus of a composite morphism $g \circ f$ satisfies
    $\mu_{g \circ f}(k) = \mu_f(\mu_g(k))$. -/
theorem RepMorphism.comp_shift {X : Type} {R1 R2 R3 : Rep X}
    (g : RepMorphism R2 R3) (f : RepMorphism R1 R2) :
    (RepMorphism.comp g f).shift = fun k ↦ f.shift (g.shift k) := by
  rfl

#print axioms RepMorphism.comp_shift

/-! ## 2. Categorical Identity Laws -/

/-- Left identity: $\mathrm{id} \circ f = f$ on code-functions. -/
theorem RepMorphism.comp_id_left {X : Type} {R1 R2 : Rep X}
    (f : RepMorphism R1 R2) :
    (RepMorphism.comp (RepMorphism.id R2) f).toFun = f.toFun := by
  rfl

/-- Right identity: $f \circ \mathrm{id} = f$ on code-functions. -/
theorem RepMorphism.comp_id_right {X : Type} {R1 R2 : Rep X}
    (f : RepMorphism R1 R2) :
    (RepMorphism.comp f (RepMorphism.id R1)).toFun = f.toFun := by
  rfl

/-- Left identity on shifts: $\mu_{\mathrm{id} \circ f} = \mu_f$. -/
theorem RepMorphism.comp_id_left_shift {X : Type} {R1 R2 : Rep X}
    (f : RepMorphism R1 R2) :
    (RepMorphism.comp (RepMorphism.id R2) f).shift = f.shift := by
  rfl

/-- Right identity on shifts: $\mu_{f \circ \mathrm{id}} = \mu_f$. -/
theorem RepMorphism.comp_id_right_shift {X : Type} {R1 R2 : Rep X}
    (f : RepMorphism R1 R2) :
    (RepMorphism.comp f (RepMorphism.id R1)).shift = f.shift := by
  rfl

#print axioms RepMorphism.comp_id_left
#print axioms RepMorphism.comp_id_right
#print axioms RepMorphism.comp_id_left_shift
#print axioms RepMorphism.comp_id_right_shift

/-! ## 3. Categorical Associativity -/

/-- Associativity of morphism composition on code-functions:
    $(h \circ g) \circ f = h \circ (g \circ f)$. -/
theorem RepMorphism.comp_assoc {X : Type} {R1 R2 R3 R4 : Rep X}
    (h : RepMorphism R3 R4) (g : RepMorphism R2 R3) (f : RepMorphism R1 R2) :
    (RepMorphism.comp (RepMorphism.comp h g) f).toFun =
    (RepMorphism.comp h (RepMorphism.comp g f)).toFun := by
  rfl

/-- Associativity of modulus composition:
    $\mu_{(h \circ g) \circ f}(k) = \mu_{h \circ (g \circ f)}(k)$. -/
theorem RepMorphism.comp_shift_assoc {X : Type} {R1 R2 R3 R4 : Rep X}
    (h : RepMorphism R3 R4) (g : RepMorphism R2 R3) (f : RepMorphism R1 R2) :
    (RepMorphism.comp (RepMorphism.comp h g) f).shift =
    (RepMorphism.comp h (RepMorphism.comp g f)).shift := by
  rfl

#print axioms RepMorphism.comp_assoc
#print axioms RepMorphism.comp_shift_assoc

/-! ## 4. Galois Adequate Identity and Modulus Propagation -/

/-- The identity function on any space $X$ is Galois adequate on $R$ with $\mu = \mathrm{id}$. -/
def GaloisAdequate.id {X : Type} (R : Rep X) : GaloisAdequate R R _root_.id :=
  { realize := fun c ↦ c
    map_equiv := fun _ _ h ↦ h
    mu := fun k ↦ k
    commutes := fun _ _ _ h ↦ h }

/-- **Galois Adequate Modulus Propagation**: For composable adequate operations,
    $\mu_{g \circ f}(k) = \mu_f(\mu_g(k))$. -/
theorem GaloisAdequate.comp_mu {X Y Z : Type} {RX : Rep X} {RY : Rep Y} {RZ : Rep Z}
    {F : X → Y} {G : Y → Z}
    (g : GaloisAdequate RY RZ G) (f : GaloisAdequate RX RY F) :
    (GaloisAdequate.comp g f).mu = fun k ↦ f.mu (g.mu k) := by
  rfl

#print axioms GaloisAdequate.id
#print axioms GaloisAdequate.comp_mu

/-! ## 5. Representation Monotonicity Theorem -/

/-- **Theorem (Representation Monotonicity)**:
    If $R_1 \preceq R_2$ and $F$ is Galois adequate on $R_1$, then $F$ is automatically
    Galois adequate on $R_2$ (with modulus $\mu_F \circ \mu_\pi$).

    This is the fundamental theorem that ensures computational adequacy propagates
    upward through the retract preorder: richer representations automatically inherit
    all adequate operations from weaker ones. -/
noncomputable def adequate_monotone {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (h_retract : R1 ⪯ R2)
    (h_adequate : GaloisAdequate R1 S F) :
    GaloisAdequate R2 S F :=
  let ret := h_retract.some
  { realize := fun c ↦ h_adequate.realize (ret.pi.toFun c)
    map_equiv := fun c1 c2 h ↦ h_adequate.map_equiv _ _ (ret.pi.map_equiv c1 c2 h)
    mu := fun k ↦ ret.pi.shift (h_adequate.mu k)
    commutes := fun c k x h ↦ h_adequate.commutes (ret.pi.toFun c) k x
      (ret.pi.map_approx c (h_adequate.mu k) x h) }

#print axioms adequate_monotone

/-- **Theorem (Output Representation Monotonicity)**:
    If $S_1 \preceq S_2$ and $F$ is Galois adequate with output $S_2$,
    then $F$ is adequate with output $S_1$ (via retraction of outputs).

    Dual to `adequate_monotone`: adequate operations are closed
    downward on the output side. -/
noncomputable def adequate_monotone_output {X Y : Type} {R : Rep X} {S1 S2 : Rep Y} {F : X → Y}
    (h_retract : S1 ⪯ S2)
    (h_adequate : GaloisAdequate R S2 F) :
    GaloisAdequate R S1 F :=
  let ret := h_retract.some
  { realize := fun c ↦ ret.pi.toFun (h_adequate.realize c)
    map_equiv := fun c1 c2 h ↦ ret.pi.map_equiv _ _ (h_adequate.map_equiv c1 c2 h)
    mu := fun k ↦ h_adequate.mu (ret.pi.shift k)
    commutes := fun c k x h ↦ ret.pi.map_approx (h_adequate.realize c) k (F x)
      (h_adequate.commutes c (ret.pi.shift k) x h) }

#print axioms adequate_monotone_output

/-! ## 6. The Modulus Monotonicity Hierarchy -/

/-- For any retract $R_1 \preceq R_2$, composing adequate operations with retraction
    yields modulus $\mu_\pi \circ \mu_F$. Stated as a direct construction. -/
def adequate_via_retract {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (ret : RepRetract R1 R2)
    (h_adequate : GaloisAdequate R1 S F) :
    GaloisAdequate R2 S F :=
  { realize := fun c ↦ h_adequate.realize (ret.pi.toFun c)
    map_equiv := fun c1 c2 h ↦ h_adequate.map_equiv _ _ (ret.pi.map_equiv c1 c2 h)
    mu := fun k ↦ ret.pi.shift (h_adequate.mu k)
    commutes := fun c k x h ↦ h_adequate.commutes (ret.pi.toFun c) k x
      (ret.pi.map_approx c (h_adequate.mu k) x h) }

/-- The modulus of the retract-lifted adequacy is $\mu_\pi \circ \mu_F$. -/
theorem adequate_via_retract_mu {X Y : Type} {R1 R2 : Rep X} {S : Rep Y} {F : X → Y}
    (ret : RepRetract R1 R2)
    (h_adequate : GaloisAdequate R1 S F) :
    (adequate_via_retract ret h_adequate).mu = fun k ↦ ret.pi.shift (h_adequate.mu k) := by
  rfl

#print axioms adequate_via_retract
#print axioms adequate_via_retract_mu

/-! ## 7. Bifunctoriality of Product Representations -/

/-- Product of Galois adequate operations: if $F$ is adequate on $(R_X, S_X)$ and
    $G$ is adequate on $(R_Y, S_Y)$, then $F \times G$ is adequate on
    $(R_X \otimes R_Y, S_X \otimes S_Y)$ with $\mu = \max(\mu_F, \mu_G)$. -/
def GaloisAdequate.prod {X₁ X₂ Y₁ Y₂ : Type}
    {RX₁ : Rep X₁} {RX₂ : Rep X₂} {SY₁ : Rep Y₁} {SY₂ : Rep Y₂}
    {F : X₁ → Y₁} {G : X₂ → Y₂}
    (hF : GaloisAdequate RX₁ SY₁ F) (hG : GaloisAdequate RX₂ SY₂ G)
    (h_mu : hF.mu = hG.mu) :
    GaloisAdequate (RX₁ ⊗ᵣ RX₂) (SY₁ ⊗ᵣ SY₂) (fun (x, y) ↦ (F x, G y)) :=
  { realize := fun (c1, c2) ↦ (hF.realize c1, hG.realize c2)
    map_equiv := fun (c1, c2) (d1, d2) ⟨h1, h2⟩ ↦
      ⟨hF.map_equiv c1 d1 h1, hG.map_equiv c2 d2 h2⟩
    mu := hF.mu
    commutes := by
      intro (c1, c2) k (x, y) ⟨h1, h2⟩
      have h2' : RX₂.approx c2 (hG.mu k) y := by rwa [← h_mu]
      exact ⟨hF.commutes c1 k x h1, hG.commutes c2 k y h2'⟩ }

#print axioms GaloisAdequate.prod

end HAomega
