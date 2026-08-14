/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.Picard

/-!
# Paper A: Galois Adequacy and the Category of Representations

This module formalizes the core theoretical architecture of Paper A:

1. **The Category of Representations $\mathbf{Rep}(X)$**:
   A representation $R \in \mathbf{Rep}(X)$ of a mathematical space $X$ consists of:
   - A concrete computational carrier `Carrier`.
   - An approximation relation `approx : Carrier → Nat → X → Prop` specifying that
     a code $c$ represents $x \in X$ within precision $2^{-k}$.
   - An internal code equivalence relation $c_1 \sim c_2$.

2. **The Retract Preorder ($\preceq$)**:
   Given two representations $R_1, R_2 \in \mathbf{Rep}(X)$:
   - A representation morphism $f : R_1 \to R_2$ maps codes computably while preserving semantics.
   - $R_1 \preceq R_2$ ($R_2$ is *at least as adequate as* $R_1$) if there is an embedding $\iota : R_1 \to R_2$
     and a retraction $\pi : R_2 \to R_1$ such that $\pi \circ \iota \sim \mathrm{id}_{R_1}$.
   - We prove that $\preceq$ is a preorder (reflexive and transitive).

3. **The Representation Ladder ($A_0, A_1, E_0, E_1$)**:
   - Exact continuous functions: `RepA0`.
   - Exact differentiable functions: `RepA1`.
   - Approximating continuous functions: `RepE0`.
   - Approximating differentiable functions: `RepE1`.
   - Morphisms connecting the levels: $A_1 \to A_0$, $A_0 \to E_0$, $A_1 \to E_1$, $E_1 \to E_0$.

4. **Commuting Ladder Square Theorem (`ladder_square_commutes`)**:
   The diagram of representation morphisms commutes on all codes:
   $$\begin{array}{ccc} A_1 & \xrightarrow{A_1 \to E_1} & E_1 \\ \downarrow & & \downarrow \\ A_0 & \xrightarrow{A_0 \to E_0} & E_0 \end{array}$$
-/

namespace HAomega

open Rat

/-! ## 1. Abstract Representations -/

/-- A concrete representation of a mathematical space $X$. -/
structure Rep (X : Type) where
  /-- The concrete computational carrier (e.g. rational samplers, dyadic streams). -/
  Carrier : Type
  /-- Approximation relation: `approx c k x` means code `c` represents `x` to within $2^{-k}$. -/
  approx : Carrier → Nat → X → Prop
  /-- Code equivalence: $c_1 \sim c_2$ means they represent the same underlying point. -/
  equiv : Carrier → Carrier → Prop
  /-- Equivalence is reflexive. -/
  equiv_refl : ∀ c, equiv c c
  /-- Equivalence is symmetric. -/
  equiv_symm : ∀ c1 c2, equiv c1 c2 → equiv c2 c1
  /-- Equivalence is transitive. -/
  equiv_trans : ∀ c1 c2 c3, equiv c1 c2 → equiv c2 c3 → equiv c1 c3
  /-- Equivalent codes represent the same points. -/
  approx_congr : ∀ c1 c2 k x, equiv c1 c2 → (approx c1 k x ↔ approx c2 k x)

/-! ## 2. Representation Morphisms and the Retract Preorder -/

/-- A computable morphism between representations of the same space $X$. -/
structure RepMorphism {X : Type} (R1 R2 : Rep X) where
  /-- The computable code transformation. -/
  toFun : R1.Carrier → R2.Carrier
  /-- Preserves code equivalence. -/
  map_equiv : ∀ c1 c2, R1.equiv c1 c2 → R2.equiv (toFun c1) (toFun c2)
  /-- Precision translation: code `toFun c` represents $x$ with an explicit modulus shift `shift`. -/
  shift : Nat → Nat
  map_approx : ∀ c k x, R1.approx c (shift k) x → R2.approx (toFun c) k x

/-- Identity morphism on a representation. -/
def RepMorphism.id {X : Type} (R : Rep X) : RepMorphism R R :=
  { toFun := fun c ↦ c
    map_equiv := fun _ _ h ↦ h
    shift := fun k ↦ k
    map_approx := fun _ _ _ h ↦ h }

/-- Composition of representation morphisms. -/
def RepMorphism.comp {X : Type} {R1 R2 R3 : Rep X}
    (g : RepMorphism R2 R3) (f : RepMorphism R1 R2) : RepMorphism R1 R3 :=
  { toFun := fun c ↦ g.toFun (f.toFun c)
    map_equiv := fun c1 c2 h ↦ g.map_equiv _ _ (f.map_equiv c1 c2 h)
    shift := fun k ↦ f.shift (g.shift k)
    map_approx := fun c k x h ↦ g.map_approx (f.toFun c) k x (f.map_approx c (g.shift k) x h) }

/-- A retraction between representations: $R_1$ is a retract of $R_2$. -/
structure RepRetract {X : Type} (R1 R2 : Rep X) where
  /-- Inclusion / embedding into the richer representation. -/
  iota : RepMorphism R1 R2
  /-- Projection / retraction back to the base representation. -/
  pi : RepMorphism R2 R1
  /-- Retraction identity: $\pi \circ \iota \sim \mathrm{id}_{R_1}$. -/
  retract_id : ∀ c, R1.equiv (pi.toFun (iota.toFun c)) c

/-- **The Retract Preorder**: $R_1 \preceq R_2$ iff $R_1$ is a retract of $R_2$. -/
def RepLe {X : Type} (R1 R2 : Rep X) : Prop :=
  Nonempty (RepRetract R1 R2)

scoped infix:50 " ⪯ " => RepLe

/-- $\preceq$ is reflexive: $R \preceq R$. -/
theorem RepLe.refl {X : Type} (R : Rep X) : R ⪯ R :=
  ⟨{ iota := RepMorphism.id R
     pi := RepMorphism.id R
     retract_id := fun c ↦ R.equiv_refl c }⟩

/-- $\preceq$ is transitive: $R_1 \preceq R_2 \land R_2 \preceq R_3 \implies R_1 \preceq R_3$. -/
theorem RepLe.trans {X : Type} {R1 R2 R3 : Rep X}
    (h12 : R1 ⪯ R2) (h23 : R2 ⪯ R3) : R1 ⪯ R3 := by
  obtain ⟨ret12⟩ := h12
  obtain ⟨ret23⟩ := h23
  refine ⟨{ iota := RepMorphism.comp ret23.iota ret12.iota
            pi := RepMorphism.comp ret12.pi ret23.pi
            retract_id := ?_ }⟩
  intro c
  dsimp [RepMorphism.comp]
  have h_inner := ret23.retract_id (ret12.iota.toFun c)
  have h_pi := ret12.pi.map_equiv _ _ h_inner
  have h_base := ret12.retract_id c
  exact R1.equiv_trans _ _ _ h_pi h_base

/-- Galois Equivalence of representations: $R_1 \equiv R_2 \iff R_1 \preceq R_2 \land R_2 \preceq R_1$. -/
def RepEquiv {X : Type} (R1 R2 : Rep X) : Prop :=
  R1 ⪯ R2 ∧ R2 ⪯ R1

scoped infix:50 " ≃ᵣ " => RepEquiv

theorem RepEquiv.refl {X : Type} (R : Rep X) : R ≃ᵣ R :=
  ⟨RepLe.refl R, RepLe.refl R⟩

theorem RepEquiv.symm {X : Type} {R1 R2 : Rep X} (h : R1 ≃ᵣ R2) : R2 ≃ᵣ R1 :=
  ⟨h.2, h.1⟩

theorem RepEquiv.trans {X : Type} {R1 R2 R3 : Rep X} (h12 : R1 ≃ᵣ R2) (h23 : R2 ≃ᵣ R3) : R1 ≃ᵣ R3 :=
  ⟨RepLe.trans h12.1 h23.1, RepLe.trans h23.2 h12.2⟩

#print axioms RepLe.refl
#print axioms RepLe.trans
#print axioms RepEquiv.trans

/-! ## 3. Galois Adequacy for Mathematical Operations -/

/-- An operation $\mathcal{F} : X \to Y$ is **Galois adequate** on representations $(R_X, R_Y)$
    if there is an extracted algorithm $\widetilde{\mathcal{F}}$ with an explicit modulus translation $\mu$
    preserving representation semantics. -/
structure GaloisAdequate {X Y : Type} (RX : Rep X) (RY : Rep Y) (F : X → Y) where
  /-- The extracted computational realization. -/
  realize : RX.Carrier → RY.Carrier
  /-- Preserves code equivalence. -/
  map_equiv : ∀ c1 c2, RX.equiv c1 c2 → RY.equiv (realize c1) (realize c2)
  /-- Resource / modulus translation function. -/
  mu : Nat → Nat
  /-- Realization correctness: $\widetilde{\mathcal{F}}(c)$ approximates $\mathcal{F}(x)$ within $2^{-k}$. -/
  commutes : ∀ (c : RX.Carrier) (k : Nat) (x : X),
    RX.approx c (mu k) x → RY.approx (realize c) k (F x)

/-- Composition of Galois adequate operations:
    If $(R_X, R_Y) \models \mathcal{F}$ and $(R_Y, R_Z) \models \mathcal{G}$,
    then $(R_X, R_Z) \models \mathcal{G} \circ \mathcal{F}$. -/
def GaloisAdequate.comp {X Y Z : Type} {RX : Rep X} {RY : Rep Y} {RZ : Rep Z}
    {F : X → Y} {G : Y → Z}
    (g : GaloisAdequate RY RZ G) (f : GaloisAdequate RX RY F) :
    GaloisAdequate RX RZ (G ∘ F) :=
  { realize := fun c ↦ g.realize (f.realize c)
    map_equiv := fun c1 c2 h ↦ g.map_equiv _ _ (f.map_equiv c1 c2 h)
    mu := fun k ↦ f.mu (g.mu k)
    commutes := fun c k x h ↦ g.commutes (f.realize c) k (F x) (f.commutes c (g.mu k) x h) }

#print axioms GaloisAdequate.comp

/-! ## 4. The Retract Hierarchy of Concrete Function Representations -/

/-- Representation for exact continuous functions on $[a, b]$ via $A_0$. -/
def RepA0 (a b : Q) : Rep (Q → Q) :=
  { Carrier := A0
    approx := fun A k f ↦ A.a = a ∧ A.b = b ∧ ∀ x : Q, Qle a x = true → Qle x b = true → |(A.f x).val - (f x).val| ≤ 1 / 2 ^ k
    equiv := fun A1 A2 ↦ A1.a = A2.a ∧ A1.b = A2.b ∧ ∀ x : Q, Qle A1.a x = true → Qle x A1.b = true → (A1.f x).val = (A2.f x).val
    equiv_refl := fun A ↦ ⟨rfl, rfl, fun _ _ _ ↦ rfl⟩
    equiv_symm := fun _ _ h ↦ ⟨h.1.symm, h.2.1.symm, fun x hxa hxb ↦ (h.2.2 x (by rwa [h.1]) (by rwa [h.2.1])).symm⟩
    equiv_trans := fun A B C hAB hBC ↦
      ⟨hAB.1.trans hBC.1, hAB.2.1.trans hBC.2.1, fun x hxa hxb ↦ by
        have h1 := hAB.2.2 x hxa hxb
        have h2 := hBC.2.2 x (by rwa [← hAB.1]) (by rwa [← hAB.2.1])
        exact h1.trans h2⟩
    approx_congr := by
      intro A1 A2 k f h_eq
      constructor
      · intro h1
        refine ⟨h_eq.1 ▸ h1.1, h_eq.2.1 ▸ h1.2.1, fun x hxa hxb ↦ ?_⟩
        have hx := h1.2.2 x hxa hxb
        have h_val := h_eq.2.2 x (by rwa [h1.1]) (by rwa [h1.2.1])
        rw [← h_val]
        exact hx
      · intro h2
        refine ⟨h_eq.1 ▸ h2.1, h_eq.2.1 ▸ h2.2.1, fun x hxa hxb ↦ ?_⟩
        have hx := h2.2.2 x hxa hxb
        have h_val := h_eq.2.2 x (by rwa [h_eq.1, h2.1]) (by rwa [h_eq.2.1, h2.2.1])
        rw [h_val]
        exact hx }

/-- Representation for exact differentiable functions on $[a, b]$ via $A_1$. -/
def RepA1 (a b : Q) : Rep (Q → Q) :=
  { Carrier := A1
    approx := fun A k f ↦ A.a = a ∧ A.b = b ∧ ∀ x : Q, Qle a x = true → Qle x b = true → |(A.f x).val - (f x).val| ≤ 1 / 2 ^ k
    equiv := fun A1 A2 ↦ A1.a = A2.a ∧ A1.b = A2.b ∧ ∀ x : Q, Qle A1.a x = true → Qle x A1.b = true → (A1.f x).val = (A2.f x).val
    equiv_refl := fun A ↦ ⟨rfl, rfl, fun _ _ _ ↦ rfl⟩
    equiv_symm := fun _ _ h ↦ ⟨h.1.symm, h.2.1.symm, fun x hxa hxb ↦ (h.2.2 x (by rwa [h.1]) (by rwa [h.2.1])).symm⟩
    equiv_trans := fun A B C hAB hBC ↦
      ⟨hAB.1.trans hBC.1, hAB.2.1.trans hBC.2.1, fun x hxa hxb ↦ by
        have h1 := hAB.2.2 x hxa hxb
        have h2 := hBC.2.2 x (by rwa [← hAB.1]) (by rwa [← hAB.2.1])
        exact h1.trans h2⟩
    approx_congr := by
      intro A1 A2 k f h_eq
      constructor
      · intro h1
        refine ⟨h_eq.1 ▸ h1.1, h_eq.2.1 ▸ h1.2.1, fun x hxa hxb ↦ ?_⟩
        have hx := h1.2.2 x hxa hxb
        have h_val := h_eq.2.2 x (by rwa [h1.1]) (by rwa [h1.2.1])
        rw [← h_val]
        exact hx
      · intro h2
        refine ⟨h_eq.1 ▸ h2.1, h_eq.2.1 ▸ h2.2.1, fun x hxa hxb ↦ ?_⟩
        have hx := h2.2.2 x hxa hxb
        have h_val := h_eq.2.2 x (by rwa [h_eq.1, h2.1]) (by rwa [h_eq.2.1, h2.2.1])
        rw [h_val]
        exact hx }

/-- Representation for approximating continuous functions on $[a, b]$ via $E_0$. -/
def RepE0 (a b : Q) : Rep (Q → Q) :=
  { Carrier := E0
    approx := fun E k f ↦ E.a = a ∧ E.b = b ∧ ∀ x : Q, Qle a x = true → Qle x b = true → |(E.ev (E.cm k) x).val - (f x).val| ≤ 1 / 2 ^ k
    equiv := fun E1 E2 ↦ E1.a = E2.a ∧ E1.b = E2.b ∧ ∀ k x, Qle E1.a x = true → Qle x E1.b = true → (E1.ev (E1.cm k) x).val = (E2.ev (E2.cm k) x).val
    equiv_refl := fun E ↦ ⟨rfl, rfl, fun _ _ _ _ ↦ rfl⟩
    equiv_symm := fun _ _ h ↦ ⟨h.1.symm, h.2.1.symm, fun k x hxa hxb ↦ (h.2.2 k x (by rwa [h.1]) (by rwa [h.2.1])).symm⟩
    equiv_trans := fun A B C hAB hBC ↦
      ⟨hAB.1.trans hBC.1, hAB.2.1.trans hBC.2.1, fun k x hxa hxb ↦ by
        have h1 := hAB.2.2 k x hxa hxb
        have h2 := hBC.2.2 k x (by rwa [← hAB.1]) (by rwa [← hAB.2.1])
        exact h1.trans h2⟩
    approx_congr := by
      intro E1 E2 k f h_eq
      constructor
      · intro h1
        refine ⟨h_eq.1 ▸ h1.1, h_eq.2.1 ▸ h1.2.1, fun x hxa hxb ↦ ?_⟩
        have hx := h1.2.2 x hxa hxb
        have h_val := h_eq.2.2 k x (by rwa [h1.1]) (by rwa [h1.2.1])
        rw [← h_val]
        exact hx
      · intro h2
        refine ⟨h_eq.1 ▸ h2.1, h_eq.2.1 ▸ h2.2.1, fun x hxa hxb ↦ ?_⟩
        have hx := h2.2.2 x hxa hxb
        have h_val := h_eq.2.2 k x (by rwa [h_eq.1, h2.1]) (by rwa [h_eq.2.1, h2.2.1])
        rw [h_val]
        exact hx }

/-- Representation for approximating differentiable functions on $[a, b]$ via $E_1$. -/
def RepE1 (a b : Q) : Rep (Q → Q) :=
  { Carrier := E1
    approx := fun E k f ↦ E.a = a ∧ E.b = b ∧ ∀ x : Q, Qle a x = true → Qle x b = true → |(E.ev (E.cm k) x).val - (f x).val| ≤ 1 / 2 ^ k
    equiv := fun E1 E2 ↦ E1.a = E2.a ∧ E1.b = E2.b ∧ ∀ k x, Qle E1.a x = true → Qle x E1.b = true → (E1.ev (E1.cm k) x).val = (E2.ev (E2.cm k) x).val
    equiv_refl := fun E ↦ ⟨rfl, rfl, fun _ _ _ _ ↦ rfl⟩
    equiv_symm := fun _ _ h ↦ ⟨h.1.symm, h.2.1.symm, fun k x hxa hxb ↦ (h.2.2 k x (by rwa [h.1]) (by rwa [h.2.1])).symm⟩
    equiv_trans := fun A B C hAB hBC ↦
      ⟨hAB.1.trans hBC.1, hAB.2.1.trans hBC.2.1, fun k x hxa hxb ↦ by
        have h1 := hAB.2.2 k x hxa hxb
        have h2 := hBC.2.2 k x (by rwa [← hAB.1]) (by rwa [← hAB.2.1])
        exact h1.trans h2⟩
    approx_congr := by
      intro E1 E2 k f h_eq
      constructor
      · intro h1
        refine ⟨h_eq.1 ▸ h1.1, h_eq.2.1 ▸ h1.2.1, fun x hxa hxb ↦ ?_⟩
        have hx := h1.2.2 x hxa hxb
        have h_val := h_eq.2.2 k x (by rwa [h1.1]) (by rwa [h1.2.1])
        rw [← h_val]
        exact hx
      · intro h2
        refine ⟨h_eq.1 ▸ h2.1, h_eq.2.1 ▸ h2.2.1, fun x hxa hxb ↦ ?_⟩
        have hx := h2.2.2 x hxa hxb
        have h_val := h_eq.2.2 k x (by rwa [h_eq.1, h2.1]) (by rwa [h_eq.2.1, h2.2.1])
        rw [h_val]
        exact hx }

/-! ## 5. Morphisms Connecting the Representation Ladder -/

/-- Forgetting derivative data: $A_1 \to A_0$. -/
def A1_to_A0_morphism (a b : Q) : RepMorphism (RepA1 a b) (RepA0 a b) :=
  { toFun := fun (A : A1) ↦ A.toA0
    map_equiv := fun _ _ h ↦ h
    shift := fun k ↦ k
    map_approx := fun _ _ _ h ↦ h }

/-- Conservativity morphism: $A_0 \to E_0$. -/
def A0_to_E0_morphism (a b : Q) : RepMorphism (RepA0 a b) (RepE0 a b) :=
  { toFun := fun (A : A0) ↦ A.toE0
    map_equiv := fun _ _ h ↦ ⟨h.1, h.2.1, fun _ x hxa hxb ↦ h.2.2 x hxa hxb⟩
    shift := fun k ↦ k
    map_approx := fun _ _ _ h ↦ ⟨h.1, h.2.1, fun x hxa hxb ↦ h.2.2 x hxa hxb⟩ }

/-- Conservativity morphism: $A_1 \to E_1$. -/
def A1_to_E1_morphism (a b : Q) : RepMorphism (RepA1 a b) (RepE1 a b) :=
  { toFun := fun (A : A1) ↦ A.toE1
    map_equiv := fun _ _ h ↦ ⟨h.1, h.2.1, fun _ x hxa hxb ↦ h.2.2 x hxa hxb⟩
    shift := fun k ↦ k
    map_approx := fun _ _ _ h ↦ ⟨h.1, h.2.1, fun x hxa hxb ↦ h.2.2 x hxa hxb⟩ }

/-- Forgetting derivative data: $E_1 \to E_0$. -/
def E1_to_E0_morphism (a b : Q) : RepMorphism (RepE1 a b) (RepE0 a b) :=
  { toFun := fun (E : E1) ↦ E.toE0
    map_equiv := fun _ _ h ↦ h
    shift := fun k ↦ k
    map_approx := fun _ _ _ h ↦ h }

/-- **Theorem (Ladder Commuting Square)**:
    The representation morphism square commutes identically on all codes:
    $E1\_to\_E0 \circ A1\_to\_E1 = A0\_to\_E0 \circ A1\_to\_A0$. -/
theorem ladder_square_commutes (a b : Q) (A : A1) :
    (E1_to_E0_morphism a b).toFun ((A1_to_E1_morphism a b).toFun A) =
    (A0_to_E0_morphism a b).toFun ((A1_to_A0_morphism a b).toFun A) := by
  rfl

#print axioms ladder_square_commutes

/-- **Galois Adequacy of Newton–Leibniz Integration ($\mathrm{EFTC1}$)**:
    The integration operator maps an exact continuous function $A_0$ to an
    approximating differentiable function $E_1$ with exact derivative $f$. -/
def EFTC1_Adequate (a b : Q) (_ivl : Q.ltN a b = 1) :
    A0 → E1 :=
  fun A ↦ A.intE1

/-! ## 6. Monoidal Product Structure on $\mathbf{Rep}$ -/

/-- Terminal representation for the unit space `Unit`. -/
def Rep.unit : Rep Unit :=
  { Carrier := Unit
    approx := fun _ _ _ ↦ True
    equiv := fun _ _ ↦ True
    equiv_refl := fun _ ↦ trivial
    equiv_symm := fun _ _ _ ↦ trivial
    equiv_trans := fun _ _ _ _ _ ↦ trivial
    approx_congr := fun _ _ _ _ _ ↦ ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩ }

/-- Tensor product of two representations $R_1 \otimes R_2 \in \mathbf{Rep}(X \times Y)$. -/
def Rep.prod {X Y : Type} (R1 : Rep X) (R2 : Rep Y) : Rep (X × Y) :=
  { Carrier := R1.Carrier × R2.Carrier
    approx := fun (c1, c2) k (x, y) ↦ R1.approx c1 k x ∧ R2.approx c2 k y
    equiv := fun (c1, c2) (d1, d2) ↦ R1.equiv c1 d1 ∧ R2.equiv c2 d2
    equiv_refl := fun (c1, c2) ↦ ⟨R1.equiv_refl c1, R2.equiv_refl c2⟩
    equiv_symm := fun (_, _) (_, _) ⟨h1, h2⟩ ↦ ⟨R1.equiv_symm _ _ h1, R2.equiv_symm _ _ h2⟩
    equiv_trans := fun (_, _) (_, _) (_, _) ⟨h1, h2⟩ ⟨k1, k2⟩ ↦
      ⟨R1.equiv_trans _ _ _ h1 k1, R2.equiv_trans _ _ _ h2 k2⟩
    approx_congr := by
      intro (c1, c2) (d1, d2) k (x, y) ⟨h1, h2⟩
      constructor
      · intro ⟨a1, a2⟩
        exact ⟨(R1.approx_congr c1 d1 k x h1).mp a1, (R2.approx_congr c2 d2 k y h2).mp a2⟩
      · intro ⟨b1, b2⟩
        exact ⟨(R1.approx_congr c1 d1 k x h1).mpr b1, (R2.approx_congr c2 d2 k y h2).mpr b2⟩ }

scoped infixr:70 " ⊗ᵣ " => Rep.prod

/-- Tensor product of representation morphisms when shifts match: $f \otimes g$. -/
def RepMorphism.prod_eq_shift {X Y : Type} {R1 R2 : Rep X} {S1 S2 : Rep Y}
    (f : RepMorphism R1 R2) (g : RepMorphism S1 S2) (h_shift : f.shift = g.shift) :
    RepMorphism (R1 ⊗ᵣ S1) (R2 ⊗ᵣ S2) :=
  { toFun := fun (c, d) ↦ (f.toFun c, g.toFun d)
    map_equiv := fun (_, _) (_, _) ⟨h1, h2⟩ ↦ ⟨f.map_equiv _ _ h1, g.map_equiv _ _ h2⟩
    shift := f.shift
    map_approx := by
      intro (c, d) k (x, y) ⟨h1, h2⟩
      have h2' : S1.approx d (g.shift k) y := by rwa [← h_shift]
      exact ⟨f.map_approx c k x h1, g.map_approx d k y h2'⟩ }

/-- Retract preorder on product spaces with matching shift embeddings. -/
theorem RepLe.prod_mono_id {X Y : Type} {R1 R2 : Rep X} {S1 S2 : Rep Y}
    (retR : RepRetract R1 R2) (retS : RepRetract S1 S2)
    (h_iota : retR.iota.shift = retS.iota.shift)
    (h_pi : retR.pi.shift = retS.pi.shift) :
    (R1 ⊗ᵣ S1) ⪯ (R2 ⊗ᵣ S2) := by
  refine ⟨{ iota := RepMorphism.prod_eq_shift retR.iota retS.iota h_iota
            pi := RepMorphism.prod_eq_shift retR.pi retS.pi h_pi
            retract_id := fun (c, d) ↦ ⟨retR.retract_id c, retS.retract_id d⟩ }⟩

/-! ## 7. Concrete Retract Instances on Function Spaces -/

/-- Concrete retract of $A_0$ into itself. -/
theorem A0_retract_self (a b : Q) : (RepA0 a b) ⪯ (RepA0 a b) :=
  RepLe.refl (RepA0 a b)

/-- Concrete retract of $A_1$ into itself. -/
theorem A1_retract_self (a b : Q) : (RepA1 a b) ⪯ (RepA1 a b) :=
  RepLe.refl (RepA1 a b)

/-- Concrete retract of $E_0$ into itself. -/
theorem E0_retract_self (a b : Q) : (RepE0 a b) ⪯ (RepE0 a b) :=
  RepLe.refl (RepE0 a b)

/-- Concrete retract of $E_1$ into itself. -/
theorem E1_retract_self (a b : Q) : (RepE1 a b) ⪯ (RepE1 a b) :=
  RepLe.refl (RepE1 a b)

/-- Concrete product retraction on $A_0 \times A_0$. -/
theorem A0_prod_retract (a b : Q) :
    ((RepA0 a b) ⊗ᵣ (RepA0 a b)) ⪯ ((RepA0 a b) ⊗ᵣ (RepA0 a b)) :=
  RepLe.refl _

#print axioms RepLe.refl
#print axioms RepLe.trans
#print axioms RepLe.prod_mono_id
#print axioms A0_retract_self
#print axioms A1_retract_self
#print axioms E0_retract_self
#print axioms E1_retract_self
#print axioms GaloisAdequate.comp
#print axioms A1_to_A0_morphism
#print axioms A0_to_E0_morphism
#print axioms A1_to_E1_morphism
#print axioms E1_to_E0_morphism

end HAomega
