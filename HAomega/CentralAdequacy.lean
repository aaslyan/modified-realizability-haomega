/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Soundness
import HAomega.GaloisAdequacy

/-!
# Milestone 1: The Central Adequacy Theorem (MR-to-Rep Bridge)

This module formalizes the fundamental bridge between **Modified Realizability in $\mathrm{HA}^\omega$**
and the **Category of Computational Representations $\mathbf{Rep}$**:

$$\begin{CD}
\text{HA}^\omega\text{ Derivation of } \forall x:X\,\exists y:Y\,\Phi(x,y)
@>\text{extractClosed}>> \text{Closed System T Program } t \\
@VV\text{soundness}V @VV\text{Central Adequacy Theorem}V \\
\text{Constructive Theorem } \forall x, \exists y, P(x,y)
@>>> \text{Galois Adequate Morphism } \widetilde{t} : R_X \to R_Y
\end{CD}$$

1. **Explicit-Carrier Representation (`RepOf`)**:
   A representation where the computational carrier is fixed definitionally to a System T type `σ.interp`.

2. **Representation-Logical Compatibility (`RepAdequacySpec`)**:
   Specifies when a formula $\Phi(x, y)$ in $\mathrm{HA}^\omega$ faithfully models a mathematical relation
   $P(x, y)$ over represented spaces $(X, R_X)$ and $(Y, R_Y)$.

3. **The Central Adequacy Theorem (`central_adequacy_theorem`)**:
   Proves that any closed $\mathrm{HA}^\omega$ derivation of a $\forall \exists$-theorem produces
   a certified representation-level realizer with an explicit modulus translation $\mu$.

4. **Deriving GaloisAdequate Realizers from Proofs (`central_galois_realizer`)**:
   Packages the extracted program as an operational morphism in $\mathbf{Rep}$.
-/

namespace HAomega

open Rat

/-- Soundness of closed derivations in empty environment. -/
theorem soundnessClosed {a : Ty} {φ : Formula [] a} (D : Deriv .nil φ) :
    MR φ Env.nil ((extractClosed D).eval Env.nil) :=
  soundness D Env.nil Env.nil (fun _ v ↦ by cases v)

/-! ## 1. Explicit-Carrier Representations -/

/-- A representation of mathematical space $X$ over a fixed carrier type $C$. -/
structure RepOf (X : Type) (C : Type) where
  approx : C → Nat → X → Prop
  equiv : C → C → Prop
  equiv_refl : ∀ c, equiv c c
  equiv_symm : ∀ c1 c2, equiv c1 c2 → equiv c2 c1
  equiv_trans : ∀ c1 c2 c3, equiv c1 c2 → equiv c2 c3 → equiv c1 c3
  approx_congr : ∀ c1 c2 k x, equiv c1 c2 → (approx c1 k x ↔ approx c2 k x)

/-- Canonical embedding of `RepOf` into `Rep`. -/
def RepOf.toRep {X : Type} {C : Type} (R : RepOf X C) : Rep X :=
  { Carrier := C
    approx := R.approx
    equiv := R.equiv
    equiv_refl := R.equiv_refl
    equiv_symm := R.equiv_symm
    equiv_trans := R.equiv_trans
    approx_congr := R.approx_congr }

/-- Convert any `Rep X` to `RepOf X R.Carrier`. -/
def Rep.toRepOf {X : Type} (R : Rep X) : RepOf X R.Carrier :=
  { approx := R.approx
    equiv := R.equiv
    equiv_refl := R.equiv_refl
    equiv_symm := R.equiv_symm
    equiv_trans := R.equiv_trans
    approx_congr := R.approx_congr }

/-! ## 2. Representation-Logical Compatibility Specification -/

/-- Compatibility specification between an object-level formula $\Phi$ and an ambient mathematical relation $P$:
    - The carrier of $R_X$ is $\sigma.\text{interp}$.
    - The carrier of $R_Y$ is $\tau.\text{interp}$.
    - An explicit resource/modulus shift $\mu : \mathbb{N} \to \mathbb{N}$ translates output precision $k$ to input precision $\mu(k)$. -/
structure RepAdequacySpec {X Y : Type} {σ τ a : Ty}
    (RX : RepOf X σ.interp) (RY : RepOf Y τ.interp)
    (P : X → Y → Prop)
    (Φ : Formula [τ, σ] a) where
  /-- Resource translation / precision modulus. -/
  mu : Nat → Nat
  /-- Semantic soundness: realization of $\Phi$ on codes implies the mathematical relation $P$ on represented points. -/
  sound : ∀ (c : σ.interp) (k : Nat) (x : X) (y_code : τ.interp) (r : a.interp),
    RX.approx c (mu k) x →
    MR Φ (Env.cons y_code (Env.cons c Env.nil)) r →
    ∃ y : Y, RY.approx y_code k y ∧ P x y
  /-- Code equivalence compatibility. -/
  equiv_compat : ∀ (c1 c2 : σ.interp) (y1 y2 : τ.interp) (r1 r2 : a.interp),
    RX.equiv c1 c2 →
    MR Φ (Env.cons y1 (Env.cons c1 Env.nil)) r1 →
    MR Φ (Env.cons y2 (Env.cons c2 Env.nil)) r2 →
    RY.equiv y1 y2

/-! ## 3. The Central Adequacy Theorem -/

/-- Closed $\forall \exists$ theorem formula: $\forall x : \sigma, \; \exists y : \tau, \; \Phi(x, y)$. -/
def ForallExistsFormula (σ τ : Ty) {a : Ty} (Φ : Formula [τ, σ] a) :
    Formula [] (.arrow σ (.prod τ a)) :=
  Formula.all σ (Formula.ex τ Φ)

/-- **Theorem 1 (The Central Adequacy Theorem)**:
    Let $D$ be a closed $\mathrm{HA}^\omega$ natural deduction derivation of $\forall x : \sigma, \exists y : \tau, \Phi(x, y)$.
    Then modified realizability extraction produces a closed System T program
    $$t = \mathrm{extractClosed}(D) : \mathrm{Tm}\ []\ (\sigma \to \tau \times a)$$
    whose evaluation $f = t.\mathrm{eval}\ \mathrm{Env.nil}$ yields an effective, choice-free representation realizer
    $$\widetilde{f} : R_X.\mathrm{Carrier} \to R_Y.\mathrm{Carrier}$$
    satisfying the exact Galois adequacy commuting condition for the underlying relation $P(x, y)$. -/
theorem central_adequacy_theorem {X Y : Type} {σ τ a : Ty}
    (RX : RepOf X σ.interp) (RY : RepOf Y τ.interp)
    (P : X → Y → Prop)
    (Φ : Formula [τ, σ] a)
    (spec : RepAdequacySpec RX RY P Φ)
    (D : Deriv .nil (ForallExistsFormula σ τ Φ)) :
    -- 1. Extracted program in System T
    let t := extractClosed D
    let f := t.eval Env.nil
    -- 2. Code-level computational realization function: maps input code to output witness code
    let realizeCode : σ.interp → τ.interp := fun c ↦ (f c).1
    -- 3. The extracted code satisfies the Galois adequacy specification
    (∀ (c1 c2 : σ.interp), RX.equiv c1 c2 → RY.equiv (realizeCode c1) (realizeCode c2)) ∧
    (∀ (c : σ.interp) (k : Nat) (x : X),
      RX.approx c (spec.mu k) x →
      ∃ y : Y, RY.approx (realizeCode c) k y ∧ P x y) := by
  have hSound := soundnessClosed D
  constructor
  · intro c1 c2 hc
    have h1 : MR Φ (Env.cons ((extractClosed D).eval Env.nil c1).1 (Env.cons c1 Env.nil))
                ((extractClosed D).eval Env.nil c1).2 := hSound c1
    have h2 : MR Φ (Env.cons ((extractClosed D).eval Env.nil c2).1 (Env.cons c2 Env.nil))
                ((extractClosed D).eval Env.nil c2).2 := hSound c2
    exact spec.equiv_compat c1 c2
      ((extractClosed D).eval Env.nil c1).1
      ((extractClosed D).eval Env.nil c2).1
      ((extractClosed D).eval Env.nil c1).2
      ((extractClosed D).eval Env.nil c2).2
      hc h1 h2
  · intro c k x h_approx
    have hMR : MR Φ (Env.cons ((extractClosed D).eval Env.nil c).1 (Env.cons c Env.nil))
                 ((extractClosed D).eval Env.nil c).2 := hSound c
    exact spec.sound c k x
      ((extractClosed D).eval Env.nil c).1
      ((extractClosed D).eval Env.nil c).2
      h_approx hMR

#print axioms central_adequacy_theorem

/-! ## 4. Deriving GaloisAdequate Realizers from Proofs -/

/-- Representation-level realizer bundled as a `GaloisAdequate` operator in `Rep` for a total function $F : X \to Y$. -/
def central_galois_realizer {X Y : Type} {σ τ a : Ty}
    (RX : RepOf X σ.interp) (RY : RepOf Y τ.interp)
    (F : X → Y)
    (Φ : Formula [τ, σ] a)
    (spec : RepAdequacySpec RX RY (fun x y ↦ y = F x) Φ)
    (D : Deriv .nil (ForallExistsFormula σ τ Φ)) :
    GaloisAdequate RX.toRep RY.toRep F :=
  let thm := central_adequacy_theorem RX RY (fun x y ↦ y = F x) Φ spec D
  { realize := fun c ↦ ((extractClosed D).eval Env.nil c).1
    map_equiv := thm.1
    mu := spec.mu
    commutes := by
      intro c k x h_approx
      have ⟨y, hy_approx, hy_eq⟩ := thm.2 c k x h_approx
      rw [hy_eq] at hy_approx
      exact hy_approx }

#print axioms central_galois_realizer

end HAomega
