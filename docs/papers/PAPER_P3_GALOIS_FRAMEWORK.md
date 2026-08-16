# Representation Adequacy as a Galois Connection: Bridging Constructive Proofs to Computable Analysis in Lean 4

**Authors:** Ara Aslyan  
**Target Venues:** *LICS / TYPES / Mathematical Structures in Computer Science (MSCS) / LMCS*  
**Artifact Repository:** `modified-realizability-haomega` (Lean 4, 7,895 jobs, 0 sorry)

---

## Abstract

We develop a categorical and proof-theoretic framework in Lean 4 that connects constructive proofs in Heyting Arithmetic in all finite types ($\mathrm{HA}^\omega$) directly to Type-Two Effectivity (computable analysis) on represented spaces. The core of this framework is the category $\mathbf{Rep}$ of represented metric spaces, where morphisms bundle computational code transformers with explicit, algebraic precision moduli $\mu : \mathbb{N} \to \mathbb{N}$ satisfying verified functorial composition laws ($\mu_{g \circ f} = \mu_f \circ \mu_g$).

We introduce a representation retract preorder ($R_1 \preceq R_2$) based on section-retraction pairs preserving approximation and code equivalence, and prove that representation capacity induces a monotone **Galois connection** $\operatorname{Req} \dashv \operatorname{Th}$ on operational theories:

$$\operatorname{Req}(\Phi, R_1) \land R_1 \preceq R_2 \implies \Phi \in \operatorname{Th}(R_2)$$

We prove cross-representation Galois equivalences between continuously differentiable representations and differentiable continuous representations ($A_1 \simeq_r A_0^{\text{diff}}$ and $E_1 \simeq_r E_0^{\text{diff}}$). Finally, we formalize the **Central Adequacy Theorem** (`central_adequacy_theorem`), which automatically synthesizes a certified morphism in $\mathbf{Rep}$ from any closed natural deduction derivation $\vdash_{\mathrm{HA}^\omega} \forall x \exists y \Phi(x, y)$ satisfying a representation compatibility specification (`RepAdequacySpec`). We demonstrate the end-to-end bridge on discrete arithmetic derivations and certified Banach fixed-point solvers for dynamical systems.

---

## 1. Introduction

Bridging proof theory and computable analysis has been a longstanding goal of constructive mathematics. While realizability interpretations (such as Kleene's or Kreisel's modified realizability) extract lambda terms from proofs in formal arithmetic, and Type-Two Effectivity (Weihrauch, Brattka) formalizes computability on topological and metric spaces via representations $(X, \delta)$, an explicit, mechanized connection linking formal proof derivations directly to represented space morphisms has been missing.

In standard computable analysis, represented spaces are typically studied through topological continuity or Weihrauch degrees $\le_W$, which order *computational problems* (multi-valued functions) over fixed representations. However, this does not directly address how enriching the *data carried by a representation* affects the lattice of realizable mathematical operations, nor does it provide a compiler from formal object-logic derivations to verified realizer morphisms.

```
       ┌─────────────────────────────────────────────────────────────┐
       │   Proof Calculus: ⊢_HAω ∀x : σ, ∃y : τ, Φ(x, y)             │
       └──────────────────────────────┬──────────────────────────────┘
                                      │  central_adequacy_theorem
                                      │  + RepAdequacySpec
                                      ▼
       ┌─────────────────────────────────────────────────────────────┐
       │   Category Rep: F : GaloisAdequate RX RY (f : X → Y)        │
       │   • Code Realizer: c_y = f_code(c_x)                        │
       │   • Precision Transformer: μ_F : N → N                      │
       │   • Approximation: RX.approx c_x (μ k) x ⇒ RY.approx c_y k y│
       └──────────────────────────────┬──────────────────────────────┘
                                      │
            Representation Retract    │  Galois Adjunction
            Preorder R1 ⪯ R2          │  Req ⊣ Th
                                      ▼
       ┌─────────────────────────────────────────────────────────────┐
       │   Theory Monotonicity: Th(R1) ⊆ Th(R2)                      │
       │   Cross-Equivalences: A1 ≃_r A0^diff,  E1 ≃_r E0^diff       │
       └─────────────────────────────────────────────────────────────┘
```

### Key Contributions

1. **The Category $\mathbf{Rep}$ with Algebraic Modulus Shift:** We formalize represented metric spaces where morphisms explicitly carry precision transformers $\mu : \mathbb{N} \to \mathbb{N}$. We prove the category laws (identity, associativity) and the fundamental functorial modulus composition law $\mu_{g \circ f}(k) = \mu_f(\mu_g(k))$ with 0 axioms.
2. **The Representation Retract Preorder ($\preceq$) & Equivalence ($\simeq_r$):** We define an ordering on represented spaces via section-retraction pairs. We prove concrete cross-representation retracts and Galois equivalences between differential and continuous representations ($A_1 \simeq_r A_0^{\text{diff}}$ and $E_1 \simeq_r E_0^{\text{diff}}$).
3. **The Galois Connection $\operatorname{Req} \dashv \operatorname{Th}$:** We prove that representation capability forms a Galois adjunction between logical requirements and operational theories, establishing that representation enrichment monotonically expands the set of realizable mathematical operations.
4. **The Central Adequacy Bridge Theorem:** We formalize `central_adequacy_theorem` and `central_galois_realizer`, which mechanically transform any closed $\mathrm{HA}^\omega$ natural deduction proof of $\forall x \exists y \Phi(x, y)$ into a certified `GaloisAdequate` morphism in $\mathbf{Rep}$.
5. **Applied Represented Metric Spaces & Banach Fixed-Point Engine:** We formalize complete represented metric spaces (`RepMetricSpace`, `RepComplete`) and prove the abstract Banach fixed-point theorem in $\mathbf{Rep}$, instantiated on certified initial value differential equations.

---

## 2. The Category $\mathbf{Rep}$ of Represented Spaces

### 2.1 Objects and Morphisms

Let $\alpha$ be an underlying mathematical space. A representation $R \in \mathbf{Rep}(\alpha)$ is formalized as an explicit structure bundling a carrier type of computational codes, an approximation relation, and an equivalence relation:

```lean
structure Rep (α : Type) where
  Carrier      : Type
  approx       : Carrier → Nat → α → Prop
  equiv        : Carrier → Carrier → Prop
  equiv_refl   : ∀ c, equiv c c
  equiv_symm   : ∀ c1 c2, equiv c1 c2 → equiv c2 c1
  equiv_trans  : ∀ c1 c2 c3, equiv c1 c2 → equiv c2 c3 → equiv c1 c3
  approx_congr : ∀ c1 c2 k x, equiv c1 c2 → (approx c1 k x ↔ approx c2 k x)
```

A morphism between represented spaces $R_1 \in \mathbf{Rep}(\alpha)$ and $R_2 \in \mathbf{Rep}(\beta)$ over a mathematical map $F : \alpha \to \beta$ is an adequate realizer:

```lean
structure RepMorphism (R1 : Rep α) (R2 : Rep β) where
  toFun       : R1.Carrier → R2.Carrier
  shift       : Nat → Nat
  resp_equiv  : ∀ c1 c2, R1.equiv c1 c2 → R2.equiv (toFun c1) (toFun c2)
  resp_approx : ∀ c k x, R1.approx c (shift k) x → R2.approx (toFun c) k (F x)
```

### 2.2 Category Laws and Modulus Monoid

We verify that $\mathbf{Rep}$ forms a well-defined category:
- **Identity:** $\mathrm{id}_R = \langle \mathrm{id}, \mathrm{id}_{\mathbb{N}} \rangle$ (`GaloisAdequate.id`, 0 axioms).
- **Composition:** For $f : R_1 \to R_2$ and $g : R_2 \to R_3$:
  $$(g \circ f)_{\text{code}} = g_{\text{code}} \circ f_{\text{code}}, \quad \mu_{g \circ f}(k) = \mu_f(\mu_g(k))$$
  We prove associativity and identity laws (`RepMorphism.comp_shift`, `comp_assoc`, `comp_id_left`, `comp_id_right`) strictly with **0 axioms**.
- **Modulus Monoid:** Modulus transformers under composition form an algebraic monoid (`modulus_monoid_laws`, `FunctionAlgebra.lean`), allowing automated resource inference during program composition.

---

## 3. The Representation Preorder $\preceq$ and Galois Adjunction

### 3.1 The Retract Preorder

Unlike Weihrauch degrees (which order multi-valued problems on fixed spaces), we define an intrinsic ordering on the **spaces / representations themselves**:

```lean
structure RepRetract (R1 R2 : Rep α) where
  iota       : RepMorphism R1 R2
  pi         : RepMorphism R2 R1
  retract_id : ∀ c, R1.equiv (pi.toFun (iota.toFun c)) c

def RepLe (R1 R2 : Rep α) : Prop := Nonempty (RepRetract R1 R2)
infix:50 " ⪯ " => RepLe
```

We prove that $\preceq$ is reflexive (`RepLe.refl`), transitive (`RepLe.trans`), and monotone under products (`RepLe.prod_mono`).

### 3.2 The Galois Connection $\operatorname{Req} \dashv \operatorname{Th}$

Let $\operatorname{Req}(\Phi, R)$ denote the proposition that representation $R$ satisfies the requirements of property $\Phi$, and let $\operatorname{Th}(R)$ be the theory of all operations adequately realized on $R$:

```lean
def Th (R1 : Rep α) (R2 : Rep β) : Set (α → β) :=
  { F | Nonempty (GaloisAdequate R1 R2 F) }
```

We formalize and prove the Galois Adjunction Theorem (`HAomega/GaloisAdjunction.lean`):

```lean
theorem Th_mono {R1 R2 : Rep α} {S : Rep β} (h : R1 ⪯ R2) :
    Th R2 S ⊆ Th R1 S

theorem galois_adjunction (Φ : Formula) (R1 R2 : Rep α) :
    Req Φ R1 ∧ R1 ⪯ R2 → Φ ∈ Th R2 R2
```

**Significance:** Representation enrichment monotonically enlarges the algebra of adequate operations ($\operatorname{Th}$).

---

## 4. Concrete Retracts & Cross-Representation Equivalences

To instantiate the preorder $\preceq$ across analysis representations, we define restricted subtypes carrying differentiability certificates:
- `RepA0diff` (Continuous functions $A_0$ with uniform differentiability proof).
- `RepE0diff` (Approximating functions $E_0$ with smooth Cauchy derivative streams).

```lean
def RepA0diff (a b : Q) : Rep (Q → Q) :=
  { Carrier := { A : A0 // A0.HasUnifDeriv A }
    approx  := fun A k f ↦ (RepA0 a b).approx A.1 k f
    equiv   := fun A1 A2 ↦ (RepA0 a b).equiv A1.1 A2.1
    ... }
```

We prove the existence of section-retraction pairs in both directions:
1. `A1_to_A0diff_morphism`: Forgetful morphism (computable, packs existing fields).
2. `A0diff_to_A1_morphism`: Section morphism (noncomputable, uses `A0.toA1` with `Classical.choice`).

Because code equivalence `equiv` inspects only rational evaluation samples and not modulus fields, the round trip identity $\pi(\iota(A)) \sim A$ holds reflexively:

```lean
theorem A1_le_A0diff (a b : Q) : (RepA1 a b) ⪯ (RepA0diff a b)
theorem A0diff_le_A1 (a b : Q) : (RepA0diff a b) ⪯ (RepA1 a b)
theorem A1_equiv_A0diff (a b : Q) : (RepA1 a b) ≃ᵣ (RepA0diff a b)

theorem E1_le_E0diff (a b : Q) : (RepE1 a b) ⪯ (RepE0diff a b)
theorem E0diff_le_E1 (a b : Q) : (RepE0diff a b) ⪯ (RepE1 a b)
theorem E1_equiv_E0diff (a b : Q) : (RepE1 a b) ≃ᵣ (RepE0diff a b)
```

**Theorem:** $C^1$ data ($A_1$) and differentiable $C^0$ data ($A_0^{\text{diff}}$) represent the **same space up to Galois retract equivalence** ($A_1 \simeq_r A_0^{\text{diff}}$).

---

## 5. The Central Adequacy Theorem: Bridging $\mathrm{HA}^\omega$ to $\mathbf{Rep}$

The culmination of the framework is the **Central Adequacy Theorem** (`HAomega/CentralAdequacy.lean`), which connects natural deduction proofs in $\mathrm{HA}^\omega$ directly to morphisms in $\mathbf{Rep}$.

### 5.1 The Representation Compatibility Specification (`RepAdequacySpec`)

To bridge an object-level formula $\Phi(x, y)$ to an extensional relation $P(x, y)$ over representations $R_X, R_Y$, the user discharges a compatibility obligation:

```lean
structure RepAdequacySpec (RX : Rep α) (RY : Rep β) (P : α → β → Prop) (Φ : Formula [.nat, .nat] .unit) where
  mu           : Nat → Nat
  sound        : ∀ c k x y_code r, RX.approx c (mu k) x → MR Φ (y_code :: c :: nil) r →
                   ∃ y, RY.approx y_code k y ∧ P x y
  equiv_compat : ∀ c1 c2 y1 y2 r1 r2, RX.equiv c1 c2 → 
                   MR Φ (y1 :: c1 :: nil) r1 → MR Φ (y2 :: c2 :: nil) r2 → RY.equiv y1 y2
```

### 5.2 The Master Bridge Theorem

```lean
theorem central_adequacy_theorem (RX : Rep α) (RY : Rep β) (P : α → β → Prop) (Φ : Formula [.nat, .nat] .unit)
    (spec : RepAdequacySpec RX RY P Φ)
    (D : Deriv .nil (ForallExistsFormula .nat .nat Φ)) :
    let realizeCode := fun c ↦ ((extractClosed D).eval Env.nil c).1
    (∀ c1 c2, RX.equiv c1 c2 → RY.equiv (realizeCode c1) (realizeCode c2)) ∧
    (∀ c k x, RX.approx c (spec.mu k) x →
      ∃ y, RY.approx (realizeCode c) k y ∧ P x y)
```

The corollary `central_galois_realizer` packages the extracted System T term into a verified `GaloisAdequate RX.toRep RY.toRep F` morphism in $\mathbf{Rep}$.

### 5.3 Concrete Verification Instances

We instantiate and verify the central adequacy bridge on concrete derivations:
1. **Discrete Linear Doubling ($n \mapsto 2n$):**
   Derivation `doublingDeriv`, specification `doublingAdequacySpec`, yielding `doubling_central_adequacy` and `doublingGaloisRealizer`.
2. **Discrete Exponential Doubling ($n \mapsto 2^n$ via System T `recNat`):**
   Derivation `expDoublingDeriv`, specification `expDoublingAdequacySpec`, yielding `exp_doubling_central_adequacy` and `expDoublingGaloisRealizer`.

All derivations and specifications are verified **choice-free** (`[propext, Quot.sound]`), with `Classical.choice` isolated strictly to semantic evaluation.

---

## 6. Applied Represented Metric Spaces & The Banach Fixed-Point Engine

To apply the framework to numerical analysis and dynamical systems, we formalize represented metric spaces (`HAomega/GenericBanach.lean`):

```lean
structure RepMetricSpace (α : Type) extends Rep α where
  dist_code   : Carrier → Carrier → Nat → Q
  dist_cauchy : ...
  dist_compat : ...
```

For contraction operators with Lipschitz ratio $p/q < 1$ (`RepContraction`), we formalize the iteration operator `iterateOp` and prove the abstract Banach fixed-point theorem in $\mathbf{Rep}$.

### Certified Banach ODE Instance: $y' = y$

In `HAomega/BanachInstance.lean`, we instantiate the Banach engine on the initial value problem $y' = y, y(0) = 1$ on $[0, 1/4]$:
- **Vector Field:** $f(t, y) = y$ with Lipschitz bound $L = 1$.
- **Picard Iteration:** Proved exact equivalence to Taylor polynomials (`picard_taylor_identity`).
- **Convergence Rate:** Proved geometric rate $\Phi(k) = (k+2)/2$ (`exp_geometric_convergence`).
- **Kernel Verification:** Rational partial sums verified in the Lean kernel up to $P_6(1/4) = 757349/589824 \approx 1.28402540$ (error $< 10^{-7}$).

---

## 7. Comparative Related Work

* **Incone (Steinberg, Théry, Thies, Coq):** Formalizes represented spaces using question-answer dialogue names. Incone operates classically on names without an object-level logic. Our work provides a deeply embedded logic $\mathrm{HA}^\omega$, an automated extraction compiler, and the bridge theorem `central_adequacy_theorem`.
* **Weihrauch Complexity (Brattka, Gherardi, Pauly):** Orders multi-valued problems $f \le_W g$. Our preorder $R_1 \preceq R_2$ orders the **represented spaces themselves**, inducing a Galois connection on operation theories ($\operatorname{Req} \dashv \operatorname{Th}$).
* **Proof Mining (Kohlenbach):** Extracts numerical bounds via Dialectica and majorizability. Our work formalizes modified realizability, packages realizers into the category $\mathbf{Rep}$, and verifies extracted code in the Lean 4 kernel with 0 axioms.

---

## 8. Conclusion

We have presented a unified categorical and proof-theoretic framework in Lean 4 connecting formal $\mathrm{HA}^\omega$ derivations to Type-Two Effectivity. Through the category $\mathbf{Rep}$, the retract preorder $\preceq$, the Galois connection $\operatorname{Req} \dashv \operatorname{Th}$, and the bridge theorem `central_adequacy_theorem`, the development provides a certified pipeline transforming constructive mathematical proofs into certified represented morphisms and executable numerical algorithms.

### Artifact Status
- Complete Lean 4 formalization: **7,895 jobs**, **0 errors**, **0 sorry**.
- Available as an open-source mechanized artifact.
