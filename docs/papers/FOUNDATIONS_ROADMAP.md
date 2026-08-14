# Roadmap: Foundations of Computational Mathematics & Galois Adequacy

**Objective**: Unify Modified Realizability in $\mathrm{HA}^\omega$ with Quantitative Representation Adequacy into a closed, compositional foundation for computational analysis.

---

## Executive Summary: The 6 Research Milestones

```
[Level 1: Logico-Computational Bridge]  ──>  Milestone 1: Central Adequacy Theorem (MR ↔ Rep) [DONE]
[Level 2: Categorical Infrastructure]   ──>  Milestone 2: Category Rep & Modulus Propagation μ_{g∘f} = μ_f ∘ μ_g
[Level 3: Poset Adjunction Theory]      ──>  Milestone 3: The Literal Galois Connection (Req ⊣ Th)
[Level 4: Compositional Algebra]        ──>  Milestone 4: Closed Function Algebra (+, -, *, /, ∘) & Resource Inference
[Level 5: Quantitative Stratification]  ──>  Milestone 5: The Smoothness Hierarchy A₀ ⊂ A₁ ⊂ A₂ ⊂ ... ⊂ A_ω
[Level 6: Abstract Spaces & Dynamics]   ──>  Milestone 6: Generic Represented Metric Spaces & Abstract Banach Engine
```

---

## Milestone 1: The Central Adequacy Theorem [COMPLETED]
* **Module**: [`HAomega/CentralAdequacy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CentralAdequacy.lean) (Commit `7a0ec22`).
* **Theorem**:
  $$\begin{CD}
  \text{HA}^\omega\text{ Natural Deduction of } \forall x:X\,\exists y:Y\,\Phi(x,y)
  @>\text{extractClosed}>> \text{Closed System T Program } t \\
  @VV\text{soundnessClosed}V @VV\text{central\_adequacy\_theorem}V \\
  \text{Mathematical Theorem } \forall x, \exists y, P(x,y)
  @>>> \text{Galois Adequate Morphism } \widetilde{t} : R_X \to R_Y
  \end{CD}$$
* **Results**:
  - `soundnessClosed`: Choice-free evaluation in the empty environment.
  - `RepOf`: Explicit-carrier representation without opaque casts.
  - `central_adequacy_theorem`: Proves that any $\mathrm{HA}^\omega$ $\forall \exists$-derivation yields a representation realizer preserving code equivalence and satisfying the quantitative error relation $P(x, y)$.
  - `central_galois_realizer`: Transforms functional derivations into `GaloisAdequate` morphisms.

---

## Milestone 2: The Category $\mathbf{Rep}$, Modulus Propagation, & Preorder Monotonicity
* **Target Module**: `HAomega/CategoryRep.lean`
* **Mathematical Core**:
  1. **Category Structure**:
     - Objects: Representations $R \in \mathbf{Rep}(X)$.
     - Morphisms $f : R_1 \to R_2$: Precision-respecting realizers with modulus shift $\mu_f : \mathbb{N} \to \mathbb{N}$.
     - Identity: $\mathrm{id}_R$ with $\mu_{\mathrm{id}}(k) = k$.
     - Composition Law: For $f : R_1 \to R_2$ and $g : R_2 \to R_3$:
       $$\mu_{g \circ f}(k) = \mu_f(\mu_g(k))$$
       Proving that precision composition is strictly associative.
  2. **Retract Preorder ($\preceq$) & Representation Degrees ($\simeq$)**:
     - $R_1 \preceq R_2$ iff $R_1$ is a computable retract of $R_2$ ($\pi \circ \iota \sim \mathrm{id}_{R_1}$).
     - Representation degree quotient: $R_1 \simeq R_2 \iff R_1 \preceq R_2 \land R_2 \preceq R_1$.
  3. **Representation Monotonicity Theorem**:
     $$R_1 \preceq R_2 \;\land\; R_1 \models \Phi \implies R_2 \models \Phi$$
     If a mathematical theorem is computationally adequate on $R_1$, it is automatically adequate on any richer representation $R_2$.

---

## Milestone 3: The Literal Galois Connection ($\operatorname{Req} \dashv \operatorname{Th}$)
* **Target Module**: `HAomega/GaloisAdjunction.lean`
* **Mathematical Core**:
  1. **The Poset of Representation Strengths**: $(\mathcal{R}, \preceq)$ quotiented by $\simeq$.
  2. **The Lattice of Theorem Theories**: $(\mathcal{P}(\mathcal{T}), \subseteq)$.
  3. **The Two Adjoint Mappings**:
     - **Theory of a Representation**:
       $$\operatorname{Th}(R) = \{ \Phi \in \mathcal{T} \mid R \models \Phi \}$$
     - **Requirement of a Theorem / Theory**:
       $$\operatorname{Req}(\Gamma) = \min_{\preceq} \{ R \in \mathcal{R} \mid \forall \Phi \in \Gamma, R \models \Phi \}$$
  4. **The Galois Adjunction Theorem**:
     $$\operatorname{Req}(\Gamma) \preceq R \iff \Gamma \subseteq \operatorname{Th}(R)$$
  5. **Closing the Question**:
     Turns "Galois Adequacy" from a naming convention into a proved Galois connection in order theory.

---

## Milestone 4: Closed Compositional Function Algebra & Resource Inference
* **Target Module**: `HAomega/FunctionAlgebra.lean`
* **Mathematical Core**:
  1. **Structural Function Combinators**:
     For represented functions $f, g \in \mathbf{Rep}(X \to \mathbb{Q})$:
     - Addition: $f + g$ with $\omega_{f+g}(k) = \max(\omega_f(k+1), \omega_g(k+1))$.
     - Subtraction: $f - g$.
     - Multiplication: $f \cdot g$ with $\omega_{f \cdot g}(k) = \max(\omega_f(k + 1 + \lceil\log_2 \|g\|\rceil), \omega_g(k + 1 + \lceil\log_2 \|f\|\rceil))$.
     - Division: $f / g$ with quantitative positivity lower bound $|g| \ge \varepsilon > 0$.
     - Composition: $g \circ f$ with $\omega_{g \circ f}(k) = \omega_f(\omega_g(k))$.
  2. **Automatic Resource Inference**:
     Expressions $e$ automatically synthesize:
     - Evaluator function
     - Modulus of uniform continuity $\omega_e$
     - Modulus of differentiability $\delta_e$
     - Extracted executable System T term.

---

## Milestone 5: The Smoothness Hierarchy ($A_0 \subset A_1 \subset A_2 \subset \dots \subset A_\omega$)
* **Target Module**: `HAomega/SmoothnessHierarchy.lean`
* **Mathematical Core**:
  1. **Indexed Smoothness Spaces $A_n$**:
     - $A_0$: Continuous function + evaluation + $\omega$.
     - $A_1$: $A_0$ + first derivative + $\delta_1$.
     - $A_n$: $C^n$ data with quantitative modulus vector $\vec{\delta} = (\delta_0, \dots, \delta_n)$.
     - $A_\omega$: Smooth function with uniform family of derivative data.
  2. **Theorem Signature Calibration**:
     - $\text{Integration}: A_n \to A_{n+1}$.
     - $\text{Differentiation}: A_{n+1} \to A_n$.
     - $\text{Taylor Remainder}: A_{n+1} \to \text{Polynomial}_n + \text{Certified Remainder}(\delta_{n+1})$.
  3. **Least Representation Strength Mapping**:
     $$\operatorname{Req}(\mathrm{EFTC1}) = A_0, \qquad \operatorname{Req}(\mathrm{EFTC2}) = A_1, \qquad \operatorname{Req}(\mathrm{Taylor}_n) = A_{n+1}$$

---

## Milestone 6: Generic Represented Metric Spaces & Abstract Banach Fixed-Point Engine
* **Target Module**: `HAomega/GenericBanach.lean`
* **Mathematical Core**:
  1. **Represented Metric Space $(X, d_X, R_X)$**:
     - Carrier $C_X$, approximation relation, and computable distance $d_X : C_X \to C_X \to \mathbf{Rep}(\mathbb{R})$.
     - Completeness certificate: Cauchy sequences in $R_X$ have computable limit points.
  2. **Abstract Banach Fixed-Point Theorem**:
     $$\text{Complete Represented Metric Space } X \;+\; \text{Contraction Modulus } \Phi(k) \implies \text{Extracted Fixed Point } x^* \in X$$
  3. **Universal Applications**:
     - **Picard–Lindelöf ODE Solver**: Derived as an instantiation on $(C[a, b], \|\cdot\|_\infty)$.
     - **Contractive Linear Systems**: $(I - A)^{-1} = \sum A^k$ for $\|A\| < 1$.
     - **Root Finding**: Contractive Newton operators.
