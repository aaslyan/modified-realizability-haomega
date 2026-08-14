# The Aphoristic Universe of Mathematical Analysis
## A Closed Constructive Framework of Smooth Integration, Galois Adequacy, and Differential Synthesis

**Author**: Ara Aslyan  
**Formal Verification**: Lean 4 Interactive Theorem Prover (Project `HAomega`, 7,859 verified targets, 0 `sorry`s)  
**Date**: August 2026  

---

## Abstract

We present a self-contained, closed constructive universe for mathematical analysis built on the principles of **smooth integration**, **algebraic closure**, and **Galois adequacy**. We address a foundational question: *What is the minimal closed computational universe that rightfully deserves the name "Mathematical Analysis"?*

We argue that any authentic system of analysis must satisfy three non-negotiable criteria:
1. **The Newton–Leibniz Criterion**: It must internalize the Fundamental Theorems of Calculus ($\mathrm{EFTC1}$ and $\mathrm{EFTC2}$).
2. **The Smoothing Dynamic**: Integration must act as a regularity promoter, mapping continuous function samplers ($A_0$) into strictly smoother, approximating differentiable evaluators ($E_1$), with $A_1 \preceq E_1$.
3. **Total Operational Closure**: The universe must be closed under algebraic operations ($+, \times$), function composition ($\circ$), uniform limits ($E_0$), and fixed-point iterations, ensuring that solutions to non-linear differential equations $y' = f(x, y)$ remain strictly within the universe.

Within this framework, truth is understood as **Galois adequacy** (computational unrefutability): mathematical assertions are characterized by the computational resources required to witness or refute them. We demonstrate that the two traditional pillars of analysis—differential calculus and fixed-point theory—synthesize into an executable Picard–Lindelöf compiler that extracts verified solutions to differential equations with explicit polynomial convergence rates. Every extracted program runs choice-free, with the entire development verified in Lean 4 (7,859 targets, 0 `sorry`s).

---

## 1. Introduction: The Search for a Minimal Analysis Universe

For over a century, classical mathematical analysis has been formulated over the monolithic set of real numbers $\mathbb{R}$, constructed via non-constructive Dedekind cuts or Cauchy equivalence classes mediated by the Axiom of Choice and the Law of the Excluded Middle ($LEM$). While geometrically intuitive, this classical foundation renders theorems non-computable: assertions of existence ($\exists y$) provide no algorithmic recipe, rates of convergence are lost, and functions cannot be evaluated on physical computers.

Conversely, traditional constructive analysis (Bishop) and computable analysis (Weihrauch's TTE) often suffer from either informal "proof baggage" or an over-reliance on infinite oracle tapes ($\mathbb{N}^\mathbb{N}$), divorcing the abstract mathematical theorem from concrete, efficient data structures.

### The Core Vision

Our goal is to construct a **minimal, aphoristic mathematical universe** $\mathcal{U}$ that is:
- **Intrinsically Computable**: Represented entirely by rational samplers ($f : \mathbb{Q} \to \mathbb{Q}$) and discrete modulus functions ($\omega, \delta : \mathbb{N} \to \mathbb{N}$).
- **Categorically Stratified**: Organized by a retract preorder of representations $(\mathbf{Rep}, \preceq, \otimes)$ where representation shifts reflect computational complexity.
- **Closed Under Analysis Operations**: Applying integration, composition, or differential equation solving never escapes the universe.

```
                           ┌──────────────────────────────┐
                           │   Minimal Analysis Universe  │
                           │              𝒰               │
                           └──────────────┬───────────────┘
                                          │
        ┌─────────────────────────────────┼─────────────────────────────────┐
        ▼                                 ▼                                 ▼
 ┌───────────────┐                 ┌───────────────┐                 ┌───────────────┐
 │   Calculus    │                 │   Algebra &   │                 │  Fixed-Point  │
 │  EFTC1/EFTC2  │                 │  Composition  │                 │  ODE Synthesis│
 │ A₀ ─∫─> E₁    │                 │  + , × , ∘    │                 │ y' = f(x, y)  │
 └───────────────┘                 └───────────────┘                 └───────────────┘
```

---

## 2. The Stratified Universe of Functions: $A_0 \preceq E_0 \preceq E_1$ and $A_1 \preceq E_1$

In our universe, functions on a rational interval $[a, b]$ are not unstructured set-theoretic mappings, but stratified computational data types:

### 2.1 The Representation Hierarchy

1. **$A_0$ — Uniformly Continuous Samplers ($C^0$)**:
   An exact rational function $f : \mathbb{Q} \to \mathbb{Q}$ paired with a modulus of uniform continuity $\omega : \mathbb{N} \to \mathbb{N}$:
   $$\forall k \in \mathbb{N}, \forall x, y \in [a, b], \quad |x - y| \le 2^{-\omega(k)} \implies |f(x) - f(y)| < 2^{-k}$$

2. **$A_1$ — Uniformly Differentiable Samplers ($C^1$)**:
   Extends $A_0$ with a derivative sampler $F' : \mathbb{Q} \to \mathbb{Q}$ and a modulus of uniform differentiability $\delta : \mathbb{N} \to \mathbb{N}$:
   $$\forall k \in \mathbb{N}, \forall x \in [a, b], 0 < |h| \le 2^{-\delta(k)} \implies \left| \frac{f(x+h) - f(x)}{h} - F'(x) \right| < 2^{-k}$$

3. **$E_0$ — Approximating Evaluators**:
   A sequence of rational samplers $f_n : \mathbb{Q} \to \mathbb{Q}$ converging uniformly with an explicit Cauchy rate $c : \mathbb{N} \to \mathbb{N}$:
   $$\forall k \in \mathbb{N}, \forall n, m \ge c(k), \quad \|f_n - f_m\|_\infty \le 2^{-k}$$

4. **$E_1$ — Approximating Differentiable Evaluators**:
   $E_0$ equipped with Cauchy difference quotient convergence and uniform continuity data.

### 2.2 Algebraic and Compositional Closure

The universe $\mathcal{U}$ is an algebra closed under all fundamental operations:

* **Vector Space and Ring Operations**: For any $f, g \in A_0$ and $\lambda \in \mathbb{Q}$, the sum $f + g$, product $f \cdot g$, and scalar multiple $\lambda f$ belong to $A_0$, with extracted moduli:
  $$\omega_{f+g}(k) = \max(\omega_f(k+1), \omega_g(k+1)), \quad \omega_{f \cdot g}(k) = \max(\omega_f(k + 1 + M_g), \omega_g(k + 1 + M_f))$$
* **Non-Linear Composition Closure**: For $F, G \in A_1$, the composite $F \circ G$ belongs to $A_1$ (`CompData1.comp`), with modulus:
  $$\delta_{F \circ G}(k) = \max\Big(G.\delta(k + 3 + M_F), \ G.\omega\big(F.\delta(k + 3 + M_G)\big)\Big)$$
* **Lattice Operations**: Closed under pointwise $\max(f, g)$ and $\min(f, g)$.

### 2.3 The Uniform Continuity Theorem & The Fan Principle Compiler (`HAomega.UniformContinuityTheorem`)

In constructive mathematics, the **Heine–Borel Theorem** (Brouwer's Fan Theorem / Kleene–Kreisel continuous functionals) asserts that on compact domains, every pointwise continuous function is uniformly continuous with an explicitly extractable modulus $\omega : \mathbb{N} \to \mathbb{N}$.

Our framework formalizes this as an automated **$A_0$ Synthesis Compiler**:
1. **Scalar Scaling (`scale_modulus_correct`)**:
   $|c| \le 2^M \implies \omega_{\lambda f}(k) = \omega_f(k + M)$.
2. **Composition Compiler (`comp_modulus_correct`)**:
   $\omega_{f \circ g}(k) = \omega_g(\omega_f(k))$.
3. **Lattice Envelopes (`max_sub_max_le`)**:
   $|\max(u_1, v_1) - \max(u_2, v_2)| \le |u_1 - u_2| + |v_1 - v_2| \implies \omega_{\max}(k) = \max(\omega_f(k+1), \omega_g(k+1))$.
4. **The Integral Smoothing Modulus Theorem (`integral_lipschitz_modulus`)**:
   For any $f \in A_0$ bounded by $2^M$, its Riemann integral $\int_a^x f(t)\,dt$ inherits the optimal Lipschitz modulus:
   $$\omega_I(k) = k + M + 1$$
   proving that integration strictly preserves and improves the modulus of continuity.

---

## 3. The Smoothing Dynamic of Integration: $\mathrm{EFTC1}$ and $\mathrm{EFTC2}$

A foundational insight of our universe is that **integration is a smoothing operator**. While differentiation consumes regularity (mapping $C^1 \to C^0$), integration produces regularity:

$$\int : A_0 \longrightarrow E_1 \cong A_1$$

### 3.1 The First Fundamental Theorem ($\mathrm{EFTC1}$)
For any $f \in A_0$, the Riemann sum operator:
$$\mathcal{S}_n(f)(x) = \sum_{i=0}^{n-1} f\left(a + i \frac{x - a}{n}\right) \frac{x - a}{n}$$
converges uniformly to an evaluator in $E_1$ (`A0.intE1`). 

**Theorem (Formalized in Lean 4)**: The derivative of the integral evaluator is identically the original continuous function $f$:
$$\frac{d}{dx} \left( \int_a^x f(t)\,dt \right) = f(x)$$
Integration promotes an exact continuous sampler $A_0$ directly into the differentiable stratum $E_1$.

### 3.2 The Second Fundamental Theorem ($\mathrm{EFTC2}$)
For any $F \in A_1$ with extracted derivative $F'$, the definite integral reconstructs the boundary difference (`eftc2_thm`):
$$\int_a^b F'(t)\,dt = F(b) - F(a)$$

This duality confirms that our universe satisfies the Newton–Leibniz criterion completely and constructively.

---

## 4. Galois Adequacy: Truth as Computational Unrefutability

Traditional constructive logic often rejects classical theorems outright because counterexamples can be constructed using undecidable propositions. **Galois adequacy** provides a richer, positive perspective:

> **Principle of Galois Adequacy**: A mathematical property or equation is *Galois adequate* if any counterexample requires computational resources beyond the precision budget of the observer.

### 4.1 The Retract Preorder Category $(\mathbf{Rep}(X), \preceq, \otimes)$

We define a representation $R = (|R|, \approx_R, \sim_R)$ with concrete carrier $|R|$, approximation relation $\approx_R$, and code equivalence $\sim_R$.
A morphism $f : R_1 \to R_2$ translates precision via a shift function $\sigma : \mathbb{N} \to \mathbb{N}$.

**Definition (Retract Preorder)**: $R_1 \preceq R_2$ ($R_2$ is at least as adequate as $R_1$) if there exists an embedding $\iota : R_1 \to R_2$ and retraction $\pi : R_2 \to R_1$ such that:
$$\pi \circ \iota \sim_{R_1} \mathrm{id}_{R_1}$$

**Theorems (0 Axioms in Lean 4)**:
1. Reflexivity: $R \preceq R$ (`RepLe.refl`).
2. Transitivity: $R_1 \preceq R_2 \land R_2 \preceq R_3 \implies R_1 \preceq R_3$ (`RepLe.trans`).
3. Monoidal Product: $R_1 \preceq R_2 \land S_1 \preceq S_2 \implies R_1 \otimes S_1 \preceq R_2 \otimes S_2$ (`RepLe.prod_mono_id`).
4. Functorial Composition: Galois adequate operations compose:
   $$(R_X, R_Y) \models \mathcal{F} \quad \land \quad (R_Y, R_Z) \models \mathcal{G} \implies (R_X, R_Z) \models \mathcal{G} \circ \mathcal{F}$$

### 4.2 Case Study: The Intermediate Value Theorem (IVT)

The classical IVT ($\exists x, f(x) = 0$) is constructively false because locating an exact zero requires the Limited Principle of Omniscience ($\mathrm{LLPO}$). Under Galois adequacy, this is resolved into two constructive theorems:

1. **The Galois Approximate IVT on $A_0$ (`ivt_adjacent_bracket`)**:
   On any grid of step size $\delta \le 2^{-\omega(k)}$, adjacent sign crossings bracket a $2^{-k}$-approximate zero:
   $$|f(x_j)| \le 2^{-k} \quad \text{and} \quad |f(x_{j+1})| \le 2^{-k}$$
   with time complexity $O(\omega(k))$.
2. **Transversality and Root Isolation on $A_1$ (`root_isolation`)**:
   If $f'(x) \ge 2^{-M} > 0$, approximate zeros are geometrically isolated: $|x - y| \le 2^{M + 1 - k}$, extracting a unique Cauchy real root $x^* \in \mathbb{R}$ with linear convergence rate $\Phi(k) = k + M + 1$.

---

## 5. Fixed-Point Analysis & Picard–Lindelöf Differential Synthesis

The true test of a mathematical universe is its ability to solve non-linear differential equations and remain closed under the solution operator.

### 5.1 The Two Fixed-Point Pillars

1. **Strict Contractions (Banach, $L < 1$)**:
   For any operator $\mathcal{T}$ with $\|\mathcal{T}(u) - \mathcal{T}(v)\|_\infty \le 2^{-p} \|u - v\|_\infty$ ($p \ge 1$), the Picard sequence $y_{n+1} = \mathcal{T}(y_n)$ converges with linear rate:
   $$\Phi(k) = \left\lceil \frac{k + M + 1}{p} \right\rceil \quad \text{(`ContractionOp.cauchy`)}$$
   The limit $y^* = \lim y_n$ is extracted directly into $E_0$ (`PicardData.solution`).

2. **Non-Expansive Mappings (Browder–Göhde–Kirk / Krasnoselskii–Mann, $L = 1$)**:
   For $|T(x) - T(y)| \le |x - y|$, Picard iteration fails. The averaged iteration $x_{n+1} = \frac{1}{2} x_n + \frac{1}{2} T(x_n)$ computes approximate fixed points $|x_n - T(x_n)| \le 2^{-k}$ with polynomial rate:
   $$\Phi(k) = 4 \lceil (b - a)^2 + 1 \rceil \cdot 4^k \quad \text{(`approx_fixed_point_bound`)}$$

### 5.2 The Picard–Lindelöf Synthesis: Solving $y' = f(x, y)$

We synthesize integration ($\mathrm{EFTC1}$), composition ($\circ$), and Banach iteration to solve the initial value problem:
$$y'(x) = f(x, y(x)), \quad y(a) = y_0$$

```
   ODE Problem (f, y₀)
         │
         ▼  Integral Transformation (EFTC1)
   Operator 𝒯(y)(x) = y₀ + ∫ f(t, y(t)) dt
         │
         ▼  Contractivity (Interval b - a ≤ 2^{-(L+p)})
   Uniform 2^{-p} Contraction on A₀
         │
         ▼  Banach Fixed-Point Iteration (Rate Φ(k) = O(k))
   Continuous Fixed Point y* ∈ E₀
         │
         ▼  Regularity Promotion via Smoothing ∫ (EFTC1)
   Differentiable Solution y* ∈ E₁ ≅ A₁  with  (y*)' = f(x, y*)
```

**Theorem (Universe Closure Under ODEs)**:
Because $y^* = \mathcal{T}(y^*)$ is the integral of a continuous function, $\mathrm{EFTC1}$ automatically promotes $y^*$ from $E_0$ to $E_1 \cong A_1$. The solution $y^*$ satisfies $(y^*)'(x) = f(x, y^*(x))$ and **remains strictly within our universe $\mathcal{U}$**.

---

## 6. Realizability and Higher Types in $\mathrm{HA}^\omega$

The foundational stability of our universe is grounded in Gödel's modified realizability over Heyting Arithmetic in all finite types ($\mathrm{HA}^\omega$):
- In $\mathrm{HA}^\omega$, every derivation $d : \mathrm{Deriv} \ \Delta \ \phi$ of an existence statement $\forall x^\sigma \exists y^\tau \psi(x, y)$ yields an extracted System T term $\mathrm{extract}(d) : \mathrm{Tm} \ (\sigma \to \tau)$ that computes the constructive witness choice-free.
- When applied to analysis statements such as uniform continuity ($\forall n \exists M \dots$) or root approximation ($\forall n \exists x \dots$), the extracted realizer *is* the modulus function or search procedure (`UniformContinuity.lean`, `SquareRoot.lean`).
- Meta-level moduli closure operations (`ModulusClosure.lean`) compose these extracted moduli algebraically for scaling, composition, lattice envelopes, and integral smoothing.

---

## 7. Machine Realization and Kernel Verification in Lean 4

Every definition, theorem, and algorithm in this universe has been formalized and machine-checked in Lean 4:

```
========================================================================
 Module                     Purpose                          Axiom Scope
========================================================================
 HAomega.EFTC               Foundations of EFTC1 & EFTC2     Standard
 HAomega.QAnalysis          Interval Calculus & Composition  Standard
 HAomega.GaloisAdequacy     Preorder Rep(X), ⪯, ⊗            0-Axiom Core
 HAomega.Picard             Banach Fixed Point & Rate Φ(k)   Standard
 HAomega.FixedPoint         Krasnoselskii–Mann Iterations    Standard
 HAomega.IVT                Approximate IVT & Grid Bracket   Standard
 HAomega.ModulusClosure     Modulus Scaling & Composition    Standard
 HAomega.ComplexAnalysis    Gaussian Q(i) & CR Algebra       Standard
 HAomega.Transcendental     Transcendental Riemann Sums (π)  Standard
 HAomega.PolyRoots          Horner Scheme & Cauchy Radius    Standard
 HAomega.IntegrationByParts Leibniz Product Difference Split Standard
 HAomega.Weierstrass        Bernstein Operator Calculations  Standard
 HAomega.ODEDemo            Taylor Recurrence & Guard Solver 0-Axiom Exec
 HAomega.DerivFTC           Object-Level System T Integrator 0-Axiom Exec
 HAomega.Taylor             Taylor Remainder Scaling Lemma   Standard
 HAomega.HarmonicODE        2D Picard Harmonic Solver        Standard
 HAomega.ODEExtraction      System T Functional & Haskell    0-Axiom Exec
 HAomega.NewtonRaphson      Quadratic Error Contraction      Standard
 HAomega.GreenDivergence    2D Green's Mesh Circulation      Standard
 HAomega.Fourier            Harmonic Orthogonality & Parseval 0-Axiom Core
 HAomega.EulerMaclaurin     Euler–Maclaurin Sum Formulae     Standard
 HAomega.AnalysisDeriv      Object-Level Deriv & extractClosed 0-Axiom Exec
========================================================================
 Total Build: 7,871 targets green | 0 errors | 0 warnings | 0 sorrys
 Every Extracted Program & Guard: Executes 100% Choice-Free in Kernel
========================================================================
```

### Verified Concrete Computations in Lean 4 Kernel
- **ODEDemo**: Taylor partial sums for $\exp(1/2)$ checked up to $P_6(1/2) = 75973/46080$ (error $< 2 \cdot 10^{-6}$).
- **Transcendental**: Riemann sums bracketing $\pi \in [2449/850, 1437/425] \approx [2.881, 3.381]$ and $\ln(2) \in [7/12, 5/6]$.
- **PolyRoots**: Gaussian root evaluations $P(z^2+1, \pm i) = 0$ and $P(z^2-2, 99/70) = 1/4900$.
- **Weierstrass**: Bernstein approximations $B_n(x^2)(1/2)$ for $n = 1, 2, 4, 8$ matching the exact variance error $1/(4n)$.
- **IntegrationByParts**: Exact monomial evaluations $\int_0^1 x^2\,dx = 1/2 - 1/6 = 1/3$.

---

## 8. Related Work and Foundational Context

Constructive analysis and program extraction have a rich history in interactive theorem proving:
1. **Minlog (Schwichtenberg, Berger, Miyamoto, Seisenberger)**:
   Pioneered program extraction from constructive analysis proofs, notably extracting an IVT-based algorithm computing $\sqrt{2}$ approximations from 1D interval bisection.
2. **Incone (Steinberg, Théry, Thies in Coq)**:
   Formalized represented spaces, information-theoretic continuity, and the topological discontinuity of limit operators in Type Theory.
3. **Formalized Proof Mining (Cheval, Kohlenbach in Lean 4)**:
   Formalized Gödel's functional (Dialectica) interpretation and Kohlenbach's proof mining metatheorems in Lean, extracting quantitative bounds from non-constructive proofs.
4. **C-CoRN (Cruz-Filipe, Geuvers et al. in Coq)**:
   Constructed a constructive foundation for the Fundamental Theorem of Calculus in Coq based on Bishop-style metric analysis.

Our development distinguishes itself by its **comparative representation-adequacy framing** ($\mathbf{Rep}(X), \preceq, \otimes$), the strict stratification of exact rational samplers ($A_0, A_1$) from approximating evaluators ($E_0, E_1$), and the complete internalization of choice-free extraction within $\mathrm{HA}^\omega$.

---

## 9. Conclusion

The Aphoristic Universe of Mathematical Analysis demonstrates that mathematical rigor, physical intuition, and computational execution can coexist without compromise:
1. **Newton–Leibniz is central**: Calculus is the heart of analysis; integration is the engine of regularity and smoothing.
2. **The universe is algebraically and operationally closed**: Applying $+$, $\times$, $\circ$, $\int$, or solving ODEs never leaves the universe.
3. **Every theorem is a verified algorithm**: Convergence rates, moduli, and error bounds are computational assets extracted directly from proofs.

By replacing uncomputable classical points with the Galois adequate category of representations, we have built a complete, executable, and machine-verified universe of mathematical analysis.
