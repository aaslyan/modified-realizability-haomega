# Related-Work Delta Analysis: Positioning $\mathrm{HA}^\omega$ in Constructive Analysis & Realizability

**Task:** P0.1 Pre-Drafting Gate  
**Status:** Completed & Verified  
**Scope:** Rigorous technical differentiation against the six primary related frameworks:
1. **Incone** (Steinberg, Théry, Thies — Coq)
2. **Weihrauch Degrees & Reducibility** (Brattka, Gherardi, Pauly)
3. **Proof Mining & Monotone Functional Interpretations** (Kohlenbach)
4. **Formalized Proof Mining** (Cheval — Lean 4)
5. **Minlog Program Extraction** (Schwichtenberg, Berger, Miyamoto, Seisenberger)
6. **C-CoRN Constructive Analysis** (Cruz-Filipe, Geuvers, Wiedijk, O'Connor, Spitters — Coq)

---

## 1. Executive Summary & Core Technical Thesis

This repository provides a **fully certified, deeply embedded development of Heyting Arithmetic in all finite types ($\mathrm{HA}^\omega$) in Lean 4**, encompassing an intrinsically-typed System T core, an object-level natural deduction system (`Deriv`), automated modified realizability extraction (`extractClosed`), an algebraic theory of represented metric spaces ($\mathbf{Rep}$), and an explicit bridge theorem (`central_adequacy_theorem`) relating formal logic to certified realizer programs.

The contributions of this work are calibrated along three distinct mathematical axes:
1. **The Axiom-Footprint Instrument:** Using Lean 4's kernel `#print axioms` as a quantitative measurement tool to isolate the non-constructive content of analysis theorems (e.g., measuring that converting $C^0$ modulus data $A_0$ to derivative data $A_1$ costs *exactly* `[Classical.choice]`, corresponding to Myhill's theorem).
2. **The Representation Retract Preorder ($\preceq$) & Galois Adjunction ($\operatorname{Req} \dashv \operatorname{Th}$):** Categorically structuring represented spaces via section-retraction pairs preserving approximation and code equivalence ($A_1 \simeq_r A_0^{\text{diff}}$, $E_1 \simeq_r E_0^{\text{diff}}$), and proving that representation capacity induces a monotone Galois connection on realizable operation theories.
3. **End-to-End Extraction from Deep Embedding:** Unifying object-level deduction ($\vdash_{\mathrm{HA}^\omega} \phi$) with choice-free operational extraction to executable functional code (Haskell/Scheme) and certified Banach/Picard numerical dynamical systems.

---

## 2. Itemized Technical Delta Analysis

### 2.1 Incone (Steinberg, Théry, Thies — Coq)

* **Prior Art:** Incone is a Coq library formalizing Type-Two Effectivity (computable analysis) on represented spaces using a dialogue model (question-answer names $Q \to A$). It establishes topological continuity, computability of real functions, and the non-computability/discontinuity of operations such as $\lim : \mathbb{R}^\mathbb{N} \to \mathbb{R}$.
* **Technical Delta:**
  - *Deep Embedding vs. Shallow Represented Data:* Incone formalizes represented spaces as shallow structures directly within Coq, using classical logic and ambient Coq functions to reason about names. In contrast, our work builds a **complete deep embedding of an object-level formal logic** ($\mathrm{HA}^\omega$), isolating formal deduction (`Deriv`) from meta-level verification.
  - *Automatic Realizability Extraction Functor:* Incone requires the user to manually construct realizers operating on names and prove their continuity/adequacy. Our system provides an **automated program extraction compiler** (`extractClosed : Deriv .nil Φ → Tm .nil (realizerTy Φ)`) with a verified meta-soundness theorem (`soundnessClosed`).
  - *The MR-to-$\mathbf{Rep}$ Bridge Theorem:* We formalize `central_adequacy_theorem`, which automatically maps an object-level proof $\vdash_{\mathrm{HA}^\omega} \forall x \exists y \Phi(x, y)$ plus a local representation compatibility specification (`RepAdequacySpec`) directly into a certified morphism in $\mathbf{Rep}$. Incone has no analogue of an automated logical bridge from formal proofs to represented morphisms.
  - *Quantitative Modulus Shift Algebra:* Incone studies continuity topologically; our category $\mathbf{Rep}$ explicitly tracks and algebraically composes quantitative precision transformers ($\mu_{g \circ f} = \mu_f \circ \mu_g$) forming a verified monoid.

---

### 2.2 Weihrauch Degrees & Reducibility (Brattka, Gherardi, Pauly)

* **Prior Art:** Weihrauch complexity classifies the algorithmic difficulty of multi-valued problems $f, g : \subseteq X \rightrightarrows Y$ on represented spaces via computable forward/backward oracle transformations:
  $$f \le_W g \iff \exists H, K \text{ computable s.t. } \forall G \vdash g,\; K \circ \langle \mathrm{id}, G \circ H \rangle \vdash f$$
* **Technical Delta:**
  - *Space/Representation Preorder vs. Problem Reducibility:* Weihrauch reducibility $\le_W$ is an ordering on *computational problems / multi-valued functions* over fixed representations. In contrast, our retract relation $R_1 \preceq R_2$ is an ordering on the **represented spaces / representations themselves**, defined by section-retraction pairs $(\iota, \ pi)$ satisfying $\pi(\iota(c)) \sim c$ while respecting approximation and code equivalence.
  - *Galois Adjunction on Operational Theories:* We prove that the retract preorder $\preceq$ generates a monotone Galois connection $\operatorname{Req} \dashv \operatorname{Th}$, where $\operatorname{Th}(R)$ is the complete algebra of adequate operations on $R$, establishing that representation expansion monotonically enlarges the realizable operational theory ($R_1 \preceq R_2 \implies \operatorname{Th}(R_1) \subseteq \operatorname{Th}(R_2)$).
  - *Constructive Cross-Representation Equivalences:* We prove concrete non-trivial retracts between differential and continuous representations ($A_1 \preceq A_0^{\text{diff}}$ and $A_0^{\text{diff}} \preceq A_1$, yielding $A_1 \simeq_r A_0^{\text{diff}}$), exhibiting how computational representations with explicit derivative data are Galois-equivalent to continuous representations equipped with differentiability certificates.

---

### 2.3 Proof Mining & Applied Proof Theory (Kohlenbach)

* **Prior Art:** Kohlenbach's proof mining program uses proof interpretations (monotone Dialectica, negative translation, majorizability) to extract effective moduli (e.g., rates of asymptotic regularity, moduli of uniqueness) from non-constructive mathematical proofs in functional analysis and convex optimization.
* **Technical Delta:**
  - *Modified Realizability vs. Monotone Functional Interpretation:* Proof mining primarily utilizes Dialectica-style interpretations designed to eliminate classical principles ($\mathrm{WKL}$, comprehension, $\mathrm{AC}$) via majorization and functional counter-witnesses. Our development formalizes **Kreisel's modified realizability ($\mathrm{mr}$)** for pure constructive $\mathrm{HA}^\omega$, where extracted programs directly compute the constructive witnesses of $\forall\exists$-theorems without majorant over-approximations.
  - *Extensional Representation Category $\mathbf{Rep}$:* Proof mining outputs raw functional bounds in System T. We organize these terms into an **extensional category of represented spaces** $\mathbf{Rep}$, where morphisms bundle the executable code transformer with verified modulus bounds $\mu : \mathbb{N} \to \mathbb{N}$ that preserve equivalence relations.
  - *Axiom-Budget Instrument via the Lean Kernel:* Rather than eliminating non-constructive steps through metatheoretic translation, our framework uses `#print axioms` to measure and pinpoint the precise classical dependencies of mathematical theorems (such as separating choice-free numerical iteration from choice-dependent modulus conversion).

---

### 2.4 Formalized Proof Mining in Lean 4 (`hcheval/formalized-proof-mining`, Cheval)

* **Prior Art:** Horațiu Cheval formalized Gödel's Dialectica interpretation, Howard-style majorizability, and Kohlenbach metatheorems directly in Lean 4.
* **Technical Delta:**
  - *Interpretation Target & Design Focus:* Cheval's library focuses on the meta-theory of the Dialectica interpretation $\phi \mapsto \exists x \forall y \phi_D(x, y)$ and logical majorization. Our library formalizes **modified realizability** ($x\ \mathbf{mr}\ \phi$), generating lean, direct computational terms from constructive natural deduction proofs with zero axiom overhead.
  - *Full Numerical Analysis & Execution Pipeline:* Cheval's formalization stops at the logical translation level. Our repository spans the full vertical stack: formal logic $\to$ soundness $\to$ program extractor $\to$ emission compiler (Haskell/Scheme) $\to$ represented metric analysis ($A_0, A_1, E_0, E_1$) $\to$ executable numerical dynamical systems (Banach-Picard solvers, symplectic Kepler integrator, Van der Pol oscillator).
  - *Integrated Category of Representations:* We provide the category $\mathbf{Rep}$, the Galois connection $\operatorname{Req} \dashv \operatorname{Th}$, and the bridge theorem `central_adequacy_theorem`, none of which are present in `formalized-proof-mining`.

---

### 2.5 Minlog (Schwichtenberg, Berger, Miyamoto, Seisenberger)

* **Prior Art:** Minlog is an interactive proof system based on first-order minimal logic and higher-type arithmetic, designed for program extraction from constructive and classical proofs (e.g., extracted $\sqrt{2}$ via the Intermediate Value Theorem, exact real computation using signed digit streams).
* **Technical Delta:**
  - *Kernel-Verified Deep Formalization vs. External Meta-Program:* In Minlog, proof checking and extraction are implemented in an unverified external Scheme/Lisp codebase. In our work, the entire pipeline—syntax, type system, natural deduction calculus `Deriv`, extraction `extractClosed`, soundness `soundnessClosed`, and adequacy `central_adequacy_theorem`—is **deeply embedded and fully verified inside the Lean 4 kernel**.
  - *Categorical Modulus Propagation:* Minlog extracts raw lambda calculus terms without an internal algebraic theory of represented spaces or modulus composition. Our category $\mathbf{Rep}$ formalizes verified precision transformers and proves functorial composition laws.
  - *Mathematical Calibration of Representations:* Minlog does not formalize a retract preorder on representation spaces ($\preceq$) or investigate the formal axiom boundary between continuous representations ($A_0$) and continuously differentiable representations ($A_1$).

---

### 2.6 C-CoRN (Cruz-Filipe, Geuvers, Wiedijk, O'Connor, Spitters — Coq)

* **Prior Art:** C-CoRN (Constructive Coq Repository at Nijmegen) is an extensive formalization of Bishop-style constructive mathematics in Coq, including constructive real analysis, metric spaces, differentiation, and the Fundamental Theorem of Calculus (FTC).
* **Technical Delta:**
  - *Deep Embedding with Realizability vs. Shallow Type-Theoretic Formalization:* C-CoRN formalizes constructive analysis shallowly as inductive definitions and terms within Coq's ambient type theory (CIC). Our work formalizes an **explicit object-level logic $\mathrm{HA}^\omega$** with a certified realizability semantics, allowing rigorous proof-theoretic extraction and separation from the meta-logic.
  - *Axiom-Footprint Calibration of EFTC1 vs. EFTC2:* C-CoRN works uniformly in constructive analysis by requiring constructive hypotheses (e.g., uniform continuity/moduli) everywhere. In our framework, we **calibrate the exact foundational cost**:
    - $\text{EFTC1}$ (integrating a differentiable function $f'$) is proved constructively in $A_1$.
    - $\text{EFTC2}$ on $A_0$ is proved to require `[Classical.choice]` *precisely* because bridging $A_0 \to A_1$ requires Myhill's theorem (`A0.toA1`), as certified by `#print axioms`.
  - *Extracted Verified Programs:* C-CoRN focuses on proving mathematical theorems; our development compiles constructive proofs directly into certified executable code with verified quantitative convergence rates (e.g. Picard-Banach ODE iterations).

---

## 3. Comparative Summary Matrix

| Dimension | Incone (Coq) | Weihrauch Degrees | Kohlenbach / Cheval | Minlog | C-CoRN (Coq) | **This Work ($\mathrm{HA}^\omega$)** |
|---|---|---|---|---|---|---|
| **Embedding** | Shallow in Coq | Mathematical theory | Deep Dialectica (Cheval) | Standalone system | Shallow in Coq | **Deep $\mathrm{HA}^\omega$ in Lean 4** |
| **Logic & Extraction** | Classical on names | Non-proof-theoretic | Dialectica / Majorants | Minimal logic / Scheme | Constructive CIC | **Modified Realizability ($\mathrm{mr}$)** |
| **Represented Spaces** | Dialogue ($Q \to A$) | Standard $(X, \delta)$ | None | Signed digit streams | Metric spaces | **Category $\mathbf{Rep}$ + Retract $\preceq$** |
| **Order Structure** | Topology / Continuity | Problem reducibility $\le_W$ | None | None | Algebraic subtyping | **Space Retract $R_1 \preceq R_2$** |
| **Galois Connection** | None | None | None | None | None | **$\operatorname{Req} \dashv \operatorname{Th}$ formalized** |
| **Logical Bridge** | Manual realizers | None | Metatheorems | Meta-extraction | None | **`central_adequacy_theorem`** |
| **Axiom Calibration** | Coq standard | None | Proof mining bounds | None | Pure constructive | **Kernel `#print axioms` instrument** |
| **Verified Instances** | Exact real arithmetic | Benchmark problems | Optimization bounds | $\sqrt{2}$ from IVT | Bishop FTC | **$A_1 \simeq_r A_0^{\text{diff}}$, Picard-Banach, Kepler** |

---

## 4. Strategic Recommendations for Paper Drafting

1. **For Paper P1 (*Calibrating the Fundamental Theorems*):**
   - Position the paper around the **axiom-footprint instrument**: how `#print axioms` provides a quantitative calibration of constructive theorems, with the flagship result being the exact measurement that $A_0 \to A_1$ (Myhill's theorem) costs `[Classical.choice]`.
   - Frame the contrast clearly against C-CoRN (which avoids non-constructive principles uniformly) and Minlog (which lacks kernel-level axiom auditing).

2. **For Paper P2 (*A Modified-Realizability Development for $\mathrm{HA}^\omega$ in Lean 4*):**
   - Position as the foundational mechanization paper: intrinsically typed System T, natural deduction calculus `Deriv`, automated extraction `extractClosed`, verified soundness `soundnessClosed`, and the zero-axiom budget regime (`doublingRealizer` verified with 0 axioms).
   - Differentiate from `hcheval/formalized-proof-mining` by contrasting modified realizability with Dialectica, and highlighting the full compiler pipeline to Haskell/Scheme.

3. **For Paper P3 (*Representation Adequacy as a Galois Connection*):**
   - Position around the categorical theory of $\mathbf{Rep}$, the retract order $\preceq$, the Galois connection $\operatorname{Req} \dashv \operatorname{Th}$, and the bridge theorem `central_adequacy_theorem`.
   - Contrast directly with Incone (dialogue spaces vs. certified MR bridge) and Weihrauch degrees (problem reducibility vs. space retract preorder).
