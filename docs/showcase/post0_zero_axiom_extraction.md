# LinkedIn / Technical Blog Showcase: Zero-Axiom Program Extraction from Constructive Proofs in Lean 4

**Hook:** What does it take to extract a working computer program from a formal mathematical proof—without assuming a single non-logical axiom?

---

In classical mathematics, proving that $\forall x, \exists y, P(x, y)$ guarantees that a solution $y$ exists, but the proof may be completely non-constructive. In constructive proof theory, the proof *is* an algorithm in disguise.

In our formalization of **Heyting Arithmetic in all finite types ($\mathrm{HA}^\omega$) in Lean 4**, we built an end-to-end extraction engine based on **Kreisel's modified realizability** that translates constructive natural deduction derivations into executable Gödel System T programs.

Here is the exact verification footprint straight from the Lean 4 compiler:

```text
#print axioms HAomega.doublingRealizer
-- info: 'HAomega.doublingRealizer' does not depend on any axioms
```

---

### The Extraction Pipeline in Action

1. **The Formal Proof (`doublingDeriv`):**
   We construct a formal object-level natural deduction proof in $\mathrm{HA}^\omega$ proving the totality of doubling:
   $$\vdash_{\mathrm{HA}^\omega} \forall x : \mathrm{nat}, \exists y : \mathrm{nat}, y = x + x$$

2. **The Extraction Functor (`extractClosed`):**
   Our automated program extraction compiler recursively translates the derivation tree into an intrinsically-typed System T lambda term:
   $$\lambda x_0.\, \langle x_0 + x_0, \star \rangle$$

3. **In-Kernel Evaluation with 0 Axioms:**
   Evaluating `(doublingRealizer.eval Env.nil) n` directly reduces in Lean's trusted kernel to $2n$ **without invoking `Classical.choice`, `propext`, or `Quot.sound`**.

---

### The Crucial Separation: Code vs. Semantic Truth

How does this relate to classical axioms?
- **The Extracted Program:** Runs with **0 axioms**. The executable artifact is purely computational.
- **The Meta-Theoretic Soundness Theorem (`soundnessClosed`):** Proves that for *any* derivation tree, the extracted realizer satisfies semantic mathematical truth across all Lean models. This meta-proof uses `Classical.choice`, as expected for model-theoretic truth, but the program itself remains entirely constructive.

---

### Beyond Arithmetic: Connecting Proofs to Computable Analysis

Using this extraction pipeline, we have constructed:
- **Certified Numerical Solvers:** Picard-Banach fixed-point iterations for differential equations ($y' = y$), verifying rational partial sums up to $P_6(1/4) = 757349/589824 \approx 1.28402540$ with error $< 10^{-7}$.
- **Symplectic Orbital Integrators:** 4th-order Stormer-Verlet integrators for 2-body Kepler planetary motion with proved angular momentum conservation.
- **Standalone Code Emission:** Direct compilation of extracted System T terms to pure, idiomatic Haskell and Scheme.

---

**Artifact Status:** Clean build across **7,895 jobs** in Lean 4 (`v4.26.0`), **0 errors**, **0 sorry**.

#Lean4 #FormalMethods #TheoremProving #ConstructiveMathematics #TypeTheory #FunctionalProgramming #ComputerScience
