# Large Paper Plan: Arithmetic, Analysis, and Executable Examples

**Working title:** *From Proofs to Programs in HA^omega: Modified Realizability, Representation Adequacy, and Executable Analysis in Lean 4*

**Purpose:** one large, unified paper that can later become the spine of a book.

**Recommended venue shape:** CPP or ITP long paper first. If it grows beyond conference size, split into a conference paper plus a later journal/book version.

## 1. Core Thesis

The paper should not be a collection of demos. It should tell one story:

> A formal constructive proof in finite-type arithmetic can be treated as executable mathematical evidence. This repository formalizes the object logic, proves modified-realizability extraction sound, emits and runs extracted programs, and then uses representation data to calibrate which constructive analysis theorems have computational content.

The unifying phrase:

> Proofs produce programs; representations determine what those programs can compute.

That lets the arithmetic and analysis material live in one paper without feeling stitched together.

## 2. Main Contributions

Use exactly these contribution claims, in this order.

1. **Deep object logic.** A Lean 4 formalization of finite-type Heyting arithmetic with intrinsically typed System T terms (`Tm`), formulas, and natural-deduction derivations (`Deriv`).
2. **Certified modified-realizability extraction.** A checked extraction map `extractClosed` from object-level derivations to executable System T terms, with semantic soundness via `soundnessClosed`.
3. **Axiom-budget accounting.** A declaration-by-declaration separation between executable artifacts, semantic soundness, and analysis bridges using Lean's `#print axioms`.
4. **Arithmetic extraction suite.** A set of first-order and finite-type examples where proof structure changes extracted program behavior: Fibonacci, gcd, Pascal/Sperner, Hanoi, Goodstein, Hydra, Hercules.
5. **Representation calibration for analysis.** The `A0/A1/E0/E1` ladder showing that integration and differentiation require different data, with `A0.toA1` marking the classical-choice bridge.
6. **Galois adequacy bridge.** A category/retract framework (`Rep`, `RepLe`, `GaloisAdequate`, `central_adequacy_theorem`) connecting extracted realizers to represented computational morphisms.
7. **Executable analysis examples.** Picard iteration and dynamical-system examples as exact rational, kernel-checked computations illustrating the reach of the framework.

## 3. What the Paper Is Not

State these limits early. They make the paper stronger.

- Not a novelty claim for constructive FTC itself.
- Not a novelty claim for program extraction itself.
- Not a claim that every theorem is axiom-free.
- Not a proof of PA-independence for Goodstein/Hydra.
- Not a proof of global dynamical-system behavior such as strange attractors, global limit cycles, or basin convergence.
- Not a claim that every numerical term is extracted from `Deriv`; only say extracted where `extractClosed` is actually used.

## 4. Proposed Manuscript Structure

Target length: **18-24 pages** for a large conference/journal-style draft. Trim to 14-16 pages for CPP/ITP.

### 1. Introduction: From Existence to Computation

Length: 2 pages.

Goal: introduce the unifying problem.

Content:

- Constructive proofs of `forall x, exists y, P x y` carry programs.
- Mechanizing the extraction machinery itself is different from extracting from the host proof assistant.
- Analysis adds a second issue: the theorem may need representation data, especially moduli.
- State the thesis: proof content plus representation content.
- Contributions list.

Opening example:

- Use `doublingRecDeriv -> doublingRealizer -> doublingExtracted`.
- Keep it tiny and exact. It anchors the reader.

### 2. Object Language: HA^omega Inside Lean

Length: 2-3 pages.

Goal: explain the formal substrate without drowning the reader.

Content:

- `Ty`: finite types.
- `Tm`: intrinsically typed System T terms.
- De Bruijn variables and contexts.
- `Formula`: equality, connectives, quantifiers.
- `Deriv`: object-level natural deduction.
- Mention substitution/evaluation infrastructure only as needed.

Key message:

> The proof being extracted is an object-language proof, not merely a Lean term.

### 3. Modified Realizability and Extraction

Length: 3 pages.

Goal: present the formal proof-to-program theorem.

Content:

- `realizerTy`.
- `MR`.
- `extract`.
- `extractClosed`.
- `soundness` and `soundnessClosed`.
- Explain how connectives translate:
  - `exists` gives witness pairs.
  - `forall` gives functions.
  - implication gives function space.
  - atomic equality gives unit computational content.

Include a small extraction table:

| Formula form | Realizer shape |
|---|---|
| `A and B` | pair |
| `A -> B` | function |
| `forall x, A x` | function in `x` |
| `exists x, A x` | witness plus realizer |
| `s = t` | unit plus equality proof in `MR` |

### 4. Axiom Budgeting as a Method

Length: 2 pages.

Goal: make axiom tracking a contribution, not an apology.

Content:

- `extract` is syntactic and choice-free.
- Running extracted artifacts such as `doublingRealizer` can have no non-logical axioms.
- `soundnessClosed` uses semantic assumptions measured by Lean.
- Analysis theorems frequently depend on `[propext, Classical.choice, Quot.sound]`.
- Explain why this matters: the project can measure computational vs semantic/classical content.

Include a table:

| Artifact | Role | Footprint |
|---|---|---|
| `extract` / `extractClosed` | compiler from proofs to terms | no axioms |
| `doublingRealizer` | extracted System T program | no axioms |
| `Tm.eval` for many extracts | execution | `[propext, Quot.sound]` or no axioms depending declaration |
| `soundnessClosed` | semantic correctness | `[propext, Classical.choice, Quot.sound]` |
| `A0.toA1` | representation bridge | `[Classical.choice]` |

### 5. Arithmetic Extraction Case Studies

Length: 4-5 pages.

Goal: show the core system doing real work before moving to analysis.

Use this section to unify the first-order and HA^omega material.

Recommended examples:

1. **Fibonacci.**
   - On-ramp.
   - Shows ordinary recursive extraction.
   - Good for reader confidence.

2. **gcd.**
   - More mathematical specification.
   - Shows proof-computed witness with divisibility claims.

3. **Pascal/Sperner.**
   - Shows proof variation matters.
   - Same theorem/invariant can produce different computational behavior.

4. **Hanoi.**
   - Shows function-valued witnesses.
   - Useful bridge to finite types.

5. **Goodstein/Hydra/Hercules.**
   - Shows logical strength and representation matter.
   - Ordinary induction vs transfinite recursion.
   - Coded natural representations vs typed structural representations.

Do not overdo all examples equally. Pick 2 as main examples and summarize the rest in a table.

Suggested table:

| Example | Theorem shape | Extracted behavior | Why it matters |
|---|---|---|---|
| Fibonacci | `forall n exists y` | computes `fib n` | baseline |
| gcd | full spec | computes divisor witness | richer postcondition |
| Sperner | function input | finds crossing | proof affects strategy |
| Hanoi | function-valued witness | emits move sequence | higher-type witness |
| Goodstein | termination | `tiRec`/ordinal descent | logical strength visible |
| Hydra | termination | typed/coded contrast | representation matters |
| Hercules | strategy quantified | higher-type game | unstatable first-order |

### 6. Representation Calibration for Constructive Analysis

Length: 4 pages.

Goal: transition from arithmetic to analysis cleanly.

Main question:

> What data must a representation carry before a theorem has constructive computational content?

Content:

- Define the roles of:
  - `A0`: exact rational evaluator plus uniform-continuity modulus.
  - `A1`: `A0` plus derivative evaluator and differentiability modulus.
  - `E0`, `E1`: approximating layers needed when exact rational-valued evaluators are too strict.
- Explain EFTC1:
  - `eftc1 (A : A0)`
  - integration is cheap: continuity modulus is enough.
- Explain EFTC2:
  - `eftc2_thm (A : A1)`
  - differentiation is expensive: derivative data and moduli are required.
- Explain `A0.toA1`:
  - converting existence of uniform derivative data into carried representation data uses classical choice.
  - this exhibits the Myhill gap; it does not reprove Myhill internally.

Key phrase:

> The function is not enough. The modulus is part of the computational content.

### 7. Galois Adequacy and Representation Order

Length: 3-4 pages.

Goal: give the framework-level contribution.

Content:

- `Rep`: represented spaces.
- `RepMorphism`: code transformer with approximation preservation.
- `RepLe`: retract preorder.
- `GaloisAdequate`: operation adequacy with explicit precision translation.
- `GaloisAdjunction`: `Req` / `Th` framing.
- `central_adequacy_theorem`: bridge from proof extraction to represented morphism.
- Concrete instances:
  - `A1_le_A0diff`
  - `A0diff_le_A1`
  - `A1_equiv_A0diff`
  - `E1_equiv_E0diff`
  - `doubling_central_adequacy`
  - `exp_doubling_central_adequacy`

Warning:

- This section must distinguish genuine framework instances from decorative theorem names.
- Use only declarations verified in the current build.

### 8. Executable Analysis and Dynamical Systems

Length: 3 pages.

Goal: use the LinkedIn material as examples, but with honest formal scope.

Subsections:

1. **Picard iteration for exponential and harmonic ODEs.**
   - exact rational polynomial iteration;
   - Haskell emission;
   - checked values such as sine/cosine approximations.

2. **Algebraic identities in dynamical systems.**
   - Van der Pol: `vanderpol_divergence_trace`.
   - Lotka-Volterra: `lotka_volterra_invariant_cancel`.
   - Duffing: `duffing_energy_dissipation_id`.
   - Lorenz: `lorenz_volume_contraction_rate`.
   - Kepler: `kepler_angular_momentum_conserved`.

3. **What these examples prove and do not prove.**
   - They prove identities and run exact rational computations.
   - They do not prove global qualitative dynamics.

### 9. Related Work

Length: 2-3 pages.

Must include:

- Cheval / formalized proof mining:
  - adjacent Lean formalization;
  - Dialectica and majorizability vs modified realizability and executable witnesses.
- Kohlenbach:
  - proof mining and extraction of bounds;
  - your work is representation calibration plus executable realizer extraction.
- Minlog:
  - program extraction prior art;
  - your difference is Lean-kernel formalization plus representation/Galois layer.
- C-CoRN:
  - constructive analysis in Coq;
  - your difference is deep object logic and axiom-footprint calibration.
- Incone:
  - represented spaces in Coq;
  - your difference is proof extraction bridge from object logic to represented morphisms.
- Weihrauch:
  - problem reducibility;
  - your relation orders representation data/capacity.

Use `docs/papers/RELATED_WORK_DELTA.md` as the starting point, but do not make the section combative.

### 10. Limitations and Auditability

Length: 1-2 pages.

Goal: earn referee trust.

Content:

- No PA-independence formalization.
- No internal Myhill negative theorem.
- No global dynamics claims.
- Some numerical System T terms are formulated, not extracted.
- Haskell emitter/runtime are part of trusted execution story unless fully formalized.
- Build counts are reproducibility metadata only.
- Every final claim should have a declaration name and axiom footprint.

### 11. Conclusion

Length: 1 page.

Return to the core thesis:

> The project makes constructive content operational and representation content measurable.

End with future work:

- more analysis derivations directly inside `Deriv`;
- stronger bridge from metric moduli to higher-type continuity;
- larger executable extracted numerical algorithms;
- a book-length treatment.

## 5. What Goes in the Main Paper vs Appendix

Main paper:

- System T / `Deriv` overview.
- Modified realizability definition.
- Extraction theorem.
- One complete arithmetic extraction example.
- Summary table of other arithmetic examples.
- Representation calibration: `A0/A1/E0/E1`, EFTC1/EFTC2.
- Galois adequacy bridge.
- Dynamical examples as evaluated case studies.

Appendix:

- Full syntax of all term constructors.
- Substitution lemmas.
- Complete axiom-footprint tables.
- Full extracted program listings.
- Haskell/Scheme emitted code.
- Detailed Goodstein/Hydra ordinal definitions.
- Detailed rational polynomial Picard machinery.

Book:

- Historical background: Curry-Howard, realizability, Dialectica, proof mining.
- Full tutorial on the Lean formalization.
- Full arithmetic examples, step by step.
- Full analysis development.
- Numerical examples with figures.
- Related work chapters.

## 6. Recommended Publication Strategy

### First submission: CPP

Best framing:

> A certified proof-to-program extraction framework in Lean, with executable arithmetic and analysis case studies.

Why CPP:

- certified programs and proofs;
- executable artifact matters;
- extraction and code emission fit naturally;
- the paper can include engineering and reproducibility details.

### Second option: ITP

Best framing:

> A Lean formalization of modified realizability for HA^omega with extraction and analysis examples.

Why ITP:

- strong fit for formalization;
- receptive to proof architecture;
- less need to sell emitted code as software engineering.

### Later journal version: JFR or JAR

JFR if the emphasis is formalization methodology.

JAR if the paper becomes more theorem-heavy and proof-theoretically polished.

## 7. Recommended Split if the Paper Gets Too Large

If the unified draft exceeds 25 pages, split it like this:

### Paper 1: Mechanization and Extraction

Title:

*A Modified-Realizability Development for HA^omega in Lean 4*

Contains:

- `Ty`, `Tm`, `Formula`, `Deriv`.
- `MR`, `extractClosed`, `soundnessClosed`.
- arithmetic examples.
- axiom budgeting.
- Haskell/Scheme emission.

Target: CPP or ITP.

### Paper 2: Representation Calibration

Title:

*How Much Data Does a Theorem Need? Representation Adequacy for Constructive Analysis in Lean 4*

Contains:

- `A0/A1/E0/E1`.
- EFTC1/EFTC2.
- `A0.toA1` and Myhill framing.
- Galois adequacy.
- analysis/dynamical examples.

Target: ITP, CPP, JFR, or LMCS-style journal after maturation.

## 8. Concrete Next Writing Tasks

1. Expand the current TeX article to this structure.
2. Add a table mapping each formal claim to a Lean declaration and source file.
3. Add a table mapping each declaration to its measured axiom footprint.
4. Choose two arithmetic examples for full exposition:
   - recommended: `doublingRealizer` and Goodstein/Hydra typed-vs-coded.
5. Choose one analysis theorem for full exposition:
   - recommended: EFTC1/EFTC2 with `A0.toA1`.
6. Keep the dynamical-system examples compact and honest.
7. Re-run `lake build` immediately before circulating the draft.

## 9. One-Paragraph Paper Pitch

We present a Lean 4 formalization of modified realizability for finite-type Heyting arithmetic that turns object-level constructive derivations into executable System T programs. The development separates proof syntax, extracted code, semantic soundness, and represented analytic data, allowing each component's axiom footprint to be measured independently. Arithmetic examples demonstrate proof-to-program extraction, including recursive computation and transfinite-recursion witnesses, while the analysis layer calibrates which data representations support constructive versions of the fundamental theorems of calculus. A category of represented spaces and a central adequacy theorem connect extracted realizers to precision-preserving computational morphisms. Exact rational Picard and dynamical-system examples demonstrate the executable end of the framework while maintaining explicit limits on what is formally proved.
