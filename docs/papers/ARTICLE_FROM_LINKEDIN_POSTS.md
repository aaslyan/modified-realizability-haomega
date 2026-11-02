# From Existence Proofs to Executable Algorithms

**Status:** draft article / paper seed, written from the LinkedIn showcase posts and checked against the Lean sources as built locally. The current build is green at **7,899 jobs**.

## Abstract

This project formalizes a small but complete path from constructive proof to executable program. Inside Lean 4, a deeply embedded version of finite-type Heyting arithmetic (`HA^omega`) contains an intrinsically typed System T term language, a natural-deduction proof calculus, Kreisel-style modified realizability, a certified extraction function, and emitters to functional source code. The public showcase posts demonstrate the visible end of that pipeline: exact rational Picard iterations for differential equations, conservation and dissipation identities for classical dynamical systems, and kernel-checked numerical outputs.

The paper-level contribution is sharper than the posts' outreach framing. The repository supports three defensible claims: first, object-level constructive derivations can be translated into executable System T terms by `extractClosed`; second, the computational artifacts can be separated from the classical axioms used by semantic soundness proofs; third, representations of analytic data can be calibrated by the quantitative moduli they carry, with Lean's `#print axioms` serving as a measurement instrument.

## 1. The Story the Posts Are Pointing At

The LinkedIn posts show a sequence of mathematical systems:

- harmonic Picard iteration, producing exact rational sine and cosine approximations;
- Van der Pol, Lotka-Volterra, Duffing, Lorenz, and Kepler systems, each with a formal algebraic identity and kernel-checked rational trajectory data;
- zero-axiom extraction from a constructive object-level derivation, with `doublingRealizer` as the cleanest proof-to-program example.

As outreach, these examples work because they are concrete. They show equations that readers recognize and values that the Lean kernel computes exactly. As a paper, however, the examples should not be presented as independent breakthroughs in dynamical systems. Their role is evidential: they demonstrate that the proof-theoretic machinery is not an inert formalization. It reaches executable numerical code.

The paper should therefore use the posts as case studies, not as the thesis. The thesis is:

> A constructive proof carries algorithmic content, and in this Lean development that content is extracted, evaluated, emitted, and audited with explicit axiom footprints.

## 2. The Formal Core

The core formalization is organized around four layers.

**System T terms.** `Tm` is an intrinsically typed term language for finite types: naturals, unit, products, functions, and the project-specific rational arithmetic extensions. Because terms are indexed by context and type, ill-typed object programs are not representable.

**Object-level proofs.** `Deriv` is a natural-deduction calculus for formulas in `HA^omega`. A derivation is not a Lean proof of an ambient theorem; it is a Lean data structure representing a proof in the embedded object logic.

**Modified realizability.** The predicate `MR` assigns computational meaning to formulas. Existential statements produce witnesses, universal statements produce functions, conjunctions produce pairs, and atomic equalities carry no computational data beyond the unit realizer.

**Extraction.** `extractClosed` maps a closed derivation to a closed System T realizer. The clean demonstration is:

```lean
def doublingRecDeriv :
    Deriv .nil (.all .nat (iterInv .nat [] (.succ .zero) doublingStepTm)) :=
  iterSequenceD .nat (.succ .zero) doublingStepTm

def doublingRealizer : Tm [] (.arrow .nat (.prod .nat .unit)) :=
  extractClosed doublingRecDeriv

def doublingExtracted (n : Nat) : Nat :=
  ((extractClosed doublingRecDeriv).eval Env.nil n).1
```

The guards in `HAomega/AnalysisDeriv.lean` check that this extracted program computes:

```text
0 -> 1
1 -> 2
2 -> 4
3 -> 8
4 -> 16
5 -> 32
10 -> 1024
```

This is the best opening example for a paper because the provenance is exact: derivation, extraction, evaluation, and axiom report all refer to named declarations.

## 3. Axiom Footprints as Measurements

The project should not claim that every theorem is axiom-free. The verified and more interesting statement is the separation:

- `extractClosed` is the syntactic program extractor.
- `doublingRealizer` does not depend on any axioms.
- `soundnessClosed` proves semantic correctness of closed extracted realizers and depends on `[propext, Classical.choice, Quot.sound]`.
- many analysis and dynamical-system identities depend on `[propext, Classical.choice, Quot.sound]`.

This separation is not a weakness. It is the main methodological point. The computational artifact can be generated and run constructively, while the ambient semantic theorem that relates all object proofs to Lean-level truth has a measured classical footprint.

For analysis, the same discipline becomes a calibration tool. The representation `A0` carries exact rational evaluation plus a modulus of uniform continuity. The representation `A1` carries the additional derivative data and modulus needed for differentiability claims. The bridge

```lean
noncomputable def A0.toA1 (A : A0) (h : HasUnifDeriv A) : A1
```

uses classical choice to select the missing data. The paper-level formulation should be precise:

> The axiom footprint of `A0.toA1` exhibits the gap identified by Myhill; it does not reprove Myhill's negative theorem inside this formal system.

That sentence should be treated as the hard boundary for the claim.

## 4. The Analysis Calibration Thesis

The representation ladder gives the mathematical paper its strongest spine.

At the `A0` level, the first fundamental theorem is available in the form proved by `eftc1`: integration needs the modulus of uniform continuity. No derivative evaluator is required.

At the `A1` level, the second fundamental theorem is available in the form proved by `eftc2_thm`: differentiation requires derivative data and a differentiability modulus.

The bridge from `A0` plus an existence proof of uniform differentiability to `A1` is `A0.toA1`, and it is noncomputable. This is where the slogan "the modulus is the content" becomes exact. The function itself is not the problem. The missing quantitative data is the problem.

This yields a defensible paper question:

> How much represented data must a theorem carry before its constructive proof yields executable numerical content?

The current project answers this through named artifacts:

| Claim | Artifact |
|---|---|
| EFTC1 holds for `A0` data | `HAomega.QAnalysis.eftc1` |
| EFTC2 holds for `A1` data | `HAomega.QAnalysis.eftc2_thm` |
| converting `A0` plus uniform derivative existence to `A1` uses choice | `HAomega.QAnalysis.A0.toA1` |
| representation retracts organize the data ladder | `HAomega.GaloisAdequacy` |
| derivations can be bridged into represented morphisms | `HAomega.CentralAdequacy.central_adequacy_theorem` |
| the zero-axiom extracted arithmetic demo runs in the kernel | `HAomega.AnalysisDeriv.doublingRealizer`, `doublingExtracted` |

## 5. How the Dynamical-System Posts Fit

The dynamical-system posts are useful, but they need disciplined language.

**Harmonic oscillator.** The post's exact values are good article material: the Lean kernel checks the rational approximations `337/384` for cosine at order 4 and `1841/3840` for sine at order 5. The paper should say that the Picard iterator is formulated as exact rational polynomial computation, with System T compilation demonstrated separately. It should not imply that every Picard solver is extracted from a `Deriv` proof unless the specific declaration is.

**Van der Pol.** The Lean source proves the divergence/trace identity `vanderpol_divergence_trace` and checks rational Picard trajectory values. Avoid claiming a formal proof of global limit-cycle existence unless that theorem is added.

**Lotka-Volterra.** The source proves the algebraic cancellation `lotka_volterra_invariant_cancel` and checks rational trajectory values. The post's discussion of closed periodic orbits is good mathematical context, but the formal claim should be the invariant cancellation.

**Duffing.** The source proves `duffing_energy_dissipation_id` and checks rational Picard values. The formal result is the dissipation identity, not a full basin-of-attraction theorem.

**Lorenz.** The source proves `lorenz_volume_contraction_rate`. The paper should not state that Lean proves existence of a strange attractor; it proves the divergence identity and computes exact initial Picard segments.

**Kepler.** The source proves `kepler_angular_momentum_conserved` and checks Picard trajectory values. The separate `SymplecticKepler.lean` guards also check angular momentum preservation for a discrete orbit trajectory. The formal claim should stay at conservation and kernel-checked computation.

These examples make the article readable. They should occupy a "showcase and evaluation" section, after the proof-theoretic and representation-calibration sections.

## 6. Proposed Paper Structure

**Working title:** *From Constructive Proofs to Executable Analysis: Modified Realizability for HA^omega in Lean 4*

1. **Introduction.** Start with the public-facing question: when does an existence proof become an algorithm? State the three contributions: deep `HA^omega`, zero-axiom extracted programs, and representation calibration.
2. **Object logic and terms.** Present `Ty`, `Tm`, `Formula`, and `Deriv`. Keep this section compact and formal.
3. **Modified realizability and extraction.** Define `MR`, `extractClosed`, and `soundnessClosed`. Show the axiom-budget separation.
4. **The smallest complete demo.** Use `doublingRecDeriv -> doublingRealizer -> doublingExtracted`. This is the reproducible anchor.
5. **Representations as data budgets.** Explain `A0`, `A1`, `E0`, `E1`, the EFTC1/EFTC2 calibration, and the exact role of `A0.toA1`.
6. **Galois adequacy.** Present `Rep`, `RepLe`, the retract/equivalence layer, and `central_adequacy_theorem` as the bridge from derivations to represented morphisms.
7. **Executable analysis case studies.** Bring in harmonic Picard, exponential Picard, Van der Pol, Lotka-Volterra, Duffing, Lorenz, and Kepler. Use them as evidence of exact rational computation and source emission.
8. **Related work.** Compare against Incone, Weihrauch reducibility, Kohlenbach/Cheval proof mining, Minlog, and C-CoRN using `docs/papers/RELATED_WORK_DELTA.md`.
9. **Limitations.** State what is not proved: no PA-independence claim, no internal proof of Myhill's negative half, no global dynamical-systems theorems unless present as declarations, and no blanket "0 axioms" claim.
10. **Conclusion.** The development makes proof content operational and makes representation content measurable.

## 7. Article Version

For a public article, use the same thesis with less formal load:

> A proof assistant is usually seen as a place where mathematics is checked. In this project, Lean is also a place where proofs become programs. A constructive derivation in finite-type arithmetic is translated into an executable System T term, evaluated inside the kernel, and emitted to ordinary functional code. The examples range from a zero-axiom extracted arithmetic program to exact rational Picard iterations for classical differential equations.

Then show three scenes:

1. **The proof-to-program scene:** the doubling derivation extracts to a program whose kernel-checked values are `1, 2, 4, ..., 1024`.
2. **The calculus scene:** `A0` and `A1` show that integration and differentiation need different data budgets.
3. **The dynamical-systems scene:** Picard iteration and algebraic invariants are checked for harmonic, Lotka-Volterra, Duffing, Lorenz, Van der Pol, and Kepler systems.

End the article with the sober claim:

> The point is not that Lean discovered new physics. The point is that exact symbolic computation, constructive proof extraction, and axiom-budget accounting can live in one checked artifact.

## 8. Claims to Avoid

- Do not say every result is axiom-free.
- Do not say every numerical solver is extracted from a `Deriv` proof.
- Do not say Lean proves global limit cycles, strange attractors, or basin convergence unless a corresponding theorem exists.
- Do not say the project proves `A0` cannot satisfy EFTC2.
- Do not use build counts from older posts; the local build checked for this draft is **7,899 jobs**.

## 9. Immediate Next Steps

1. Convert this draft into either a 2,000-word public article or a 12-16 page paper skeleton.
2. Re-run `lake build` immediately before publishing and update the build count.
3. For every formal claim in the final article, include the exact declaration name and source file.
4. Decide whether the first academic submission should be P2, the mechanization paper, or P1, the calibration paper. Based on the current repository, P2 is the cleanest first submission and P1 is the sharper mathematical story.
