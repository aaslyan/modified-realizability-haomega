# Research Plan: Completing the Modified-Realizability System

Project goal: turn the current Lean 4 development into a more complete
mechanized modified-realizability system, with a clear path from the present
artifact to a paper, repository, and executable textbook.  This document is a
planning ledger, not an implementation commitment.

## 0. Current Baseline

The project already contains substantially more than a prototype:

- a first-order arithmetic fragment with derivation trees (`Deriv Γ φ`);
- a modified-realizability relation (`MR`);
- an extraction function (`extract`);
- soundness for every derivation rule;
- a generic continuity theorem for extracted closed type-2 realizers;
- extracted and certified programs for Goodstein, Hydra, Hanoi, Pascal,
  Euclid/gcd, Sperner, and Fibonacci;
- embedded `#print axioms`, `#eval`, and `#guard` checks run by `lake build`;
- no source-level `sorry`/`admit` in the Lean development.

The remaining completeness question is not whether extraction works.  It is:

> Which semantic schemas are still imported into the object theory, and what
> object-language infrastructure would be required to prove them internally?

## 1. Deliverable Tracks

### Track A: Conference Paper

Target venues: CPP 2027 or ITP 2027.

Core message:

- native Lean 4 formalization of a modified-realizability extraction pipeline;
- uniform extraction and soundness over a growing first-order fragment;
- generic continuity for extracted closed type-2 realizers;
- case studies including Goodstein and Hydra;
- axiom audit separating executable content from proof packaging;
- explicit accounting of remaining object-theory imports.

Paper risk:

- the paper must not claim formalized PA-independence or non-derivability of
  Goodstein/Hydra in the custom fragment;
- Goodstein/Hydra should be presented as fragment derivations relative to a
  small audited set of semantic schemas, each discharged by Lean theorems.

### Track B: Open-Source Repository and Executable Book

Target artifact:

```text
lean-realizability/
├── Realizability/
│   ├── Core/
│   ├── Signature/
│   ├── Ordinals/
│   ├── Common/
│   └── Theorems/
├── book/
├── paper/
├── lakefile.lean
└── README.md
```

The current repository already follows this structure closely.  The practical
work is packaging:

- CI running `lake build`;
- stable README and reader guide;
- artifact instructions;
- mdBook or LeanInk/Verso-style executable text;
- small tutorial modules whose code snippets are build-checked.

### Track C: Applied Proof Mining

Longer-term extension:

- extract quantitative witnesses/bounds from additional constructive proofs;
- keep each case study inside the same audit discipline;
- avoid adding opaque semantic schemas unless they are explicitly tracked in
  the internalization ledger below.

## 2. Internalization Gap Ledger

The current Goodstein and Hydra developments prove their main termination
arguments inside the fragment, but some semantic facts about the interpreted
function symbols remain imported as object-theory schemas.

### Goodstein Imports

| Object schema | Current semantic theorem | Role | Why it is not internal yet | Missing object-language infrastructure | Cost |
|---|---|---|---|---|---|
| `ordBump` | `ordOf_bumpN` | base change preserves the ordinal assignment | proof depends on hereditary representation, logarithm, division/modulo, and normal-form/canonicity facts | internal `hlog`, `div`, `mod`, inequalities, representation grammar, normal forms | high |
| `ordPredLt` | `olt_ordOf_of_lt` | monotonicity of the ordinal assignment under predecessor | proof depends on strict order, CNF comparison, normality of assigned ordinals | internal `<`, `≤`, predecessor/subtraction lemmas, ordinal comparison theory | high |
| `bumpNeZero` | `bumpN_ne_zero` | nonzero values remain nonzero after base bump | smallest remaining Goodstein import, but still depends on structural facts about `bumpN` | nonzero/order reasoning, internal case analysis for `bump`, possibly limited representation facts | medium |

Current status:

- the former composite Goodstein descent schema has already been decomposed;
- `Deriv.ordDescent` is now derived inside the fragment from the three schemas
  above;
- no remaining schema mentions the Goodstein sequence itself.
- closed numeral instances of `bumpNeZero` are derivable without the
  `bumpNeZero` schema as `Deriv.bumpNeZeroNumeral`; the remaining gap is the
  uniform open-term schema.

### Hydra Import

| Object schema | Current semantic theorem | Role | Why it is not internal yet | Missing object-language infrastructure | Cost |
|---|---|---|---|---|---|
| `hordCutLt` | `olt_ordOfHydraN_step` via `cutH_descends` | one live Hydra move strictly decreases the ordinal assignment | proof depends on encoded tree surgery, forests, replication, and CNF ordinal comparison | internal tree/forest constructors or codecs, append/replicate, Hydra ordinal assignment, normal forms, ordinal comparison | very high |

Current status:

- `hydraZero`, `hydraSucc`, and `hcutNum` let the fragment compute concrete
  battles;
- `hordCutLt` is faithful: reading it through soundness recovers the Lean
  semantic descent theorem;
- the fully strategy-quantified Hydra theorem remains metatheoretic because the
  fragment has no function variables.

## 3. Closure Levels

### Level 1: Faithfulness Closure

Goal: every imported schema has a round-trip theorem showing that its
realizability interpretation recovers exactly the intended Lean theorem.

Status:

- Goodstein has `ord_descent_via_fragment` for the derived composite descent;
- Hydra has `hydra_descent_via_fragment` for `hordCutLt`.

Next work:

- add explicit round-trip lemmas for the individual Goodstein schemas:
  `ordBump`, `ordPredLt`, and `bumpNeZero`;
- add an index table mapping every schema constructor to its semantic theorem.

### Level 2: Decomposition Closure

Goal: replace broad imported schemas with smaller, orthogonal schemas.

Status:

- Goodstein is mostly at this level: the composite descent was split into
  `ordBump`, `ordPredLt`, and `bumpNeZero`;
- Hydra is not: `hordCutLt` is still one broad move-descent schema.

Next work:

- attempt a Hydra decomposition analogous to Goodstein:
  - preservation/shape facts for `hcut`;
  - ordinal facts for forest append/replication;
  - live-hydra nonzero facts;
  - one final syntactic derivation assembling descent.

### Level 3: Object-Theory Closure

Goal: prove the remaining schemas as derivations in the object theory.

Goodstein route:

1. add an object-level order predicate or characteristic function;
2. add `div`, `mod`, and `hlog` symbols with recursion/equation schemas;
3. internalize hereditary-base representation facts;
4. internalize normal-form/canonicity for the ordinal assignment;
5. derive `bumpNeZero`;
6. derive `ordBump`;
7. derive `ordPredLt`;
8. derive `ordDescent` without imported ordinal-assignment schemas.

Hydra route:

1. add object-level tree/forest coding operations or expose enough destructors;
2. internalize append and replicate on forests;
3. internalize the Hydra ordinal assignment;
4. internalize normality of Hydra ordinals;
5. prove move descent from smaller tree/ordinal lemmas;
6. derive `hordCutLt` rather than importing it.

Expected scale:

- Goodstein object-theory closure is large but plausible as a staged project;
- Hydra object-theory closure is significantly larger because it combines tree
  surgery, list/forest algebra, and ordinal comparison.

### Level 4: Foundational/Strength Closure

Goal: prove metatheoretic claims about the object theory itself, such as
interpretability in PA, conservativity, or formalized independence results.

This is separate from extraction.  It should not be required for the CPP/ITP
paper unless the paper claims proof-theoretic strength results.

## 4. Near-Term Work Plan

### Phase 1: Audit and Packaging

Target: August-September 2026.

- add CI for `lake build`;
- add a generated or manually maintained schema-to-theorem table;
- ensure all `#print axioms` blocks are documented in one place;
- reduce or intentionally silence existing Lean linter warnings;
- keep the paper's claims aligned with the internalization ledger.

### Phase 2: Paper Draft

Target: September-October 2026.

- write a 12-page CPP/ITP-style draft;
- make the central contribution the extraction engine plus continuity/audit;
- include Goodstein/Hydra as audited case studies;
- state remaining semantic imports explicitly;
- include an artifact appendix explaining `lake build`, expected output, and
  axiom-budget checks.

### Phase 3: Executable Book

Target: November-December 2026.

- create a `book/` tree;
- start with chapters that build against the current code:
  - derivation trees;
  - realizability clauses;
  - extraction by examples;
  - soundness;
  - axiom audit;
  - Goodstein/Hydra case study boundaries.

### Phase 4: Internalization Sprint

Target: January-March 2027.

Preferred first target: `bumpNeZero`.

Reason:

- it is the smallest remaining Goodstein schema;
- success would demonstrate the method for moving one semantic import into the
  fragment;
- failure would reveal the minimum missing object-language features.

Deliverables:

- done as a first step: derive every closed numeral instance as
  `Deriv.bumpNeZeroNumeral`, using `bumpNum`, equality, and `succNeZero`;
- next: decide whether to introduce the extra object-language structure needed
  for the uniform open-term schema;
- if not, write a precise negative report listing the extra symbols/rules
  needed.

### Phase 5: Larger Extensions

Target: April-June 2027.

- decide whether to pursue full Goodstein internalization;
- decide whether Hydra decomposition is worth the complexity;
- prepare book proposal or longer manuscript only after the conference paper
  has a stable technical core.

## 5. Paper Abstract Skeleton

We formalize a modified-realizability extraction pipeline in Lean 4 for a
small first-order arithmetic fragment.  Derivations are represented explicitly
as syntax, interpreted by a formula-indexed modified-realizability relation,
and mapped by a verified extraction function into higher-type pure functionals.
We prove soundness for the full derivation system and a generic continuity
theorem showing that every closed extracted type-2 realizer denotes a
continuous functional.  The framework is exercised on several case studies,
including extracted witnesses for Goodstein termination, a Kirby-Paris Hydra
battle, Tower of Hanoi, Pascal parity, gcd, Sperner, and Fibonacci.  The
development includes a machine-checked axiom audit: executable extracted
programs avoid `Classical.choice`, while the remaining classical dependencies
are confined to proof packaging.  We also give an explicit ledger of the
semantic schemas still imported by the object theory and the steps required to
internalize them.

## 6. Book Outline

Part I: Foundations of intuitionistic proofs

1. Intuitionistic logic and the BHK interpretation.
2. Representing derivations as formal trees in Lean 4.

Part II: The extraction engine

3. Modified realizability and the pure-type hierarchy.
4. The soundness metatheorem and the `extract` function.
5. Generic continuity of extracted functionals.

Part III: Case studies

6. Primitive recursion and Fibonacci.
7. Branching recursion and Tower of Hanoi.
8. Pascal parity and finite computation inside the fragment.
9. Goodstein termination and transfinite induction up to `ε₀`.
10. Hydra termination and the boundary of first-order expressivity.

Part IV: Constructivity in practice

11. Auditing `Classical.choice`.
12. The Kleene-Kreisel continuous functionals and `CtQ`.
13. Remaining semantic imports and object-theory internalization.
