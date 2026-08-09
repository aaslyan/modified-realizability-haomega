# Status: COMPLETE through Phase H9, Phase E (Hanoi), Phase F (Pascal mod 2) and Phases G/G2 (Kummer/Lucas, with its core inside the fragment) — Goodstein's theorem *and* the Kirby–Paris Hydra theorem are proved inside the fragment, each with its witness function extracted, certified, and executed; and the Hydra theorem is proved again in the metatheory in its full strategy-free form

Phases: milestone (modified realizability + extraction + soundness),
generic continuity, induction (2), arithmetic (A), hereditary base-`k`
and the Goodstein sequence (B), transfinite induction to `ε₀` (C),
Phase D in four checkpoints — `∃` (D0), the ordinal-assignment
obligations (D1), Goodstein's theorem (D2), the extracted function
(D3) — the derived descent (D5), and the Hydra project in six: tree
coding (H1), the move (H2), the ordinal assignment and its descent
theorem (H3), the game inside the fragment (H4), termination as a closed
derivation (H5), the extracted battle-length program (H6), and the
general game — every strategy, every schedule — in the metatheory (H7),
the fast tree-level evaluator with the battle trace (H8), and a second
strategy covered by H7 for free (H9).

`lake build` succeeds, zero `sorry`/`admit`.  `#print axioms` on the
soundness theorem (now covering the `ind` rule and the Phase-A rules),
the recursor's preservation theorem, the generic-continuity theorem, and
the collapse-demo theorem reports:

```
'Realizability.soundness' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Realizability.MR_indRecC' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Realizability.extract_continuous' depends on axioms:
  [propext, Quot.sound]
'Realizability.collapse_demo' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

and on the four Phase-A equation theorems (`#print axioms` commands are
in `Arithmetic.lean` itself, so this is checked at every build):

```
'Realizability.plus_zero_realized'   … [propext, Classical.choice, Quot.sound]
'Realizability.plus_succ_realized'   … [propext, Classical.choice, Quot.sound]
'Realizability.times_zero_realized'  … [propext, Classical.choice, Quot.sound]
'Realizability.times_succ_realized'  … [propext, Classical.choice, Quot.sound]
'Realizability.plus_zero_extract_continuous'   … [propext, Quot.sound]
'Realizability.plus_succ_extract_continuous'   … [propext, Quot.sound]
'Realizability.times_zero_extract_continuous'  … [propext, Quot.sound]
'Realizability.times_succ_extract_continuous'  … [propext, Quot.sound]
```

and on the Phase-C theorems (`#print axioms` in
`TransfiniteInduction.lean`, checked at every build — note the first
line, which is the well-foundedness of the notation order that the
transfinite recursor is defined by, and which is deliberately
`Classical`-free so the continuity budget survives):

```
'Realizability.oLt_wf'                     … [propext, Quot.sound]
'Realizability.MR_tiRecC'                  … [propext, Classical.choice, Quot.sound]
'Realizability.ti_demo_realized'           … [propext, Classical.choice, Quot.sound]
'Realizability.prec_one_omega_realized'    … [propext, Classical.choice, Quot.sound]
'Realizability.ti_demo_extract_continuous' … [propext, Quot.sound]
'Realizability.ordOf_goodstein_three_descends' … does not depend on any axioms
```

and on the Phase-B certification theorems (`#print axioms` in
`Goodstein.lean`, likewise checked at every build):

```
'Realizability.hrep_self_realized'    … [propext, Classical.choice, Quot.sound]
'Realizability.good_compute_realized' … [propext, Classical.choice, Quot.sound]
'Realizability.hrep_self_extract_continuous'    … [propext, Quot.sound]
'Realizability.good_compute_extract_continuous' … [propext, Quot.sound]
```

(likewise `MR_liftR_dropR`, `FR_famOf`, `indC_tracked` —
`[propext, Quot.sound]` — `demo_extract_eq`, and
`demo_extract_continuous`, the latter a one-line corollary of
`extract_continuous`).

## What is delivered

- `Syntax.lean` — terms (since Phase A over `{0, succ, +, ×}`, since
  Phase B additionally `pred`/`exp`/`bump`/`good`, since Phase H4
  additionally `hcut`/`hydra`/`hord`, with the fuel-structural
  value-level functions `hlog`/`bumpN`/`goodN` and the
  `numeral` embedding), the fragment's formulas, capture-safe
  substitution, the decidability instances for the quantifier rules' side
  conditions (moved here from `GoodsteinTheorem.lean` in H5, since both
  theorem phases discharge them by `decide +kernel`), and the 70-rule
  natural-deduction family — since the
  Phase-2 extension including the arithmetic induction rule `ind`
  (from `φ(0)` and `∀x (φ(x) → φ(succ x))`, conclude `∀x φ(x)`; side
  condition: no variable capture for the substituted `succ x`, same
  shape as `∀`-elim's); since the Phase-A extension the
  equational-logic kit (`eqRefl`, and `eqSymm`/`eqTrans`/`eqCongSucc`/
  `eqCongPlus`/`eqCongTimes` as implication schemas, `succInj`-style)
  plus the four first-argument recursion equations defining `+`/`×`
  (`zeroPlus`, `succPlus`, `zeroTimes`, `succTimes`); and since the
  Phase-B extension the recursion schemas for `pred`/`exp`/`good`
  (`predZero`, `predSucc`, `expZero`, `expSucc`, `goodZero`,
  `goodSucc`), the two `bump` axioms (`bumpZero`, and the numeral
  graph `bumpNum` — see the Phase-B section), and the four matching
  congruence schemas (`eqCongPred`, `eqCongExp`, `eqCongBump`,
  `eqCongGood`); and since the Phase-H4 extension the Hydra group (the
  battle's recursion equations `hydraZero`/`hydraSucc`, the move's
  numeral graph `hcutNum`, the imported descent `hordCutLt`, and the
  three congruences `eqCongHcut`/`eqCongHydra`/`eqCongHord` — see the
  Phase-H4 section).
- `ModifiedRealizes.lean` — the pure-type devices (`up`/`down`,
  `pairPT`/`fstPT`/`sndPT`, `app₁`/`abs₁` with beta) and the
  **flexible-ambient** modified-realizability relation `MR ρ φ n x`
  with realizers in `PureType (n+1)`, plus environment-congruence
  (`MR_congr`) and the substitution lemma (`MR_subst`).
- `Transport.lean` — the formula-indexed level transports
  `liftR`/`dropR` with the mutual preservation induction
  (`MR_liftR_dropR`), iterated versions, and the family generator
  `famOf` with `FR_famOf`.  This is the pure-type "finite types as
  retracts" machinery, reusable by the parent project's deferred
  arbitrary-finite-types chapter.
- `Extraction.lean` — the extraction function, dispatching to one named
  combinator per rule (full list below), and the ambient bound
  `derivBound`.
- `Soundness.lean` — `CtxR_congr` and **`soundness`**: for every
  derivation, environment, and realizing context assignment, the
  extracted family realizes the conclusion at every ambient level above
  `derivBound`.
- `GenericContinuity.lean` — the **generic continuity theorem**
  (`extract_continuous`): the extracted type-2 realizer of *every*
  closed derivation is continuous.  Proved by induction on the
  derivation, threading the oracle-parameterized continuity relation
  `Tracked` (a Kripke-style logical relation on Baire-space-indexed
  families of pure-type objects), with one named preservation lemma per
  extraction combinator (full list below) and tracking preservation for
  every pure-type device and transport (`up`/`down`, the pairing
  devices, `app₁`/`abs₁`, `liftR`/`dropR`, `famOf`).
- `Arithmetic.lean` (Phase A) — the four defining equations of `+`/`×`
  as closed `ind` theorems with extracted, certified realizers; see the
  Phase-A section below.
- `Goodstein.lean` (Phase B) — hereditary base-`k` representation **as
  a term of the fragment's own syntax in one distinguished base
  variable**, the bump-and-decrement step, and the Goodstein sequence,
  with fragment-internal certification (`hrepSelfDeriv`,
  `bumpHrepDeriv`, `goodComputeDeriv`) and kernel-verified value
  cross-checks against `WilliamAngus/Goodstein`; see the Phase-B
  section below.  Goodstein's theorem itself is **not** proved and not
  claimed — Phases C/D.
- `Epsilon0.lean` (Phase C, and the only module *before* `Syntax.lean`)
  — the ordinal notations below `ε₀` as natural-number codes, their
  Cantor-normal-form order `≺`, the normal-form predicate that makes it
  well-founded, and **`oLt_wf`**; plus a hand-rolled choice-free,
  kernel-computable triangular pairing (Mathlib's `Nat.pair` could not be
  used — see the Phase-C section).
- `TransfiniteInduction.lean` (Phase C) — the identification of the
  notations with Phase B's `HTerm` grammar (`ordTerm`), the Goodstein
  ordinal assignment `ordOf` with kernel-verified descent instances, the
  rule exercised end to end, and the `#print axioms` block.
- `CollapseDemo.lean` — `RealizesCtQ` (the class of a closed
  derivation's extracted type-2 realizer in `CtQ 2`, via the parent
  project's capstone equivalence `ctQTwoEquiv`) — now **total on closed
  derivations**, the continuity obligation discharged uniformly by
  `extract_continuous` — and the named demo: `demoDeriv₁`/`demoDeriv₂`,
  two different derivations of `A ∧ B → B ∧ A` whose extracted terms
  are proved equal as functionals (`demo_extract_eq`) and hence denote
  the same element of `CtQ 2` (**`collapse_demo`**).  The demo's
  continuity certificates are one-line corollaries of
  `extract_continuous`; the concrete value computation
  (`demo_extract_apply`) is kept as the worked illustration of the
  modulus.

## The per-rule extraction combinators (all in `Extraction.lean`)

1. `axC` — hypothesis projection (rule `ax`);
2. tail recursion on the context (rule `wk`);
3. `andIC` — pointwise pairing (`andI`);
4. `andE₁C` — pointwise first projection (`andE₁`);
5. `andE₂C` — pointwise second projection (`andE₂`);
6. `orI₁C` — tag 0 (`orI₁`);
7. `orI₂C` — tag 1 (`orI₂`);
8. `orEC` — pointwise tag split, rebuilding the branch hypothesis's
   family from the payload at each ambient (`orE`);
9. `impIC` — abstraction over the bound realizer's transport-generated
   family (`impI`);
10. `impEC` — application, major premise one ambient up (`impE`);
11. `botEC` — vacuous (`botE`);
12. `allIC` — abstraction reading the numeral off the argument
    (`allI`);
13. `allEC` — application at the numeral of the term's value (`allE`);
14. `eqDecC` — decidable-equality tag (`eqDec`);
15. `axiomC` — contentless realizer for `succNeZero`;
16. `axiomC` — contentless realizer for `succInj` (vacuous or
    true-equation implication clauses);
17. `indC` — **the induction recursor** (rule `ind`): the type-indexed
    primitive recursion `indRecC` — `indRecC a b 0 = a`,
    `indRecC a b (k+1) = app₁ (app₁ b (natPT _ k)) (indRecC a b k)` —
    at the realizer's own type `PureType (m + 1)`, uniformly in the
    ambient `m`, packaged into the concluded `∀x. φ(x)` by the existing
    `allIC` device.  The one combinator that *iterates*: the number of
    `app₁` steps performed is the numeral being realized.  Correctness
    is `MR_indRecC` (`Soundness.lean`), closure of `MR` under primitive
    recursion at every ambient level, stated once and instantiated —
    no level-by-level instances exist;
18. –27. `axiomC` — contentless realizers for the ten Phase-A schemas
    (`eqRefl`, `eqSymm`, `eqTrans`, `eqCongSucc`, `eqCongPlus`,
    `eqCongTimes`, `zeroPlus`, `succPlus`, `zeroTimes`, `succTimes`):
    atomic conclusions carry no computational content, so each
    soundness case is just the equation's truth from its premises'
    truths (`derivBound`: 0 for the bare-equation schemas, 1/2 for the
    single/nested implication schemas);
28. –39. `axiomC` — contentless realizers for the twelve Phase-B
    schemas (`predZero`, `predSucc`, `expZero`, `expSucc`, `bumpZero`,
    `bumpNum`, `goodZero`, `goodSucc`, `eqCongPred`, `eqCongExp`,
    `eqCongBump`, `eqCongGood`), same discipline and bounds as the
    Phase-A group;
40. `tiC` — **the transfinite recursor** (rule `tiEps0`): `tiRecC`,
    defined by `WellFounded.fix` along the notation order `≺`, packaged
    by `allIC` exactly as `indC` is.  The second combinator that
    recurses, and the only one whose recursion is not along `ℕ`'s
    successor structure.  Correctness is `MR_tiRecC` (`Soundness.lean`);
    `tiRecC_eq` is the non-dependent unfolding both the soundness and
    the continuity proof use;
41. –42. `axiomC` — contentless realizers for the two remaining Phase-C
    schemas (`precNum`, the numeral graph of the order, and
    `eqCongPrec`).

## The per-combinator continuity preservation lemmas (all in `GenericContinuity.lean`)

One per combinator, same order as the list above; each says the
combinator sends tracked inputs to tracked outputs:

1. `axC_tracked` (rule `ax`);
2. `wk_tracked` — the tail of a tracked context is tracked (rule `wk`);
3. `andIC_tracked` (`andI`);
4. `andE₁C_tracked` (`andE₁`);
5. `andE₂C_tracked` (`andE₂`);
6. `orI₁C_tracked` (`orI₁`);
7. `orI₂C_tracked` (`orI₂`);
8. `orEC_tracked` (`orE`) — continuous tag read, tracked `famOf`
   payload families, pointwise case split;
9. `impIC_tracked` (`impI`) — abstraction closure **by β-reduction**
   under the tracking relation (see below);
10. `impEC_tracked` (`impE`) — application, major premise one ambient
    up;
11. `botEC_tracked` (`botE`);
12. `allIC_tracked` (`allI`) — the bound numeral is a continuous read
    off the tracked argument;
13. `allEC_tracked` (`allE`) — application at the numeral of a
    continuously computed term value;
14. `eqDecC_tracked` (`eqDec`) — case split on the equality of two
    continuously computed values;
15. `axiomC_succNeZero_tracked` (`succNeZero`);
16. `axiomC_succInj_tracked` (`succInj`);
17. `indC_tracked` (`ind`) — per fixed iteration count the recursor is
    tracked by a small induction on the numeral (each step is `app₁` of
    tracked pieces, existing closure lemmas only); the *actual* count,
    read continuously off the abstraction's argument, is absorbed by
    the one new closure fact `tracked_apply_nat` (with its base form
    `continuous2_apply_nat`): consulting a family of tracked families
    at a continuously computed numeral preserves tracking, because near
    any oracle the numeral is locally constant — the countably-branching
    generalization of the binary case split `ite_tracked`;
18. –27. `axiomC_eqRefl_tracked` … `axiomC_succTimes_tracked` — one per
    Phase-A schema, all the tracked junk family.  The one place Phase A
    genuinely touches the continuity module is *not* per-rule:
    `termEval_continuous` gains the `plus`/`times` cases (a binary
    composition of two continuous reads, `continuous2_comp₂`, already
    in the closure kit) — the `allE` case reads term values off tracked
    environments, so evaluation over the extended signature had to stay
    continuous.  No case of `extract_tracked` is left silent;
28. –39. `axiomC_predZero_tracked` … `axiomC_eqCongGood_tracked` — one
    per Phase-B schema, all the tracked junk family; and
    `termEval_continuous` gains the `pred`/`exp`/`bump`/`good` cases —
    `bump`/`good` are *arbitrary* functions of two continuously
    computed values, so `continuous2_comp₂` again covers them with no
    new closure fact.  No case of `extract_tracked` is left silent.

40. `tiC_tracked` (`tiEps0`) — the recursor is tracked at each *fixed*
    notation by well-founded induction along `≺` (`tiRecC_tracked`), and
    the oracle-dependent notation code is absorbed by the same
    `tracked_apply_nat` that rule `ind` needed — no new closure fact was
    required.  The case split on `j' ≺ j` inside the recursor does not
    depend on the oracle, so it is discharged index by index rather than
    by `ite_tracked`.  `termEval_continuous` gains the `prec` case
    (`continuous2_comp₂ oltN`);
41. –42. `axiomC_precNum_tracked`, `axiomC_eqCongPrec_tracked`.

The capstone `extract_continuous` is the induction on `Deriv`
(`extract_tracked`) invoking one preservation lemma per case — the same
shape as `soundness` — instantiated at the constant environment, empty
context, and the tracked identity family of Baire space.

## Design decisions and deviations (flagged)

- **Flexible ambient level.**  `MR ρ φ n x` is defined at every ambient
  `n`, all clauses at one level with binders stepping down — no level
  coercion occurs in the definition.  The coercions concentrate in the
  transports, which extraction alone needs.
- **`Realizes` in `CtQ`, uniformly.**  `RealizesCtQ` lands in `CtQ 2`
  via `ctQTwoEquiv`, for **every** closed derivation: the continuity
  obligation is discharged once by `extract_continuous`
  (`GenericContinuity.lean`), with no per-derivation certificate and no
  level hypothesis.  The brief's `lvl φ ≤ 1` restriction turned out to
  be unnecessary — continuity of the extract is a property of the
  extraction combinators alone; the formula's level matters only for
  *realization* (`soundness`), not for continuity.

  *How the 2026-07-27 sizing finding was resolved (superseded
  2026-07-28):* the earlier analysis was right that the ambient-1
  extract consults extracts at every ambient (`impEC`/`allEC` climb,
  cut formulas are unbounded), and right that "every extract **has an
  associate** at every ambient" is countability-chapter-sized (its hard
  core is associate-level abstraction closure).  It was wrong to
  conclude those are the only invariant choices.  The compositional
  invariant that works is the **oracle-parameterized continuity
  relation** (`Tracked`): a Baire-indexed *family* of pure-type objects
  is tracked iff its pointwise application to every tracked argument
  family is a continuous function of the oracle — the classical
  relative-continuity logical relation.  Tracking constrains only how
  numbers are read out of a family through continuously supplied
  arguments, never a single functional in isolation, so **abstraction
  closure holds by β-reduction** (`abs₁_tracked`): applying `abs₁ G` to
  a tracked argument computes `G`, and no associate is ever
  constructed.  The capstone then reads the extract off along the
  tracked identity family `α ↦ α`.  The associate-level closure theorem
  remains genuinely open — but it is needed for the parent project's
  finite-types chapter, not for this theorem.
- The `→` clause of `MR` is the `Assoc`/`CtPer` clause *shape* at the
  level of pure functionals; the literal `Assoc`-instance reading enters
  through the `CtQ` packaging, not as a redundant re-proof.

## The induction rule (Phase 2): COMPLETE

The specification recorded here since the first milestone ("exactly one
new theorem is required: closure of `MR` under primitive recursion at
every ambient level") is now discharged.  What was added, per file:

- `Syntax.lean` — the rule `ind`: from `Deriv Γ (φ.subst x zero)` and
  `Deriv Γ (all x (φ.imp (φ.subst x (succ (var x)))))`, conclude
  `Deriv Γ (all x φ)`, with the no-capture side condition
  `SubstOK (succ (var x)) φ` (same shape as `∀`-elim's).
- `Extraction.lean` — combinator 17 (`indRecC`/`indC`, listed above);
  `derivBound (ind D₁ D₂ _) = max (derivBound D₁) (derivBound D₂) + 1`.
- `Soundness.lean` — **`MR_indRecC`**, the actual new theorem: if `a`
  realizes `φ(0)` at ambient `m` and `b` realizes
  `∀x (φ(x) → φ(succ x))` at ambient `m + 2`, then `indRecC a b k`
  realizes `φ` under `ρ[x ↦ k]` at ambient `m`, for every `k` — proved
  **uniformly in the ambient level `m`** (one statement, no
  level-by-level instances), by ordinary natural-number induction on
  the numeral `k`.  The two inductions are kept explicitly distinct:
  `MR_indRecC` is the "small" induction (on the numeral, at a fixed
  ambient), invoked exactly once by the `ind` case of the "big"
  induction over `Deriv` in `soundness`, which only unfolds the `allIC`
  packaging and dispatches.

One structural point deserves flagging, because it is *why* the small
induction stays level-uniform rather than needing the transports: the
flexible-ambient design makes `MR`'s `→` clause consume and produce
realizers at the *same* level, so the iterate never crosses ambient
levels at all — the step realizer, consumed through the `∀` clause at
`m + 2` and the `→` clause at `m + 1`, maps ambient-`m` realizers of
`φ(k)` to ambient-`m` realizers of `φ(succ k)`.  The first milestone's
specification predicted the iterate would cross implication levels and
lean on the transports; in the event the transports are needed only
where they always were (the binder cases of extraction), and the
recursion is genuinely primitive recursion at the fixed type
`PureType (m + 1)`, uniformly in `m`.  The substitution lemma
(`MR_subst`) does the conversion between `φ(0)`/`φ(succ x)` under `ρ`
and `φ` under the updated environment at both ends of each step.

**Generic continuity against the new combinator — answered
explicitly.**  The generic continuity theorem does *not* cover `ind`
for free: `extract_tracked` is an induction over `Deriv`, so the new
rule adds a case, and `indC_tracked` is its per-combinator preservation
lemma (item 17 above).  But the *invariant* needed no strengthening,
and only one genuinely new closure fact was required:
`tracked_apply_nat` — the iteration count is read off the oracle
through the `allIC` abstraction, and a count that is a continuous
function of the oracle is locally constant, so the recursor (tracked at
each fixed count by the existing `app₁`-closure lemmas) stays tracked
at the oracle-dependent count.  `extract_continuous`, `RealizesCtQ`,
and `collapse_demo` then cover `ind`-derivations with no further
change — `CollapseDemo.lean` was not touched.

## Citation (checked as far as the primary text allows)

The construction follows the standard realizer of the induction axiom
in modified realizability: Gödel's primitive-recursor constants
applied to the base and step realizers, iterating application along
the numeral — A.S. Troelstra (ed.), *Metamathematical Investigation of
Intuitionistic Arithmetic and Analysis*, Springer LNM 344, 1973:
**Ch. III, §3.4** (modified realizability and its soundness theorem)
for the interpretation, with the recursor constants of the underlying
system **N-HAω from Ch. I, §1.6**.

Granularity, stated plainly per the house discipline: the primary text
was **not accessible** in this environment (Springer's per-chapter
PDFs are paywalled; no scan exists in the ILLC eprints repository, the
Troelstra Archive index, or the Internet Archive — all checked
directly).  The section-level attribution above was cross-checked
against a primary-adjacent source, Troelstra's own corrections report
*Corrections to some Publications* (ILLC X-2018-02, December 2018,
`eprints.illc.uva.nl/id/eprint/1650`), which confirms directly: §3.4
of LNM 344 is the modified-realizability section (its corrections
reference items "3.4.7" and "3.4.14" on pp. 215–222, and the relation
`y mr A`), and §1.6.15 defines the system there called `HAω` with its
combinator/equality axioms.  The item-level clause number for the
induction case inside §3.4's soundness proof is deliberately **not**
cited, rather than guessed — refining to definition granularity
requires the book itself and remains a documentation-only follow-up,
exactly as recorded for Longley–Normann chapter-level citations in the
parent project's docs/first-order/STATUS.md.

## Out of scope (per the brief)

Full first-order quantification with unbounded nesting beyond the one
`∀`-pair; Dialectica; any claim of soundness for HA.

## Phase A (arithmetic): COMPLETE — Option 2, "mirror recursion" form

The brief posed Option 1 (the four briefed equations as bare axiom
rules) against Option 2 (the equations *proved* using `ind`), and asked
for the choice and its rationale to be recorded here.

**Option 2 was taken, in the following form.**  `Term` gains `plus` and
`times`; the axiom rules *defining* them (`Syntax.lean`) are the
primitive-recursion equations **on the first argument** —

```
0 + t = t          succ s + t = succ (s + t)
0 × t = 0          succ s × t = (s × t) + t
```

— while the four briefed equations recurse on the *second* argument,
and are therefore genuine theorems, each proved by `ind` on its first
argument (`Arithmetic.lean`): even `∀x. x + 0 = x` is an induction,
exactly as `0 + n = n` is in Lean itself (where `Nat.add` recurses on
the second argument — the same mirror, reflected).

**Why this form, stated plainly.**  The brief's own Option-2 sketch
("`x + 0 = x` is then the base case of a recursion on the second
argument") harbors a collapse: had the defining axiom schemas been the
briefed equations themselves, each deliverable would have been one
`allI` away from an axiom citation, `ind` would never fire, and Option
2 would have been Option 1 with different labels.  The alternative that
keeps the axioms second-argument *and* the theorems non-trivial is a
term-level recursion binder — exactly the "deeper syntactic machinery"
wall the brief anticipated (a binding term former, substitution through
it, new capture conditions).  First-argument axiomatization dissolves
the dilemma: the definition stays four schema rules with contentless
realizers (the `succNeZero`/`succInj` pattern, nothing new in the
machinery), and all four deliverables genuinely exercise Phase 2's
induction — five `ind` derivations in total, including the auxiliary
`(z + x) + y = (z + y) + x` (`plusRightCommDeriv`) that the
multiplication step needs, plus theorem-to-theorem reuse
(`timesZeroDeriv` and `timesSuccDeriv` instantiate `plusZeroDeriv`,
`plusSuccDeriv`, and the auxiliary inside their step cases).

**The equational-logic kit had to be added regardless.**  Before Phase
A the fragment could not derive *any* equation outright — no rule
produced an atomic conclusion (`eqDec` yields a disjunction; `succInj`
an implication; the `orE` escape from the negative branch is circular).
The kit is the standard first-order-with-equality apparatus for the
signature `{0, succ, +, ×}`: `eqRefl`, plus symmetry, transitivity and
one congruence per function symbol as implication schemas in the
`succInj` style, all with contentless realizers (`axiomC`), soundness
cases one line each.  A single Leibniz replacement rule was considered
and rejected: it subsumes the kit but drags a formula parameter and two
`SubstOK` side conditions into every use site, and its soundness case
needs `MR_subst` gymnastics; the per-symbol kit keeps both the
machinery cases and the derivations trivial.

**Bound-variable discipline** (`Arithmetic.lean`): `∀`-elimination's
no-capture condition forbids instantiating `∀x∀y. φ` at terms
containing `y`, so the two-variable lemmas exist in α-variant form
where needed — `plusSuccDeriv'` (bound variables 2, 3) is derived from
the deliverable `plusSuccDeriv` by instantiate-and-regeneralize (allE
twice at fresh variables, allI twice), not re-proved; the auxiliary
binds 2, 3, 4 outright.

**Machinery cases added, none silent**: `extract`/`derivBound` (ten
`axiomC` dispatches; bounds 0/1/2 by implication depth), `soundness`
(ten one-line truth cases), `extract_tracked` (ten junk-family cases),
and — the one substantive continuity touch — `termEval_continuous`
gains `plus`/`times` via the pre-existing `continuous2_comp₂`, keeping
`allE`'s term-value reads continuous over the extended signature.
`extract_continuous` therefore covers every new rule; the eight
`#print axioms` checks live in `Arithmetic.lean` and run at every
build (outputs quoted at the top of this file).

**Out of scope, per the brief**: hereditary base-`k` notation and
anything Goodstein-specific (Phase B); `TI(ε₀)` (Phase C); any
strength claim beyond the two operations and their four equations.

## Phase B (hereditary base-k and the Goodstein sequence): COMPLETE

**Scope, stated plainly per the brief**: this phase makes Goodstein's
theorem *expressible* and certifies the definitions; it does **not**
prove Goodstein's theorem, does not touch `TI(ε₀)` or ordinal
notations, and no such claim is made anywhere.  Those are Phases C/D.

### The encoding decision (the load-bearing choice)

**A hereditary base-`k` representation is a term of the fragment's own
syntax, in one distinguished free variable — variable `0`, "the
base".**  `hrep k n` (`Goodstein.lean`) is the term
`x^(hrep k e)·c + hrep k r` over `{0, succ, +, ×, exp}`, exponents
hereditarily in the same shape.  Justification:

- *Bumping the base is not an operation at all* under this encoding —
  it is evaluating the **same term** at base `k + 1`
  (`hrep_eval_bump`), which is the mathematical essence of a Goodstein
  step.  The reference repository's base-change `f` does exactly this
  (it maps `HBase base h → HBase (base+1) _` leaving the tree
  untouched); our encoding makes that structural fact definitional.
- *Existence is a derivable equation, not an axiom*: the certifying
  evaluator `hrepSubstDeriv` proves, inside the fragment,
  `(hrep k n)[base := b̂] = (value)̂` for every base numeral, from the
  recursion axioms of `+`/`×`/`exp` alone; `hrepSelfDeriv` is its
  existence instance `(hrep k n)[base := k̂] = n̂`.  No axiom about
  `hrep` exists.
- The alternative encodings the brief anticipated (Gödel-coded digit
  sequences via pairing arithmetic, or `pairPT`-level realizer
  structure) would put the representation *outside* the term language
  or demand a coding apparatus (`div`/`mod`/β-function) far heavier
  than Phase D needs.  The fragment's own terms already *are* finite
  trees over exactly the right signature.

The grammar of representations is `HTerm` (`Prop`-valued: base
variable, `zero`, `succ`, `+`, `×`, `exp` — nothing else), with
`hrep_hterm` and `HTerm.vars_eq_zero` the well-formedness facts.

### The `bump` compromise, flagged

`bump`'s recursion is course-of-values *through the hereditary
exponent structure* — not a first-order equation schema over open
terms.  It therefore enters the fragment by its **numeral graph**
(`bumpNum : ⊢ bump k̂ n̂ = (bumpN k n)̂`) plus zero-absorption
(`bumpZero`, a genuine term schema).  The semantic characterization
"`bump` is the representation read at the next base" is **derived**,
per numeral instance, as `bumpHrepDeriv` — proved from `bumpNum` and
the certifying evaluator, not axiomatized.  Open-term decomposition
axioms for `bump` (for `ind` proofs *about* `bump` in Phase D, if the
descent argument needs them fragment-side) are deliberately deferred;
what Phase D certainly needs value-side is already here.  `pred`,
`exp`, and `good` need no such compromise: their defining equations
are honest first-order schemas (`good`'s recursion `goodZero`/
`goodSucc` is exactly the sequence's definition, and the fragment
*computes* the sequence from it: `goodComputeDeriv`, e.g. the closed
theorem `⊢ good 4̂ 1̂ = 26̂`).

### Uniqueness: deferred, and why that is safe

Existence is proved (meta: `hrep_eval_self`; fragment:
`hrepSelfDeriv`, both unconditional in `k` — degenerate bases `k ≤ 1`
yield the one-digit representation and the identity bump, so no
`k ≥ 2` side condition contaminates the statements).  Uniqueness —
canonicity of digit bounds (`c < k`) and exponent ordering, the
reference's `NFBelow`/`NF` layer — is **deferred**: every object Phase
D consumes factors through the *deterministic function* `hrep`; no
statement in this development quantifies over "some representation of
`n`", so canonicity is never load-bearing here.  It becomes Phase-D
work exactly if the ordinal assignment is defined on arbitrary
`HTerm`s rather than on `hrep`'s image.

### Implementation note: fuel, not well-founded recursion

`hlog`/`bumpN`/`hrep` recurse structurally on fuel `= n` (adequacy:
`hlog_lt`, `pow_hlog_le`) instead of well-founded recursion or
Mathlib's `Nat.log`, because `WellFounded.fix` does not reduce in the
kernel: the concrete cross-checks (`goodN_four` etc.) are `rfl`, and
`goodFourOneDeriv`'s type `numeral (goodN 4 1) = numeral 26` checks by
kernel computation.  Division, modulus and powers are
kernel-accelerated, so only the logarithm needed the treatment.

### Cross-check against `WilliamAngus/Goodstein` (reference only)

Checked against `Goodstein/HBase.lean` and `Goodstein/Goodstein.lean`
of that repository (classical Mathlib development; no code imported —
their machinery proves facts about `ℕ`/ordinals directly, ours must
live inside the derivation system):

- `hrep` ↔ `HBase.ofNat`; term shape `x^e·c + r` ↔ constructor
  `hadd i aᵢ rest ↦ base^(eval i)·aᵢ + eval rest`; checked at
  `n = 4, k = 2`: both produce `2^(2^(2^0))` (theirs as a tree, ours
  as the term with base variable), value `4`.
- `bumpN` ↔ `eval ∘ f` (their base replacement): `bumpN 2 4 = 27 =
  3^(3^(3^0))`, kernel-verified (`bumpN_two_four`).
- `Term.gstep`/`pred (bump …)` ↔ their `G = (f …).pred`; value at
  `(2, 4)` is `26` both ways.
- `goodN`/`good` ↔ `goodsteinSequence start h n i` at `start = 2`:
  their step `i → i+1` applies `G` at base `start + i = 2 + i`; ours
  bumps base `s + 2` at step `s → s+1` — the same convention, no
  off-by-one (the brief's explicit worry).  Values kernel-verified:
  `goodN 4 = 4, 26, 41, 60, …` (`goodN_four`) and
  `goodN 3 = 3, 3, 3, 2, 1, 0, 0` (`goodN_three`), the classical
  sequences.
- Their `HBase.pred` ↔ our `pred` symbol (truncated predecessor);
  their `NFBelow`/`NF` ↔ our deferred canonicity layer (above).

### File placement

`Syntax.lean` holds only what must live with `Term`/`eval`/`Deriv`:
the value-level functions (`hlog`, `bumpN`, `goodN`), `numeral`, the
four constructors, and the twelve rules.  Everything else — `hrep`,
the grammar, the meta theorems, the derivation-formers, the certifying
evaluator, the certification block — is the new `Goodstein.lean`
(importing `Arithmetic.lean`).  Machinery cases added with no silent
gaps: `extract`/`derivBound`/`soundness`/`extract_tracked` (twelve
each) and `termEval_continuous` (`pred`/`exp`/`bump`/`good` via the
existing `continuous2_comp₂`); `extract_continuous` covers every new
rule, and the four `#print axioms` checks in `Goodstein.lean` run at
every build (outputs quoted at the top of this file).

## Phase C (transfinite induction up to `ε₀`): COMPLETE

**Scope, stated plainly per the brief**: this phase adds the rule
`tiEps0`, extracts and certifies its realizer, and proves that realizer
continuous.  It does **not** prove Goodstein's theorem (Phase D), makes
**no** conservativity/consistency/strength claim about the extended
fragment, does not claim (and does not prove) that the fragment fails to
derive the rule — that is standard metatheory for PA, invoked only as
framing — and does not generalize beyond `ε₀`.

```
∀x. (∀y. y ≺ x → φ(y)) → φ(x)
─────────────────────────────  (tiEps0)
          ∀x. φ(x)
```

### The representation decision: notations are natural-number codes

The fragment has **one sort** — its variables range over `ℕ` and its
atomic formulas are equations — so `tiEps0`'s `∀x`/`∀y` cannot range over
a separate type of notations, and `y ≺ x` cannot be a new atomic
predicate.  Both are therefore *coded*: `x`, `y` are natural numbers read
as Cantor-normal-form trees, and `y ≺ x` is the equation
`prec y x = succ zero`, `prec` being a new function symbol whose value
semantics is the characteristic function of the order (`oltN`).  The
coding (`Epsilon0.lean`) is

```
code 0                      ↦ the ordinal 0
mkO e c r = ⟪e, ⟪c, r⟫⟫ + 1  ↦ ω^(e)·(c+1) + (r)
```

and it is a **bijection** `ℕ ≅ {CNF trees}` (`mkO_oE_oC_oR`): the rule's
`∀x` ranges over exactly the notations, with no undecodable codes.

*One tempting alternative is a trap, and is worth recording.*  Since
Phase B already represents `n` hereditarily in base `k`, one could code a
notation by the natural number whose hereditary base-2 representation it
is — no new coding at all.  That collapses the phase: the map
`n ↦ ord₂(n)` is *order-preserving*, so `≺` becomes `<` on `ℕ`, and
`tiEps0` becomes ordinary course-of-values induction, derivable from
Phase 2's `ind`.  (Hereditary base-2 reaches only ordinals whose Cantor
normal form has all coefficients `1`, an initial segment of order type
`ω` — which is exactly why it is order-isomorphic to `ℕ` and exactly why
it is useless here.)  The coding above avoids this: it is not
order-preserving, and the kernel-verified Goodstein instance in
`TransfiniteInduction.lean` shows the descent `9 ≻ 2 ≻ 10 ≻ 3 ≻ 1 ≻ 0`
*increasing* numerically at its second step.

### Canonicity: load-bearing here — the Phase-B flag, closed

Phase B deferred canonicity of hereditary representations and flagged
that it becomes load-bearing "exactly if the ordinal assignment is
defined on arbitrary `HTerm`s".  This phase quantifies over arbitrary
notations, so the question was checked directly, as the brief required.
**The answer is that canonicity is not optional, and the failure is not
subtle.**  On arbitrary CNF trees the comparison admits an infinite
descending chain:

```
ω  ≻  1 + ω  ≻  1 + (1 + ω)  ≻  1 + (1 + (1 + ω))  ≻  …
```

Every step wins by comparing head exponents (`0 ≺ 1`), and every term in
the chain denotes the *same* ordinal `ω`, since `1 + ω = ω`.  Two
representations of one ordinal, ranked strictly — precisely the ambiguity
Phase B could defer.  Machine-checked witnesses:
`precB_onePlus_omega`, `precB_onePlus_onePlus_omega`,
`nfB_onePlus_omega`.

Resolution, per the brief's first option: the order the rule uses
(`oltB`) is the comparison **conjoined with the normal-form predicate**
`nfB` — hereditarily, the remainder's head exponent strictly below the
head exponent.  This is the `NFBelow`/`NF` layer Phase B deferred, now
built.  Two consequences worth being explicit about:

* the rule's *conclusion* is still unrestricted (`∀x φ(x)` for every
  natural number, not only for normal codes): a non-normal code has no
  `≺`-predecessors, so progressiveness proves `φ` of it outright.  No
  side condition of `tiEps0` mentions normality;
* nothing in the phase quantifies over "some representation of an
  ordinal" — the assignment `ordOf` is again a deterministic function,
  as `hrep` was.

### What Lean needed — the brief's prediction, corrected

The brief predicted that no well-foundedness theorem would be needed:
the recursor was to be built by structural recursion on the notation's
subterms, and Lean's acceptance of that recursion was to be the formal
counterpart of Gentzen's "direct inspection of a concretely presented
notation system".  **The prediction does not hold, and the reason is
structural, not technical**: `≺`-descent is not subterm descent.  From
`ω^ω` one descends to `ω^2·2 + ω·2 + 2`, a *larger* tree — Phase B's own
numbers exhibit it (`hrep 2 4` is `ω^ω`; one Goodstein step lands on the
three-summand notation for `26`).  A recursion that only reaches
subterms cannot reach the predecessors the rule quantifies over, so no
amount of care with the recursion's shape avoids the issue.

So `Epsilon0.lean` proves **`oLt_wf`**, well-foundedness of `≺` on normal
forms, and `tiRecC` is `WellFounded.fix` on it.  The brief's *point*
survives intact, and in a sharper form than the structural version would
have given:

> The proof needs no ordinals, no `Classical`, and nothing beyond what
> Lean's own inductive types provide: three nested inductions —
> accessibility of the head exponent (outer), the coefficient (middle,
> ordinary strong induction on `ℕ`), accessibility of the remainder
> (inner, itself supplied by the outer hypothesis, since a normal form's
> remainder has a smaller head exponent) — matching the three ways one
> notation can precede another.  Gentzen's answer to Hilbert's programme
> was that inspecting an explicitly presented notation system convinces
> us it is well-ordered, and that this conviction is not reducible to the
> arithmetic it justifies.  Here that inspection is a short induction the
> kernel checks, and its cost is visible in the build: `oLt_wf` needs
> `[propext, Quot.sound]`, strictly less than the
> `[propext, Classical.choice, Quot.sound]` of the realization theorems
> it underwrites.  (The other half of Gentzen's point — that the
> *arithmetic* cannot return the favour — is standard metatheory for PA,
> not something proved here for this fragment; see the citation note.)

### `Classical.choice` had to be kept out of the *definition* — and that forced a hand-rolled pairing

A constraint that shaped the module and is worth recording because it is
easy to trip over: `tiRecC`'s **definition** mentions `oLt_wf`, so every
axiom of the well-foundedness proof is inherited by `extract`, hence by
`extract_continuous`, whose budget is `[propext, Quot.sound]`.  Two
things had to be dealt with:

* **Mathlib's `Nat.pair`/`Nat.unpair` cannot be used.**  Its inverse goes
  through `Nat.sqrt`, and *every* Mathlib lemma about that pairing
  (`Nat.pair_unpair`, `Nat.unpair_left_le`, …) depends on
  `Classical.choice` — measured, not assumed.  `Epsilon0.lean` therefore
  builds the triangular (Cantor) pairing from scratch: `tri` structurally,
  the inverse by a fueled downward search, arithmetic-only proofs.  Bonus:
  it also *reduces in the kernel*, which Mathlib's does not, so the
  Phase-B practice of kernel-verified cross-checks survives into this
  phase (`ordOf_goodstein_three` is `rfl`; the descent instances are
  `decide`).
* **The `by_cases` tactic can fall back on `Classical.byCases`.**  It did,
  inside the strong-induction helper, and quietly cost `Classical.choice`
  for the whole module.  Every case split in `Epsilon0.lean` now goes
  through the explicit decidable split `dec_em`, and the file's strong
  induction is proved locally rather than imported.  This is a standing
  invariant of that module, not a one-off cleanup.

### The realizer, and the level bookkeeping the rule costs

`tiRecC φ b k = app₁ (app₁ b k̂) ⟨progressiveness argument at k⟩`, the
argument returning the recursive value at `j` when handed `j` and any
realizer of `j ≺ k`.  Two structural points:

* **The order premise carries no computational content.**  `y ≺ x` is an
  *equation* of the fragment, so realizing it *is* the fact
  `oltN j k = 1`, i.e. `OLt j k` — exactly the descent the well-founded
  recursion needs.  All of the rule's content is in the recursion; none
  is in the premise.  (This is the `succNeZero`/`axiomC` design decision
  paying off in a place where it matters: had `≺` been given
  computational content, the recursor would have had to *check* the
  descent instead of receiving it.)
* **Two `dropR φ` transports are forced by levels.**  Contrast `ind`,
  whose step formula `∀x (φ(x) → φ(succ x))` let the iterate stay at one
  ambient level (recorded in the Phase-2 section as the pleasant
  surprise that the transports were not needed).  Here the antecedent is
  *itself* a `∀→` pair, so it consumes realizers of `φ(y)` two ambient
  levels below the level at which the recursion produces them.  Hence
  `MR_tiRecC`'s hypothesis `lvl φ ≤ m₂` and `derivBound`'s
  `max (derivBound D) (lvl φ + 2) + 1`.  So Phase C is the first rule
  whose realizer genuinely needs `Transport.lean` in its *recursion*, not
  only at its binders.

`MR_tiRecC` is the phase's new theorem — the counterpart of
`MR_indRecC` one level of recursion up — proved by well-founded induction
in Lean along `≺`, the "small" induction, invoked exactly once by the
`tiEps0` case of the big induction over `Deriv`.  Its three side
conditions are each used exactly once: `x ≠ y` to read `x`'s value
through the inner binder, `SubstOK (var y) φ` for `MR_subst`, and
`¬ φ.FreeIn y` for the `MR_congr` step that discards the inner binder's
assignment.

### Generic continuity against the new combinator — answered explicitly

As with `ind`, generic continuity does not come for free (`extract_tracked`
is an induction over `Deriv`, so the rule adds a case), but the invariant
needed **no strengthening and no new closure fact**.  `tiRecC_tracked`
mirrors `MR_tiRecC`: well-founded induction along `≺` gives tracking at
each *fixed* notation, and the oracle-dependent notation code is absorbed
by `tracked_apply_nat` — the same lemma rule `ind` introduced for its
iteration count.  One simplification is worth noting: the recursor's
internal case split (`j' ≺ j`) does **not** depend on the oracle, so it
is discharged index by index and `ite_tracked` is not needed.  The two
`dropR`s are covered by `liftR_dropR_tracked`.  `CollapseDemo.lean` was
not touched, and `RealizesCtQ`/`collapse_demo` cover `tiEps0`-derivations
unchanged.

### Machinery cases added, none silent

Rule count 39 → **42**: `tiEps0`, plus `precNum` (the numeral graph of
the order) and `eqCongPrec` (its congruence schema, completing the
equational kit).  `prec` joins the signature, so `Term.eval`/`vars`/
`subst`/`eval_subst`/`eval_congr` each gain a case, as does
`termEval_continuous` (`continuous2_comp₂ oltN`).  Per-rule discipline:
`extract` + `derivBound` (three cases), `soundness` (three), and
`extract_tracked` (three).  `precNum` follows the flagged Phase-B
`bumpNum` pattern for the same reason — the comparison's recursion is
course-of-values through the notation structure, not a first-order
equation schema — and, as there, the general facts about it are proved,
not axiomatized (`Epsilon0.lean`'s order constructors).

### The bridge to Phase B, and what Phase D still owes

`ordTerm` decodes a notation code into a term of Phase B's grammar
(`ordTerm_hterm : HTerm (ordTerm c)`): the notations of this phase *are*
Phase B's hereditary representations, with the base variable read as `ω`
instead of as a numeral — no second encoding, per the brief.  `ordOf k n`
is the ordinal assignment for the Goodstein sequence, clause for clause
the mirror of `hrepAux` with `mkO` for the term constructors.  Verified
in the kernel (`TransfiniteInduction.lean`): the ordinals along `G(3)`
are `ω+1, ω, 3, 2, 1, 0` (codes `9, 2, 10, 3, 1, 0`), all normal, each
strictly `≺` its predecessor, and `ordOf 3 (bumpN 2 3) = ordOf 2 3` — the
base change leaving the ordinal fixed.

Phase D's remaining obligations are stated in that module rather than
implied: (1) `nfB (ordOf k n) = true` for `2 ≤ k` (Phase B's deferred
digit-bound/exponent-ordering facts, i.e. real `hlog` theory); (2)
`ordOf (k+1) (bumpN k n) = ordOf k n` in general (the fuels differ on the
two sides, unlike Phase B's `hrepAux_eval_bump`, so a fuel-adequacy lemma
for `ordOfAux` comes first); (3) the descent
`OLt (ordOf (k+1) (bumpN k n - 1)) (ordOf k n)`.  Only (3) uses
`tiEps0`; (1) and (2) are ordinary Phase-B-style work.

**And the gap that is not ours to close here**: the fragment still has no
`∃`, so `∀m ∃s. good m s = 0` cannot be *stated*, let alone proved (open
item 3½ in docs/internal/QUESTIONS.md, raised during Phase B and deliberately not
folded into this phase — the transfinite-induction work turned out to be
self-contained, and `∃` touches `Formula`, `MR`, the transports and the
tracking relation, which is a phase-sized change of its own).

### Citation (checked as far as the primary text allows)

The construction is the standard one for functionals defined by
transfinite recursion on a primitive-recursive ordering: W. W. Tait,
*Functionals defined by transfinite recursion*, **Journal of Symbolic
Logic 30(2) (June 1965), 155–174**, DOI 10.2307/2270132 (Zbl
0133.25202).  Its companion is *The substitution method*, JSL 30(2)
(1965), 175–192, DOI 10.2307/2270133; the similarly-dated *Infinitely
long terms of transfinite type* (in Crossley–Dummett, eds., *Formal
Systems and Recursive Functions*, North-Holland 1965, 176–185, DOI
10.1016/S0049-237X(08)71689-6) is a **different** paper and is not the
source for this construction.

Granularity, stated plainly per the house discipline — the brief asked
for this explicitly, and Phase B's Troelstra citation is the template.
**The primary text was not accessible**; this citation is at *abstract*
granularity.  Checked directly: Cambridge Core (abstract and reference
list free, body paywalled), JSTOR (403 to this environment), Project
Euclid (the legacy URL now redirects to the homepage; JSL is no longer
hosted there), Unpaywall / OpenAlex / Semantic Scholar (all report the
DOI closed with no repository copy), the Internet Archive (no item; the
1965 conference volume is present but lending-restricted with
search-inside disabled), Google Books (nothing), zbMATH Open (metadata
and reference list, no review text), and Tait's own former homepage at
`home.uchicago.edu/~wwtx/` (now 404; its 2024-10-05 Wayback snapshot
posts 20 papers, none earlier than 1981).  Both JSL reviews — Vesley,
JSL 31(3) (1966), 509–510, and López-Escobar, JSL 40(4) (1975), 623–624 —
are likewise paywalled, the former offering only a first-page image.

What the author's abstract (free, and byte-identical to Crossref's
record) *does* verify, and all that is claimed on its authority: the
paper treats quantifier-free second-order systems of primitive recursive
arithmetic extended by rules that "have the form of definition by
transfinite recursion up to some ordinal ξ (where ξ is represented by a
primitive recursive (p.r.) ordering)"; the systems are described in
**§2**, elementary closure properties in **§3**, less elementary ones in
**§§5–7**, and "the key lemma (**Theorem 1**) needed for the reduction of
these equations to transfinite recursion is simply a sharpening of the
Brouwer-Kleene idea".  No section or theorem beyond §2, §3, §§5–7 and
Theorem 1 is cited, and **the abstract does not single out `ε₀`** — it
states the recursion for a general ordinal given by a p.r. ordering — so
no `ε₀`-specific claim is made on its authority.  (The distributed
abstract also has a lacuna after "The main results of this paper are of
two sorts:" and prints subscripts inconsistent with its own gloss; both
are the publisher's transcription, not ours.)

For the `ε₀` scheme specifically the granularity available was Tait's own
later restatement, read in full: W. W. Tait, *The substitution method
revisited*, in Feferman et al. (eds.), *Proofs, Categories and
Computations: Essays in Honor of Grigori Mints*, Tributes 13, College
Publications 2010, 231–241 (Zbl 1225.03076), obtained from the archived
copy of his homepage.  There he works in "the quantifier-free system
PRA²_{ε₀} … with definition by recursion on each ordinal α < ε₀", with
"the order type ε₀ … represented in some standard way by a primitive
recursive ordering ≺ of ω with least element 0" — the setup this phase
formalizes — and attributes to the 1965 paper by number both a
conservativity result ("Tait 1965a, Theorem 4") and a bound on the
ordinals needed ("Tait 1965a, §5").  **Those numbers are Tait's own
citations, verified in the 2010 text and not checked against the 1965
text.**  Two further pointers found in the literature — a "Theorem 3" and
a page reference "p. 163" — rest on OCR and on a paywalled paper
respectively, and are therefore *not* recorded as verified.

Kirby–Paris and Gentzen are cited here only for the *framing* (that the
fragment cannot derive the rule), which this development does not prove
and does not claim.

## Phase D (Goodstein's theorem and its extracted function): COMPLETE

Four checkpoints, each built and axiom-checked separately, as the brief
required.  The results, in order.

### D0 — `∃` added to the fragment: COMPLETE

**The flagged design question, answered: `∃` needed two new rules but no
new devices.**  Its realizability clause is

    MR ρ (∃y φ) n x  ↔  MR ρ[y ↦ fstPT x (defaultPT n)] φ n (sndPT x)

— the first component read at the canonical point *is* the witness — so
it is literally the `∨` clause with the two-valued tag generalized to a
numeral.  Consequences, all of them reuse rather than new machinery:

* `exIC` is `orI₁C` with the witness numeral in place of the constant
  tag; `exEC` is `orEC` with the tag split replaced by passing the
  witness into the environment.  The same `pairPT`/`fstPT`/`sndPT` — no
  second pairing mechanism, as the brief required;
* the transports gain one case each (`liftR_ex`/`dropR_ex`), shaped like
  `∨`'s; tracking gains `exIC_tracked`/`exEC_tracked`, which are
  `orI₁C_tracked`/`orEC_tracked` with the case split deleted;
* **`∃` costs no ambient level**: `lvl (∃y φ) = lvl φ`.  Worth recording
  as the invariant behind the level discipline: binders that *consume*
  realizers (`→`, `∀`) cost a level, binders that merely *package* them
  do not.  No `derivBound` anywhere grew.

The one place `∃` is not just `∨`: elimination's side conditions
(`FreshIn x Γ`, `¬ ψ.FreeIn x`) keep the witness from escaping its
scope.  In the soundness proof they are exactly what let `CtxR_congr`
carry the context across the environment update and `MR_congr` carry the
conclusion back.

Checkpoint (`Exists.lean`, run at every build): the fragment's first
existential theorem, `⊢ ∃s. good(3,s) = 0` with witness `5`, together
with an `exE` round trip so the elimination rule is exercised too.

```
'Realizability.good_three_ex_realized'                    … [propext, Classical.choice, Quot.sound]
'Realizability.good_three_ex_round_trip_realized'         … [propext, Classical.choice, Quot.sound]
'Realizability.good_three_ex_extract_continuous'          … [propext, Quot.sound]
'Realizability.good_three_ex_round_trip_extract_continuous' … [propext, Quot.sound]
```

`extract_continuous`'s induction gained both new cases — confirmed, not
skipped: they are `exIC_tracked` and `exEC_tracked`, and the `exE` case
threads `trackedEnv_update` because the witness enters the *environment*.

### D1 — the three named obligations: COMPLETE

All three proved (`OrdinalAssignment.lean`), and the brief's question
"did (1) and (2) turn out to be ordinary work as predicted?" is answered
**no — they were the substantial part of Phase D**:

1. `nfB_ordOf` (normality of the assignment) needed logarithm theory
   Phase B never built.  Phase B used exactly two facts about `hlog`
   (`hlog_lt`, `pow_hlog_le`); canonicity needs the *maximality* half —
   `lt_pow_hlog_succ` — and from it the digit bounds (`one_le_digit`,
   `digit_lt`), the exponent ordering (`hlog_rem_lt`), monotonicity
   (`hlog_le_hlog`), and a uniqueness lemma (`hlog_of_digits`).  It also
   needed the assignment's **monotonicity** (`precB_ordOf_of_lt`), which
   is a three-case digit comparison mirroring the three order
   constructors of Phase C.
2. `ordOf_bumpN` (base change preserves the ordinal) needed, as Phase C
   predicted, a fuel-adequacy lemma first — in fact three
   (`hlogAux_eq_of_le`, `bumpNAux_eq_of_le`, `ordOfAux_eq_of_le`), each
   with its own `_succ_eq` step, since all three recursions are fueled.
   It also needed **`bumpN` to be a well-behaved function**, which Phase
   B never established: `bumpN_mono_bound` proves strict monotonicity and
   the digit bound `r < k^e → bump r < (k+1)^(bump e)` *together*, by one
   strong induction, because each case of either half consumes the other
   at a smaller argument.  That lemma is the largest single proof in the
   phase.
3. `ordOf_descent` (the Goodstein step descends) was, as predicted, short
   — given 2, it is monotonicity applied to `bumpN k n - 1 < bumpN k n`.

**A correction to Phase C's prediction, which the brief asked to be
checked rather than assumed**: Phase C guessed that (3) would be "the one
that actually uses `tiEps0`'s machinery".  It does not.  All three
obligations are value-level arithmetic about `ℕ`, with no reference to
`Deriv`, `MR`, or the recursor; `tiEps0` enters only in D2, where the
*induction* is performed.  What (3) actually needs is (2) plus
monotonicity — and monotonicity is the same digit-comparison work as
(1), so (1) and (3) share their hard core rather than being independent.

One hypothesis had to be added: obligations 2 and 3 hold for `2 ≤ k`
only.  At `k = 1` base change is not ordinal-preserving (`bumpN 1 4 = 4`,
whose base-2 ordinal is `ω^ω` but whose base-1 ordinal is the finite
`4`).  Harmless — Goodstein bases are `s + 2` — but it is a real side
condition, unlike Phase B's unconditional statements.

```
'Realizability.nfB_ordOf'         … [propext, Quot.sound]
'Realizability.ordOf_bumpN'       … [propext, Classical.choice, Quot.sound]
'Realizability.ordOf_descent'     … [propext, Classical.choice, Quot.sound]
'Realizability.bumpN_mono_bound'  … [propext, Classical.choice, Quot.sound]
```

**File placement changed** (a structural move, no content change,
reported because it touches Phase-B and Phase-C files): `hlog`, `bumpN`,
`goodN` moved out of `Syntax.lean`, their Phase-B facts out of
`Goodstein.lean`, and `ordOf` out of `TransfiniteInduction.lean`, all
into the new `OrdinalAssignment.lean`, which sits *before* `Syntax.lean`.
Forced: `Term.eval` must consume `ordOf` (Phase D adds the `ord` symbol),
and `Soundness.lean` must consume D1's theorems (the `ordDescent` case).

### D2 — Goodstein's theorem: COMPLETE

```
goodsteinTheorem : Deriv [] (Formula.all 2 (Formula.ex 4
  (Formula.eq (Term.good (Term.var 2) (Term.var 4)) Term.zero)))
```

`⊢ ∀m ∃t. good(m,t) = 0` — the genuine statement, universally quantified
over the start value and existentially over the number of steps, with no
restriction to concrete values and no bound on either quantifier.  The
`#check` of that exact type runs at every build.

The proof is the classical ordinal descent, on the induction formula

    φ(x) := ∀s. ord(s+2, good(m,s)) = x → ∃t. good(m,t) = 0

with `m` a parameter, generalized only at the end.  Progressiveness
splits on `good(m,s) = 0` (`eqDec`): if it holds, `s` is the witness; if
not, `goodSucc` rewrites the next state into `pred (bump (s+2) …)`, the
`ordDescent` axiom gives that its ordinal is `≺ x`, and the induction
hypothesis at that ordinal — instantiated at the state `s+1` — returns
the witness.

**Two things about this derivation deserve a reviewer's attention.**

*First, the one imported fact.*  `ordDescent` is an axiom schema of the
fragment whose truth is D1's `ordOf_descent`, discharged in the
`ordDescent` case of `soundness`.  This follows the precedent of Phase
B's `bumpNum` and Phase C's `precNum`, and for the same reason: the
content is course-of-values recursion through the hereditary structure,
which is not a first-order equation schema over the fragment's terms.
What the fragment *derives* is everything else — the case split, the
gluing of `goodSucc` with the descent, the transfinite induction, and the
witness.  Stated plainly: the arithmetic of the ordinal assignment is
metatheory (proved in Lean, D1); the logic is the fragment's.

*Second, a substitution obstacle and the technique that resolves it.*
The fragment's substitution is naive, with `SubstOK` forbidding capture
outright rather than renaming.  The step wants to instantiate the
induction hypothesis `∀y. y ≺ x → φ(y)` at `ord(s+3, good(m,s+1))`,
which mentions `s` — and `s` is bound in φ.  That is a **genuine**
capture, not a spurious side condition: the substituted occurrence sits
inside φ's own `∀s`.  The derivation therefore **names the ordinal**: it
proves `∀z. (z = ord(s+3,good(m,s+1))) → ∃t. good(m,t) = 0`, instantiating
the induction hypothesis at the *variable* `z` (which captures nothing),
and then instantiates *that* at the term, with `eqRefl`.  One extra `∀`
in the derivation, nothing in the extract's structure.  This is the
general technique for naive-substitution calculi, and it is the reason
the fragment never needed α-renaming machinery.

```
'Realizability.goodstein_realized' … [propext, Classical.choice, Quot.sound]
```

The standard three, as expected — `oLt_wf`'s reduced set does *not*
propagate here, because realization goes through `soundness`, which uses
`Classical.choice` in many earlier cases.  (Continuity does keep the
reduced set; see D3.)

### D3 — the extracted function: COMPLETE, with one honest limitation

1. **Continuity applies with no modification.**
   `goodstein_extract_continuous` is a one-line corollary of
   `extract_continuous`; the generic-continuity discipline covered
   `tiEps0`, `exI`/`exE` and `ordDescent` without a per-derivation
   certificate, exactly as designed.  `[propext, Quot.sound]` — the
   reduced set survives all of Phase D.
2. **`RealizesCtQ` gives a genuine class**: `goodsteinRealizesCtQ`, the
   theorem's program as an element of `CtQ 2`.
3. **The extracted function is correct and it runs.**
   `goodsteinStopTime m` reads the witness off the realizer at ambient
   12 (the derivation's own bound).  Two separate claims, deliberately
   kept apart:

   * `goodsteinStopTime_spec : ∀ m, goodN m (goodsteinStopTime m) = 0` —
     proved from `soundness`, **for every** `m`.  This is the real
     payoff: the extracted number is a stopping time at values no
     evaluator will ever reach.
   * The evaluator's output, verbatim from the build log of
     `GoodsteinExtraction.lean`:

     ```
     info: Realizability/GoodsteinExtraction.lean:99:0: 0
     info: Realizability/GoodsteinExtraction.lean:100:0: 1
     ```

     i.e. `#eval goodsteinStopTime 0` prints `0` and
     `#eval goodsteinStopTime 1` prints `1`, both correct
     (`goodN 1 1 = 0`, kernel-checked as `goodN_one_at_one`).  Each takes
     under a second.

**The limitation, reported rather than papered over.**  `m = 2` did not
finish.  Measured, all on this machine (24 cores, single-threaded
evaluation): 110 s at the certified ambient 12 — terminated, no output;
110 s at ambient 3 (uncertified — see the Phase-D4 correction below,
this run was not a scaled-down version of the same computation); 900 s at ambient 12
— terminated, no output, with the evaluator's resident memory past
1.7 GB and still climbing.  So the failure is not a slow constant, it is
the space and time of an exponentially branching re-evaluation.  `m = 3`
was not attempted.  For contrast, the *value-level* sequence is trivial
here: `G(2) = 2, 2, 1, 0` (`#eval` returns instantly), so the stopping
time being computed is `3`.  The cause is not the Goodstein numbers, which are tiny here
(`G(2) = 2, 2, 1, 0`), but the *extract's* shape: every recursive value
is wrapped in two `dropR` transports, and `app₁`/`abs₁` duplicate their
argument at each application, so the realizer re-evaluates its own
recursive calls exponentially often in the number of Goodstein steps.
Nothing memoizes.  So the honest summary is: the extraction pipeline is
**executable, and executes correctly at 0 and 1**, but is not an
efficient program — the certified correctness statement
(`goodsteinStopTime_spec`) is what carries the content at larger inputs.
Making the extract efficient (sharing, or a transport-free realizer for
this derivation shape) is a genuine open engineering problem and is not
claimed to be solved here.

**One change to earlier phases was needed for D3**, and is flagged:
`noncomputable` was removed from the transports (`Transport.lean`) and
the extraction combinators (`Extraction.lean`).  Those markers were
defensive, not necessary — Lean compiles all of them, `PureType` values
included — and without the change `#eval` on the extract is impossible
("no executable code").  No definition's content changed; only the
modifier was deleted.

## Phase D4 (making the extracted function fast): DIAGNOSED, NOT FIXED

> **Superseded in one respect by Phase D6** (below): D4's headline
> measurement — 2377 recursor entries, 2376 at the same code — is real but
> is *not* a cost proxy, because producing the recursor's value at a code
> is `O(1)` closure allocation.  D6 collapses those entries completely
> (measured: 2376 hits, 0 misses) and the wall clock does not move.

The brief asked for a profile first and a `@[csimp]`-based fix second.
The profile came out clean and decisive; the fix does not exist under the
brief's own constraint that every replacement be proof-backed.  Both
halves are below, with the measurements that support them.

**No Lean file changed in this phase.**  `goodsteinStopTime_spec`, its
statement and its proof, `soundness`, and the extraction algorithm are
byte-for-byte as they were at the end of D3 — `git diff` for D4 touches
only this file and docs/internal/QUESTIONS.md.

### The measurements

All at ambient 12 (the derivation's own bound, i.e. the level at which
the extract is certified), on this machine, by attaching tracing
implementations to the primitives with `@[csimp]` lemmas proved by `rfl`
(`dbg_trace` is definitionally transparent, so the traced pipeline is the
same function).

| | `m = 0` | `m = 1` |
|---|---|---|
| Goodstein steps to `0` | 0 | 1 |
| `tiRecC` fix-body entries | 1 | **2377** |
| distinct codes entered at | 1 | **2** |
| entries at code `0` | — | **2376** |
| `app₁` calls | 6 | **346 437** |

Two further measurements:

* **Ambient-independence.**  The same count at ambient 13: 2376 entries
  at code `0`, identical.  So the multiplier is *not* the pure-type
  transport towers, whose depth grows with the ambient level.
* **Per-entry cost is constant**: 346 437 / 2377 ≈ 146 `app₁` calls per
  entry.  Total work is therefore (entries) × (a constant), and the
  entry count is the entire story.

### Cause 1 (`WellFounded.fix`) — ruled out, with evidence

The brief asked whether evaluating `tiRecC` re-derives accessibility
proofs at every recursive call.  **It does not.**  In the generated C
(`.lake/build/ir/Realizability/Extraction.c`) the recursion is compiled
to a direct self-recursive function,
`l_WellFounded_fixC___at___00Realizability_tiRecC_spec__0`, whose body
calls itself, `l_Realizability_natPT`, `l_Realizability_app_u2081` and
`l_Realizability_oltB` — and

```
grep -cE "lean_Acc|Acc_rec|WellFounded_apply" .lake/build/ir/Realizability/Extraction.c
0
```

`Acc` is a `Prop`, so the accessibility argument is erased before code
generation; the decidable test `oltB` is all that survives of it.

Worth stating because it looks like a contradiction with Phase B: that
phase avoided `WellFounded.fix` for `hlog`/`bumpN`/`goodN` for a
*different* evaluator.  Kernel reduction (`rfl`, `decide`) does not erase
proofs, so `WellFounded.fix` genuinely blocks there.  Compiled evaluation
(`#eval`) does erase them.  Both statements are true; they are about
different machines.

### Cause 2 (unshared duplication) — confirmed, but not where the brief expected

The blowup is re-evaluation of an **identical** recursive call: 2376 of
the 2377 entries are at the same code `0`, requested over and over.  The
per-step multiplier ≈ 2400 is the number of points at which the
surrounding extract applies the recursor's abstraction — the extracted
derivation consults its induction hypothesis that many times per
Goodstein step.  Extrapolating: ≈ 1.4 × 10¹⁰ entries at `m = 2` (three
steps) and ≈ 5 × 10¹⁶ at `m = 3` (five steps).

But it is *not* redundant substitution inside a primitive, which is the
form the brief anticipated and the form `csimp` could repair.  Three
sharing variants were written and proved, then measured:

* `orECFast` — reads the major premise's `d n` once instead of twice
  (once for the tag, once for the payload);
* `exECFast` — the same duplication in `∃`-elimination;
* `tiRecCFast` — reads the notation code `ζ (defaultPT _)` once instead
  of twice (once to decide `≺`, once to recurse), and binds the
  recursive value before the inner abstraction so it is not rebuilt per
  application point.

All three are `let`-rebindings, hence definitionally equal, so
`@[csimp] theorem … := rfl` type-checks for each; all three were
compiled into the pipeline.  **Measured effect: none.**  `tiRecC`
entries 2377 → 2377; `app₁` calls 346 437 → 346 437, exactly.  Lean's
compiler was already sharing those subexpressions.  They were reverted
rather than shipped: a `csimp` that changes nothing, documented as an
optimization, would misrepresent the state of the code.

### Why no proof-backed `csimp` can fix this

The duplicated work is not *inside* any primitive; it is *how many times
the surrounding term calls it*.  `csimp` replaces what a function
computes, never how often its caller calls it — so no replacement of
`app₁`, `abs₁`, `dropR` or `tiRecC`, however clever, can collapse 2376
identical calls into one.

Collapsing them requires memoization keyed by the notation code, i.e.
state that survives across *independent evaluations of the same
expression*.  In pure Lean that is not available as a function provably
equal to the original: `Thunk` memoizes a single value, not a
`ℕ`-indexed family of function values; a lazily-expanded infinite trie of
`Thunk`s would need coinduction; and a `HashMap`/`IO.Ref` cache can only
be attached with `@[implemented_by]`, which carries **no** proof
obligation and would make every `#eval` in this development depend on
unverified code.  Since the brief requires each replacement to be backed
by a checked equality proof, that route was not taken.

What *would* fix it, recorded and out of scope: reduce how often the
extracted derivation consults its induction hypothesis (a change to the
derivation), lower `derivBound` so fewer transports are built (likewise),
or give `Fam` a memoizing representation (a change to the extraction
algorithm).  All three change the extract itself, which this brief
explicitly excludes.

### `m = 2` and `m = 3`: a performance limit, not an astronomical answer

The brief asks that these not be conflated.  They are not the same here,
and the distinction is unambiguous: **the answers are tiny.**
`G(2) = 2, 2, 1, 0`, so the stopping time is `3`; `G(3) = 3, 3, 3, 2, 1,
0`, so it is `5`.  Both are computed instantly at the value level
(`goodN`, kernel-verified in Phase B).  What is astronomical is only the
*extract's re-evaluation count* at those inputs.  So this is entirely a
performance limitation of the extracted term's evaluation, and the true
answers are small and known.

`#eval goodsteinStopTime 2` therefore still produces no output (measured
again after the sharing variants: no output at 200 s).  `m = 3` was not
attempted.  The certified content is unaffected:
`goodsteinStopTime_spec` proves `goodN m (goodsteinStopTime m) = 0` for
every `m`, including 2 and 3, and it needs no evaluation.

### Correction to a Phase-D3 measurement

D3 reported a 110 s run "at ambient 3 (uncertified, diagnostic only)" as
if it were a smaller instance of the same computation.  **It is not**,
and the D3 text has been amended.  Below the derivation's bound the
extract's reads produce junk codes, and `oltB` on a junk code runs
`unTri`'s linear search over a huge number — that run was measuring
garbage arithmetic, not a scaled-down version of the certified
computation.  The valid scaling evidence is the ambient-independence
measurement above (12 versus 13, identical counts).

## Phase D5 (closing the `ordDescent` gap): the composite is now DERIVED

D2 proved Goodstein's theorem in the fragment but imported its core step
— *bump the base, subtract one, the ordinal strictly decreases* — as a
single axiom schema.  That was the honest weak point: the fragment proved
the theorem relative to the very fact that makes it true.  This phase
removes that import.

### What changed

The schema `ordDescent` is **deleted**.  In its place the fragment has
three schemas, each a property of one function symbol, and each
corresponding to exactly one Phase-D1 theorem:

| schema | says | discharged by |
|---|---|---|
| `ordBump` | base change leaves the ordinal alone | `ordOf_bumpN` |
| `ordPredLt` | the assignment strictly decreases at `pred` | `olt_ordOf_of_lt` |
| `bumpNeZero` | bumping a nonzero number gives a nonzero number | `bumpN_ne_zero` |

and the composite is **derived inside the fragment**
(`OrdinalDescent.lean`, `Deriv.ordDescent`): from `n ≠ 0`, `bumpNeZero`
gives that the bumped value is nonzero, `ordPredLt` at the bumped base
gives the strict decrease, and `ordBump` rewrites the right-hand side
back to the original base — the rewriting step being congruence of
`prec`.  D1's obligation 3, `ordOf_descent`, is no longer assumed
anywhere; it survives in `OrdinalAssignment.lean` as the semantic twin of
what the fragment now proves.

Rule count 46 → 48 (one removed, three added).

### The derivation is not vacuous, and that is checked

`ord_descent_via_fragment` reads the *derived* descent back through
`soundness` and recovers the semantic statement

    2 ≤ k → n ≠ 0 → OLt (ordOf (k+1) (bumpN k n - 1)) (ordOf k n)

using only the three component schemas — not `ordOf_descent`, which is
proved independently.  Fragment-side derivation and metatheorem now agree
without either being defined in terms of the other, which is the check
that the syntactic proof has real content.

```
'Realizability.ord_descent_realized'           … [propext, Classical.choice, Quot.sound]
'Realizability.ord_descent_via_fragment'       … [propext, Classical.choice, Quot.sound]
'Realizability.ord_descent_extract_continuous' … [propext, Quot.sound]
```

`goodsteinTheorem` is **untouched**: the derived former has the same name
and signature as the deleted constructor, so `GoodsteinTheorem.lean`'s
derivation text is unchanged, the theorem's type is unchanged (the
spelled-out `#check` still runs at every build), and
`goodsteinStopTime`'s `#eval` still prints `0` and `1`.

### What this does *not* achieve — stated plainly

The three schemas remain **axioms of the fragment**, justified by
theorems proved in Lean rather than by derivations in the object theory.
The metatheoretic dependence is the same size as before in logical
strength; what changed is its *shape*: no imported fact is now about the
Goodstein sequence, or about a step of anything.  Each is one general
property of the ordinal assignment or of `bump`, and the Goodstein
reasoning — the case split, the descent's composition, the transfinite
induction, the witness — is entirely the fragment's own.

So: the gap is narrowed from "the theorem's core lemma is assumed" to
"three general properties of the assignment are assumed".  It is not
eliminated, and this file does not claim it is.

### What full internalization would take (scoped, not attempted)

To derive the three schemas *inside* the fragment rather than import
them, the fragment would need to become a usable arithmetic theory:

1. **New symbols with recursion equations**: `hlog`, `div`, `mod` — the
   digit decomposition is not expressible without them.
2. **An order relation.**  The fragment's atomic formulas are equations
   only.  Since D0 there is `∃`, so `m ≤ n` can be encoded as
   `∃c. m + c = n`, but every arithmetic law about it (transitivity,
   antisymmetry, compatibility with `+`/`×`/`exp`) then has to be derived.
3. **Course-of-values induction**, derived from `ind` by the standard
   bounded-quantifier trick — which needs 2 first.
4. **Phase D1 redone syntactically**: `lt_pow_hlog_succ`, the digit
   bounds, `hlog_of_digits`, `bumpN_mono_bound` (a nested strong
   induction over powers and division), `ordOf_bumpN`, monotonicity.

That is a research-scale project — building a working fragment of
elementary number theory inside the object theory — not a phase, and it
would roughly double the size of the development.  Recorded here so the
decision is informed rather than implicit.

## Hydra project — see also `docs/first-order/HYDRA.md`

The Hydra work runs to eight phases and has its own self-contained
document, **`docs/first-order/HYDRA.md`**: what is proved, what is assumed, what is out of
scope, the phase map, the trace, and the reproduction commands.  The
sections below remain the authoritative per-phase record — rationale,
flagged deviations, measurements — and `docs/first-order/HYDRA.md` is the map over them.

## Hydra project, Phase H1 (tree encoding) and H2 (the move): COMPLETE

A new mathematical layer on top of the finished Goodstein work, reusing
the existing `TI(ε₀)` machinery and the realizability pipeline unchanged.
This entry covers H1 and H2 only; H3 (the ordinal assignment and its
descent proof) was the hard part and is written up in the sections that
follow, as are H4–H6.  *(Written when H3 had not been started; the
sections below record how it went and supersede the forward-looking
paragraphs in this one.)*

### H1 — finite rooted trees as natural numbers

`Hydra.lean`.  A hydra is a mutual pair of inductives — `Hydra` (a node
carrying a `Forest`) and `Forest` (a list of hydras) — rather than the
nested `Hydra := List Hydra`, because the encode/decode proofs are mutual
structural recursions and nested inductives make those fight the
recursor.  The coding is the standard list coding through **Phase C's
existing pairing**:

    ⌜nil⌝ = 0,   ⌜cons h f⌝ = ⟪⌜h⌝, ⌜f⌝⟫ + 1,   ⌜node f⌝ = ⌜f⌝

No new coding primitive was introduced.  That matters for the reason
Phase C recorded: Mathlib's `Nat.pair`/`Nat.unpair` are unusable in this
development (every lemma about them carries `Classical.choice`, and
`Nat.unpair` does not reduce in the kernel), so `Epsilon0.lean`'s
hand-rolled triangular pairing is what everything is built on.

**Both round trips are proved**, which is what makes "the fragment's `∀x`
ranges over exactly the hydras" exact rather than approximate:

* `encodeF_forestOf : encodeF (forestOf n) = n` — every natural number is
  a code;
* `hydraOf_encodeH : hydraOf (encodeH h) = h` — every tree is recovered
  from its code.

```
'Realizability.encodeF_decodeF' … [propext, Quot.sound]
'Realizability.decodeF_encodeF' … [propext, Quot.sound]
'Realizability.hydraOf_encodeH' … [propext, Quot.sound]
'Realizability.encodeF_forestOf' … [propext, Quot.sound]
```

Choice-free, as the constraint requires.  Decoding is fueled with
`pr1`/`pr2` decreasing the code, exactly as everything else in this
development.  The four smallest codes are kernel-checked
(`hydraOf_small`): `0` a bare head, `1` a root with one head, `2` the
two-deep chain, `3` a root with two heads.

### H2 — the cutting-and-regrowth step

**The rule implemented, stated precisely** (its citation is being
verified separately; see the note below):

* a **head** is a leaf — a node with no children;
* Hercules chops one head.  Let `p` be the head's parent;
* if `p` is the **root**, the head is removed and nothing grows;
* otherwise let `g` be `p`'s parent.  After the head is removed from `p`,
  the hydra grows `n` extra copies of the resulting subtree at `p`, all
  attached to `g`; the modified `p` stays where it is.

Two parameters are deliberately left open, so that the eventual theorems
quantify over them rather than baking in one reading: **which** head is
chopped, and **how many** copies grow.  `cutH n : Hydra → Hydra × Bool`
returns the new subtree together with the one bit the caller needs —
"the head I chopped was a direct child of me" — which is exactly what
tells a node whether it is the grandparent and must grow the copies.  At
the root that bit is discarded, which *is* the "parent is the root,
nothing grows" clause.

`hydraStepN : ℕ → ℕ → ℕ` is the move on codes (decode, step, re-encode) —
the value-level function a fragment symbol will evaluate by in H4 — and
`hydraSeqN start s` is the battle with `s + 1` copies grown at step `s`.

**Worked examples, kernel-verified by `rfl`** (`hydraSeq_two_heads`,
`hydraSeq_chain`, `hydraSeq_one`):

| start | battle (codes) | reading |
|---|---|---|
| `1` | `1, 0` | one head at the root: chopped, nothing grows |
| `3` | `3, 1, 0` | two heads at the root: chopped one at a time |
| `2` | `2, 3, 1, 0` | **the hydra grows**: emptying the child makes the root grow a copy of it, so one child with one head becomes two heads |

The third row is the phenomenon in miniature, and the reason H3's ordinal
assignment is needed at all: the node count goes *up* at that step, so
nothing about the tree's size is decreasing — only the assigned ordinal
is.

### The citation, now checked — and two corrections it forced

A dedicated research pass closed the item flagged below.  Three findings
change what this section originally said.

**The rule implemented is Kirby–Paris, and the battle lengths confirm
it.**  There are two *different* games in circulation and they are widely
conflated.  Wikipedia introduces a "simple hydra game" first — copies are
**bare leaves attached to the parent** — whose path-hydra battle lengths
are `1, 3, 11, 1114111`.  Kirby–Paris is the grandparent rule with the
whole post-cut subtree copied, and its lengths are `1, 3, 37, >` Graham's
number.  `37` is therefore the discriminating number: a wrong attachment
point or copy count would not land on it.  (Googology Wiki hosts a
38-state bracket trace of that 37-step battle on the 4-node path,
`File:Hydra3.svg`.)

**Verified in-session.**  Running our own `hydraStep` on the path hydras
gives

```
path 1 (2 nodes) → 1      path 2 (3 nodes) → 3      path 3 (4 nodes) → 37
```

— the published Kirby–Paris values, `37` included.  Paths 1 and 2 are
`rfl`-checked at build time (`battleLen_small`); path 3 takes ≈ 98 s, so
it is run out of band (`#eval battleLen 200 1 (encodeH (path 3))`, output
`37`) and recorded here rather than on every build.  **Superseded by
Phase H8**: the tree-level evaluator does the same battle in under a
second, and all three values are `#guard`ed at every build.  The research pass
independently reports the same 37 under the *rightmost* strategy with
different intermediate states, which is a further check: our strategy is
leftmost, and the length is strategy-independent.

Getting there needed both halves of the pairing made fast, and both are
proved rather than assumed:

* `tri` gained a constant-time closed form (`tri_eq_triFast`, via
  `2 * tri n = n * (n + 1)`, so no division enters the induction);
* `unTri` gained an `O(log n)` **binary search** (`unTriBin`), proved
  correct by maintaining exactly the invariant `tri lo ≤ n < tri (hi + 1)`
  and closing with `unTri_unique` — those two inequalities characterise
  the answer, and Phase C had already proved them for `unTri`
  (`tri_unTri_le`, `lt_tri_unTri_succ`).

Both are attached with `@[csimp]`, so the definitions and every proof
about them are untouched; only compiled evaluation changes.  Both proofs
are `Classical`-free, preserving the module invariant that
`Epsilon0.lean` must stay at `[propext, Quot.sound]`.

**Correction on attribution — this one matters for the theorem we will
state.**  Kirby and Paris proved termination for the replication factor
equal to the round number.  Our `cutH` deliberately takes the copy count
as a parameter, so what this development will prove is the **free**
battle (arbitrary, adversarial replication).  That generalization must
**not** be attributed to Kirby–Paris 1982; it belongs to the later
literature and to Castéran's development.  Relatedly, Dershowitz and
Moser ("The Hydra Battle Revisited") record explicitly that they shift
the factor by one relative to the original — so the convention has to be
pinned rather than assumed.  Ours: `hydraSeqN` grows `s + 1` copies at
step `s`, i.e. round numbering from 1.

**Sources.**  Kirby & Paris, *Accessible independence results for Peano
arithmetic*, Bull. LMS 14 (1982), 285–293; a scan with a text layer is at
`cs.tau.ac.il/~nachumd/term/Kirbyparis.pdf`.  Castéran's Coq development
is at `rocq-community.org/hydra-battles/` (the `coq-community` URL times
out); its §2.0.1 states the rule as "`h′` is replaced by `n + 1` copies of
`h′` which share the same root", with the replication factor equal to the
round index — the same rule as ours.

**Not verified, and not claimed**: `Hydra(4) > Graham's number` and the
`f_α` growth-rate bounds (asserted by the wikis, unchecked here); and a
numeric instance of Castéran's `l_std` formula, which did not obviously
reproduce the small cases and may be an indexing offset — deliberately
left alone rather than quoted.

### One thing still flagged

**The original citation note (now superseded, kept for the record).**  The brief requires the exact regrowth
rule to be stated and cited before implementing, since the literature has
inequivalent-looking variants (copies at the grandparent versus the
parent; `n` copies at stage `n` versus adversarially many; heads as
leaves versus as edges).  The rule above is stated precisely and is the
standard Kirby–Paris one to the best of my knowledge, but the primary
text (Kirby & Paris, *Accessible independence results for Peano
arithmetic*, Bull. LMS 14 (1982), 285–293) has **not** yet been checked
directly, and no claim is made here that it has.  The worked examples
above are therefore *hand-computed from the rule as stated*, not
cross-checked against a literature source — unlike Phase B's Goodstein
values, which were checked against `WilliamAngus/Goodstein`.  This must
be closed before H3 is built on top of it.

**Evaluation blows up quickly, and that is expected.**  Hydra codes grow
explosively (regrowth multiplies subtrees, and the pairing is
quadratic), and `Epsilon0.lean`'s `tri`/`unTri` are unary/linear — fine
for the notation codes Phase C needed, too slow for hydra codes beyond
the tiny battles above, where the interpreter's stack overflows.  A
closed-form `tri` via `@[csimp]` was tried and set aside (the equality
proof needs division-free arithmetic plumbing that this light-import
module does not have).  Per the brief, evaluation efficiency is out of
scope for H1–H5; recorded here as the known first obstacle for the
visualization phase, which will need bigger battles than these.

### H3, part one: the assignment exists and descends on the worked battle

Added since the entry above.  `insertExp e c` is the Cantor normal form
of `ω^e ⊕ c` — equal exponents merge into the coefficient, a larger one
is prepended, a smaller one recurses into the remainder — fueled on
`oR c < c`, with the usual adequacy pair (`insertExpAux_succ_eq`,
`insertExpAux_eq_of_le`) and its defining equation `insertExp_pos`.  This
is the ordinal arithmetic the development previously lacked.  On top of
it, `ordOfHydra`/`ordOfForest` are a plain structural recursion needing
no fuel, and `ordOfHydraN` is the assignment on codes.

Kernel-checked (`ordOfHydraN_small`): the four smallest hydras get
ordinals `0`, `1`, `ω`, `2` — note the two-deep chain gets `ω` while two
heads get `2`.

And the point of the whole construction, also kernel-checked
(`ordOfHydraN_descends_two`, `ordOfHydraN_descends_rest`): along the
battle `2 → 3 → 1 → 0`, the assigned ordinals are `ω ≻ 2 ≻ 1 ≻ 0`.  The
first step is the one where the **tree grows** — one child with one head
becomes two heads — and it is exactly there that `ω` drops to `2`.  The
node count went up; the measure came down.

### H3 chain, steps 1–3: DONE

* **1. Totality of `≺` on normal forms** (`precB_trichotomy`,
  `precB_total`, and the form insertion needs,
  `precB_of_ne_of_not_precB`).  Phase C proved the order well-founded and
  irreflexive but never *total* — its descent always related notations
  built to be related.  The Hydra layer needs totality, and the proof is
  the same three-way induction as the comparison itself: head exponents,
  then coefficients, then remainders, the recursive calls shrinking the
  sum.
* **2. `nfB_insertExp` — insertion preserves normal form.**  Three cases
  are the normal-form destructors read back; the fourth, recursing into
  the remainder, is exactly where totality is consumed: an exponent
  neither equal to nor above the head must sit below it, which is what
  keeps the new remainder under the old head.  `oE_insertExp` and
  `insertExp_ne_zero` are the two small facts it needs.
* **3. `nfB_ordOfHydra` / `nfB_ordOfForest` — the assignment lands in
  normal form**, by mutual induction over the tree.  This is the
  precondition for *any* descent statement, since `OLt` requires
  normality on both sides.

**Step 4, first half, and a simplification.**
`precB_insertExp_self : c ≺ ω^e ⊕ c` — inserting strictly increases the
ordinal, by the same four-case recursion (bigger coefficient, bigger head
exponent, bigger remainder, then recurse).  At `e = 0` this *is* the
descent's base case, and it is recorded in that form:
`ordOfForest_cons_leaf_descends` — a node loses a head hanging off it and
its ordinal drops, which is the Kirby–Paris clause where nothing regrows.

The other half of step 4 turned out to be **already available**: the
inequality that makes arbitrarily many copies harmless — `ω^a·(m+1) ≺ ω^b`
whenever `a ≺ b` — is exactly Phase C's `precB_mkO_exp`, which says a
smaller head exponent wins *regardless of coefficient and remainder*.  No
new lemma is needed; the replication factor never appears in the
comparison.

Remaining: monotonicity of `insertExp` in each argument (replacing a
child by one of smaller ordinal lowers the parent's), and then the general
descent by induction over `cutH`'s recursion.

**Monotonicity: DONE** (third attempt), together with the prerequisite it
exposed.  `precB_trans_aux`/`precB_trans` and `precB_asymm` were proved
first — the same three-way induction as the comparison, with the recursive
calls at the three head exponents and the three remainders — and then
`precB_insertExp_mono` followed the grid exactly as written up, landing
with one correction (an unreduced outer `if` on the right-hand side in two
branches).  `≺` is now a full strict linear order on normal forms:
well-founded, irreflexive, transitive, asymmetric, total.

The history below is kept because the diagnosis is what made the third
attempt work.

**Monotonicity: attempted once, reverted, and what it will take.**  The
statement is `c₁ ≺ c₂ → ω^e ⊕ c₁ ≺ ω^e ⊕ c₂` (for normal forms).  The
proof is *not* a simple recursion: the case analysis is a square, because
insertion branches on how `e` compares with the head of its accumulator,
and the two accumulators may branch differently.  So the cases are
`(branch taken for c₁) × (branch taken for c₂)` — nine, of which some are
impossible and must be excluded by totality and irreflexivity — and only
the both-recursed corner is an induction step.  A first attempt got four
of them wrong and was reverted rather than left half-proved.  **Doing the square on paper first found the actual blocker, and it is not
the square.**  Writing out the nine corners:

* `c₁ = 0` against `c₂`'s three branches — all three settle immediately
  (coefficient `0 < oC c₂ + 1`; remainder `0 ≺ c₂`; head `e ≺ oE c₂`);
* `oE c₁ = oE c₂` with `c₁, c₂ ≠ 0` — both accumulators take the *same*
  branch, and each corner is one order constructor, with only the
  both-recursed corner an induction step;
* `oE c₁ ≺ oE c₂` — **this is where it breaks.**  To know which branch
  `c₁` takes one must chain `oE c₁ ≺ oE c₂` with the branch condition on
  `c₂`, e.g. from `oE c₂ ≺ e` conclude `oE c₁ ≺ e`.  That is
  **transitivity** of `≺`.  Excluding the impossible corners needs
  **asymmetry** (not both `a ≺ b` and `b ≺ a`).

Phase C proved the order well-founded, irreflexive, and — in the Hydra
work above — total, but **never transitive or asymmetric**: nothing before
now compared three notations at once.  So the prerequisite list grew by
one entry, and it sits before monotonicity:

0. `precB` is transitive on normal forms, and asymmetric (the latter
   follows from transitivity plus irreflexivity, both already available).
   Same nested induction as trichotomy — head exponents, coefficients,
   remainders — and comparable in size.

Both attempts are written up in full in `docs/internal/NOTES_insertExp_monotonicity.md`
— the Lean skeleton and its four rejected corners, then the grid on
paper with rows Z and "equal head exponents" already worked out, so the
next attempt starts from a plan rather than from scratch.

That is a genuine gap in the notation layer, not a Hydra-specific one:
`Epsilon0.lean` has carried a strict order all along without ever proving
it transitive, because Goodstein's descent only ever compared two
notations related by construction.

### The original note, superseded by step 1 above

Worth recording because it would otherwise be found mid-proof.  Before
any *general* descent theorem can even be stated, the assignment must be
shown to land in normal form (`OLt` requires normality of both sides), and
that reduces to: `insertExp` preserves `nfB`.  Three of its four cases go
through directly from `nfB_exp`/`nfB_rem`/`nfB_below`.  The fourth — where
the inserted exponent recurses into the remainder — needs to know that if
`e ≠ oE c` and `oE c ⊀ e` then `e ≺ oE c`.

That is **trichotomy of `precB` on normal forms**, and `Epsilon0.lean`
does not have it: Phase C proved irreflexivity and the three
constructors, but never needed the comparison to be *total*.  So the
dependency order for the rest of H3 is:

1. `precB` is trichotomous on normal forms (a new `Epsilon0.lean` lemma,
   by the same strong induction that `precB_ordOf_of_lt` used —
   compare head exponents, then coefficients, then remainders);
2. `insertExp` preserves normal form (needs 1);
3. `nfB (ordOfHydra h)` (mutual induction over the tree, needs 2);
4. monotonicity of `insertExp` in the inserted exponent, and
   `ω^a·(m+1) ≺ ω^b` for `a ≺ b` — the fact that makes arbitrarily many
   copies harmless;
5. the general descent theorem, by induction over `cutH`'s recursion.

`oE_insertExp` (the head of an insertion is either the inserted exponent
or the old head) is proved and is what step 2 will consume.

### What the rest of H3 needs (superseded — this is how it was scoped before it was done; the plan held)

The assignment sends a hydra to a `≺`-notation: `ord(node [c₁,…,cₖ])` is
the Cantor normal form of `ω^{ord c₁} ⊕ … ⊕ ω^{ord cₖ}`.  Building it on
Phase C's codes means implementing, and proving monotone, the CNF *sum*
of a multiset of exponents — sorting the children's codes, collecting
equal exponents into coefficients — which is ordinal arithmetic on codes
that this development does not yet have.  The descent then needs three
facts: removing a leaf child strictly decreases a node's ordinal;
`ω^a·(m+1) < ω^b` whenever `a < b` (this is what makes arbitrarily many
copies harmless); and monotonicity of the parent's ordinal in each
child's.  D1's retrospective on the analogous Goodstein assignment called
that work the substantial part of the phase, and this one is strictly
harder because it must see the whole tree shape rather than read off a
linear hereditary notation.

### H3, the descent theorem: COMPLETE

`cutH_descends` — for every replication factor `n` and every hydra that
is not already a bare head, `ord(cut n h) ≺ ord h`.  The three cases are
`cutH`'s own:

* a head hanging off this node — `ordOfForest_cons_leaf_descends`, i.e.
  `precB_insertExp_self`, the "parent is the root" clause where nothing
  regrows;
* a deeper cut with no regrowth here — exponent monotonicity,
  `precB_insertExp_mono_exp`;
* a deeper cut where this node *is* the grandparent and `n` copies grow —
  `precB_insertIter_lt` via `ordOfForest_append_replicate`, which turns
  the regrown children into an iterate.  **That lemma is insensitive to
  `n`**, so the case closes without ever looking at how many copies
  appeared: the replication factor never enters the comparison, exactly
  as the informal proof says.

The bare head is excluded by hypothesis — `cutH` leaves it alone, and a
dead hydra's ordinal does not drop.  `hydraStepN_descends` is the same
statement on codes, and (added in H4) `olt_ordOfHydraN_step` restates it
with the fragment's own side condition, `code ≠ 0`, using the bijection
fact `hydraOf_eq_leaf_iff`.

So the measure is proved to work in general, not merely computed on the
small battles: the tree may grow without bound at any step, and the
ordinal comes down every time.

## Hydra Phase H4 (the game inside the fragment): COMPLETE

`HydraFragment.lean`, plus the extension points in `Syntax.lean`,
`Extraction.lean`, `Soundness.lean` and `GenericContinuity.lean`.

### The three symbols

| symbol | arity | evaluated by | reading |
|---|---|---|---|
| `hcut n c` | 2 | `hydraStepN` | one move on the hydra coded `c`, growing `n` copies at the grandparent |
| `hydra s t` | 2 | `hydraSeqN` | the state after `t` moves from the hydra coded `s` |
| `hord c` | 1 | `ordOfHydraN` | the ordinal notation assigned to the hydra coded `c` |

**No coding side condition is needed anywhere**, and that is H1's round
trips paying off: the coding is a bijection between `ℕ` and finite rooted
trees, so the fragment's `∀h` ranges over exactly the hydras rather than
over "codes, some of which are junk".  The dead hydra is the bare head,
whose code is `0`, so `hydra(h,t) = 0` is literally "the battle from `h`
is over after `t` moves" — termination is an equation of the fragment's
existing atomic language, with no new predicate and no new relation.

This required moving the Hydra math layer *before* `Syntax.lean` in the
import chain (`Syntax.lean` now imports `Realizability.Hydra`), the same
move Phase D made for `OrdinalAssignment.lean` and for the same reason:
the value-level functions must exist before `Term.eval` mentions them,
and `Soundness.lean` needs the H3 theorem for the descent case.  The
prerequisite was that those functions be `Classical`-free and
kernel-computable — checked, not assumed (`#print axioms hydraStepN`,
`hydraSeqN`, `ordOfHydraN`: *does not depend on any axioms*).  Had they
not been, every continuity theorem's `[propext, Quot.sound]` budget would
have broken, since `Term.eval` sits inside `extract`.

### The five schemas, and exactly what is imported

* `hydraZero`, `hydraSucc` — the battle's recursion equations, `goodZero`/
  `goodSucc`'s shape.  Honest first-order schemas; their soundness cases
  are `hydraSeqN`'s own definition.
* `hcutNum` — the move's **numeral graph**, for the reason `bumpNum` and
  `precNum` exist: a move is tree surgery through the decoding, i.e.
  course-of-values recursion, not a first-order equation schema over the
  fragment's terms.  Flagged as the same documented compromise as
  `bump`'s.
* `eqCongHcut`, `eqCongHydra`, `eqCongHord` — the equational kit for the
  extended signature, one congruence per new symbol.
* `hordCutLt` — **the one imported mathematical fact of the phase**: from
  `c ≠ 0`, `hord(hcut(n,c)) ≺ hord(c)`.  Its Lean twin is
  `olt_ordOfHydraN_step`.

`hordCutLt` follows the pattern D5 established for `ordPredLt`: it is a
property of *one* function symbol (`hcut`) relative to *one* ordinal
symbol (`hord`), and it says nothing about the battle — no sequence, no
step counter, no stage-indexed replication.  It quantifies over the
number of regrown copies, so the fragment's proof covers every
replication rule at once, adversarial ones included.  Everything
battle-specific — gluing the descent to the recursion equation, the case
split on death, the induction — is the fragment's own work in H5.

What is **not** claimed: that the fragment proves `hordCutLt`.  Like
Goodstein's three schemas it is an axiom of the object theory justified
by a Lean theorem.  Internalizing it would mean formalizing tree surgery
and Cantor normal forms inside an equations-only first-order language —
strictly harder than the Goodstein case that D5 already scoped as
research-scale and did not attempt.

### The import is faithful, and that is checked

`hydra_descent_via_fragment` is the round trip: reading `hordCutLt` back
through `soundness` returns exactly `OLt (ordOfHydraN (hydraStepN n code))
(ordOfHydraN code)` for every `n` and every `code ≠ 0` — H3's theorem, not
a weaker or differently-quantified statement.  This is the same
non-vacuity check `ord_descent_via_fragment` performs for the Goodstein
descent.

### The fragment computes battles, not only reasons about them

`hydraComputeDeriv start t` derives the numeral of the state after `t`
moves, by a derivation whose length is the number of moves — the Hydra
analogue of `good_compute`.  So `hydra_chain_derivable` is a closed
derivation of `hydra(2̂, 3̂) = 0`, passing through the state where the tree
*grows* (code `2 → 3`, one child with one head becoming two heads).

### Machinery cases added, none silent

Per the per-rule discipline: three cases each in `Term.eval`, `vars`,
`subst`, `eval_subst`, `eval_congr` and `termEval_continuous`; seven cases
each in `extract`, `derivBound`, `soundness` and `extract_tracked`, with
seven new `axiomC_*_tracked` lemmas.  Bounds follow the Phase-A
accounting: bare equations `0`, single implications `1`, nested `2`.

## Hydra Phase H5 (Hercules wins): COMPLETE

`HydraTheorem.lean`:

```
hydraTheorem : Deriv [] (∀h ∃t. hydra(h, t) = 0)
```

spelled out and `#check`ed against the unabbreviated formula in
`HydraExtraction.lean`, so what is proved cannot drift behind a
definition.  The quantifier is over all naturals — by H1's bijection, all
finite rooted trees — the witness is unbounded, and the number of heads
regrown at each move is whatever the move symbol's argument says.

### The argument

`tiEps0` along `≺`, on

    φ(x)  :=  ∀s. hord(hydra(h,s)) = x  →  ∃t. hydra(h,t) = 0

with `h` a parameter, quantified only at the end.  Fix `x`, assume φ(y)
for `y ≺ x`, let `s` be a state with ordinal `x`.  Either `hydra(h,s) = 0`
and `t := s` witnesses; or not, and then `hord(hydra(h,s+1)) ≺ x`, so the
induction hypothesis at that ordinal, instantiated at `s+1`, supplies the
witness.  `∀x φ(x)` is instantiated at the initial state's ordinal, whose
hypothesis is reflexivity.

This is `GoodsteinTheorem.lean` line for line, **including the naming
step**: the induction hypothesis cannot be instantiated at
`hord(hydra(h,s+1))`, because that term mentions `s`, which φ binds, and
the fragment's substitution is naive.  So `hydraNamedIHDeriv` proves
`∀z. z = hord(hydra(h,s+1)) → …` first — instantiating at the *variable*
`z`, which captures nothing — and only then instantiates at the term.
That D2 technique transferred with no modification, which is evidence it
is the right general device for naive-substitution calculi rather than a
Goodstein-specific trick.

### The one Hydra-specific difference

Where the descent comes from.  Goodstein assembled it from three schemas
about `ord`, `bump` and `pred` (D5); here `hydraDescentDeriv` glues
`hordCutLt` to the battle's recursion equation `hydraSucc` by congruence
of `hord` — three lines, entirely the fragment's own.  **Nothing about the
number of regrown copies is ever used**: the schema quantifies over it, so
the derivation never inspects how far the hydra grew.  That is the point
of the game, and it is visible in the proof term.

### Refactor this phase forced

The decidability instances for the quantifier rules' side conditions
(`decidableFreeIn`, `decidableSubstOK`, `decidableFreshIn`) moved from
`GoodsteinTheorem.lean` to `Syntax.lean`.  Both theorem phases discharge
those conditions by `decide +kernel`, and the Hydra layer should not have
to import the Goodstein layer to obtain them.  It does not:
`HydraTheorem.lean` imports only `HydraFragment.lean`.

### Out of scope, stated plainly

**Independence from PA is not formalized and is not claimed.**  Kirby–
Paris has two halves — every hydra dies, and PA cannot prove it — and
only the first is here.  The second needs a model-theoretic or
proof-theoretic argument about PA itself (indicators, or the
`ε₀`-ordinal analysis), which this development has no machinery for.

## Hydra Phase H6 (the extracted program): COMPLETE, with the same limit as D3

`HydraExtraction.lean`.  `hydraBattleLength h` reads the witness off
`hydraTheorem`'s realizer at the derivation's own ambient level
(`derivBound hydraTheorem = 12`, the same as `goodsteinTheorem`'s — same
derivation shape, same level accounting), and

```
hydraBattleLength_spec : ∀ h, hydraSeqN h (hydraBattleLength h) = 0
```

is proved from `soundness`, not by computation, so it holds at trees no
evaluator will reach.  Continuity is `extract_continuous` with no
per-derivation certificate; `hydraRealizesCtQ` is the class in `CtQ 2`.

It runs at the small trees, checked at every build:

```
#eval hydraBattleLength 0   -- 0   (the bare head, already dead)
#eval hydraBattleLength 1   -- 1   (a root with one head)
```

both cross-checked against `hydraSeqN` by `rfl`
(`hydraSeqN_one_at_one`, `hydraSeqN_zero_at_zero`).

**The limit, reported rather than papered over.**  `hydraBattleLength 2`
produced no output at 600 s on this machine.  As in D3/D4 the distinction
matters and is unambiguous: **the answer is tiny.**  The battle is
`2 → 3 → 1 → 0`, so the length is `3`, and `hydraSeqN` computes it
instantly.  What is astronomical is only the extract's re-evaluation
count, for the cause D4 diagnosed and did not fix: every recursive value
in `tiRecC`'s output is wrapped in two `dropR` transports, and
`app₁`/`abs₁` duplicate their argument at each application, so the
realizer re-evaluates its own recursive calls exponentially often in the
number of moves, with nothing memoized.  The Hydra layer **inherits** that
bottleneck and adds none of its own — the same shape of derivation, the
same recursor, the same transports.  The certified content is unaffected.

### Axiom budgets for the Hydra phases (checked at every build)

```
'Realizability.hydraTheorem'                     … [propext, Quot.sound]
'Realizability.hord_cut_lt_realized'             … [propext, Classical.choice, Quot.sound]
'Realizability.hord_cut_lt_extract_continuous'   … [propext, Quot.sound]
'Realizability.hydra_chain_realized'             … [propext, Classical.choice, Quot.sound]
'Realizability.hydra_chain_extract_continuous'   … [propext, Quot.sound]
'Realizability.hydra_descent_via_fragment'       … [propext, Classical.choice, Quot.sound]
'Realizability.hydra_theorem_realized'           … [propext, Classical.choice, Quot.sound]
'Realizability.hydra_theorem_extract_continuous' … [propext, Quot.sound]
'Realizability.hydra_realized'                   … [propext, Classical.choice, Quot.sound]
'Realizability.hydraBattleLength_spec'           … [propext, Classical.choice, Quot.sound]
'Realizability.hydra_extract_continuous'         … [propext, Quot.sound]
```

Unchanged from every earlier phase, which is the point: adding three
symbols and seven rules to the fragment cost nothing in axiom footprint,
because the value-level functions are choice-free and the schemas are
contentless.

## Hydra Phase H7 (Hercules wins *whatever he does*): COMPLETE

`HydraGeneral.lean`.  Phase H5 proves termination inside the fragment for
the battle the fragment can *name*: leftmost head, `s + 1` copies at step
`s`.  That is Kirby–Paris's own schedule, but it is one play.  This phase
proves the general statement — every play, every head choice, every
replication factor — in the metatheory, from the same ordinal assignment.

### Why it is not in the fragment, and that is not a shortfall

A strategy is a *function* `ℕ → (which head)`, and a schedule is a
function `ℕ → ℕ`.  The fragment is first-order with one sort: it has no
function variables, so "for every play" is **not expressible** in it, at
any length.  This is a property of the object language chosen in the
brief, not a gap in the proof — and it is the honest reason H5's theorem
names one battle.  What H5 *does* show is that the derivation is uniform
in the factor: `hordCutLt` quantifies over it, so the same proof term
serves any battle symbol with the same recursion equation.

### What is proved

`Play n h h'` is the legal-move relation: some head of `h` — any head, at
any position — is chopped, and if its parent is not the root, `n` copies
of the modified parent grow at the grandparent.  Nothing selects which
head.

* `play_descends` — every legal move strictly decreases the assigned
  ordinal.  H3's `cutH_descends` is the special case "leftmost head".
* **`hercules_wins : WellFounded PlayRel`** — the move relation is
  well-founded.  Every play from every hydra is finite, whatever Hercules
  chops and however many heads grow back.  This is `oLt_wf` pulled back
  along `ordOfHydra`; all the content is in `play_descends`.
* `no_infinite_play` — the same in sequence form: no `F : ℕ → Hydra` has a
  legal move at every index.
* `play_stuck_iff_leaf` — the only position with no legal move is the dead
  hydra.  This is what makes "the play is finite" mean "the hydra dies"
  rather than "the play gets stuck".
* `hydraStep_play` — **the fragment's battle is one of these plays**, so
  H5's theorem is an instance of this one rather than a separate claim
  about a differently-defined game.  Proved by relating `cutH`'s Boolean
  flag to the relation's constructors (`cutH_flag_cut`,
  `cutH_flag_move`).

### What it cost: nothing new mathematically

Each constructor maps to one lemma H3 already had:

| constructor | what it does | lemma |
|---|---|---|
| `CutF.here` | a head hangs off this node | `precB_insertExp_self` |
| `CutF.there` | …off a later sibling | `precB_insertExp_mono` |
| `MoveF.grand` | this node is the grandparent; `n` copies grow | `precB_insertIter_lt` |
| `MoveF.deep` | the move is deeper inside a child | `precB_insertExp_mono_exp` |
| `MoveF.tail` | …inside a later child | `precB_insertExp_mono` |

One observation this phase adds: the *second-argument* monotonicity
`precB_insertExp_mono` — the hard lemma of H3, the one that needed
transitivity and asymmetry first and that `cutH_descends` never used — is
exactly what the two "later sibling" constructors consume.  **Chopping the
leftmost head is the case where that lemma can be avoided.**  So the
effort H3 spent on it was not incidental; it is what the general theorem
runs on.

### Non-vacuity, checked

`play_two_choices` exhibits a hydra (a root with a head *and* a child
carrying a head) from which two *different* legal moves lead to two
*different* hydras at the same `n` — the second being one `cutH` would
never make — and `play_two_choices_descend` runs both through
`play_descends`.  Without this the relation could have described only the
leftmost strategy, and `hercules_wins` would have been a restatement of
H3 rather than a generalization.

### Budget

The whole phase is `Classical`-free:

```
'Realizability.play_two_choices'   … does not depend on any axioms
'Realizability.play_descends'      … [propext, Quot.sound]
'Realizability.hercules_wins'      … [propext, Quot.sound]
'Realizability.no_infinite_play'   … [propext, Quot.sound]
'Realizability.hydraStep_play'     … [propext]
'Realizability.play_stuck_iff_leaf'… [propext]
```

`Subrelation.wf` is applied to a pattern-matched existential rather than
to `Exists.choose`, and `play_stuck_iff_leaf` case-splits on the tree
instead of using `by_contra`; both were `Classical.choice` in the first
version and neither needed to be.

### Still out of scope

Independence from PA, exactly as in H5.  `hercules_wins` is the "every
hydra dies" half of Kirby–Paris, now in its full strategy-free form; the
unprovability-in-PA half is not formalized and is not claimed.

## Hydra Phase H8 (running the battle, and seeing it): COMPLETE

`HydraDisplay.lean`.  No new mathematics; two things the earlier phases
wanted.

### The battle was a hundred times slower than it needed to be

`battleLen` (H2) runs on **codes**: every move decodes a natural number
into a tree, cuts, re-encodes.  That is what made `Hydra(3) = 37` take
≈ 98 s and forced the discriminating cross-check out of the build.

The cost was never the pairing — H2 had already made `tri` constant-time
and `unTri` logarithmic, and this was recorded at the time as the
suspected bottleneck.  **That diagnosis was wrong.**  Hydra codes grow
*doubly* exponentially: `⟪a,b⟫ ≈ (a+b)²/2`, so each level of nesting
squares the magnitude, and the path-3 battle reaches 20-node trees.  Every
step was doing arithmetic on numbers with astronomically many digits to
compute something the tree answers instantly.

`battleLenH` runs the same battle directly on `Hydra` and never encodes.
Measured on this machine: **98 s → under 1 s.**  And it is not a different
measurement — `battleLen_eq_battleLenH` proves the two agree at every
fuel, stage and code, from `hydraOf_encodeH` and `hydraOf_eq_leaf_iff`.

Consequence: the three published Kirby–Paris lengths are now `#guard`ed at
**every build**, `37` included.  That number is the discriminating one —
the other game in circulation (copies as bare leaves at the parent) gives
`1, 3, 11` — so the build now checks that the implemented rule is
Kirby–Paris rather than its neighbour.  It was previously a hand-checked
claim in this file, run out of band; the STATUS entry above is superseded
on that point.

(`#guard` was verified to do real work: the deliberate false variant
`battleLenH 200 1 (path 3) == 38` fails the build, and it evaluates with
the compiled code, so it picks up the `csimp` closed forms that kernel
`rfl` does not.  That is why `battleLen_path_small` stops at paths 1 and
2 — kernel reduction still runs the unary `tri`.)

### The trace: the tree grows, the ordinal falls

`battleTrace` prints each state in bracket notation with its ordinal
beside it.  The first ten of the thirty-eight states of the 4-node path,
verbatim from the build log:

```
(((o)))                    [ω^ω]
((o o))                    [ω^2]
((o) (o) (o))              [ω·3]
(o o o o (o) (o))          [ω·2 + 4]
(o o o (o) (o))            [ω·2 + 3]
(o o (o) (o))              [ω·2 + 2]
(o (o) (o))                [ω·2 + 1]
((o) (o))                  [ω·2]
(o o o o o o o o o (o))    [ω + 9]
(o o o o o o o o (o))      [ω + 8]
```

Read the two columns against each other: the bracket string gets longer,
the ordinal gets smaller, on every line.  `sizeTrace` is the same battle
as node counts —

```
4, 4, 7, 9, 8, 7, 6, 5, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 20, 19, …, 2, 1
```

— peaking at 20, five times the starting size, before it dies.

`ordStr` reads a notation code back as Cantor normal form through
`oE`/`oC`/`oR`, fueled on `oE n < n` and `oR n < n`.  Worth noting that
the ordinal codes stay *small* even as the tree explodes: `ω^ω` is a
three-node code, so the printing costs nothing.  Only the tree codes blow
up, which is the whole point of the previous section.

### The descent, watched rather than proved

`descendsAlong` checks `ord(next) ≺ ord(current)` at every step of the
real battle and is `#guard`ed on the 37-move path-3 battle.  This is a
**demonstration, not a proof** — the proof is `cutH_descends` (H3), which
covers every hydra and every replication factor, and `hercules_wins`
(H7), which covers every play.  What the `#guard` adds is that the thing
proved and the thing computed are visibly the same thing, on the one
battle big enough to be interesting.

### Budget

```
'Realizability.battleLen_eq_battleLenH' … [propext, Quot.sound]
'Realizability.isLeaf_iff'              … [propext]
```

## Hydra Phase H9 (a second strategy, for free): COMPLETE

`HydraStrategies.lean`.  The test of whether H7 bought anything: a general
theorem that cannot be applied to a second instance without redoing the
work is not general.

`cutRightF` chops the **rightmost** head instead of the leftmost — same
grandparent regrowth, same replication parameter — and is defined on
forests, walking to the last member instead of the first.  (The first
attempt defined it on hydras and recursed at `.node (tail)`, which is not
a subterm, so Lean compiled it by well-founded recursion and nothing
unfolded definitionally.  Restructuring on forests fixed that; the
equation lemmas are used explicitly where the overlapping patterns still
block `rfl`.)

`rightStep_play` exhibits each rightmost move as one of H7's plays.  Then

    rightStep_descends := play_descends (rightStep_play …)

is the entire descent proof — one line, against H3's `cutH_descends`,
which is a three-case induction over the tree consuming
`precB_insertExp_self`, `precB_insertExp_mono_exp` and
`precB_insertIter_lt`.  None of that is repeated.  Termination follows the
same way through `no_infinite_play` (`no_infinite_right_battle`, at an
arbitrary replication schedule).

### What the build now checks that it previously assumed

`#guard`: the rightmost strategy gives the published lengths `1, 3, 37` on
the path hydras, and the two strategies pass through **different** states
(after three moves on the 4-node path, `(o o o o (o) (o))` against
`((o) (o) o o o o)`).  The path hydras are the right test precisely
because they *start* as chains, where the strategies agree; they diverge
as soon as the first regrowth branches the tree, and still land on the
same length.

The earlier entry above reported that agreement on the authority of a
research pass ("the research pass independently reports the same 37 under
the rightmost strategy with different intermediate states").  That is now
checked by the build, under our own definitions.

**Stated carefully**: strategy-independence of the battle *length* is a
known result and is **not proved here**.  What is proved is that both
strategies terminate (via H7); what is checked is that their lengths agree
at the three published instances.

### Budget

```
'Realizability.rightStep_play'           … [propext]
'Realizability.rightStep_descends'       … [propext, Quot.sound]
'Realizability.no_infinite_right_battle' … [propext, Quot.sound]
```

## Phase D6 (memoizing the evaluation path): IMPLEMENTED, PROVED, AND MEASURED TO NOT HELP

The brief authorized the fix D4 named and declined to attempt: give the
evaluation path genuine memoization, keyed by the ordinal-notation code,
as an explicit verified table threaded as data rather than hidden state.
It is implemented and proved in `Extraction.lean`.  **It works exactly as
designed, achieves a 100 % cache hit rate, and does not change the wall
clock at all.**  The measurements below say why, and they correct D4's
headline proxy.

### What was built

* `MemoTbl`/`memoFind`/`memoVal` — an association list from notation code
  to the recursor's value, with a `match`-based lookup (deliberately not
  `Option.getD`, whose default is evaluated eagerly and would recompute on
  every *hit*).
* `memoRec` — the memoizing evaluator, `ℕ → ℕ → MemoTbl → PureType × MemoTbl`.
  Before building the closure at `k` it folds itself over the candidate
  codes `≤ B` lying `≺ k`, **threading the table**, so each code is
  computed at most once across the whole build.
* `tiRecCRaw` — a copy of `tiRecC`, `rfl`-equal to it, used as the
  fallback.  It exists so that switching the memo path on cannot loop:
  a fallback calling `tiRecC` would re-enter the memoized implementation
  with a fresh table.
* `tiCTable`/`tiCFast` — the same idea one level up, building the table
  *outside* the `abs₁` so it is shared across applications of the
  `∀x φ(x)` realizer.

### The two obligations, proved

| theorem | says | axioms |
|---|---|---|
| `memo_ok` | the evaluator's output is `tiRecC`'s, **and** every table it returns satisfies the invariant | `[propext, Quot.sound]` |
| `tiRecCFast_eq` | `tiRecCFast φ b k = tiRecC φ b k`, at every code | `[propext, Quot.sound]` |
| `tiCFind_sound` | every entry of a built table is the value it stands for | `[propext, Quot.sound]` |
| `tiCFast_eq` | `tiCFast φ b = tiC φ b`, at every ambient | `[propext, Quot.sound]` |

The invariant is `MemoOK φ b tbl := ∀ j v, memoFind tbl j = some v → v = tiRecC φ b j`.
Correctness holds for **every** bound `memoBound` and **every** fuel: a
lookup that misses recomputes, so those are speed parameters only.  (The
brief's stronger phrasing — that even a *corrupted* table costs only time
— is not achievable and is not claimed: a wrong entry would be returned.
What is proved is that the tables this code builds are correct, and that
any table satisfying the invariant may be substituted freely.)

### The measurements

Instrumented at `m = 1`, ambient 12, with the memo path switched on:

| | value |
|---|---|
| `MEMOHIT` (requests served from the table) | **2376** |
| `MEMOMISS` (requests recomputed) | **0** |
| `TICFAM` (evaluations of the `tiC` family) | 1 |
| fallbacks into the raw recursion | 0 |

So the table serves *every one* of D4's 2376 repeated requests for code
`0`.  The memo is not partially effective; it is completely effective at
what it was built for.

Wall clock, like for like — same source, the two `csimp` lemmas attached
versus detached, timed inside the evaluator with `IO.monoMsNow`:

| | memo on | memo off |
|---|---|---|
| `goodsteinStopTime 0` | 1 ms | 1 ms |
| `goodsteinStopTime 1` | 4693 ms | 4614 ms |
| `hydraBattleLength 0` | 1 ms | 1 ms |
| `hydraBattleLength 1` | 4703 ms | 4758 ms |
| `goodsteinStopTime 2` | no output at 600 s | no output at 600 s |

`m = 3` was not attempted; `m = 2` bounds it.  The differences at `m = 1`
are within noise and have no consistent sign.

### Why — and the correction to D4

`app₁ F x` is `fun w => F (pairPT x (up n w))`: a **closure**.  So
`tiRecC φ b k` allocates two closures and performs no work — producing
the recursor's value at a code is `O(1)`.  A table that hands back the
same closure rather than rebuilding it therefore saves exactly two
allocations per hit, and 2376 × `O(1)` is nothing.

The cost is in *applying* that value.  Each of the 2376 consumers applies
it to **its own argument**, and each application runs the progressiveness
realizer from scratch; that is what branches ≈ 2376-fold per Goodstein
step and gives D4's extrapolated 1.4 × 10¹⁰ at `m = 2`.  Caching a
function does not cache its applications, in any pure language.

**This corrects D4's headline proxy.**  D4 reported "2377 recursor body
entries, 2376 of them at the same code" as the measure of the problem.
Those entries are real, but they are `O(1)` each, so the entry count was
never a cost proxy — and collapsing it, which this phase does completely,
buys nothing.  The quantity that actually tracks the cost is the number
of *applications* of the recursor's value (≈ 10⁵ at `m = 1`, measured),
and no table keyed by the notation code touches it.

The sharper statement of the obstruction: a table that would collapse the
tree must be keyed by `(code, argument)`, and the arguments are
`PureType` values — functions — with no decidable equality to key on.
The blocker is not that pure Lean lacks the state D4 pointed at; it is
that the repeated work is *function application*, which has no key.

### What is shipped, and what is not

The two `csimp` lemmas are **deliberately left detached**, so the
compiled evaluation path is byte-identical to what it was before this
phase.  This follows D4's own precedent, which reverted three proved-but-
inert `csimp` variants rather than ship them: an optimization that is
measured to change nothing should not be presented as one.  The
definitions and the four theorems stay, as the record of what was tried
and what it establishes; switching the path on is adding `@[csimp]` to
`tiRecC_eq_tiRecCFast` and `tiC_eq_tiCFast`, and the module header says
so.

### Regression check (required by the brief, run explicitly)

* `lake build` succeeds, 691 jobs, zero `sorry`/`admit`.
* Every `#print axioms` line in the repository was captured before and
  after and diffed: **identical**, 57 lines, no change anywhere —
  arithmetic, Goodstein, Hydra, collapse demo, generic continuity.  The
  four new theorems are additions at `[propext, Quot.sound]`.
* Every `#eval`/`#guard` unchanged: `goodsteinStopTime 0/1` = `0/1`,
  `hydraBattleLength 0/1` = `0/1`, `battleLenH 200 1 (path 3) = 37` and
  the rightmost-strategy guards still pass, the battle traces and node
  counts byte-identical.

### The residual, quantified

The extract's cost at `m = 1` is ≈ 1.0 × 10⁵ applications of the
recursor's value (measured: 104 466), taking ≈ 4.6 s, i.e. ≈ 44 µs each.
The branching factor is ≈ 2376 per Goodstein step and is ambient-
independent (D4).  So `m = 2` (three steps) is ≈ 5.9 × 10¹¹ applications,
≈ 7 × 10⁶ s, and `m = 3` (five steps) ≈ 3 × 10¹⁸ — consistent with both
phases' observations that neither terminates.  Memoization by code
removes 0 % of that.

Closing it would need one of: sharing at the level of *applications*
(a different evaluator, not a different function); a derivation that
consults its induction hypothesis fewer times (D4's option 1, out of
scope for this brief); or an extraction whose realizers are first-order
data rather than closures.  None is attempted here, and none is claimed.

## Phase E (Tower of Hanoi): COMPLETE — correctness, optimality, and the extracted solver

The third showpiece, and deliberately the *easiest* infrastructure: Hanoi
is an ordinary PA theorem, so this phase uses **no `TI(ε₀)` and no
ordinals at all** — only `ind` (Phase 2), `∃` (D0), and the arithmetic of
Phase A.  What it exercises that neither Goodstein nor Hydra did is a
**branching** recursion: two sub-calls per level.

### E1 — the value layer (`Hanoi.lean`, before `Syntax.lean`)

Moves are arithmetic: `mvN src dst = src * 3 + dst`, so the *fragment*
can write a move with `×` and `+` and needs no symbol for one.  Sequences
use the cons coding `Hydra.lean` already uses for forests, over
`Epsilon0.lean`'s triangular pairing — third client of that one pairing,
second of this list convention, no new scheme.

Two design choices worth recording:

* **The solver is written in difference-list form**,
  `hanoiAux n f t v r` = "the `n`-disk solution followed by `r`".  That
  is what keeps this module free of general list theory: correctness
  needs only the two `hanoiAux` equations, never associativity of append.
  `happN` exists solely because the *fragment's* step case receives its
  two sub-solutions as opaque values and must join them; `hanoiN_succ`
  connects the two forms.
* **`Solves` is a parser, not an equality test.**  `hcheck n f t v k`
  reads an `n`-disk solution off the front of `k` and returns the rest,
  and `solvesN … = 1` when the whole of `k` is consumed.  So it validates
  an arbitrary `k` rather than comparing it against the canonical answer
  — which is what makes the existence theorem say something.  The
  `#guard`s check both directions: the solver's output validates, and
  three non-solutions are rejected.

### E2 — the fragment layer

Four symbols (`hcons`, `happ`, `mvcount`, and the five-place `solves`)
and four schemas, each discharged by exactly one E1 theorem:

| schema | ↔ | E1 theorem |
|---|---|---|
| `solvesZero` | | `solvesN` at `n = 0` |
| `solvesSucc` | | `solvesN_succ` (the branching step) |
| `mvcountNil` | | `hlen_nil` |
| `mvcountApp` | | `hlen_happN` with `hlen_cons` |

Unlike Goodstein's and Hydra's imports, **both `solves` schemas are
ordinary statements of PA**, and the induction that consumes them is
`ind`.  Continuity needed one new closure lemma, `continuous2_comp₅`, for
the five-place symbol.

### E3 — the theorem

```
hanoiTheorem : Deriv [] (∀n ∀f ∀t ∀v. ∃k. Solves(n,f,t,v,k) ∧ MoveCount k = 2^n − 1)
```

**Both conjuncts are carried by the same induction** — the decision the
brief asked to be recorded.  Separately would mean proving existence and
then re-running the same induction to count the witness it produced,
which needs that witness *named*, i.e. a second existential elimination
inside a second induction.  Together, the step gets both facts about each
sub-solution from one `∃`-elimination and pays one `andI`.

The count is carried subtraction-free as `succ (MoveCount k) = 2^n`,
because the fragment has `pred` but no order relation; `2^n − 1` is
recovered at the end by `predSucc`.  The arithmetic the step needs —
`2^x + 2^x = 2^(x+1)` — is derived, not imported: `expSucc` plus Phase
A's `×` theorems, no induction of its own (`expDoubleDeriv`).

**The substitution obstacle, and a new device.**  Hanoi's recursion
*permutes its pegs*: solving `f → t via v` needs `f → v via t` and
`v → t via f`.  So the induction hypothesis `∀f∀t∀v` must be instantiated
at a permutation of the variables the goal has just bound — and with
naive substitution **every such instantiation captures**, because
instantiating the second binder at the third variable happens while the
third is still bound.  Both permutations the recursion needs hit it, and
no ordering of the binders avoids it.  This is a *different* instance of
the problem from D2's, and a sharper one: D2's was one term mentioning a
bound variable, this is unavoidable in principle for any permuting
recursion.

The fix is cheaper than D2's naming trick: **α-rename the induction
hypothesis first** (`ihRenamed`).  Instantiating `∀f∀t∀v` at three
*fresh* variables is capture-free; re-generalizing gives the same
statement over binders disjoint from the goal's; instantiating *that* at
the permutation is capture-free in turn.  Six lines, reusable for any
recursion that permutes its parameters.  A smaller instance of the same
issue: both sub-solutions must be in scope at once, so the second
existential's witness variable is renamed `5 → 9` before elimination.

### E4 — the extracted solver, and the artifact

`derivBound hanoiTheorem = 26`.  `hanoiSolution n f t v` reads the
witness off the realizer; `hanoiSolution_spec` certifies it at **every**
input from `soundness`:

```
solvesN n f t v (hanoiSolution n f t v) = 1  ∧  hlen (hanoiSolution n f t v) = 2^n − 1
```

Decoded with `hanoiMoves`, verbatim from the build log (peg `0` source,
`2` target, `1` spare):

```
n = 1   [(0,2)]
n = 2   [(0,1), (0,2), (1,2)]
n = 3   [(0,2), (0,1), (2,1), (0,2), (1,0), (1,2), (0,2)]
n = 4   [(0,1), (0,2), (1,2), (0,1), (2,0), (2,1), (0,1),
         (0,2), (1,2), (1,0), (2,0), (1,2), (0,1), (0,2), (1,2)]
```

These are the classical optimal solutions.  `#guard`s check the lengths
(`0, 1, 3, 7, 15`) and that the *extracted* witness is the same number as
the value-level solver's output at `n ≤ 4` — agreement that soundness by
itself does not assert.

### The branching question, answered with numbers

The brief asked to confirm explicitly whether the extracted program's
recursion branches or whether extraction linearizes it.  **It branches.**
Instrumented counts, at ambient 26:

| `n` | recursor body entries | `app₁` calls | moves |
|---|---|---|---|
| 1 | 2 | 90 | 1 |
| 2 | 16 | 594 | 3 |
| 3 | 114 | 4 122 | 7 |
| 4 | 800 | 28 818 | 15 |

Both columns grow by a factor of **≈ 7.0 per disk** (8, 7.1, 7.0 and
6.6, 6.9, 7.0), not linearly — a linearized extract would enter the
recursor `n` times.  So the induction hypothesis really is consulted
twice per level and both consultations are re-evaluated rather than
shared: the same "applications are not shared" phenomenon Phase D6
isolated, now visible as a *branching* factor rather than a flat
multiplier.  Of the ≈ 7, a factor of 2 is the branching itself; the rest
is the per-level realizer machinery.

### The evaluation wall is the *encoding*, not the extraction

`n = 5` does not finish — but neither does the **value-level** solver, so
this is not an extraction problem.  Measured code sizes:

| `n` | moves | code bit-length |
|---|---|---|
| 1 | 1 | 3 |
| 2 | 3 | 15 |
| 3 | 7 | 154 |
| 4 | 15 | 53 855 |

The cons coding squares the magnitude at every move, so the bit-length is
*doubly* exponential in `n`; at `n = 5` a single code needs ≈ 5.8 × 10⁹
bits.  This is the same phenomenon Phase H8 recorded for hydra codes, and
it is a property of the pairing-based list encoding the brief specified
(deliberately, to avoid a second scheme), not of the pipeline.  At `n ≤ 4`
the extract and the value-level function are both sub-millisecond and
indistinguishable.

### Budget

```
'Realizability.solvesN_hanoiN'         … [propext, Quot.sound]
'Realizability.solvesN_succ'           … [propext, Quot.sound]
'Realizability.hlen_hanoiN'            … [propext, Quot.sound]
'Realizability.hanoi_realized'         … [propext, Classical.choice, Quot.sound]
'Realizability.hanoiSolution_spec'     … [propext, Classical.choice, Quot.sound]
'Realizability.hanoi_extract_continuous' … [propext, Quot.sound]
```

The expected pattern, matching every prior phase.  Full regression: every
`#print axioms` line in the repository was captured before and after and
diffed — **no pre-existing line changed**; the only differences are the
additions above.

### E5 — uniqueness, and exactly what "optimal" means here

The brief's prose says the goal is not just "produce a solution" but
"produce the shortest one, and prove it's shortest".  The formal goal it
states — `∃k. Solves ∧ MoveCount k = 2^n − 1` — is proved.  Two further
theorems make precise how much of "shortest" that is, and how much it is
not:

* **`solvesN_unique`** — `solvesN n f t v k = 1 → k = hanoiN n f t v`.
  The parser accepts *exactly one* sequence, and it is the canonical
  solution.  Induction on `n` with the remainder generalized, mirroring
  `hcheck_hanoiAux` in the other direction.
* **`solvesN_length`** — hence every accepted sequence has exactly
  `2^n − 1` moves, not merely the one the derivation produces.

So "optimal" here is exact *relative to this `Solves`*: the relation
admits one sequence, of the classical optimal length.

**What is still not proved, and is not claimed**: classical minimality —
"no legal sequence of moves solves the puzzle in fewer steps".  That
needs a *different* `Solves`: a legality relation on arbitrary move
sequences with a tower-state semantics (a disk may move only onto a
larger one), of which the recursive shape used here is one particular
family.  The `2^n − 1` lower bound over that relation is a different
theorem — it needs the state semantics and a counting argument, not just
the recursion — and is out of scope for this phase.  Recorded rather than
left ambiguous, because the brief's prose and its formal goal differ on
exactly this point.

### Out of scope, as stated

Only the classical three-peg problem; no claim about four-peg or
restricted variants.  No general list theory beyond what this encoding
needs.  Classical minimality over arbitrary legal move sequences, as
above.

## Phase F (Pascal's triangle mod 2): COMPLETE — the extracted Sierpiński decider

The lightest of the three showpieces, deliberately: the statement is a
**decidable disjunction**, not an existence statement, so the extract is a
decision *function* rather than a witness — and there is no `TI(ε₀)`, no
ordinal, and (unlike Hanoi) no `∃` anywhere in the phase.

### F1 — the value layer (`Pascal.lean`, before `Syntax.lean`)

```
pas(0,0) = 1     pas(0,k+1) = 0     pas(n+1,0) = 1
pas(n+1,k+1) = pas(n,k) XOR pas(n,k+1)
```

structural in the row, both recursive calls one row up — branching, like
Hanoi's, but cheap.

**Why `XOR` is a symbol and not a term, decided and recorded as the brief
asked.**  The brief offered `a + b − 2·a·b` or a case-split axiom.
Neither is used, because **`a + b − 2ab` is not expressible in this
fragment at all**: the arithmetic is `+`, `×`, `exp`, `pred`, and `pred`
is the only non-monotone operation — it subtracts *constants* from terms,
so a composition of monotone operations under finitely many outer `pred`s
is monotone in `x`, and `1 − x` is not.  So `xor` enters by its **numeral
graph**, the `bumpNum`/`precNum`/`hcutNum` pattern, for the same reason
each of those has one.  The case analysis then lands in the *proofs*,
driven by the totality theorem, rather than in four conditional axioms.

### F2 — the fragment layer

Two symbols (`pas`, `xor`), and the import is exactly `pasN`'s four
structural equations plus `xor`'s numeral graph.  **The characteristic
clauses are not assumed**: `pas(n,n) = 1` and vanishing above the
diagonal are derived in F3.

### F3 — four theorems, all by ordinary `ind`

| theorem | says |
|---|---|
| `pasZeroCol` | `∀n. pas(n,0) = 1` |
| `pasAbove` | `∀n ∀j. pas(n, succ(n+j)) = 0` |
| `pasDiag` | `∀n. pas(n,n) = 1` |
| **`pasTotal`** | `∀n ∀k. pas(n,k) = 1 ∨ pas(n,k) = 0` |

`pasAbove` is the real one: it needs its hypothesis at **two** arguments
(`j` and `j+1`), which is what makes the inner `∀j` load-bearing, and it
consumes Phase A's `x + succ y = succ (x + y)` to line the indices up.
`pasDiag` reads the diagonal off `pasAbove` at `j = 0`.

**A device worth naming.**  The fragment has no case-analysis axiom
("every number is `0` or a successor") and no order relation, so a
variable cannot be split into `0`/`succ k` by any rule.  Where an
informal proof says "case on `k`", these derivations run `ind` on `k` and
**discard the induction hypothesis** — the base and step of an induction
are exactly the two cases of a `0`/`succ` split.  It recurs three times
in this phase, and `pasTotal` is a genuinely nested induction: outer on
the row, inner on the column.

### F4 — the extracted decider

`derivBound pasTotal = 8`.  The realizer of a disjunction carries the
**tag** saying which side holds, so `pasTag n k` *is* the decision, and

```
pasDecide_eq : ∀ n k, pasDecide n k = pasN n k
```

proves from `soundness` that it decides correctly at every `(n,k)` —
which is what makes this extract a decision procedure rather than a
witness.

**Cross-checks against an independent reference.**  `Nat.choose` appears
only in `PascalExtraction.lean`, only in `#guard`s, never in the fragment
or in any proof — the role `WilliamAngus/Goodstein` played in Phase B.
Checked at every build: the **extracted decider** against
`Nat.choose n k % 2` for all `n ≤ 8`, and the fragment's symbol against
it for all `n ≤ 16`, plus named instances (`C(7,3) = 35` odd,
`C(16,8) = 12870` even, `C(15,5) = 3003` odd, `C(20,4) = 4845` odd).

### The grid, recorded verbatim

Rows 0–7 are printed **by the extracted realizer** (`pasRowExtract`);
rows 0–15 by the fragment's own symbol, which `pasDecide_eq` proves
computes the same bits:

```
[[1],
 [1, 1],
 [1, 0, 1],
 [1, 1, 1, 1],
 [1, 0, 0, 0, 1],
 [1, 1, 0, 0, 1, 1],
 [1, 0, 1, 0, 1, 0, 1],
 [1, 1, 1, 1, 1, 1, 1, 1],
 [1, 0, 0, 0, 0, 0, 0, 0, 1],
 [1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
 [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1],
 [1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1],
 [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1],
 [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
 [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]
```

and as a picture (`#` = 1, `.` = 0), verbatim from the build log:

```
                #
               # #
              # . #
             # # # #
            # . . . #
           # # . . # #
          # . # . # . #
         # # # # # # # #
        # . . . . . . . #
       # # . . . . . . # #
      # . # . . . . . # . #
     # # # # . . . . # # # #
    # . . . # . . . # . . . #
   # # . . # # . . # # . . # #
  # . # . # . # . # . # . # . #
 # # # # # # # # # # # # # # # #
```

Every cell is one instance of the proved disjunction, resolved by the
proof itself — which is the sense in which this visualization *is* the
theorem rather than a picture of its behaviour.

### The realizer's evaluation wall, measured

Running the **extracted realizer** (rather than the fragment's symbol)
costs, per single cell, at the middle of row `n`:

| row | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|
| ms | 29 | 62 | 342 | 719 | 4 210 | 8 861 | 51 434 |

≈ 3.4× per row — the branching blowup Phase E measured for Hanoi and
Phase D6 diagnosed: the induction hypothesis is consulted twice per step
(at `k` and `k+1`) and both consultations are re-evaluated rather than
shared.  So a 16-row triangle drawn by the realizer is out of reach
(row 16 alone would be hours per cell), and the build draws rows 0–7 that
way and the rest from the fragment's symbol.

This costs nothing in what is *proved*: `pasDecide_eq` holds at every
`(n,k)`, so the recorded grid is certified to be what the realizer
computes exactly where running it is infeasible.  The gap between the two
is evaluation cost, not content.

### Budget

```
'Realizability.pasN_total'             … [propext, Quot.sound]
'Realizability.pasN_diag'              … [propext, Quot.sound]
'Realizability.pasN_above'             … [propext, Quot.sound]
'Realizability.pas_realized'           … [propext, Classical.choice, Quot.sound]
'Realizability.pasDecide_eq'           … [propext, Classical.choice, Quot.sound]
'Realizability.pas_extract_continuous' … [propext, Quot.sound]
```

The expected pattern.  Full regression: every `#print axioms` line in the
repository diffed before and after — **no pre-existing line changed**.

### Out of scope, as stated

The Kummer/Lucas bitwise characterization (`pas(n,k) = 1` iff `k`'s
binary digits are a submask of `n`'s) is **not** attempted, per the
brief: it is the stretch goal, needs base-2 digit extraction via Phase
B's `hrep` technique, and is a genuinely stronger theorem than anything
here — this phase's content is `pas`'s own recursive characterization.
No general binomial-coefficient theory, factorials or division enter
anywhere.

## Phase G (Kummer/Lucas at `p = 2`): COMPLETE in the metatheory

Phase F's stretch goal, and — unlike everything in F — **not** an
internal consistency check of `pas`'s own definition:

```
pasN_eq_one_iff      : pasN n k = 1 ↔ ∀ i, digit k i ≤ digit n i
pasN_eq_one_iff_land : pasN n k = 1 ↔ k &&& n = k
```

`C(n,k)` is odd exactly when `k`'s binary digits are a submask of `n`'s
(Kummer 1852 / Lucas 1878, at `p = 2`).  This is what makes the
Sierpiński picture *inevitable* rather than merely observed: the mask
condition is self-similar under doubling, which is the gasket.

### The route: the binary step identities

Everything goes through four identities proved from Pascal's recursion
alone, by one induction:

```
pas(2n,   2k)   = pas(n,k)       pas(2n,   2k+1) = 0
pas(2n+1, 2k)   = pas(n,k)       pas(2n+1, 2k+1) = pas(n,k)
```

The proof's shape is the interesting part and is worth recording: the two
odd-row clauses follow from the two even-row clauses **at the same `n`**,
and the even-row clauses at `n+1` follow from the odd-row clauses at `n`.
So the induction *alternates* between even and odd rows — which is
exactly the alternation the gasket's self-similarity expresses.  Read
together they give `pasN_lucas_step`: `pas(n,k) = pas(n/2, k/2)` when
`k`'s low bit is at most `n`'s, and `0` otherwise.  Iterating that down
the bits, by strong induction on `n`, is the theorem.

### Digit extraction needed no new mechanism — and no `hrep`

The brief asked that digits reuse Phase B's hereditary-base-`k`
technique rather than introduce a second scheme.  **Neither was needed.**
The `i`-th binary digit is `(m / 2^i) % 2`, ordinary arithmetic, and
that is all the proof uses.  The reason is worth stating, because it is a
real difference between the two problems: Phase B's `hrep` exists because
`bump` must look at a digit's *own hereditary structure* and rewrite it
at a new base.  Lucas needs only a digit's **value**, which is `0` or
`1`.  Nothing hereditary is involved, so the heavier machinery would have
bought nothing.

The `&&&` form is derived from the digit form through `Nat.testBit`
(`testBit_eq_digit`, `land_eq_self_iff`) — a repackaging, not a second
proof.

### Cross-check

`#guard` at every build: `pasN n k = 1 ↔ k &&& n = k` over the whole
triangle to row 16.  (Compiled, the same check clears 19 rows in 1.5 s;
`#guard` runs interpreted, so 16 is what fits comfortably.  A cell in row
`n` costs about `C(n,k)` calls — `pasN` is the unmemoised Pascal
recursion — and the theorem is what covers the rest.)  Plus the two named
rows: row 8 is `1 0 0 0 0 0 0 0 1`, because the only submasks of `1000₂`
are `0` and itself; row 7 is all ones, because `111₂` contains every mask
below it.

### Budget

```
'Realizability.pasN_even'             … [propext, Quot.sound]
'Realizability.pasN_lucas_step'       … [propext, Quot.sound]
'Realizability.pasN_eq_one_iff'       … [propext, Quot.sound]
'Realizability.pasN_eq_one_iff_land'  … [propext, Quot.sound]
```

`Classical`-free throughout.  Full regression: every pre-existing
`#print axioms` line diffed before and after — none changed.

### Scope: this is metatheory, and the fragment cannot currently state it

Phases F1–F4 put Pascal's recursion *inside* the fragment; Phase G proves
Lucas **about** `pasN`, in Lean, not inside the fragment.  That is not an
oversight, and the obstruction is precise:

* **The fragment cannot state it.**  The submask condition needs either
  binary digits (`m / 2^i % 2` — the fragment has `exp` but **no
  division**) or a bitwise-`and` symbol.  A new symbol with a numeral
  graph would fix the statement, at the cost of one more import.
* **The fragment could not then prove it.**  The proof recurses `n → n/2`,
  i.e. course-of-values recursion, and deriving that from `ind` requires
  an order relation on `ℕ` — which the fragment does not have.  Its only
  order, `prec`, is the ordinal-notation order of `Epsilon0.lean`, and on
  notation codes it is not the numeric order.

**Superseded: Phase G2 below does exactly this.**  What the fragment
*could* prove, and what Phase G2 now does, is the
four binary step identities: they are `∀`-statements of the fragment's
own language, provable by `ind` on `n` with the index arithmetic supplied
by Phase A.  Lucas would then still need its final assembly — the
induction down the bit positions — outside.  That split is recorded here
rather than attempted, on the same principle as H7: the fragment proves
what it can state, and the metatheory proves the general form.

## Phase G2 (the binary step identities, inside the fragment): COMPLETE

Phase G's own section scoped this as "what a Phase G2 would be".  It is
now done: all four identities are derived **inside the fragment**, by
ordinary `ind`, from Pascal's recursion and Phase A's arithmetic.

```
binEvenDeriv : ⊢ ∀n ∀k. pas(n+n, k+k) = pas(n,k) ∧ pas(n+n, succ(k+k)) = 0
binOddDeriv  : ⊢ ∀n ∀k. pas(succ(n+n), k+k) = pas(n,k)
                      ∧ pas(succ(n+n), succ(k+k)) = pas(n,k)
```

So the mathematical core of Kummer/Lucas is now the fragment's own, and
only the final assembly — the induction down the bit positions — remains
in the metatheory, for the reason Phase G recorded (the fragment has no
division, so it cannot state the submask condition, and no order on `ℕ`,
so it cannot run the `n → n/2` recursion).

### Doubling is `n + n`, not `2 × n` — recorded because it is load-bearing

The proofs need `2(n+1)` as `succ (succ (n+n))`, since that is the shape
`pasSuccSucc` consumes.  With `n + n` that is two rewrites — `succPlus`,
then Phase A's `plusSuccDeriv'` — packaged once as `dblSuccDeriv`.  With
`2 × n` it would be `timesSucc` followed by unfolding `+ 2` into two
successors: strictly more work for the same result.

### The alternation, now visible in a proof term

`oddFromEven` derives the two odd-row identities from the two even-row
ones **at the same `n`**; the induction step then derives the even-row
identities at `n + 1` from the odd-row ones at `n`.  So the fragment's
induction alternates between the two rows of the triangle — the same
alternation the gasket's self-similarity expresses, and the same shape
the Lean proof has, now as a `Deriv`.

Three places need a `0`/`succ` case split on the *column*; the fragment's
only way to do that is `ind` with the hypothesis discarded, the device
Phase F3 introduced.  `xor` on bits needs three derivation-formers
(`xorZeroLeft`, `xorZeroRight`, `xorSelf`), each an `orE` on the totality
disjunction closed by the numeral graph — which is exactly why F1 chose
the numeral graph over four conditional axioms.

### The round trip

`bin_even_via_fragment` and `bin_odd_via_fragment` read the fragment's
derivations back through `soundness` and recover Phase G's value-level
`pasN_even` and `pasN_odd` (up to `2*n = n+n`).  So the fragment proved
the same mathematics, not a weaker syntactic shadow of it — the same
check `ord_descent_via_fragment` and `hydra_descent_via_fragment` perform
for their phases.

### Budget

```
'Realizability.binEvenDeriv'             … [propext, Quot.sound]
'Realizability.binOddDeriv'              … [propext, Quot.sound]
'Realizability.binEven_realized'         … [propext, Classical.choice, Quot.sound]
'Realizability.bin_even_via_fragment'    … [propext, Classical.choice, Quot.sound]
'Realizability.bin_odd_via_fragment'     … [propext, Classical.choice, Quot.sound]
'Realizability.binEven_extract_continuous' … [propext, Quot.sound]
```

`derivBound binEvenDeriv = 18`, `derivBound binOddDeriv = 22`.  Full
regression: 701 jobs green, zero `sorry`, and every pre-existing
`#print axioms` line diffed before and after — none changed.

### What is still outside, precisely

Lucas itself.  Given the four identities, the remaining step is: iterate
them down the binary digits, i.e. strong induction on `n` with the
recursive call at `n / 2`.  The fragment cannot express `n / 2` (no
division symbol) and could not justify the recursion if it could (no
order on `ℕ`; its `prec` is the ordinal-notation order, which on codes is
not the numeric one).  Adding a division symbol would fix the first but
not the second.  So the split is now: **the fragment proves the
recursion, the metatheory does the descent** — and both halves are
machine-checked.

## Phase Z0 (numeric order on `ℕ` and strong induction — the Zeckendorf foundation): COMPLETE

Prompted by a Zeckendorf's-theorem brief.  Before committing to that
theorem the brief flagged one dependency — "largest Fibonacci `≤ n`
needs numeric comparison" — and pointed at a companion Euclid brief to
supply it.  Investigation found that comparison **did not exist in any
form**: no order symbol, no `Deriv` rule, not even a value-level
`ℕ → ℕ → Bool` a symbol could evaluate to, and no Euclid/comparison work
landed or planned.  The only "order" is `prec`, the Cantor-normal-form
order on notation codes, which on a numeral does not track magnitude.
And the docs' own boundary (`OrdinalDescent.lean`, Phase G2 above) records
that internalizing this class of result needs "an order relation… and
course-of-values induction derived from `ind`" — "a research-scale
project".

So, on the user's decision ("foundation first, then reassess"), this
phase builds exactly that missing layer — the order relation and strong
induction — as a standalone, reusable deliverable, and stops there.
`Realizability/StrongInduction.lean`.

### What is delivered (all in the fragment, **zero new symbols, zero new
axiom schemas**)

- **`plusAssocDeriv`** `∀u∀v∀w. (u+v)+w = u+(v+w)`, and its α-variant
  `plusAssocDeriv'` at bound variables `6,7,8` — the one arithmetic fact
  Phase A had not proved that the descent needs.  Genuine `ind` theorems,
  in the exact style of `plusZeroDeriv`.
- **Order as a defined notion, not a symbol**: `ltT d s t := ∃d. succ s + d = t`
  (`≤`/`<` are `∃` over `+`, already in the fragment since D0).  Every
  order lemma below is therefore a *derivation*, imported from nothing.
- **The order kit**: `ltZeroElim` (nothing is `< 0`, via `succNeZero`),
  `ltSuccSelfV` (`a < succ a`), and the load-bearing **`ltStepDown`**
  (`z < y` and `y < succ v` give `z < v`; the new difference is the sum
  of the two old ones, landed by `plusAssocDeriv'`).  Plus the utilities
  `Deriv.wkNil` (weaken a closed derivation into any context) and
  `freshIn_cons`.
- **Strong induction, derived from `ind`**: `demoAuxDeriv` proves
  `∀v. Aux(v)` where `Aux(v) := ∀y. y < v → φ(y)`, by ordinary `ind` on
  `v`; `strongIndDemo` reads `φ` back off `Aux(succ v)`.  This is the
  numeric-`<` analogue of `tiEps0` — except `tiEps0` is the fragment's one
  *primitive* rule and this is *derived*.

### The design decision worth recording: transport-free strong induction

The textbook "strong induction from ordinary induction" splits `y ≤ x`
into `y < x ∨ y = x` and, in the `y = x` case, turns `φ(x)` into `φ(y)`
by `y = x`.  That step is **replacement of equals inside a formula**,
which the fragment does not have — its equality kit is reflexivity,
symmetry, transitivity and *per-symbol congruence*, all of which rewrite
inside **terms**, never across `∧∨→∀∃`.  A generic Leibniz schema would be
its own recursion-over-formulas sub-project.

The derivation dodges it: `φ(y)` is never *transported*, it is *produced
at `y`*.  Progressiveness is applied at `y` itself
(`H y : (∀z. z<y → φ(z)) → φ(y)`) and its antecedent discharged from the
induction hypothesis `Aux(v)` by order-transitivity (`z < y` and
`y < succ v` give `z < v`, `ltStepDown`).  Every `φ(·)` appears exactly
where it is needed.  This is the same flavour of manoeuvre as Goodstein's
"naming" trick and Hanoi's `ihRenamed` — routing around naive
substitution, not repairing a mathematical error.

### What is *not* done, and is the reassess point

`strongIndDemo` proves `⊢ ∀v. (v = v)`.  The demonstration `φ` is trivial,
but the derivation is **deliberately routed through the whole scaffold**
(`ind` on `Aux`, progressiveness at the point, `ltStepDown`), so every
piece is certified together rather than short-circuited by the one-line
`eqRefl` the trivial `φ` would allow.  Two things are consequently *not*
yet built:

1. **A course-of-values theorem that genuinely needs the IH at a
   non-adjacent point** (even/odd, `div`/`mod`, …).  Any such theorem
   forces the scaffold to carry real content; the demonstration only
   shows the scaffold is sound and extracts.
2. **A fully generic-in-`φ` `natStrongInd` *former*** (a `def` taking a
   progressiveness derivation for *arbitrary* `φ` and returning the
   conclusion, à la `tiEps0`).  Running `ind` on an *abstract* `φ` makes
   the base/step substitutions `(φ.subst v (var y)).subst v u` stick
   (they do not compute), so the former needs a small
   **formula-substitution lemma library** — `subst_self`, `subst_notFree`,
   `not_freeIn_self_subst`, and a rename-composition lemma — none of which
   the repo currently has (only `numeral_subst`/`eval_subst` exist).  For
   a *concrete* `φ` everything computes and no such library is needed,
   which is why this phase ships concretely.

Neither is hard in principle; both are bounded next increments, to be
chosen at the reassess before (or instead of) proceeding to Zeckendorf
proper.

### Relation to the earlier "research-scale" flags

D5 and G2 said full internalization needs "an order relation… and
course-of-values induction derived from `ind`".  This phase supplies both
(the order relation `ltT` with its kit, and strong induction from `ind`),
choice-free at the derivation level.  It does **not** supply `div`/`mod`
or `hlog` as symbols, so those flags are only *partly* retired: Zeckendorf
needs `fib` and a "largest index" fact on top of this; Lucas would still
need `div`.  What is now removed is the specific obstruction "the fragment
has no order on `ℕ` and no strong induction".

### Budget (checked at every build)

```
'Realizability.strongIndDemo_realized'           … [propext, Classical.choice, Quot.sound]
'Realizability.strongIndDemo_extract_continuous'  … [propext, Quot.sound]
```

Exactly the project's realization/continuity budgets.  The order kit adds
no symbol, so `Term.eval`/`extract`/`soundness`/`extract_tracked` are
untouched and every pre-existing `#print axioms` line is unchanged.  Full
regression: 702 jobs green, zero `sorry`.

## Phase E1 (order + Euclid-roadmap foundation): IN PROGRESS — decisions recorded

A second brief arrived (numeric order → Euclid → Bézout → CRT, phases
E1–E4), whose E1 overlaps Phase Z0 above.  This section records how they
reconcile and the load-bearing design decisions the brief asked to be
fixed.  **Phase Z0 is the start of E1**; both the Euclid roadmap and the
Zeckendorf brief depend on E1's order, and E1 lands first — the `fib`
symbol work for Zeckendorf is deferred so it *reuses* this order rather
than building a second one.

### Decision 1 (order vs. monus): defined order, no monus symbol

**Chosen**: keep Z0's *defined* order `ltT d s t := ∃d. succ s + d = t`
(no new symbol), and reason with the order **witness** rather than a
truncated-subtraction symbol.  Rationale: `a ≤ b` unpacks by `∃`-elim to
`b = a + d`, and that witness `d` *is* `b − a` — additively, expressible
with `+` alone.  So subtractive Euclid can recurse `gcd(a,b) → gcd(a,d)`
using only `+`, and no `∸` symbol is needed for the subtraction.  This
keeps E1 in the "derive, don't import" spirit and adds **zero symbols**.
*Escape hatch, flagged*: if E4's `mod` turns out materially cleaner with a
genuine `∸` symbol (repeated subtraction bounded by fuel), it will be
added there and this decision amended — recorded now so the choice is not
silent.

### Decision 2 (strong induction as a reusable principle)

The brief wants strong induction "proved once, as a named lemma… rather
than re-deriving per proof".  Z0 delivered it *concretely* (certifies the
scaffold).  The reusable form is a **generic-in-`φ` former** with a
`tiEps0`-style signature — which, run on an abstract `φ`, needs the
formula-substitution facts that a concrete `φ` computes away.  Those are
now built (this phase): `Term`/`Formula` `subst_self`, `subst_notMem` /
`subst_notFree`, and `notMem_self_subst` / `notFree_self_subst` in
`StrongInduction.lean`, by structural induction — reusable across all
later phases.

### Status

- Done and green: Z0 (order kit + `plusAssocDeriv` + concrete strong
  induction, certified), and the substitution-lemma library.
- Pending for E1: the generic `natStrongInd` former (needs one more
  substitution-composition/rename lemma on top of the library above), and
  the order **trichotomy** `∀a∀b. a ≤ b ∨ b < a` for Euclid's branch.
- Then E2 (Euclid `gcd` with the full greatest-common-divisor
  characterisation), E3 (Bézout — the signed-coefficient formulation is
  its own flagged decision, deferred to that phase), E4 (CRT).

Full regression after the substitution library: 702 jobs green, zero
`sorry`, every pre-existing `#print axioms` line unchanged.

### E1 update — order layer for Euclid complete

Since the note above, the concrete order layer Euclid (E2) branches on is
done and certified, all in `StrongInduction.lean`, still **zero new
symbols**:

- **`caseNatDeriv`** `∀n. n = 0 ∨ ∃m. n = succ m` — the fragment's
  `0`/`succ` split, a one-line `ind` theorem (witness variable `5`, clear
  of low indices).  The docs long called case analysis a missing *rule*;
  it is a derivable *fact*.
- **`leT`** (`≤`) alongside `ltT` (`<`), both defined via `∃`+`+`.
- **`trichotomyDeriv`** `⊢ ∀a ∀b. a ≤ b ∨ b < a` — order totality, by
  `ind` on `a` with `caseNat` on the difference `a ≤ b` provides
  (difference `0` ⟹ `a = b` ⟹ `b < succ a`; a successor ⟹ `succ a ≤ b`).
  Certified: `trichotomy_realized` `[propext, Classical.choice,
  Quot.sound]`, `trichotomy_extract_continuous` `[propext, Quot.sound]`.

Remaining for E1: only the generic `natStrongInd` former (the
substitution-lemma library it needs is already in place — one
rename-composition lemma plus the assembly).  Then E2 (Euclid `gcd`)
begins on top of trichotomy + the order witnesses.

Regression: 702 jobs green, zero `sorry`, every pre-existing
`#print axioms` line unchanged.

## Phase E2 (Euclid): COMPLETE — divisibility foundation → gcd theorem + extraction

`Realizability/Euclid.lean`.  The greatest-common-divisor
characterisation rests on divisibility algebra; that algebra is now in,
in the fragment with **no new symbols**:

- **`distribDeriv`** `∀d∀x∀y. d·(x+y) = d·x + d·y`, an `ind` theorem on
  `y` (uses `plusSucc`/`timesSucc`/`plusAssoc`).  The one general fact the
  divisibility laws need that Phase A did not prove.
- **`dvdT`** — `d ∣ a := ∃q. a = d·q` (just `∃` and `×`; no symbol).
- **`dvdReflDeriv`** (`d ∣ d`, quotient 1), **`dvdZeroDeriv`** (`d ∣ 0`,
  quotient 0), and **`dvdAddDeriv`** (`d ∣ a → d ∣ b → d ∣ (a+b)`,
  quotient `qₐ+q_b` — the payoff of distributivity).

Certified: `distrib_realized`/`dvdAdd_realized`
`[propext, Classical.choice, Quot.sound]`, the `*_extract_continuous`
`[propext, Quot.sound]`.

**Design fixed here**: `gcd` is stated **existentially** —
`∃g. g ∣ a ∧ g ∣ b ∧ (∀d. d ∣ a → d ∣ b → d ∣ g)` — so the extracted
realizer *is* the gcd and no `gcd` symbol is added, the same
witness-carrying design as Goodstein and Hanoi.

Remaining for E2: the subtractive-step divisibility lemma
(`d ∣ a → d ∣ (a+c) → d ∣ c`, and its converse already have `dvdAdd`),
then the gcd characterisation itself by strong induction on the second
argument (recursion `gcd(a,b) → gcd(a, b−a)`, the difference supplied by
trichotomy's order witness), extracted and run.

Regression: 703 jobs green, zero `sorry`, every pre-existing
`#print axioms` line unchanged.

### E2 update — cancellation and `addEqZero`; `dvdSub` scoped

Added (green, certified via the full regression): **`cancelAddDeriv`**
(`∀a∀x∀y. a+x = a+y → x = y`, left cancellation by `ind` on `a`) and
**`addEqZeroDeriv`** (`∀x∀c. x+c = 0 → c = 0`, by `caseNat` + `succNeZero`)
— the two arithmetic tools the subtractive divisibility law needs.

**`dvdSubDeriv`** (`d∣a → d∣(a+c) → d∣c`) is scoped but deferred one step:
its proof splits by `trichotomy` on the two quotients, and instantiating
`trichotomyDeriv` at the natural quotient indices *collides with
trichotomy's own difference variables* `2`,`3`.  The fix is a deliberate
non-colliding renaming (or an α-variant of `trichotomyDeriv` at high diff
vars) — recorded so it is done cleanly rather than rushed.  Once `dvdSub`
lands, the gcd characterisation's "greatest" direction is unblocked and
the existence proof (strong induction on `b`) assembles.

Regression remains 703 jobs green, zero `sorry`.

### E2 update — `dvdSub` complete; divisibility toolkit done

**`dvdSubDeriv`** (`∀d∀a∀c. d∣a → d∣(a+c) → d∣c`) is proved and certified
(`dvdSub_realized` `[propext, Classical.choice, Quot.sound]`,
`dvdSub_extract_continuous` `[propext, Quot.sound]`).  The variable
collision flagged last step was resolved by *relabelling `dvdSub`'s own
variables* (`c = var 4`, quotients `5,6`) so trichotomy's difference
variables `2,3` stay clear — no α-variant of `trichotomyDeriv` needed.
Both trichotomy branches are handled: `q₆ = q₅ + r` (cancel to `c = d·r`)
and `q₅ = succ q₆ + s` (which forces `c = 0` via two `addEqZero` peels,
and `d ∣ 0`).

**The divisibility toolkit is now complete**: `distrib`, `dvdT`,
`dvdRefl`/`dvdZero`/`dvdAdd`, `cancelAdd`, `addEqZero`, `dvdSub`.  Both
directions of the gcd characterisation are unblocked —
"divides both" from `dvdAdd`, "greatest" from `dvdSub`.

Regression: 703 jobs green, zero `sorry`, every pre-existing
`#print axioms` line unchanged.

### E2 COMPLETE — the gcd existence theorem and its extraction

**`gcdTheorem`** (`GcdTheorem.lean`):

    ⊢ ∀a ∀b. ∃g. g ∣ a ∧ g ∣ b ∧ (∀d. d∣a → d∣b → d∣g)

a closed derivation of the fragment; the extracted `g` **is** the gcd (no
`gcd` symbol, per the existential design).  Certified with the standard
budgets: `gcd_realized` `[propext, Classical.choice, Quot.sound]`,
`gcd_extract_continuous` `[propext, Quot.sound]`.

**Design fork resolved — no positivity precondition.**  The handoff's
form carried `(a>0 ∨ b>0)`; it is **unnecessary** and the delivered
theorem is the stronger `∀a∀b. ∃g. …spec`.  `spec(0,0,0)` holds
(everything divides `0`, so `∀d. d∣0→d∣0→d∣0` is trivial and `0∣0`), the
convention `gcd(0,0)=0` = `Nat.gcd 0 0`.  The base case `a=0` returns
`g:=b` unconditionally, and the recursion never needs to re-establish a
precondition — simpler everywhere.  Recorded in docs/internal/QUESTIONS.md (item 9).

**Measure**: strong induction on the **sum `a+b`**.  Subtractive Euclid
recurses `gcd(a,b) → gcd(a, b−a)` for `a ≤ b` and `gcd(a,b) → gcd(a−b, b)`
for `b < a`; neither argument decreases every step, but the sum does
(`a+(b−a)=b<a+b`, `(a−b)+b=a<a+b`).  Predicate
`φ(m) := ∀a∀b. (a+b=m) → ∃g. spec`, run through the derived
strong-induction scaffold (`Aux(v):=∀y.y<v→φ(y)`, `ind`, `ltStepDown`) of
`StrongInduction.lean` — approach A, inlined at the concrete φ, no generic
former needed.  The `b<a` branch recurses on `(b, succ s)` (not
`(succ s, b)`), so `b + succ s = a` needs **no commutativity** in the
recombination; `plusCommDeriv` (added here, one instantiation of
`plusRightCommDeriv`) is needed only for the two descents (`b<a+b`).

**Both naive-substitution dodges appear, composed.**  Instantiating the
IH at the sub-pair's *sum* (a term mentioning the bound `a`) captures, and
so does instantiating φ there at the *sub-pair*: the sum is **named** by a
fresh `∀17` (Goodstein's `namedIHDeriv` device) and φ's inner `∀a∀b` is
**α-renamed** to `15,16` (Hanoi's `ihRenamed` device).  One further local
rename: in `b<a`, the difference `s` is moved off `var 3` to `var 2`, so
`succ s` avoids the divisibility lemmas' quotient variables `{3,4,5,6,7}`
(else `SubstOK` conservatively rejects `dvdAddDeriv` at `succ (var 3)`).

**Extraction** (`GcdExtraction.lean`): `gcdWitness`, `gcdWitness_dvd`
(the extract is a common divisor of every `(a,b)`, from soundness),
continuity, and the `CtQ 2` class.  **No `#eval`**: the derivation is the
repository's deepest (`derivBound = 41`, vs Goodstein 12 / Hanoi 26), and
`pairPT`/`up`/`down` at ambient 41 are functionals nested 40 deep, so even
`gcdWitness 0 0` does not return.  The realizer is certified (soundness
holds at every input), but running it is walled by the level — the same
kind of wall as `hanoiSolution 5` (encoding) and Hydra code-2.  The
"greatest" half of the spec is `gcd_realized`'s third conjunct (formally
proved), not re-extracted at value level.

Regression: 705 jobs green, zero `sorry`, every pre-existing
`#print axioms` line unchanged.

### NEXT STEP (precise handoff) — E3 (Bézout)

E2 (order → divisibility → gcd) is complete.  Next is **E3, Bézout**:
`∀a∀b. ∃x∃y. gcd(a,b) + a·y = b·x` (or the sign-managed equivalent —
**the signed-coefficient formulation is a flagged decision**: the fragment
has no negatives, so Bézout must be stated additively, e.g.
`∃x∃y. a·x = b·y + g ∨ b·y = a·x + g`, or carry the gcd on the smaller
side; decide and record in docs/internal/QUESTIONS.md before starting).  It reuses the
same strong-induction-on-`a+b` scaffold as `gcdTheorem` — the extended
Euclid recursion carries the coefficient pair alongside the gcd — so
`gcdTheorem` is the template.  Then **E4** (CRT, needing `mod` — revisit
the monus decision there).  `div`/`fib` remain not-yet-built.

## Phase S1 (Sperner 1D / discrete IVT): COMPLETE

**`spernerTheorem`** (`SpernerTheorem.lean`):

    ⊢ ∀n ∀c. (c 0 = 0) → (c n = 1) → ∃k. k < n ∧ c k ≠ c(k+1)

the 1-dimensional Sperner lemma — colour a line's points with the ends `0`
and `1`, then adjacent colours must differ somewhere (the discrete
ancestor of the IVT).  Certified: `sperner_realized`
`[propext, Classical.choice, Quot.sound]`, `sperner_extract_continuous`
`[propext, Quot.sound]`.  **2D Sperner and Brouwer are explicitly out of
scope** (they need a triangulation object); this brief is the honestly-
scoped 1D instance.

**The coloring, and the one new symbol.**  The fragment has no function
variables, so the arbitrary coloring `c` is a `ℕ` **code** `w` (variable
`2`) and `c k` is a new symbol **`look`** (`Coloring.lean`),
`look w k = lookN w k` decoding the cons-list coded by `w` (reusing
`Hanoi.lean`'s `hcons`/`hhead`/`htail` over Phase C's choice-free pairing,
so structural in the index and choice-free).  This is the one place the
"no new symbols" discipline is genuinely forced: `c k` for a bound `k` is
data access — a decode recursion, not a relation — so unlike order it
cannot be an `∃`-encoding.  It is a *safe* symbol (primitive-recursive,
kernel-computable, not in `Epsilon0`), added through all ~16 sites; every
pre-existing `#print axioms` line is unchanged and the Hydra/Hanoi
choice-free checks still pass.

**Proved for arbitrary `ℕ`-valued colorings** — the `{0,1}` restriction is
never used, so the delivered theorem is the general discrete IVT and
binary Sperner is its special case (recorded in docs/internal/QUESTIONS.md item 18).

**The argument** is a forward scan: `ind` on the invariant
`P(m) := (c m = 0) ∨ ∃k<m. c k ≠ c(k+1)`; the step compares `c(m+1)` to `0`
by `eqDec` and either stays on the left disjunct or reports the crossing at
`m`; at the end `c n = 1 ≠ 0` forces a crossing.  No `TI(ε₀)` — an ordinary
PA-strength theorem.  `≠` is the negated equation, `k < n` is `ltT` (the E1
order layer, a payoff of the Euclid work).

**Extraction and the ambient story** (`SpernerExtraction.lean`).
`spernerBody` leaves `n, c` free; `spernerWitness` reads the ∃-witness off
it at the certified bound `derivBound = 11`, and `spernerWitness_spec`
proves from `soundness` that it is `< n` and a genuine crossing, at every
coloring meeting the boundary.  The extracted search is a genuine
**linear scan returning the first crossing** — this is forced by the
invariant, which carries the minimal crossing once found and never revises
it.  *Running* it: the ambient-11 pure-type realizer overflows the
interpreter stack even at `n = 1` (the same wall as `gcd`), but the witness
numeral is **ambient-independent**, so `spernerScan` reads the *same*
derivation at ambient 5 (checked to agree with ambient 11 under
`lean --run` on every pair where both terminate), which the interpreter
evaluates; its build-time `#guard`s run the search on concrete colorings —
`[0,1] → 0`, `[0,0,1] → 1`, `[0,0,0,1] → 2`, and the multiple-crossing
cases `[0,1,0,1] → 0` and `[0,1,1,0,1] → 0`, confirming it returns the
**first** crossing, not merely *a* crossing.  Continuity and the `CtQ 2`
class as in every extraction phase.

Regression: 708 jobs green, zero `sorry`.

## Phase Fib (Fibonacci — the paired-invariant on-ramp): COMPLETE

**`fibPairedTheorem`** (`FibonacciTheorem.lean`):

    ⊢ ∀n. (∃y. fib n = y) ∧ (∃z. fib (n+1) = z)

the most recognizable recursive function, extracted from a constructive
proof by the pipeline **unchanged** — meant to sit *before*
Goodstein/Hydra in the narrative as the easy case that shows the
mechanism working before anything ordinal-flavored appears.  Certified:
`fib_realized` `[propext, Classical.choice, Quot.sound]`,
`fib_extract_continuous` `[propext, Quot.sound]`, and — the check the
brief demanded, traced not assumed — the extracted function itself,
`#print axioms fibonacci` = `[propext, Quot.sound]`.

**The design: a paired invariant proved by *ordinary* `ind`, not strong
induction.**  `fib (n+2)` needs both `fib (n+1)` and `fib n` (the
course-of-values snag); it is dodged by carrying the pair.  The step from
`(y, z)` with `fib n = y`, `fib (n+1) = z` witnesses `(z, y+z)`:
`fib (n+1) = z` is the old hypothesis and `fib (n+2) = y+z` is `fibSucc`
rewritten by the two hypotheses — the shift *is* the step, and the
extracted realizer is exactly that iteration, computing `fib` by `+`
alone.  `lvl = 1` (checked by `fib_lvl : lvl … = 1 := rfl`), the same as
every headline theorem, so `PureType 2` / `CtQ 2` as usual.

**Why the ∧-of-∃'s shape, not nested `∃y ∃z`.**  Both are `lvl 0`, but
with `∃y ∃z (A ∧ B)` the step's outer `exI` supplies `z`, which is the
*inner* binder's variable, so naive substitution captures it (the
Goodstein/Hanoi renaming dance).  Written `(∃y. A) ∧ (∃z. B)` each
existential body is atomic, so the witnesses drop into binder-free
formulas and nothing captures — no renaming needed.  The brief flagged
`lvl 1` as the correctness signal for the formula shape; it comes out
`lvl 1` on the nose.

**The encoding: `fib` as a value symbol** (Option 1 of the brief), the
same category as Hanoi's `solves` or Pascal's `pas` — a genuinely
recursively-defined value, not an order/divisibility-style `∃`-relation.
Added through all ~16 sites; value function `fibN` via a *structural*
paired recursion `fibPair : (a,b) ↦ (b, a+b)` (`Signature/Fibonacci.lean`),
so it reduces in the kernel (`fibN 10 = 55` by `rfl`) and `fibSucc`
(`fib (n+2) = fib n + fib (n+1)`) is `rfl`-sound.  Choice-free, like every
`Term.eval` symbol; every pre-existing `#print axioms` line is unchanged.

**Extraction and the evaluation wall** (`FibonacciExtraction.lean`).
`derivBound = 5`; `fibonacci` reads the first existential's witness off the
realizer, and `fibonacci_spec : fibonacci n = fibN n` proves from
`soundness` that it computes the `n`-th Fibonacci number at **every** `n`.
Reading *both* witnesses (`fibonacci`, `fibNext`) yields the iterative
loop's exact pair-state — `fib_pair_spec : (fibonacci n, fibNext n) =
(fibN n, fibN (n+1))` certifies it, and the build-checked `#guard` runs it:
`(0,1) → (1,1) → (1,2) → (2,3)`, the `(a,b) ↦ (b,a+b)` iteration falling out
of a proof that never mentions a loop (the extraction made visible).
Because it is `ind`-based (not `tiEps0`), it *runs* — but its cost is
**exponential in `n`** (≈ ×4/step: the step forces the accumulated pair
without sharing, the D4/D6 wall memoization was measured not to fix).  So
the extract is `#guard`ed at the small `n` it reaches (`0…3`), and the
headline `fibonacci 10 = 55` is the **certified** `fibonacci_ten` —
`fibonacci_spec` rewrites it to the kernel-checked `fibN 10 = 55` — proved,
not evaluated, exactly as Goodstein's `m = 4` and gcd are certified-not-run.

**Side effect: this unblocks Zeckendorf**, which STATUS flagged as needing
`fib` and a "largest index" fact on top of Z0.  Zeckendorf itself is *not*
in scope for this phase — this leaves `fib` in the state its brief needs.

Regression: 711 jobs green, zero `sorry`.

## Phase P (presentation — the extracted program made visible): COMPLETE

The first refinement block that produced Lean code rather than moves and
renames.  Nothing here changes a certified declaration: the two new
`Meta/` modules add no axioms, and every pre-existing `#print axioms`
line is unchanged.  What it adds is the ability to *see* the artifact the
pipeline produces, one genuinely new mathematical step, and the paper.

Regression: **713 jobs green, zero `sorry`**, 17 linter warnings (unused
variables / unused `simp` arguments, all pre-existing — see the
refinement agenda below).

### P1 — `#realizer`: the realizer's structure, since its value is unreadable

`Realizability/Meta/RealizerDisplay.lean`.  The problem it solves is real
and was previously undocumented: **the certified artifact could not be
looked at.**  Two independent failures —

- `#reduce (extract goodsteinTheorem …)` never returns.  It forces
  `tiRecC`, the same wall that stops `gcdWitness 0 0` (Phase E2) and
  `goodsteinStopTime 2` (D4).
- Where reduction *does* terminate it **over-reduces**: the smallest
  realizer in the repository, `extract goodThreeExDeriv`, collapses under
  `#reduce` to `fun n z => 30` — that is `Nat.pair 5 0` — so the witness
  `5` that the proof supplies is gone from the output.

`#realizer d` sidesteps both by walking the **derivation** (a finite
constructor tree) instead of the extracted value: it never calls
`extract`, never builds a `PureType`, and never runs a recursion
combinator.  So it terminates exactly where evaluation cannot.  Measured:
`goodsteinTheorem` and `hydraTheorem` each render as a **29-line
skeleton**, `fibPairedTheorem` as 20.

**The collapse rule, and why it keys on the conclusion.**  A realizer of
an equation (or `⊥`) is contentless — its value is junk and the `MR`
clause ignores it — so any sub-derivation *whose conclusion* is an
equation or `⊥` renders as a single `·` leaf, however it was proved.
This is what folds `goodComputeDeriv`'s long equational chain into one
node, and it is what makes 29 lines the right size for Goodstein: what
survives is exactly the computational scaffolding (the `∀`-binders, the
`eqDec` case split, the `exI` witness read-off, the `tiEps0` node, and
the descent discharged against the induction hypothesis through three
`wk`s).

**`toSkel` is the fifth per-rule site.**  It matches every `Deriv`
constructor with **no wildcard**, so a new rule breaks its build until
given a case — exactly like `extract`, `derivBound`, `soundness`, and
`extract_tracked`.  `CLAUDE.md`'s per-rule discipline section is updated
to say five places, not four.  A new *function symbol* additionally needs
a `termStr` case here.

Pinned regression `#guard`: `realizerSkeleton goodThreeExDeriv` is fixed
verbatim to the two-line `exI ⟨witness = 5, ·⟩` / `· ⟨contentless⟩
good(3,5) = 0`, so the witness that `#reduce` loses is the thing the
build now checks is displayed.

### P2 — `#realizerCH`: the extraction map, rule by rule

The same walk rendered as three columns per node — **program operation**,
**logic rule**, **proposition** — so that extraction being
structure-preserving is legible line by line rather than asserted.
`λk. — ∀-intro`, `return ⟨5,·⟩ — ∃-intro`, `rec (well-founded on ≺) —
TI(ε₀)`, and so on.  `paper/curry-howard.tex` (+`.pdf`) is a standalone
figure of the same map.  Pinned `#guard`: line 1 of the correspondence
view of `goodThreeExDeriv` is `return ⟨5, ·⟩  — ∃-intro
⟦∃x1.good(3,x1) = 0⟧`.

**Flagged deviation — `toCH` uses a wildcard, and its stated safety
argument does not hold.**  The module header justifies the wildcard by
"a new content-bearing rule would break `toSkel`'s build first."  That is
true but does not give the property wanted: once the required `toSkel`
case is added, `toCH` compiles again and renders the new rule as
`· — axiom (proof-irrelevant)`, i.e. it produces a **wrong label rather
than a missing case** — the one failure mode the per-rule discipline
exists to prevent.  Recorded as a known gap, not a design decision; the
fix is ~60 one-line cases routed through a shared contentless helper.
`toSkel` itself is unaffected and remains wildcard-free.

### P3 — `#program`: pseudocode, explicitly not the artifact

A readability layer over the same skeleton, rendering the combinators as
pseudocode (`allI ↦ fun k =>`, `exI ↦ return witness … with
certificate`, `tiEps0 ↦ wellFoundedRecOnPrec`).  The module header states
the scope correctly and it is restated here because it is the kind of
claim that drifts: **the pseudocode is a generated reader-facing view,
not the certified artifact.**  The certified artifact is still
`extract D`, correct by `soundness` and continuous by
`extract_continuous`.

**Flagged compromise — the renderer dispatches on `toSkel`'s display
strings.**  `pseudoHeader`/`leafPseudo` match string *prefixes* of the
labels `toSkel` produces, so renaming a label (say `"ind / indRecC
(recurse on succ)"`) silently degrades the pseudocode to echoing the raw
label — no error, and only the three-line `goodThreeExDeriv` output is
`#guard`ed.  The clean fix is to carry a rule tag as structured data in
`Skel` and derive both renderings from it.  Left as-is deliberately (this
is display-only code), but recorded so it is not mistaken for robustness.

### P4 — search versus descent: the theorem as a totality certificate

`Realizability/Theorems/Goodstein/GoodsteinSearch.lean`.  One function,
the Goodstein stopping time `m ↦ s`, computed two ways, to exhibit what
the extraction actually buys:

- **`stopBySearch`** — the μ-operator, `μ s. goodN m s = 0`.  Lean
  requires `partial`: nothing in the definition bounds the search, and
  its totality *is* Goodstein's theorem.  The `partial` keyword is that
  missing certificate, sitting in the source.
- **`goodsteinStopTime`** (D3) — extracted from the proof, recursing
  along `≺`.  A *total* `def`: termination is carried intrinsically by
  well-foundedness, however large the intermediate values get.

**The contribution is that the dependency is machine-checked, not
narrated.**  `Nat.find` is total only when handed an existence proof, and
the only one available is `goodReachesZero`, which *is*
`goodsteinStopTime_spec`.  So `minStop := Nat.find (goodReachesZero m)`
is the same μ-search as `stopBySearch` but total — **because it literally
consumes Goodstein's theorem as its termination argument**.  "The search
halts iff the theorem holds" stops being prose and becomes the type of
`Nat.find`.

Two honesty points, both recorded in the module and repeated here:

- **The certificate buys termination, not speed.**  At runtime the
  existence proof is erased, so `minStop` *evaluates* by the cheap
  `goodN` search, not by the ambient-12 realizer.  `minStop 4` is
  therefore as unreachable as the naive loop.
- **Its budget is not an extracted-program budget.**  `#print axioms
  minStop` reports `[propext, Classical.choice, Quot.sound]` — it is
  metatheory inheriting choice through `soundness`, reasoning *about* an
  extract.  The extracts themselves are unchanged at
  `[propext, Quot.sound]`.

Build-checked: `[minStop 0..3] == [0,1,3,5] == [stopBySearch 0..3]`, the
published stopping times, and both agree with the ordinal-descent extract
where it evaluates (`m = 0, 1`).  Independence from PA is **not** used
and **not** claimed — the contrast needs only "an unbounded search halts
iff a zero exists," which is elementary.

### P5 — `ProgramExtraction`: the witness-reading boilerplate, factored

`Realizability/Meta/ProgramExtraction.lean` packages the repeated "apply
the realizer to numerals and read the witness/tag" pattern as
`extractedFamily` / `extractedAt` / `extractedCtQ`, `apply₁…₄`,
`witness₁…₄`, `tag₂` (with ASCII aliases for the paper).  It **re-proves
nothing**; the module header is explicit that this is not a compiler from
arbitrary Lean theorems, since a Lean theorem must first be represented
as a `Formula` and proved as a `Deriv`.  Budget checked in-file: all
computable helpers report `[propext, Quot.sound]`.
`docs/first-order/EXTRACTED_PROGRAMS.md` is the new quick index of the concrete programs.

Three flagged points:

1. **`Meta/` is no longer purely non-certified.**  `CLAUDE.md` describes
   the layer as "display tooling, not part of the certified pipeline",
   but `GoodsteinExtraction`, `HanoiExtraction`, and `PascalExtraction`
   now import `Meta.ProgramExtraction` and define their headline extracts
   through it.  The layer is currently half display, half load-bearing
   API.  **Resolution pending** (refinement agenda): move
   `ProgramExtraction` to `Core/`, where an API over `extract` belongs,
   and keep `Meta/` at zero certified impact.
2. **The call-site number changed meaning.**  `goodsteinStopTime` was
   `extract … 12` with `12 = derivBound` matching the recorded
   `goodstein_derivBound`; it is now `witness₁ goodsteinTheorem 11 m`,
   where `11` is *bound minus arity* (the ambient level after the
   applications).  Semantics are identical — a wrong number breaks the
   `_spec` proof, so the build catches it — but the literal in the source
   no longer matches the theorem that documents it.  Same at Hanoi
   (26 → 22) and Pascal (8 → 6).
3. **Adoption is 3 of 7.**  Migrated: Goodstein, Hanoi, Pascal.  Still
   hand-rolling `fstPT (app₁ …)`: Sperner, gcd, Fibonacci, Hydra — and
   `GoodsteinExtraction` itself retains two raw occurrences in its
   `#eval` demonstrations.  Fibonacci needs a reader for the *first
   conjunct's* existential (`fstPT (fstPT …)`), a shape the current API
   does not cover, which is why it was not migrated.

### P6 — the first dent in the import ledger: `bumpNeZeroNumeral`

`Deriv.bumpNeZeroNumeral` (`Theorems/Goodstein/OrdinalDescent.lean`) —
the only forward *mathematical* step in this phase.  For every concrete
numeral `n`, the fragment now derives

    n ≠ 0 → bump(b+2, n) ≠ 0

**without the `bumpNeZero` schema**, from the numeral graph `bumpNum`,
equality reasoning, and `succNeZero` (via the new helper
`Deriv.neZeroOfEqSucc`, which turns "`t` is a successor" into "`t ≠ 0`").
The supporting `bumpN_ne_zero` was reproved directly from
`bumpN_pos_eq` rather than through `bumpN_lt_bumpN`.

This is the first internalization step against `docs/internal/RESEARCH_PLAN.md`'s
ledger, and it targets the schema that plan picks first, for the reason
it gives: `bumpNeZero` is the smallest remaining Goodstein import.
**What remains imported is the uniform open-term schema** — the closed
instances are now derivable, the general one is not.  The open-term case
needs case analysis on `bump` inside the fragment, which the signature
does not currently support.  No schema was removed; the object theory
still imports `ordBump`, `ordPredLt`, `bumpNeZero` exactly as before.

New `#print axioms` lines, quoted verbatim:

    'Realizability.bumpN_ne_zero'            … [propext, Quot.sound]
    'Realizability.Deriv.neZeroOfEqSucc'   does not depend on any axioms
    'Realizability.Deriv.bumpNeZeroNumeral'  … [propext, Quot.sound]

`neZeroOfEqSucc` being *axiom-free* is the expected reading and worth
keeping: it is a pure derivation-builder, assembling `succNeZero` with
symmetry/transitivity and `impI`/`impE`, so it touches no quotient or
propositional-extensionality reasoning at all.

### P7 — the paper, and the planning ledger

`paper/how-a-proof-becomes-a-program.{tex,pdf}` (LaTeX, numbered
bibliography in `refs.bib`, TikZ figures including `sierpinski.tikz`),
plus `paper/curry-howard.tex` (P2's figure) and the `#realizer` X-ray
appendix built from `xray-goodstein.tex`/`xray-small.tex` — the appendix
is what closes the loop, since it prints the artifact the rest of the
paper describes.  LaTeX build products are `.gitignore`d, not tracked.

`docs/internal/RESEARCH_PLAN.md` is a **planning ledger, not an implementation
commitment** (its own words).  Its durable contribution is §2, the
**internalization gap ledger**: every remaining imported schema
(`ordBump`, `ordPredLt`, `bumpNeZero`; Hydra's `hordCutLt`) with its
semantic theorem, why it is not internal, the missing object-language
infrastructure, and a cost estimate.  That is the honest statement of
where the object theory stops, and it belongs in the record.

**Scope discipline in the paper — one item to fix.**  The paper is
careful in the places that matter: Gentzen is cited for TI(ε₀) lying
beyond PA, and the Hydra boundary is framed correctly as *inexpressible*
("does not parse") rather than merely unprovable.  But two sentences
(≈ lines 1315 and 1521) assert that Goodstein and Kirby–Paris "genuinely
need" more than PA — a **necessity** claim, i.e. the independence result
this repository's standing rule says is neither formalized nor claimed.
Both are true statements of the literature; both need the citation and a
"not formalized here" clause at that spot.  Not yet applied.

### Budget

Unchanged from the previous phase.  The two `Meta/` modules are
`partial def`s and macros with no theorems; `GoodsteinSearch` is
metatheory whose budget is explicitly labelled as such.  New lines only:

    'Realizability.extractedFamily'         … [propext, Quot.sound]
    'Realizability.extractedAt'             … [propext, Quot.sound]
    'Realizability.witness₁'                … [propext, Quot.sound]
    'Realizability.witness₄'                … [propext, Quot.sound]
    'Realizability.tag₂'                    … [propext, Quot.sound]
    'Realizability.witness1'                … [propext, Quot.sound]
    'Realizability.tag2'                    … [propext, Quot.sound]
    'Realizability.minStop'  … [propext, Classical.choice, Quot.sound]

`minStop`'s classical dependency is metatheory (via `soundness`), not an
extracted-program budget — see P4.

### Out of scope, as stated

- No independence claim, in the code or the paper's technical content
  (the two prose sentences above are flagged for correction, not
  defended).
- `#program`'s pseudocode is a display view and is not certified to
  correspond to the extract beyond `toSkel`'s own per-rule structure.
- `bumpNeZero` is **not** internalized: closed numeral instances only.

## Phase X (the level-free emitter): COMPLETE — the certified programs, executed

A **second extraction** of the same derivations, into native Lean types
(`Meta/EmitLean.lean`), plus a Haskell backend for the same walk
(`Meta/EmitHaskell.lean`) and the evidence module that runs both on every
case study (`Meta/EmitDemo.lean`).

Regression: **716 jobs green**, zero `sorry`.

### Why it exists

The repository has always contained a **certified program it could not
execute.**  `derivBound gcdTheorem = 41`, so the realizer is functionals
nested 40 deep and `gcdWitness 0 0` does not return — at *any* input.
Sperner overflows the interpreter at ambient 11; Goodstein stops at
`m = 1`; Fibonacci at `n = 3`.

### The observation the phase rests on

**The realizers' cost is not their computational content.**  It is the
`PureType` tower and the `liftR`/`dropR` transports, which exist so `MR`
can be stated at a flexible ambient and so `extract_continuous` can
quantify over every derivation at once.  None of that computes.

The type translation makes this precise and is the whole of the design:

    ⟦s = t⟧, ⟦⊥⟧ = Unit        ⟦φ→ψ⟧ = ⟦φ⟧ → ⟦ψ⟧
    ⟦φ∧ψ⟧  = ⟦φ⟧ × ⟦ψ⟧         ⟦∀x φ⟧ = ℕ → ⟦φ⟧
    ⟦φ∨ψ⟧  = ℕ × (⟦φ⟧ × ⟦ψ⟧)   ⟦∃x φ⟧ = ℕ × ⟦φ⟧

It reads the connective skeleton only — **no level index, and no
dependence on `ρ`**, which is exactly why a realizer's *type* only ever
depended on `lvl`.  What is left is System T plus one well-founded
recursor.  `emit` is choice-free: `[propext, Quot.sound]`.

### Measured reach

| theorem | certified extract | emitted | remaining wall |
|---|---|---|---|
| gcd | **no input at all** | hundreds (`700,525` in 8 s) | cost grows with `a+b` — subtractive Euclid through the strong-induction scaffold |
| Fibonacci | `n = 3` | `n = 25` | none hit; linear |
| Goodstein | `m = 1` | `m = 3` | `m = 4` is astronomical — the *mathematics* |
| Hydra | code 1 | code 3 | as Goodstein |
| Pascal | row 7 | row 7+ | none hit |
| Hanoi | `n = 4` | `n = 4` | **unchanged — and that is a result** |

The Hanoi row is worth keeping.  STATUS has claimed since E4 that Hanoi's
wall is the *encoding* (code bit-length squares per move), not the
extraction.  Deleting the entire ambient tower moved it not at all, which
is independent confirmation of that diagnosis.

### The evidence, and its exact strength

`EmitDemo.lean` runs two kinds of build-time check.  **Agreement**: the
emitted answer equals the *certified* extract's wherever the certified one
terminates — Fibonacci `n≤3`, Goodstein `m≤1`, Hydra code ≤1, the decoded
Hanoi move lists at `n≤3`, all of Pascal row 6.  **Reach**: the emitted
program then runs past that point, with gcd cross-checked against
`Nat.gcd`.

**This is not a proof that `emit` and `extract` agree.**  No such theorem
exists here, and none is claimed.  The agreement checks are evidence of
the same species as `SpernerExtraction.lean`'s ambient-5-vs-ambient-11
check — read the same derivation a cheaper way, verify the readings match
— and they are run by the kernel every build rather than asserted.  A
soundness theorem for `emit` is the obvious next step and is **not** done.

Both emitters are therefore scoped exactly as `#program`'s pseudocode is:
generated views, useful and unproved.  The certified artifact remains
`extract`, with `soundness` and `extract_continuous`.

### The one place a proof has to be recovered

`tiEps0`'s premise `y ≺ x` is an equation, so its realizer is contentless
and carries no evidence of descent.  `tiRecC` handles this by
*re-deciding* `OLt` at the recursive call, falling back to a default;
`emit` does the same.  `OLt` is decidable and `oLt_wf` is `Classical`-free,
so nothing is smuggled in.

### The Haskell backend, and what it costs

`hsTy`/`hsDefault`/`hsEmit` mirror `tyOf`/`defaultOf`/`emit` clause for
clause.  Verified end to end: the generated modules **compile under GHC and
run**, giving `gcd → [6,1,0,12,21]` (including `gcd 1071 462 = 21`, which
the *Lean* emitter times out on), `fib 0..15`, and Pascal rows 6 and 7
matching the certified `pasTag`.  Emitted source is small — gcd is 6 KB
from a 531-line derivation — because the collapse rule prints every
equational sub-derivation as `()`.

Three costs, all recorded rather than worked around:

1. **Nothing checks the output.**  Lean type-checks `emit`; only GHC
   checks `hsEmit`'s product.  This is the standard arrangement — Coq's
   extraction to OCaml/Haskell sits in the trusted base rather than being
   verified, which is what motivates verified-extraction work such as
   CertiCoq.
2. **`tiEps0` loses its termination guarantee.**  Haskell cannot express
   well-founded recursion along `≺`, so `tiRec` is an ordinary recursive
   function.  An emitted Goodstein program is one Haskell cannot certify
   halts — epistemically back beside `GoodsteinSearch.lean`'s `partial def
   stopBySearch`, which is precisely the distinction P4 exists to draw.
   Agda, Idris, or Rocq would preserve it.
3. **The prelude is a second trusted boundary.**  The value symbols need
   Haskell copies whose fidelity is an assumption.  `hsPrelude` therefore
   splits them explicitly: the arithmetic, `fibN`, `pasN`, `xorN` are
   **implemented**; everything decoding Phase C's pairing (`bumpN`,
   `goodN`, `ordOf`, `oltN`, the Hydra/Hanoi coders, `lookN`) is a
   **stub** naming the Lean source to port from — deliberately an `error`
   rather than a plausible re-implementation that might silently diverge.
   So gcd, Fibonacci and Pascal emit to complete runnable Haskell;
   Goodstein, Hydra, Hanoi and Sperner emit structurally complete programs
   whose prelude must be finished first.

### Per-rule discipline: now seven sites

`emit` and `hsEmit` both match every constructor with **no wildcard**,
bringing the count to seven (`extract`, `derivBound`, `soundness`,
`extract_tracked`, `toSkel`, `emit`, `hsEmit`).  The ban matters more here
than anywhere else: a new content-bearing rule falling through to a
contentless realizer would still compile and still return answers, just
wrong ones.  A new function symbol also needs an `hsTerm` case.

### Out of scope, as stated

- No soundness theorem for `emit`, and no theorem relating it to `extract`.
- The Haskell prelude's pairing-dependent symbols are stubs, not
  implementations; the theorems needing them do not run in Haskell yet.
- No claim that the emitted programs are continuous, in `CtQ 2`, or
  otherwise inherit any property proved of `extract`.

## Refinement targets (the consolidation phase's agenda)

New-content work pauses after Sperner (the last *headline* theorem); the
Fibonacci on-ramp above is the one deliberate addition of the
consolidation period — a pedagogical easy case, and the `fib` prerequisite
Zeckendorf needs.  The next phase is refinement.

**Done in refinement so far:**
- **The level-free emitter (Phase X)** — a second extraction into native
  Lean types plus a Haskell backend, which finally *executes* the
  certified-but-unrunnable programs (gcd above all).  Full account in
  **Phase X** above, including what the agreement `#guard`s do and do not
  establish.
- **Presentation phase (P1–P7)** — the `#realizer` / `#realizerCH` /
  `#program` display commands, the `ProgramExtraction` witness-reading
  API, `GoodsteinSearch` (search versus descent), the first internalized
  fragment of `bumpNeZero`, and the paper.  Full account in **Phase P**
  above, including its four flagged items (`toCH`'s wildcard,
  `#program`'s string dispatch, `Meta/`'s changed status, and the paper's
  two necessity sentences).
- **Layered directory reorg** — the flat `Realizability/*.lean` (38 files) is
  now `Ordinals/` · `Signature/` (value layers) · `Core/` (the engine) ·
  `Common/` (shared lemmas) · `Theorems/<name>/`; imports follow the path.
  Pure `git mv` + import rewrites, build green.
- **Dependency vendored in — the build is now standalone.** The subset of
  the Kleene–Kreisel development this project actually depends on (the
  transitive closure of `ContinuousFunctionals.Hierarchy` + `CtQ`, **12
  files**) is copied verbatim into
  `Realizability/Core/ContinuousFunctionals/ContinuousFunctionals/*.lean`
  and built by an in-package `lean_lib «ContinuousFunctionals»`
  (`srcDir := "Realizability/Core/ContinuousFunctionals"`). The old symlink
  to `../kleene-kreisel-lean` and its `require` are gone; `lakefile.lean`
  now requires Mathlib directly, pinned to the same `v4.26.0` (verified: no
  dependency-rev drift in `lake-manifest.json`). Verified by cloning this
  repo alone, with no `kleene-kreisel-lean` nearby, and running `lake build`
  from a clean tree. The vendored files are a **read-only mirror**: `Density/`
  and `KleeneTree/` are not reachable and were not copied, and fixes belong
  upstream, not here. (This supersedes the earlier "do not vendor" note — the
  user's decision settled toward a self-contained, reproducible repository.)
- **Mathlib-conventions pass over the project's own 41 files** (the vendored
  mirror left untouched). Applied, each stage compile-verified: `fun … =>` →
  `↦` (533 arrows), the 4 over-limit lines wrapped, doc-strings added to the
  ~19 undocumented defs, Mathlib copyright headers + a `/-!` module docstring
  after the imports on every file (with an Apache-2.0 `LICENSE`, author
  *Ara Aslyan* — change the license here if a different one is wanted), and
  the one genuine naming drift `decEm → dec_em`. The auditor's residual
  flags are all false positives or deliberate vocabulary kept on purpose:
  the acronym-prefixed proofs (`MR_*`, `FR_*`, `CtxR_*` — `MR` = *Modified
  Realizes*, an acronym, rule 6) and the correctly-`UpperCamelCase`
  predicates/types (`PureType`, `CtQ`, `Tracked`, `FreeIn`, …) are **not**
  renamed — that would erase the project's own vocabulary, which the
  convention guide explicitly warns against. Axiom budgets and the
  choice-free `Epsilon0`/Hydra definitions are unchanged (cosmetic edits +
  a rename). `docs/first-order/DOSSIER.md` cites declarations by **name** (no line numbers),
  so it needed no resync beyond the rename; `docs/first-order/CONSTRUCTIVITY.md`'s two
  line-number citations were re-synced to the post-header positions.

**Remaining targets** noticed while building E2/S1, to be worked from real
uses rather than speculation:

- **The operation-library idea** (the conservative-definitional-extension
  route): package `monus`/difference handling as a *defined relation* with
  its defining property and a small lemma library, so subtraction-heavy
  proofs (a future Bézout, a retrofit of `gcd`) stop re-deriving the
  difference-as-existential-witness algebra ad hoc.  Reserve a *signature*
  symbol only where **statability** forces it (CRT's `mod`, Sperner's
  `look`), not for mere operations.  Grounded in: the `gcdTheorem` proof's
  size is ~half this algebra.
- **The generic `natStrongInd` former** (deferred "approach B"): `gcd`
  inlined the strong-induction scaffold; a generic-in-`φ` former (needing
  the substitution-composition library, already partly in
  `StrongInduction.lean`) would amortize it across future course-of-values
  proofs.  Build it if a second real use appears.
- **The pure-type `#eval` wall** is now a recurring theme (`gcd` at 41,
  Sperner at 11): the interpreter overflows on ambient-N realizers.
  Sperner found a partial answer (the witness is ambient-independent, so
  read it low).  Worth a general note / helper, and possibly measuring
  whether a compiled runner lifts the wall.
- **`gcd` cleanup**: the 525-line proof has deep `set`-context `wk` chains
  and duplicated branch machinery that a factored recombination lemma (or
  the library above) could shrink.
- Documentation: keep docs/first-order/HYDRA.md-style maps and the `#print axioms` quotes
  in step; the signature is now 21 symbols / 76 rules (Fibonacci's `fib`
  and its four schemas `fibZero`/`fibOne`/`fibSucc`/`eqCongFib`).

**Added by Phase X** (the emitter's own gaps, in priority order):

- **A soundness theorem for `emit`** — the phase's obvious sequel and the
  thing that would move the emitted programs from "checked at points" to
  "certified".  Two routes: prove `emit D` realizes `φ` directly in a
  `tyOf`-valued relation (a second, much simpler `MR`), or relate `emit D`
  to `extract D` through the transports.  The first looks far easier and
  would not need the pure-type layer at all.
- **Finish the Haskell prelude** — port the pairing-dependent symbols from
  `Epsilon0`/`Hydra`/`Hanoi`/`Coloring`, so Goodstein, Hydra, Hanoi and
  Sperner run in Haskell as gcd, Fibonacci and Pascal already do.  Worth
  doing only with a differential check against the Lean values, since the
  whole risk is silent divergence.
- **An OCaml backend** — strict evaluation gives a predictable cost model
  (the Haskell numbers above are muddied by laziness), and it is Coq
  extraction's default target, so the comparison to prior work is direct.
  `hsEmit` is the template; only the printer changes.

**Added by Phase P** (each is a flagged item from the section above, with
the fix already identified — these are the shortest items on the list):

- **Move `ProgramExtraction` from `Meta/` to `Core/`.**  Three certified
  extraction modules now depend on it, so `Meta/` no longer satisfies its
  own "zero certified impact" description.  Moving it restores the
  invariant; amending `CLAUDE.md` instead would weaken it.
- **Remove `toCH`'s wildcard** (~60 one-line cases through a shared
  contentless helper).  Its current safety argument is wrong: after a new
  rule is added to `toSkel`, `toCH` silently mislabels rather than
  failing to build.
- **Give `Skel` a structured rule tag** so `#program` stops dispatching on
  display-string prefixes, where a label rename degrades the output with
  no error.
- **Finish the `ProgramExtraction` migration** (4 of 7 call sites remain),
  which needs one new shape: a reader for a witness under `∧` — Fibonacci's
  `fstPT (fstPT …)`.
- **Fix the paper's two necessity sentences** (≈ lines 1315, 1521): cite
  Kirby–Paris and add "not formalized here", matching how the same file
  already handles Gentzen.
- **CI for `lake build`** — `docs/internal/RESEARCH_PLAN.md` Phase 1 lists it for
  Aug–Sep 2026 and there is no `.github/`.  For a project whose test
  suite *is* the build, this is the largest gap between the plan and the
  repository.
- **The 17 linter warnings** (unused variables, unused `simp` arguments),
  also a `docs/internal/RESEARCH_PLAN.md` Phase 1 item: fix or intentionally silence.
