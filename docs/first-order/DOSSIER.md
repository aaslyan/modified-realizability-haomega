# Research Fact Dossier — `modified-realizability-lean`

Internal research notebook. **Not a paper.** Every entry is grounded in a Lean
declaration or a quoted comment. Evidence levels: **E0** direct theorem · **E1**
immediate corollary · **E2** definition · **E3** structural code observation ·
**E4** documentation/comment claim (quoted) · **E5** interpretation/inference.
E4/E5 are never presented as E0.

Fact IDs are cluster-prefixed and traceable:
`ARCH`/`STAT`/`CONST`/`KK` (cross-cutting, authored from the axiom audit and direct
inspection) · `CORE` (object language + MR) · `EXT` (extraction/soundness/continuity) ·
`ORD` (ε₀ + transfinite induction) · `GOOD` (Goodstein) · `HYD` (Hydra) ·
`HP` (Hanoi + Pascal/Lucas) · `ES` (Euclid/gcd + Sperner).

The full cluster fact-entries are in §CLUSTER FACTS below; the cross-cutting facts
and the synthesis (§FINAL SUMMARY) are here at the top.

---

## Repository Architecture

==============================================================
Fact ID: ARCH-001
Title: Layered directory structure
Category: Repository Architecture
Evidence Level: E3
File: Realizability/ (tree) ; CLAUDE.md
Lean declarations: —
Summary: 38 `.lean` modules under five layers — `Ordinals/` (ε₀ substrate), `Signature/` (the value layers `Term.eval` evaluates by), `Core/` (the realizability engine), `Common/` (shared lemmas), `Theorems/<name>/` (each headline result).
Evidence: Directory tree: `Realizability/{Ordinals/Epsilon0, Signature/{Hydra,Hanoi,Pascal,Coloring,OrdinalAssignment}, Core/{Syntax,ModifiedRealizes,Transport,Extraction,Soundness,GenericContinuity,CollapseDemo}, Common/{Arithmetic,Exists,StrongInduction}, Theorems/{Goodstein,Hydra,Hanoi,Pascal,Euclid,Sperner}/}`. Imports follow the path (`import Realizability.Core.Syntax`).
Dependencies: —
Used later for: Architecture figure; module dependency graph
Confidence: High
Notes: Value layers (`Signature/`) precede `Core/Syntax` because `Term.eval` interprets their functions — so `Core` depends on `Signature`, a deliberate layering, not a cycle.
==============================================================
Fact ID: ARCH-002
Title: The per-rule discipline — every rule touches four sites; every symbol touches ~16
Category: Repository Architecture
Evidence Level: E4
File: CLAUDE.md ; corroborated by EXT-001/027, EXT-028, EXT-032, CORE-011
Lean declarations: extract, derivBound, soundness, extract_tracked, termEval_continuous
Summary: Each of the 72 `Deriv` rules has a matching case in exactly four places — `extract` + `derivBound` (Extraction), `soundness` (Soundness), `extract_tracked` (GenericContinuity); adding a function symbol additionally needs a `termEval_continuous` case plus cases in `Term.eval`/`vars`/`subst`/`eval_subst`/`eval_congr` (~16 sites total).
Evidence: QUOTE (CLAUDE.md): "Every derivation rule has a matching case in **four places** … No case may be left silent." Confirmed structurally by EXT-027/028 (one `*_tracked` per combinator), EXT-032 (`termEval_continuous` one arm per symbol).
Dependencies: —
Used later for: Methodology / extensibility discipline figure
Confidence: High
Notes: The `look` symbol was added through all sites in the Sperner phase (CORE-002).
==============================================================
Fact ID: ARCH-003
Title: Two headline theorems derived inside the fragment; two out-of-scope claims fenced
Category: Repository Architecture
Evidence Level: E4
File: CLAUDE.md
Lean declarations: goodsteinTheorem, hydraTheorem, hercules_wins
Summary: The stated scope: Goodstein's theorem (`∀m∃t. good(m,t)=0`) and the Kirby–Paris Hydra theorem (`∀h∃t. hydra(h,t)=0`) derived inside the fragment, each with certified extracted witness; the Hydra theorem also proved metatheoretically in strategy-free form (`hercules_wins`). Explicitly: neither independence result (unprovability in PA) is formalized, and neither may be claimed.
Evidence: QUOTE (CLAUDE.md): "Neither independence result (unprovability in PA) is formalized, and neither may be claimed."
Dependencies: —
Used later for: Scope/limitations section
Confidence: High
Notes: See ORD-018, HYD-027 for the in-source negative facts.
==============================================================
Fact ID: ARCH-004
Title: Dependency on the Kleene–Kreisel `ContinuousFunctionals` project (in-tree symlink)
Category: Repository Architecture
Evidence Level: E3
File: lakefile.lean ; Realizability/Core/ContinuousFunctionals (symlink)
Lean declarations: —
Summary: The build requires the sibling Kleene–Kreisel development, declared `require ContinuousFunctionals from "Realizability/Core/ContinuousFunctionals"` — an in-tree symlink → `../kleene-kreisel-lean`; it supplies `PureType`, `Continuous2`, `Ct`, `CtQ`, `Assoc`, `CtPer`, `ctQTwoEquiv`.
Evidence: `lakefile.lean` require line; only two of its modules are imported (`ContinuousFunctionals.Hierarchy`, `ContinuousFunctionals.CtQ`).
Dependencies: —
Used later for: TCB; dependency figure
Confidence: High
Notes: Interim symlink; pinning as a git dependency is a deferred decision (docs/internal/QUESTIONS.md).
==============================================================

## Repository Statistics

==============================================================
Fact ID: STAT-001
Title: 38 Lean modules, 14,244 lines
Category: Repository Statistics
Evidence Level: E3
File: Realizability/ (measured)
Lean declarations: —
Summary: 38 `.lean` files totalling 14,244 lines. By layer: Ordinals 1 file/1,050; Signature 5/2,440; Core 7/4,439; Common 3/1,134; Theorems/Goodstein 5/1,203; Hydra 6/1,288; Hanoi 2/373; Pascal 4/1,084; Euclid 3/969; Sperner 2/264.
Evidence: `find … -name '*.lean' | wc` and per-directory counts (measured this session).
Dependencies: —
Used later for: Repository-scale table
Confidence: High
Notes: —
==============================================================
Fact ID: STAT-002
Title: 708 lake jobs green, zero `sorry`/`admit`
Category: Repository Statistics
Evidence Level: E3
File: whole build
Lean declarations: —
Summary: `lake build` completes with 708 jobs and no `sorry`/`admit`; correctness is the build.
Evidence: `Build completed successfully (708 jobs)` (measured). No `sorry`/`admit` in any module.
Dependencies: —
Used later for: Rigor claim
Confidence: High
Notes: 26 modules embed `#print axioms` checks run every build (STAT-007).
==============================================================
Fact ID: STAT-003
Title: 20 function symbols + `var` (21 `Term` constructors)
Category: Repository Statistics
Evidence Level: E0/E3
File: Realizability/Core/Syntax.lean
Lean declarations: Term
Summary: The signature is 20 function symbols `{zero, succ, plus, times, pred, exp, bump, good, prec, ord, hcut, hydra, hord, hcons, happ, mvcount, solves, xor, pas, look}` plus `var`; `Term` has 21 constructors.
Evidence: Enumerated from the `Term` inductive (see CORE-001).
Dependencies: —
Used later for: Signature table
Confidence: High
Notes: `solves` is 5-ary; five symbols (`bump/prec/hcut/xor/look`) enter by numeral graph (CORE-019/043).
==============================================================
Fact ID: STAT-004
Title: 72 natural-deduction rules
Category: Repository Statistics
Evidence Level: E3
File: Realizability/Core/Syntax.lean
Lean declarations: Deriv
Summary: The `Deriv` inductive family (`Type`-valued) has exactly 72 constructors: 11 intuitionistic structural rules, `ind`, `tiEps0`, `exI`/`exE`, three Peano axiom schemas, the equational-logic kit (refl/symm/trans + one congruence per symbol), the recursion-equation schemas, and five numeral-graph schemas.
Evidence: Enumerated constructor-by-constructor (see CORE-011).
Dependencies: —
Used later for: Rule-family table
Confidence: High
Notes: Only `tiEps0` is not a consequence of the fragment's own resources (CORE-014).
==============================================================
Fact ID: STAT-005
Title: Documentation corpus (8 markdown files)
Category: Repository Statistics
Evidence Level: E3
File: repository root
Lean declarations: —
Summary: docs/first-order/STATUS.md (3,353 lines, authoritative record), docs/first-order/HYDRA.md (445), READERS_GUIDE.md (390), docs/first-order/CONSTRUCTIVITY.md (387, the axiom audit), docs/internal/NOTES_insertExp_monotonicity.md (306), docs/internal/QUESTIONS.md (296, decision log), CLAUDE.md (110), README.md (100).
Evidence: `wc -l *.md` (measured).
Dependencies: —
Used later for: Documentation-discipline section
Confidence: High
Notes: docs/internal/QUESTIONS.md logs design forks with resolutions (e.g. items 17 gcd-precondition, 18 Sperner colors).
==============================================================
Fact ID: STAT-006
Title: 49 commits
Category: Repository Statistics
Evidence Level: E3
File: git history
Lean declarations: —
Summary: 49 commits; the phase structure (A–H, Z0, E, F, G, S) is reflected in the commit messages.
Evidence: `git rev-list --count HEAD = 49` (measured).
Dependencies: —
Used later for: Development-history note
Confidence: High
Notes: —
==============================================================
Fact ID: STAT-007
Title: 26 modules carry embedded `#print axioms` checks
Category: Repository Statistics
Evidence Level: E3
File: Realizability/ (grep)
Lean declarations: —
Summary: 26 of 38 modules end with `#print axioms` commands on their headline realization/continuity results, enforcing the axiom budgets at every build.
Evidence: `grep -rl "#print axioms" Realizability | wc -l = 26` (measured).
Dependencies: —
Used later for: Axiom-hygiene methodology
Confidence: High
Notes: The literal budget strings are build output, not in source text (agents noted this per-file as E5).
==============================================================

## Trusted Computing Base / Constructivity (verified by `#print axioms`, this session)

==============================================================
Fact ID: CONST-001
Title: Every executable object is `Classical.choice`-free
Category: Trusted Computing Base
Evidence Level: E0
File: Realizability/Core/{Extraction,ModifiedRealizes,Transport}.lean etc.
Lean declarations: extract, indRecC, tiRecC, up, down, pairPT, fstPT, app₁, abs₁, natPT, defaultPT, liftR, dropR, MR, Function.update, WellFounded.fix
Summary: `#print axioms` reports `extract`, `tiRecC`, `tiRecC_eq`, `tiC` as `[propext, Quot.sound]`; `indRecC`, `indC`, `allIC`, `axiomC`, `up`, `down`, `pairPT`, `fstPT`, `app₁`, `abs₁`, `natPT`, `defaultPT`, `liftR`, `dropR`, `MR`, `Function.update`, `WellFounded.fix` as **no axioms**. **No `Classical.choice` anywhere in the executable layer.**
Evidence: Literal `#print axioms` outputs (run this session).
Dependencies: —
Used later for: Constructivity claim; TCB table
Confidence: High
Notes: `propext`/`Quot.sound` in `extract`/`tiRecC` enter via `oLt_wf` (a termination certificate, erased at runtime) — see CONST-005.
==============================================================
Fact ID: CONST-002
Title: Every extracted program is `[propext, Quot.sound]`
Category: Trusted Computing Base
Evidence Level: E0
File: Theorems/*/…Extraction.lean
Lean declarations: goodsteinStopTime, hanoiSolution, gcdWitness, spernerWitness, spernerScan
Summary: `#print axioms` reports `goodsteinStopTime`, `hanoiSolution`, `gcdWitness`, `spernerWitness`, `spernerScan` all as `[propext, Quot.sound]` — no `Classical.choice`. Same for the derivation proof-objects `goodsteinTheorem`/`hydraTheorem`/`hanoiTheorem`/`gcdTheorem`/`spernerTheorem`/`hercules_wins`.
Evidence: Literal `#print axioms` outputs (this session).
Dependencies: —
Used later for: Constructivity claim
Confidence: High
Notes: The `propext`/`Quot.sound` are framework infrastructure (extract contains the `tiRecC`/`oLt_wf` case regardless of whether a given theorem uses `tiEps0`); an `ind`-only extractor would be axiom-free.
==============================================================
Fact ID: CONST-003
Title: `Classical.choice` source ① — Mathlib environment lemmas, Prop-only
Category: Constructivity
Evidence Level: E0
File: Mathlib.Logic.Function.Basic ; Core/ModifiedRealizes.lean ; Core/Soundness.lean
Lean declarations: Function.update_comm, Function.update_idem, MR_subst, soundness, MR_indRecC, MR_tiRecC
Summary: `soundness`, `MR_indRecC`, `MR_tiRecC`, `MR_subst`, and the `_spec` theorems report `[propext, Classical.choice, Quot.sound]`. Traced by bisection: `MR_congr` (which avoids the update lemmas) is choice-free; `MR_subst` (which uses `Function.update_comm`/`Function.update_idem`, both `#print axioms` = `[propext, Classical.choice, Quot.sound]`) carries the choice. All in `Prop`; the `Function.update` *definition* is choice-free.
Evidence: `#print axioms Function.update_comm`/`update_idem` = classical; `#print axioms MR_congr` = `[propext, Quot.sound]` vs `MR_subst` = classical (this session). Usage sites: ModifiedRealizes.lean 285/300/313/337, Soundness.lean 79 + via MR_subst.
Dependencies: —
Used later for: TCB; constructivity §; "removable" analysis
Confidence: High
Notes: These two lemmas are constructively true (funext + DecidableEq); a local reproof would make soundness `[propext, Quot.sound]`. Removability: Easy–Moderate.
==============================================================
Fact ID: CONST-004
Title: `Classical.choice` source ② — the `CtQ` extensional collapse (packaging)
Category: Constructivity
Evidence Level: E0
File: ContinuousFunctionals (dependency) ; Core/CollapseDemo.lean
Lean declarations: RealizesCtQ, ContinuousFunctionals.{Ct, CtQ, Assoc, CtPer}
Summary: `RealizesCtQ` reports `[propext, Classical.choice, Quot.sound]`, inherited from `Ct`/`CtQ`/`Assoc`/`CtPer` in the Kleene–Kreisel dependency (all `[propext, Classical.choice, Quot.sound]`). It is semantic packaging (the extensional-collapse class), used only when forming a `CtQ 2` class; no extracted program depends on it.
Evidence: `#print axioms RealizesCtQ`, `#print axioms ContinuousFunctionals.CtQ/Ct/Assoc/CtPer` (this session).
Dependencies: —
Used later for: TCB; constructivity §
Confidence: High
Notes: The dependency's computational core is choice-free — see KK-002. Removability: Hard/inherent.
==============================================================
Fact ID: CONST-005
Title: `extract_continuous` is choice-free; `propext`/`Quot.sound` are Lean-kernel packaging
Category: Constructivity
Evidence Level: E0
File: Core/GenericContinuity.lean ; Ordinals/Epsilon0.lean
Lean declarations: extract_continuous, oLt_wf
Summary: `extract_continuous` reports `[propext, Quot.sound]` (no choice) — the continuity theorem is constructive. `propext` and `Quot.sound` are Lean's kernel axioms, do not imply excluded middle, and in `extract`/`tiRecC` they occur inside `oLt_wf` (the ε₀ well-foundedness *proof* consumed by `WellFounded.fix`, `#print axioms oLt_wf = [propext, Quot.sound]`, erased in compiled code) — computationally inert.
Evidence: `#print axioms extract_continuous` = `[propext, Quot.sound]`; `#print axioms oLt_wf` = `[propext, Quot.sound]` (this session).
Dependencies: —
Used later for: Constructivity §; the standard "constructive = no Classical.choice" criterion
Confidence: High
Notes: `WellFounded.fix` itself is axiom-free (CONST-001), so `tiRecC` adds no axiom of its own.
==============================================================
Fact ID: CONST-006
Title: Verdict — constructive except for proof packaging; TCB of programs = {kernel, propext, Quot.sound}
Category: Trusted Computing Base
Evidence Level: E5
File: docs/first-order/CONSTRUCTIVITY.md (this session's audit)
Lean declarations: —
Summary: Every executable artifact depends only on `propext`, `Quot.sound`, never `Classical.choice`; the single classical axiom is confined to (i) Prop-level correctness proofs (via two Mathlib environment lemmas) and (ii) the `CtQ` collapse. The Trusted Computing Base of every extracted computation is { Lean kernel, `propext`, `Quot.sound` } — no classical content.
Evidence: Synthesis of CONST-001..005 (inference over verified E0 facts).
Dependencies: CONST-001, CONST-002, CONST-003, CONST-004, CONST-005
Used later for: Paper TCB section (headline)
Confidence: High
Notes: Marked E5 because it is the interpretive conclusion; every constituent fact is E0.
==============================================================
Fact ID: CONST-007
Title: `derivBound` and `#eval` feasibility per theorem
Category: Performance
Evidence Level: E0/E3
File: Theorems/*/…Extraction.lean
Lean declarations: goodstein_derivBound, hanoi_derivBound, pas_derivBound, hydra_derivBound, gcd_derivBound, sperner_derivBound
Summary: Certified ambient bounds: Goodstein 12, Hydra 12, Pascal(Total) 8, Hanoi 26, gcd 41, Sperner(body) 11; binEven 18, binOdd 22. `#eval` feasibility tracks the bound and the encoding: Goodstein m≤1, Hanoi n≤4, Pascal rows≤8 run; gcd (41) does not run at all; Sperner runs only via the lower-ambient `spernerScan`.
Evidence: `theorem *_derivBound : … = N := rfl` in each extraction file (GOOD-029, HP-019, HP-032, HYD-029, ES-022, ES-034); `#eval`/`#guard` observations (GOOD-032, HP-022, HYD-030, ES-024, ES-036).
Dependencies: —
Used later for: Performance table
Confidence: High
Notes: The pure-type wall is ambient-driven (`pairPT`/`up`/`down` nested N deep); the encoding wall (Hanoi n=5) is code-magnitude-driven (HP-011).
==============================================================

## Kleene–Kreisel Dependency (axioms verified this session; structure partly inferred — the KK reader did not finish)

==============================================================
Fact ID: KK-001
Title: `PureType` and `Continuous2` are axiom-free (the computational core of the dependency)
Category: Kleene–Kreisel Infrastructure
Evidence Level: E0
File: ContinuousFunctionals (Hierarchy)
Lean declarations: ContinuousFunctionals.PureType, ContinuousFunctionals.Continuous2
Summary: `#print axioms` reports `PureType` (the pure/finite-type hierarchy where realizers live) and `Continuous2` (the type-2 continuity predicate the realizability project uses) as depending on **no axioms** — the parts of the dependency the executable pipeline touches are fully constructive.
Evidence: `#print axioms ContinuousFunctionals.PureType` / `Continuous2` (this session).
Dependencies: —
Used later for: TCB; constructivity of the realizer types
Confidence: High
Notes: This is why `extract`/`extract_continuous` avoid `Classical.choice`.
==============================================================
Fact ID: KK-002
Title: `Ct`/`CtQ`/`Assoc`/`CtPer` depend on `Classical.choice` (the collapse is classical)
Category: Kleene–Kreisel Infrastructure
Evidence Level: E0
File: ContinuousFunctionals (CtQ)
Lean declarations: ContinuousFunctionals.Ct, .CtQ, .Assoc, .CtPer
Summary: `#print axioms` reports `Ct`, `CtQ`, `Assoc`, `CtPer` (the continuous functionals, their extensional collapse, and the associate/partial-equivalence layer) all as `[propext, Classical.choice, Quot.sound]` — the classical part of the dependency, entering the realizability project only through `RealizesCtQ`.
Evidence: `#print axioms ContinuousFunctionals.Ct/CtQ/Assoc/CtPer` (this session).
Dependencies: —
Used later for: TCB; constructivity §
Confidence: High
Notes: `CtQ` is defined via a quotient (extensional equality). `ctQTwoEquiv` (the equivalence `CtQ 2 ≃ {continuous type-2 functionals}`) is what `RealizesCtQ` uses.
==============================================================
Fact ID: KK-003
Title: The pipeline imports only two dependency modules; the collapse is used at one place
Category: Kleene–Kreisel Infrastructure
Evidence Level: E3
File: Realizability/**.lean (imports)
Lean declarations: ContinuousFunctionals.Hierarchy, ContinuousFunctionals.CtQ
Summary: The realizability project imports exactly `ContinuousFunctionals.Hierarchy` (→ `PureType`) and `ContinuousFunctionals.CtQ` (→ `CtQ`, `ctQTwoEquiv`); the classical `CtQ` is consumed only in `RealizesCtQ` and the per-theorem `…RealizesCtQ` wrappers.
Evidence: `grep "ContinuousFunctionals\." Realizability/*` = `CtQ`, `Hierarchy`; `RealizesCtQ` in CollapseDemo.lean (EXT-035).
Dependencies: —
Used later for: Dependency-surface figure
Confidence: High
Notes: `up`/`down`/`pairPT`/`app₁` etc. are defined **in the realizability project** (`ModifiedRealizes.lean`, CORE-034/036), not in the dependency.
==============================================================
Fact ID: KK-004
Title: The continuity invariant deliberately avoids the dependency's open "associate/countability" chapter
Category: Continuous Functionals
Evidence Level: E4
File: Realizability/Core/GenericContinuity.lean
Lean declarations: Tracked, extract_continuous
Summary: The chosen continuity invariant is NOT "the extract has an associate at every ambient" (the parent project's deferred countability chapter, whose hard core is associate-level abstraction closure); the oracle-parameterized `Tracked` relation sidesteps associate construction entirely.
Evidence: QUOTE (GenericContinuity.lean header, via EXT-039): "The compositional invariant is *not* 'the extract has an associate at every ambient' (that is the parent project's deferred countability chapter …). It is the **oracle-parameterized continuity relation** … it sidesteps associate construction entirely."
Dependencies: EXT-025, EXT-026, EXT-039
Used later for: Continuous Functionals §; relation to parent project's open work
Confidence: High
Notes: KK reader agent did not finish (session limit); the associate/`Assoc`/`Ct` semantics are documented only at the level the realizability project's own comments state (CORE-031, EXT-035).
==============================================================

---

# FINAL SUMMARY

## 1. All facts

- Cross-cutting: `ARCH-001..004`, `STAT-001..007`, `CONST-001..007`, `KK-001..004`.
- Object language + MR: `CORE-001..044`.
- Extraction/soundness/continuity: `EXT-001..041`.
- ε₀ + transfinite induction: `ORD-001..037`.
- Goodstein (+ Arithmetic, Exists): `GOOD-001..035`.
- Hydra: `HYD-001..043`.
- Hanoi + Pascal/Lucas: `HP-001..045`.
- Euclid/gcd + Sperner (+ StrongInduction, Coloring): `ES-001..038`.

Total ≈ 300 fact entries. Full bodies in §CLUSTER FACTS.

## 2. Strongest scientific contributions

- **SC1 — Two consistency-strength theorems inside one minimal fragment, with certified extracted witnesses.** Goodstein's theorem `∀m∃t. good(m,t)=0` [GOOD-025, GOOD-026] and the Kirby–Paris Hydra theorem `∀h∃t. hydra(h,t)=0` [HYD-025], both by the single transfinite-induction rule `tiEps0` [CORE-014, ORD-017], each yielding an extracted witness function certified correct at *every* input by soundness [GOOD-030, HYD-029]. Supports: the headline result.
- **SC2 — Generic continuity of extraction.** *Every* closed derivation's extracted type-2 realizer is `Continuous2` [EXT-024], via an oracle-parameterized (Kripke) logical relation `Tracked` [EXT-025] whose abstraction-closure case holds by β-reduction so **no associates are ever constructed** [EXT-026]; the brief's `lvl φ ≤ 1` restriction is dropped [EXT-038].
- **SC3 — The extracted computational content is fully constructive.** All executables depend only on `propext`, `Quot.sound`, never `Classical.choice` [CONST-001, CONST-002]; the one classical axiom is confined to Prop-level correctness proofs [CONST-003] and the semantic collapse [CONST-004]. TCB of the programs = {kernel, propext, Quot.sound} [CONST-006].
- **SC4 — The strategy-free Hydra theorem in the metatheory.** `hercules_wins : WellFounded PlayRel` — every play finite for any choice of head and any replication [HYD-033], with the fragment's leftmost battle shown to be one such play [HYD-036] and genuine nondeterminism exhibited [HYD-037]. The fragment provably *cannot state* this (no function variables) [HYD-034].
- **SC5 — One realizability/extraction pipeline spanning PA-strength and beyond.** Goodstein/Hydra use `tiEps0`; Hanoi [HP-013], Pascal-mod-2 [HP-029], gcd [ES-016], and 1D Sperner [ES-028] are ordinary-`ind` theorems — demonstrating the fragment reaches a branching recursion (Hanoi), a decision procedure (Pascal), the Euclidean algorithm (gcd), and the discrete IVT (Sperner) on the same infrastructure.

## 3. Strongest engineering contributions

- **EC1 — Flexible-ambient-level modified realizability** eliminating all level-coercion bookkeeping (all `MR` clauses at one ambient) [CORE-028, CORE-030].
- **EC2 — One-named-combinator-per-rule extraction**, with the identical per-rule discipline mirrored in `soundness` and `extract_tracked` [EXT-001, EXT-041, EXT-027, ARCH-002].
- **EC3 — Hand-rolled, kernel-computable, `Classical`-free ε₀ substrate** (triangular pairing, CNF order, `oLt_wf`) — deliberately not Mathlib's `Nat.pair` (choice-dependent, non-reducing) [ORD-003, ORD-004, ORD-013], which is what keeps the continuity budget at `[propext, Quot.sound]`.
- **EC4 — The two-ambient extraction trick** (witness numeral is ambient-independent; read a certified-but-unrunnable high-ambient realizer at a low ambient) [ES-035], and the **memoization null-result** kept as record with its `csimp` lemmas detached [EXT-013, EXT-014].
- **EC5 — Two reusable naive-substitution dodges**: naming the IH instance with a fresh `∀` [GOOD-027] and α-renaming the IH [HP-017], composed together in gcd [ES-019].
- **EC6 — Formula-indexed level transports** `liftR`/`dropR` + `famOf`, the "sole blocker for extraction" resolved [CORE-038, CORE-042].

## 4. Strongest reusable abstractions

- `tiEps0` rule + `tiRecC` recursor along `≺` [CORE-014, EXT-004]. — RA1
- Order and divisibility as `∃`-encodings with **zero new symbols** [ES-001, ES-011]. — RA2
- Strong induction **derived** from ordinary `ind` [ES-007]. — RA3
- The single cons-list encoding reused by Hydra, Hanoi, and Sperner [HYD-002, HP-002, ES-038]. — RA4
- The `Tracked` oracle-parameterized continuity relation [EXT-025]. — RA5
- `famOf` + the transports, packaging one realizer into a bounded realizing family [CORE-042]. — RA6
- `axiomC` — contentless realizers for atomic/implication schemas [EXT-008]. — RA7

## 5. Biggest surprises

- **The memoization is a complete no-op** — 2376/2377 recursor entries at the *same* code, yet 0 ms saved, because the recursor value is `O(1)` (a closure) and the cost is in *applications*, which no code-keyed table reaches [EXT-013, EXT-014].
- **Along the ordinal descent the codes are not numerically decreasing** (`…,2,10,…`) — the descent is genuinely along `≺`, not `<` [ORD-028]; and the Hydra ordinal falls exactly where the tree *grows* [HYD-008, HYD-018].
- **The extract is choice-free while its correctness proof is not** — `Classical.choice` enters `soundness` only through two Mathlib `Function.update` lemmas [CONST-003].
- **Hydra length 37 (not 11) is the discriminating fingerprint** of the grandparent rule + copy count vs the other game in circulation [HYD-009, HYD-039].
- **gcd needs no positivity precondition** — `gcd(0,0)=0` realizes the spec [ES-018].
- **The witness numeral is ambient-independent**, letting a low ambient run what the certified ambient cannot [ES-035].
- **1D Sperner holds for arbitrary ℕ colorings**; `{0,1}` is never used [ES-029].

## 6. Unresolved questions

- Generic-in-φ strong-induction former (the substitution-lemma library exists; the former does not) [ES-008].
- Internalizing the imported schemas (`ordDescent`, `hordCutLt`) into the object theory — "research-scale, not a phase" [ORD-033, HYD-021].
- PA-independence of Goodstein/Hydra is **not** formalized and must not be claimed [ORD-018, HYD-027, ARCH-003].
- Removing `Classical.choice` from `soundness` (reprove `Function.update_comm`/`idem` constructively) — Easy–Moderate [CONST-003].
- The pure-type evaluation wall (gcd never runs; Hydra code-2, Hanoi n=5 don't finish) [ES-024, HYD-030, HP-011].
- Strategy-independence of Hydra battle length is checked at instances, not proved [HYD-043].

## 7. Candidate "wow moments"

- W1: `#eval goodsteinStopTime 1 = 1` — a Goodstein stopping time *computed by a program extracted from the fragment's own proof* [GOOD-032].
- W2: The Sierpiński gasket printed by the *extracted* Pascal decider, where "every cell is one instance of the proved disjunction resolved by the realizer itself" [HP-034, HP-033].
- W3: The Hydra battle trace — tree grows to 5× its size while its ordinal strictly falls, `battleLenH 200 1 (path 3) == 37` build-checked [HYD-040, HYD-039].
- W4: Two syntactically different proofs of `A∧B→B∧A` collapse to the same `CtQ 2` element [EXT-036].
- W5: The rightmost-head strategy's termination in **one line** because H7 generalized the descent [HYD-042].
- W6: The whole executable content is `Classical.choice`-free — machine-verified [CONST-001, CONST-002].

## 8. Candidate paper figures

- FIG1 — Extraction pipeline: `Deriv [] φ → extract → PureType realizer → executable → _spec`, annotated with axiom budgets. [EXT-001, EXT-018, CONST-002]
- FIG2 — Signature (20 symbols) × schema-type (open-term vs numeral-graph) and the 72-rule family. [CORE-001, CORE-011, CORE-019]
- FIG3 — Hydra battle trace in bracket notation with ordinals beside each state (tree grows, ordinal falls). [HYD-040, HYD-008]
- FIG4 — Sierpiński gasket from the extracted decider. [HP-034]
- FIG5 — Ordinal-code descent for Goodstein and Hydra (codes not monotone in `<`). [ORD-028, HYD-018]
- FIG6 — The per-rule discipline: each rule → {extract, derivBound, soundness, tracked}; each symbol → +{eval,vars,subst,eval_subst,eval_congr,termEval_continuous}. [ARCH-002]
- FIG7 — Constructivity map: `Classical.choice` confined to two boxes (Prop proofs via `update_comm/idem`; `CtQ` collapse), disjoint from all executables. [CONST-003, CONST-004]
- FIG8 — Layered module dependency graph. [ARCH-001]

## 9. Candidate paper tables

- TAB1 — Object → Axioms (the `#print axioms` table). [CONST-001..005, KK-001..002]
- TAB2 — Per-theorem: statement · induction principle (`tiEps0`/`ind`) · capture-dodge used · `derivBound` · `#eval` reach · limitation. [GOOD-025/029/032, HYD-025/029/030, HP-013/019, ES-016/022/024, ES-028/034, HP-029/032]
- TAB3 — Signature symbols → value function → schema (recursion-equation vs numeral-graph vs congruence). [CORE-003, CORE-018, CORE-019, CORE-043]
- TAB4 — Reuse matrix: which theorem uses ε₀/tiEps0, cons-list encoding, order layer, strong induction, `∃`. [ORD-017, HYD-002, HP-002, ES-001, ES-007]

## 10. Candidate paper claims (each supported by explicit Fact IDs)

- **C1.** A 20-symbol, 72-rule intuitionistic arithmetic fragment with a single transfinite-induction rule proves Goodstein's theorem and the Kirby–Paris Hydra theorem, each with a certified extracted witness function. — [STAT-003, STAT-004, CORE-014, GOOD-025, GOOD-030, HYD-025, HYD-029]
- **C2.** Every closed derivation's extracted type-2 realizer is continuous, proved through an oracle-parameterized logical relation that constructs no associates; the level restriction of the original brief is unnecessary. — [EXT-024, EXT-025, EXT-026, EXT-038]
- **C3.** All extracted programs are constructive: their axiom footprint is `[propext, Quot.sound]`, never `Classical.choice`; the one classical axiom lives only in Prop-level correctness proofs (via `Function.update_comm`/`idem`) and the `CtQ` collapse, so the TCB of every computation is {kernel, propext, Quot.sound}. — [CONST-001, CONST-002, CONST-003, CONST-004, CONST-006]
- **C4.** Order and divisibility are added with zero new symbols (as `∃`-over-`+`/`×`), and course-of-values induction is derived from ordinary induction. — [ES-001, ES-011, ES-007]
- **C5.** The extracted gcd witness is a greatest common divisor with no `gcd` symbol and no positivity precondition (`gcd(0,0)=0`). — [ES-016, ES-018, ES-023]
- **C6.** 1D Sperner / the discrete IVT is derived for arbitrary ℕ-valued colorings; the extracted search is a genuine forward scan returning the first crossing. — [ES-028, ES-029, ES-036]
- **C7.** Modified realizability of `∃` reuses the `∨` machinery and costs no ambient level, so witness extraction is uniform with disjunction. — [CORE-037, GOOD-011, EXT-009]
- **C8.** The Hydra theorem is proved twice — once inside the fragment (one battle), once in the metatheory over all strategies (`hercules_wins`) — the split forced because the fragment has no function variables. — [HYD-025, HYD-033, HYD-034, CORE-044]
- **C9.** The transfinite recursor `tiRecC` is the only well-founded recursion in the pipeline; its well-foundedness certificate `oLt_wf` is elementary and `Classical`-free, which is what holds the continuity budget at `[propext, Quot.sound]`. — [EXT-004, EXT-005, ORD-013, ORD-014, CONST-005]
- **C10.** A fully verified memoization of the transfinite recursor changes evaluation time by nothing, because the recursor value is `O(1)` and the cost is in function application — a measured negative result. — [EXT-013, EXT-014]
- **C11.** Two naive-substitution capture obstacles (instantiating the IH at a term mentioning a bound variable, and at a permutation of just-bound variables) are dodged by naming and α-renaming, composed together in the gcd derivation. — [GOOD-027, HP-017, ES-019]

*(Every claim above is traceable to E0/E2/E3 facts except where a fact is explicitly E4/E5.)*

---

# CLUSTER FACTS

*(The full grounded fact-entries produced by the extraction pass follow, by cluster.
Each entry keeps its ID, Title, Category, Evidence Level, File, Lean declarations,
Summary, Evidence, Dependencies, and Notes.)*

## CORE — Object language + Modified Realizability (`Core/Syntax`, `Core/ModifiedRealizes`, `Core/Transport`)

- **CORE-001** [E2] *Term signature — 20 function symbols plus `var`* (`Core/Syntax.lean`, `Term`). The `Term` inductive has `var : ℕ → Term` plus exactly 20 function symbols `zero, succ, plus, times, pred, exp, bump, good, prec, ord, hcut, hydra, hord, hcons, happ, mvcount, solves, xor, pas, look`. `solves` is 5-ary; `hord/mvcount/pred` unary; the rest binary. Matches CLAUDE.md's "20-symbol signature."
- **CORE-002** [E2] *`look` is the coloring-lookup symbol* (`Term.look`). `look : Term → Term → Term`, evaluated `look s t ↦ lookN (s.eval ρ)(t.eval ρ)`; the `lookNum`/`eqCongLook` rules carry the comment "a lookup is a cons-list decode — course-of-values through the encoding, not a first-order equation schema, the same reason `bump`/`hcut` have one."
- **CORE-003** [E2] *`Term.eval` interprets each symbol by a value-layer function* (`Term.eval`). Arithmetic native (`pred` = truncated −1, `exp` = ^); every Phase-B/H/E/F/S symbol by its value function (`bumpN, goodN, oltN, ordOf, hydraStepN, hydraSeqN, ordOfHydraN, hconsN, happN, hlen, solvesN, xorN, pasN, lookN`).
- **CORE-004** [E2] *Capture-safe term substitution* (`Term.subst`). `subst x u (var i) = if i=x then u else var i`, recursing structurally through all symbols. (Call prefix.)
- **CORE-005** [E0] *`Term.eval_subst` / `Term.eval_congr`*. `(subst x u t).eval ρ = t.eval (update ρ x (u.eval ρ))`; evaluation depends only on values of occurring variables. Both by induction over `Term`.
- **CORE-006** [E0] *Numerals* (`numeral`, `numeral_eval`). `numeral n` = `n`-fold `succ zero`; `(numeral n).eval ρ = n`. Used by every numeral-graph rule.
- **CORE-007** [E2] *Formula language `⊥,=,∧,∨,→,∀,∃`* (`Formula`, `Formula.neg`). 7 constructors; atoms are equations only; `neg φ := φ.imp bot`; `ex` is the Phase-D0 existential.
- **CORE-008** [E2] *`FreeIn`/`binders`/`Formula.subst`*. Capture-safe formula substitution stops at a rebinding of the same variable; capture excluded by `SubstOK`.
- **CORE-009** [E2] *Side conditions `SubstOK`/`FreshIn`, all decidable* (`decidableFreeIn/SubstOK/FreshIn`). `SubstOK u φ := ∀y∈u.vars, y∉φ.binders`; `FreshIn x Γ := ∀φ∈Γ, ¬φ.FreeIn x`; all decidable → discharged by `decide +kernel`.
- **CORE-010** [E4] *Design: quantifier side conditions decidable for `decide +kernel`* (quoted: "All three conditions … are decidable, so concrete derivations discharge them by `decide +kernel` rather than by hand").
- **CORE-011** [E3] *`Deriv` has exactly 72 rules* (`Deriv`, `Type`-valued). Enumerated: 11 structural (ax…botE), ind, tiEps0, exI/exE, eqDec/succNeZero/succInj, eqRefl/eqSymm/eqTrans + one congruence per symbol, the recursion-equation schemas, and 5 numeral-graph schemas. `Type`-valued so `extract` can recurse.
- **CORE-012** [E2] *Structural core is intuitionistic ND, no classical rule* (ax/wk/andI/andE/orI/orE/impI/impE/botE). `botE` is ex-falso; only `eqDec` gives a disjunction (decidable equality), not general excluded middle.
- **CORE-013** [E2] *`ind` — recursion along `succ`*. From `φ(0)` and `∀x(φ(x)→φ(succ x))` with `SubstOK (succ (var x)) φ`, conclude `∀x φ(x)`. Realizer `indRecC`.
- **CORE-014** [E2] *`tiEps0` — the one non-derivable rule* (`Deriv.tiEps0`). Transfinite induction along ε₀ notations; from progressiveness `∀x((∀y. prec y x = succ 0 → φ(y)) → φ(x))` conclude `∀x φ(x)`, side conditions `x≠y`, `SubstOK (var y) φ`, `¬φ.FreeIn y`; `y≺x` is the equation `prec y x = 1` (contentless); realizer `tiRecC`. Quoted: "the one rule of the fragment that is not a consequence of its own resources — this is the content of Gentzen/Kirby–Paris."
- **CORE-015** [E2] *Three arithmetic axiom schemas* (`eqDec`, `succNeZero`, `succInj`).
- **CORE-016** [E2] *Equational-logic kit* (`eqRefl/eqSymm/eqTrans` + one `eqCong*` per symbol; `eqCongSolves` chains 5 antecedents). "All contentless" implication schemas.
- **CORE-017** [E4] *Design: `+`/`×` axioms recurse on the FIRST argument (mirror recursion)* so the second-argument equations become genuine `ind` theorems (quoted).
- **CORE-018** [E2] *Phase-B recursion equations* (`predZero/predSucc/expZero/expSucc`, `bumpZero`+`bumpNum`, `goodZero/goodSucc`).
- **CORE-019** [E4] *Design: `bump/prec/hcut/xor/look` enter by NUMERAL GRAPH, not open-term schema* — course-of-values recursion through a coding/structure, not a first-order equation (quoted per symbol).
- **CORE-020** [E4] *Limitation: `1−x`/`a+b−2ab` not expressible, forcing `xor` as a symbol* (quoted).
- **CORE-021** [E2] *`exI`/`exE`* with `SubstOK` (intro) and `FreshIn x Γ` + `¬ψ.FreeIn x` (elim, "without which the witness could leak out of the scope").
- **CORE-022** [E2] *`allI`/`allE`* with freshness/no-capture conditions.
- **CORE-023** [E4] *Design: Goodstein descent split into three single-symbol schemas* (`ordBump`↔`ordOf_bumpN`, `ordPredLt`↔`olt_ordOf_of_lt`, `bumpNeZero`↔`bumpN_ne_zero`); bases written `succ(succ b)` because base change is false at base 1 (quoted).
- **CORE-024** [E2] *Hydra-layer rules* (`hydraZero`/`hydraSucc` recursion; `hordCutLt` the single imported descent `c≠0 → prec(hord(hcut n c))(hord c)=1`; `hcutNum`).
- **CORE-025** [E2] *Hanoi rules* (`solvesZero/solvesSucc` branching step with middle move `f×3+t`; `mvcountNil/mvcountApp`; count as `succ(mvcount k)=2^n`, subtraction-free).
- **CORE-026** [E2] *Pascal rules* (four `pas` recursion equations + `xorNum`; diagonal/above-diagonal are theorems not axioms).
- **CORE-027** [E4] *Design: `Deriv` `Type`-valued, contexts are lists, `ax`/`wk`* (quoted).
- **CORE-028** [E4] *Flexible-ambient-level MR design* (`MR`). Quoted: "`MR ρ φ n x` says `x : PureType (n+1)` realizes `φ` at ambient `n`. All clauses stay at one ambient level … This eliminates level-coercion bookkeeping entirely."
- **CORE-029** [E2] *Level function `lvl`*. atoms 0; ∧/∨ = max; → = max+1; ∀ = +1; **∃ = lvl φ (no added level)**.
- **CORE-030** [E2] *`MR` and its seven clauses* — ⊥=False; eq = eval equality; ∧ = both `fstPT`/`sndPT`; ∨ = numeric tag; → (n=0: False; else `∀x, MR φ m x → MR ψ m (app₁ F x)`); ∀ (n=0: False; else `∀k, MR (update ρ y k) φ m (app₁ F (natPT (m+1) k))`); ∃ = `MR (update ρ y (fstPT x (defaultPT n))) φ n (sndPT x)`.
- **CORE-031** [E4] *Design: `→` clause is the `Assoc`/`CtPer` clause shape at functional level* (quoted); associate-level counterpart enters in Soundness at `CtQ`.
- **CORE-032** [E0] *`MR_congr`* — MR depends only on free-variable values (`[propext, Quot.sound]`, no choice).
- **CORE-033** [E0] *`MR_subst`* — `MR ρ (φ.subst x u) n a ↔ MR (update ρ x (u.eval ρ)) φ n a`; ∀/∃ rebinding cases use `Function.update_idem`/`update_comm` (the `Classical.choice` carriers, CONST-003).
- **CORE-034** [E2] *Pure-type devices* — `defaultPT`, `natPT`, mutual `up`/`down`, `pairPT`/`fstPT`/`sndPT` (via `Nat.pair`/`.unpair`). **These live in the realizability project, not the dependency.**
- **CORE-035** [E0] *`down_up`* — `down n (up n x) = x` (up is a section).
- **CORE-036** [E0] *`app₁`/`abs₁` and the beta law `app₁_abs₁`* — `app₁ (abs₁ G) x = G x`; what makes MR's →/∀ clauses computable.
- **CORE-037** [E4] *Design: `∃` reuses `∨`'s pairing, costs no ambient level* (`lvl (∃yφ)=lvl φ`; "binders that consume realizers cost a level, binders that package them do not") (quoted).
- **CORE-038** [E2] *Formula-indexed transports `liftR`/`dropR`* — atoms generic `up`/`down`; ∧/∨ componentwise; →/∀ contravariant sandwich `abs₁(lift∘app₁ F∘drop)`; ∃ repackages witness.
- **CORE-039** [E4] *Design: generic `up`/`down` fail at implications → formula-indexed transports* ("the sole blocker for extraction"; drop direction "genuinely false below the formula's level") (quoted).
- **CORE-040** [E0] *`MR_liftR_dropR`* — transports preserve MR above `lvl φ` (one mutual induction; implication contravariance needs both directions simultaneously).
- **CORE-041** [E0] *Iterated transports + `MR_cast`* (`liftIter`/`dropIter`/`MR_liftIter`/`MR_dropIter`/`MR_cast`).
- **CORE-042** [E0] *`famOf`/`FR`/`FR_famOf`* — one realizer above `lvl φ` generates a bounded realizing family; "closes exactly the 'binders provide one ambient, bodies consume several' gap."
- **CORE-043** [E3] *Exactly five numeral-graph symbols* (`bumpNum`/`precNum`/`hcutNum`/`xorNum`/`lookNum`), of form `symbol(numeral a, numeral b) = numeral (f a b)`.
- **CORE-044** [E3] *Negative: no function/second-order variables* — `var : ℕ → Term`, quantifiers bind ℕ-named variables; the fragment cannot quantify over plays/functions (→ H5 names one battle; `hercules_wins` is metatheory).

## EXT — Extraction, Soundness, Continuity, Collapse (`Core/Extraction`, `Core/Soundness`, `Core/GenericContinuity`, `Core/CollapseDemo`)

- **EXT-001** [E2] *`extract` — one named combinator per rule* (`extract`). Recursion on the derivation, each rule → its combinator; all 72 rules have a match arm; last two arms `.lookNum`/`.eqCongLook`.
- **EXT-002** [E2] *`Fam` — ambient-indexed realizer families* (`Fam := (n:ℕ) → PureType (n+1)`; `CtxR` asserts each hypothesis' family realizes above its level; transports turn a binder's single-ambient realizer into a family via `famOf`).
- **EXT-003** [E2] *`indRecC` — type-indexed primitive recursor* (`indRecC a b 0 = a`, `…(k+1) = app₁ (app₁ b (natPT (m+2) k)) (indRecC a b k)`; "the `Nat.rec` motive is the pure type, not `ℕ`; the ambient never changes"). `indC := allIC …`.
- **EXT-004** [E2] *`tiRecC` — transfinite recursor via `WellFounded.fix` on `oLt_wf`* (used here and only here; recursive value transported down two ambient levels by two `dropR φ`).
- **EXT-005** [E4] *Design: `WellFounded.fix` on `oLt_wf` unproblematic — noncomputable, kernel-irreducible, Classical-free* (quoted; "so the continuity theorems' axiom budget is unaffected").
- **EXT-006** [E0] *`tiRecC_eq`* — non-dependent unfolding (`WellFounded.fix_eq` + `dite_eq_ite`); rewritten by both `MR_tiRecC` and `tiC_tracked`.
- **EXT-007** [E2] *`allIC` packages both recursors identically to `∀`-intro* (`indC`/`tiC` reuse it; `tiFamAt` sends sub-`lvl φ+2` ambients to junk, kept unreachable by `derivBound`).
- **EXT-008** [E2] *`axiomC` — contentless realizer* (`= defaultFam`) for every atomic/implication schema (the `succNeZero` pattern); dozens of `extract` arms map here.
- **EXT-009** [E2] *`exIC`/`exEC` reuse `∨`'s pairing for `∃`* (`exIC k f = pairPT (natPT k) f`; `exEC` reads witness + rebuilds hypothesis family with `famOf`, "no second pairing mechanism"). `exIC_witness`: `fstPT (exIC k f n)(defaultPT n) = k`.
- **EXT-010** [E2] *`impEC`/`impIC`* — apply the major premise one ambient up (`app₁ (f (n+1)) (g n)`); `impIC` abstracts over the bound realizer's `famOf` family; "why `derivBound (impI) = max(…, lvl φ)+1`."
- **EXT-011** [E2] *`derivBound`* — ambient above which the extract realizes `φ`; `impI/allI/ind` add 1, `tiEps0` adds `lvl φ+2 …+1`, `∃` costs nothing; "explains why gcd (bound 41) does not `#eval`."
- **EXT-012** [E2] *`eqDecC`* — decidable-equality tag (0 equal / 1 not), contentless payloads; `extract .eqDec = eqDecC (decide (s.eval=t.eval))`.
- **EXT-013** [E4] *D6 memoization kept with `@[csimp]` DETACHED* (`memoRec`/`tiRecCFast`/`tiCFast`, `tiRecC_eq_tiRecCFast`). Quoted measurements: `MEMOHIT=2376, MEMOMISS=0` at m=1; wall clock 4693 ms vs 4614 ms (within noise); m=2 no output at 600 s. "Left detached: measured to change nothing."
- **EXT-014** [E4] *Why memoization can't help* — `app₁ F x` is a closure, so the recursor value is `O(1)`; the cost is in *applying* it; a table would need to be keyed by `(code, argument)` and arguments are `PureType` functions with no decidable equality (quoted). "Corrects D4's headline proxy: the entry count is not a cost proxy."
- **EXT-015** [E0] *`memo_ok`* — memo evaluator returns `tiRecC`'s value and preserves the table invariant (by fuel induction); connected by proof, not `@[implemented_by]`; `memoBound := 32`.
- **EXT-016** [E4] *Repetition is one level up — `tiCFast` builds the table outside the `abs₁`* — instrumentation `TICFAM=1` (the abstraction is applied once), so nothing to share there either (quoted).
- **EXT-017** [E2] *`orEC`* — pointwise tag-split, each branch rebuilds its hypothesis family via `famOf` ("no cross-ambient tag-coherence invariant is ever needed").
- **EXT-018** [E0] *`soundness`* — every derivation's extract realizes `φ` at every ambient ≥ `derivBound`, by one big induction over `Deriv`, one case per rule.
- **EXT-019** [E0] *`MR_indRecC`* — closure of MR under primitive recursion, uniform in the ambient (ordinary numeral induction; iteration never changes ambient); cites Troelstra 1973.
- **EXT-020** [E0] *`MR_tiRecC`* — closure under transfinite recursion along `≺` (well-founded induction on `oLt_wf`; realizing the order premise `y≺x` IS the descent `OLt j k`; two `dropR` transports "forced by levels, not by taste").
- **EXT-021** [E4] *The two small inductions each invoked exactly once by soundness* ("stated once for every ambient `m`, per the level-free-core discipline; no level-by-level instances").
- **EXT-022** [E3] *Axiom/congruence soundness cases are true-equation discharges* (matching contentless `axiomC`); recursion-equation cases are the value functions' definitions (`goodSucc`→`rfl`, `solvesSucc`→`solvesN_succ`, `ordPredLt`→`olt_ordOf_of_lt`, `hordCutLt`→`olt_ordOfHydraN_step`, `bumpNeZero`→`bumpN_ne_zero`).
- **EXT-023** [E0] *`CtxR_congr`* — context realization stable under environment changes off free variables.
- **EXT-024** [E0] *`extract_continuous`* — every closed derivation's `extract D ρ [] 1` is `Continuous2`, uniformly; proof instantiates `Tracked` at the constant env/empty context and applies to the tracked identity family.
- **EXT-025** [E2] *`Tracked` — the oracle-parameterized (Kripke) continuity relation* (base = `Continuous2`; function-type = pointwise application to any tracked argument is continuous in the oracle). "*Not* 'the extract has an associate at every ambient'."
- **EXT-026** [E0] *`abs₁_tracked` — abstraction closure by β-reduction, no associates constructed* ("the case that would require associate-level closure … immediate, because tracking of `abs₁ G` is tested by application, which computes `G`").
- **EXT-027** [E0] *`extract_tracked`* — tracking threaded through every rule, one per-combinator preservation lemma per case (same shape as `soundness`).
- **EXT-028** [E3] *One `*_tracked` lemma per combinator* (incl. a separate `axiomC_<rule>_tracked := defaultFam_tracked` for each contentless schema).
- **EXT-029** [E0] *`indC_tracked` + `tracked_apply_nat`* — continuous-index absorption for `ind` (recursor tracked by induction on the count; oracle-read count locally constant).
- **EXT-030** [E0] *`tiRecC_tracked`/`tiC_tracked`* — transfinite recursor tracked by `≺`-induction; uses `dec_em` (not `by_cases`), consistent with the Classical-free discipline.
- **EXT-031** [E0] *`Continuous2` closure kit* (`const`, `comp₁/₂/₅`, `eval`, `apply_nat`, `ite`) with explicit moduli; `comp₅` is "the arity Phase E2's `solves` needs."
- **EXT-032** [E0] *`termEval_continuous`* — term evaluation in a tracked environment is continuous, one arm per symbol (each `continuous2_comp` on the value function).
- **EXT-033** [E0] *`famOf_tracked` + transport tracking* (`liftR_dropR_tracked`, mutual formula induction, "no level side condition" unlike `MR_liftR_dropR`).
- **EXT-034** [E0] *`id_tracked`* — the oracle `α↦α` is tracked at level 1 (via `continuous2_eval`); the family `extract_continuous` reads the extract off.
- **EXT-035** [E2] *`RealizesCtQ` — the `CtQ 2` meaning of a closed derivation* (`ctQTwoEquiv.symm ⟨extract D ρ [] 1, extract_continuous D ρ⟩`); total on closed derivations because continuity is supplied once and for all.
- **EXT-036** [E0] *`collapse_demo`* — two syntactically different proofs of `A∧B→B∧A` have equal `RealizesCtQ` classes (`demoDeriv₁`/`demoDeriv₂`, extra pair-and-project cancels by the pairing retraction).
- **EXT-037** [E0] *`demo_extract_apply`* — the shared functional's concrete continuity modulus (value at α depends only on α 0 and one further position).
- **EXT-038** [E4] *The brief's `lvl φ ≤ 1` restriction is not needed for continuity* ("continuity of the extract is a property of the extraction combinators alone … the level enters only through `soundness`") (quoted).
- **EXT-039** [E4] *Continuity invariant deliberately avoids the parent project's associate/countability chapter* ("it sidesteps associate construction entirely") (quoted); negative fact: no associates constructed anywhere.
- **EXT-040** [E0] *`up_down_tracked` + pure-type device tracking* (`pairPT/fstPT/sndPT/app₁/natPT/defaultPT/ite/cast` all preserve tracking).
- **EXT-041** [E3] *Extraction combinator inventory* (`axC, andIC, andE₁C, andE₂C, orI₁C, orI₂C, orEC, impIC, impEC, botEC, allIC, allEC, indC, tiC, eqDecC, exIC, exEC, axiomC`).

## ORD — ε₀ substrate + transfinite induction (`Ordinals/Epsilon0`, `Signature/OrdinalAssignment`, `Theorems/Goodstein/{TransfiniteInduction,OrdinalDescent}`)

- **ORD-001** [E2] *Notations below ε₀ as ℕ codes* (`mkO`/`oE`/`oC`/`oR`). `mkO e c r = pr e (pr c r)+1` codes `ω^e·(c+1)+r`; `+1`/`c+1` reserve 0 for the zero ordinal and force positive coefficients.
- **ORD-002** [E0] *The coding is a bijection* (`mkO_oE_oC_oR`, `oE_mkO`, …, `mkO_ne_zero`). `∀x` ranges over precisely the notations, no unused codes.
- **ORD-003** [E4] *Design: hand-rolled triangular pairing, NOT Mathlib `Nat.pair`* (quoted: `Nat.unpair` goes through `Nat.sqrt`, "every Mathlib lemma about that pairing depends on `Classical.choice`" and doesn't reduce in the kernel; the coding enters `tiRecC`'s definition, hence the continuity budget `[propext, Quot.sound]`).
- **ORD-004** [E4] *Both pairing directions reduce in the kernel, `propext`-only* (`pr1_pr`, `pr2_pr`, `pr_pr1_pr2`; "nothing below depends on any axiom beyond `propext`").
- **ORD-005** [E4] *Design: `by_cases` banned; `dec_em` used* (`dec_em (p) [Decidable p] : p ∨ ¬p`; quoted: `by_cases` can fall back on `Classical.byCases` and everything feeds `tiRecC`'s definition).
- **ORD-006** [E3] *Fast pairing/log/triangular via `@[csimp]`* (`triFast`, `unTriFast` binary search; unary `tri`/`unTri` overflow the interpreter on the Hydra layer's large codes; kernel-facing defs + proofs untouched).
- **ORD-007** [E0] *Destructor strictly decreases the code* (`oE_lt`, `oR_lt`) — the fuel measure for `precAux`/`nfAux`/`ordOfAux`.
- **ORD-008** [E2] *CNF comparison `precB`* — compare exponents, then coefficients, then remainders; fueled at `a+b`.
- **ORD-009** [E0] *`precB` order properties* — irreflexive, transitive, asymmetric, total/trichotomous on normal forms (transitivity + totality added for the Hydra layer).
- **ORD-010** [E2] *Normal-form predicate `nfB`* — strictly decreasing exponents hereditarily (`OBelow`); positive coefficients built into the coding.
- **ORD-011** [E0] *Normal forms load-bearing: bare comparison has an infinite descending chain* (`precB_onePlus_omega`, `not_olt_onePlus_omega`; `1+ω ≻ ω ≻ …` all denote ω, machine-checked; the offenders fail `nfB`).
- **ORD-012** [E2] *The order `oltB`/`OLt`/`oltN`* — comparison conjoined with normality (`oltB a b := nfB a && nfB b && precB a b`); `oltN` is the `prec` symbol's semantics; a non-normal code has no `≺`-predecessors.
- **ORD-013** [E0] *`oLt_wf : WellFounded OLt`, Classical-free* — three nested inductions for normal codes + trivial accessibility of non-normal ones; "no ordinals, no choice, … keeps the continuity budget `[propext, Quot.sound]` even though `tiRecC` is well-founded recursion on `OLt`."
- **ORD-014** [E4] *Design: a stray `Classical.choice` here breaks every continuity budget* (quoted; `tiRecC`'s definition mentions `oLt_wf`).
- **ORD-015** [E4] *Design: fuel recursion, not `WellFounded.fix`, at the value level* (`WellFounded.fix` doesn't reduce in the kernel; cross-checks are `rfl`/`decide`).
- **ORD-016** [E2] *`nat_strong_ind` proved locally* (keeps the module's axiom footprint to `propext` alone).
- **ORD-017** [E4] *`tiEps0` — added not derived* (`≺`-descent is not structural descent; from `ω^ω` one descends to a *larger* tree, so structural recursion cannot reach the predecessors) (quoted).
- **ORD-018** [E4] *Negative: PA-independence not formalized/claimed for the fragment* ("neither proves nor claims non-derivability for its own fragment — that would need an interpretation of the fragment in PA") (quoted).
- **ORD-019** [E4] *`oLt_wf` proof elementary/choice-free* — "an 85-line induction the kernel checks, axiom footprint `[propext, Quot.sound]` visibly weaker than the `Classical.choice` the realization theorems use" (quoted).
- **ORD-020** [E0] *Notations are Phase-B `HTerm`s read at base ω* (`ordTerm`, `ordTerm_hterm`) — no second encoding.
- **ORD-021** [E2] *Ordinal assignment `ordOf`* — the code of the ordinal of `n`'s hereditary base-`k` rep read at base ω; `ordOf k n = mkO (ordOf k (hlog k n)) (n/k^e−1) (ordOf k (n%k^e))`.
- **ORD-022** [E0] *Obligation 1 — `nfB_ordOf`* (assignment lands in normal form, for `2≤k`), built on strict monotonicity `precB_ordOf_of_lt`/`olt_ordOf_of_lt`.
- **ORD-023** [E0] *Obligation 2 — `ordOf_bumpN`* — base change preserves the ordinal (`ordOf (k+1)(bumpN k n) = ordOf k n`, `2≤k`), in general.
- **ORD-024** [E0] *Obligation 3 — `ordOf_descent`* — one Goodstein step strictly decreases the ordinal; uses nothing from the derivation system (corrects Phase C's prediction it would use `tiEps0`).
- **ORD-025** [E0] *`bumpN` strictly monotone + digit-bound* (`bumpN_mono_bound`) by one simultaneous strong induction.
- **ORD-026** [E2] *`hlog`/`bumpN`/`goodN` fuel-structural, before `Term`; degenerate bases identity* (`bumpN 0 n = bumpN 1 n = n`, so no `2≤k` side condition for soundness).
- **ORD-027** [E0] *Full `hlog`/digit theory built in D1* (`lt_pow_hlog_succ`, `hlog_of_digits`, `hlog_rem_lt`) — the canonicity content Phase B deferred.
- **ORD-028** [E0] *Kernel-verified Goodstein descent instances* — ordinals along G(3) are codes `(9,2,10,3,1,0)`, all normal, first four descents `by decide`; codes **not** numerically decreasing (`2` then `10`) — descent genuinely along `≺`.
- **ORD-029** [E2] *`tiEps0` exercised end to end* (`tiDemoDeriv : Deriv [] (∀x. 0=0)`, certified realized + continuous; `precOneOmegaDeriv` computes `1 ≺ ω`).
- **ORD-030** [E3] *`#print axioms` checks in TransfiniteInduction* (`oLt_wf`, `MR_tiRecC`, `soundness`, `extract_continuous`, demos).
- **ORD-031** [E0] *D5 — descent DERIVED from three single-symbol schemas* (`Deriv.ordDescent` built via `bumpNeZero`/`ordPredLt`/`ordBump`), keeping the deleted constructor's name so `GoodsteinTheorem.lean` is unchanged.
- **ORD-032** [E4] *Why deriving matters — D2 assumed the theorem's core lemma* ("the fragment proved the theorem *relative to* the very step that makes it true"; D5 narrows the gap to "three general properties of the ordinal assignment are assumed") (quoted).
- **ORD-033** [E4] *Limitation: D5 does not eliminate metatheory dependence* (fully internalizing needs `hlog/div/mod` symbols, an order relation, course-of-values induction, Phase D1 redone syntactically — "a research-scale project, not a phase") (quoted).
- **ORD-034** [E0] *`ord_descent_via_fragment`* — reading the derived descent back through `soundness` recovers D1's obligation 3, making the derivation non-vacuous.
- **ORD-035** [E1] *`Deriv.ordDescent` certified* (soundness + generic continuity apply unchanged).
- **ORD-036** [E0] *`precB_cases`* — the three ways one notation precedes another (smaller exponent / equal exp smaller coeff / equal exp-coeff smaller remainder).
- **ORD-037** [E0] *Sanity chain `1 ≺ ω ≺ ω^ω`* on normal notations.

## GOOD — Goodstein + Arithmetic + Exists (`Common/{Arithmetic,Exists}`, `Theorems/Goodstein/{Goodstein,GoodsteinTheorem,GoodsteinExtraction}`)

- **GOOD-001** [E0] *Four +/× second-argument equations as `ind` theorems* (`plusZeroDeriv`, `plusSuccDeriv`, `timesZeroDeriv`, `timesSuccDeriv`) — "every one by the induction rule `ind`, not cited as axioms."
- **GOOD-002** [E4] *Design: mirror recursion — defining axioms recurse on the FIRST argument* ("had the defining axioms been the briefed equations themselves … `ind` would never fire") (quoted).
- **GOOD-003** [E0] *`plusRightCommDeriv`* — `(z+x)+y=(z+y)+x` by `ind` on `y`; five inductions total in Arithmetic.
- **GOOD-004** [E4] *α-variant `plusSuccDeriv'` by instantiate-and-regeneralize* (SubstOK forbids instantiating `∀x∀y.φ` at a term containing `y`) (quoted).
- **GOOD-005** [E2] *Equational-logic derivation-formers* (`symmE/transE/congSuccE/congPlusE/congPlusL/congPlusR`) so proofs read as calculations.
- **GOOD-006** [E2] *Side-condition helpers* (`freshIn_nil`, `freshIn_singleton_all`, `substOK_of_forall`).
- **GOOD-007** [E1] *Arithmetic realizers certified by soundness* (`plus_zero_realized`, …).
- **GOOD-008** [E1] *Arithmetic continuity via generic theorem* (`plus_zero_extract_continuous`, …).
- **GOOD-009** [E3] *8 `#print axioms` checks on the Arithmetic results.*
- **GOOD-010** [E0] *`∃`'s first theorem `∃s. good(3,s)=0`* (`goodThreeExDeriv`, `exI` at witness 5, over `goodComputeDeriv 3 5`).
- **GOOD-011** [E4] *Design: `∃` reuses `∨`'s pairing, costs no ambient level* (`exIC`=`orI₁C` with numeral tag; `lvl (∃yφ)=lvl φ`; "no `derivBound` in the development grew") (quoted).
- **GOOD-012** [E0] *Witness readable off the `∃` realizer = 5* (`good_three_ex_witness`: `fstPT (extract …)(defaultPT n)=5` for every ρ,n).
- **GOOD-013** [E0] *`exE` round trip* (`goodThreeExRoundTrip`).
- **GOOD-014** [E1] *`∃` realizers certified* (soundness, continuity, 5 `#print axioms`).
- **GOOD-015** [E4] *Design: hereditary base-k rep is a TERM in base variable 0* (`hrep`, `HTerm`) — "bumping the base is evaluating the same term at base k+1" (quoted).
- **GOOD-016** [E4] *Bumping the base = evaluating the same term at base k+1* (`hrep_eval_bump`, `bumpHrepDeriv`) (quoted; counterpart of the reference repo's base-replacement `f`).
- **GOOD-017** [E0] *Existence of representation, meta + in-fragment* (`hrep_eval_self`, `hrepSelfDeriv` — "proved from the recursion axioms of +/×/exp alone, no axiom about `hrep`").
- **GOOD-018** [E4] *Negative: Goodstein's theorem NOT proved in Goodstein.lean (Phase B)* ("makes Goodstein's theorem expressible … does not prove it") (quoted).
- **GOOD-019** [E4] *Limitation: uniqueness/canonicity of the representation deferred* (everything Phase D consumes factors through the deterministic `hrep`) (quoted).
- **GOOD-020** [E0] *Fragment computes numeral arithmetic + its own Goodstein sequence* (`goodComputeDeriv m s ⊢ good m̂ ŝ = (goodN m s)̂`; `goodFourOneDeriv : good 4̂ 1̂ = 26̂`).
- **GOOD-021** [E3] *Kernel-verified cross-checks vs WilliamAngus/Goodstein* (`bumpN 2 4 = 27`, `goodN 4 = 4,26,41,60`, `goodN 3 = 3,3,3,2,1,0,0`).
- **GOOD-022** [E0] *Zero absorbing in the fragment* (`Deriv.goodZeroStep`: `G(s,t)=0 → G(s,t+1)=0`).
- **GOOD-023** [E2] *Extra congruence derivation-formers* (`congTimesE/congPredE/congExpE/congBumpE/congGoodE`).
- **GOOD-024** [E1] *Goodstein.lean realizers certified* (soundness + continuity + 4 `#print axioms`).
- **GOOD-025** [E0] *`goodsteinTheorem : Deriv [] (∀m ∃t. good(m,t)=0)`* — the genuine quantified statement, by `allI` over `goodTerminatesDeriv`.
- **GOOD-026** [E0] *Proof by `tiEps0` on the ordinal-of-state formula* (`goodProgressive` case-splits via `eqDec`: witness `s` if already 0, else `stepBranch`; instantiate at the initial state's ordinal).
- **GOOD-027** [E4] *The naming trick `namedIHDeriv`* — naive substitution forbids instantiating the IH at `ord(s+3,good(m,s+1))` (mentions bound `s`); name the ordinal with a fresh `∀z` (quoted; "a general technique for naive-substitution calculi … costs one extra `∀` and nothing in the extract's structure").
- **GOOD-028** [E0] *Descent glued in the fragment* (`descentDeriv` glues imported `ordDescent`, `goodSucc`, state hypothesis).
- **GOOD-029** [E2] *`goodsteinStopTime` — extracted stopping-time function* at ambient 12 (`derivBound goodsteinTheorem = 12`).
- **GOOD-030** [E0] *`goodsteinStopTime_spec`* — `goodN m (goodsteinStopTime m)=0` for every m, from soundness, "holds far beyond where evaluation could reach."
- **GOOD-031** [E1] *Goodstein extract continuity + `CtQ 2` class* (`goodsteinRealizesCtQ`).
- **GOOD-032** [E3] *`#eval`: m=0→0, m=1→1 (table 0,1,3,5); m=4 not attempted (astronomical)* (quoted).
- **GOOD-033** [E3] *Spelled-out theorem `#check`ed to prevent drift.*
- **GOOD-034** [E4] *Descent imported since D5 from three single-symbol schemas* ("was an imported axiom schema in D2 … derived since D5, none of which mentions the Goodstein sequence") (quoted).
- **GOOD-035** [E3] *3 `#print axioms` on the D3 results.*

## HYD — Hydra (`Signature/Hydra`, `Theorems/Hydra/{HydraFragment,HydraTheorem,HydraExtraction,HydraGeneral,HydraDisplay,HydraStrategies}`)

- **HYD-001** [E2] *Hydras/forests as a mutual inductive pair* (`Hydra := node Forest`, `Forest := nil | cons Hydra Forest`; not `Hydra := List Hydra`, so mutual structural recursion drives the proofs).
- **HYD-002** [E2] *Coding into ℕ reuses Epsilon0 pairing* (`encodeH/encodeF/decodeH/decodeF`, fueled; adds only the list-of-children layer; not Mathlib `Nat.pair`).
- **HYD-003** [E0] *Both round trips proved (ℕ ↔ trees bijection)* (`encodeF_forestOf`, `hydraOf_encodeH`) — makes "∀h ranges over exactly the hydras" true, not approximate.
- **HYD-004** [E0] *Dead hydra is exactly code 0* (`encodeH_leaf = 0`, `hydraOf_eq_leaf_iff`) — the fragment's termination test.
- **HYD-005** [E0] *Small hydra codes by rfl* (`hydraOf_small : (hydraOf 0..3) = (leaf,…)`).
- **HYD-006** [E2] *Kirby–Paris move `cutH`/`hydraStep`* — chop leftmost head, flag "child of me"; grandparent grows `n` copies via `append`/`replicate`; root discards flag.
- **HYD-007** [E2] *Move `hydraStepN` + battle `hydraSeqN`* (replication at step s is s+1; `hydraStepN n 0 = 0`).
- **HYD-008** [E0] *Battle grows before it dies — 2→3→1→0* (`hydraSeq_chain := (2,3,1,0)` by rfl; the tree got *wider* before dying).
- **HYD-009** [E4] *Published lengths 1,3,37 as the discriminating check* (`battleLen_small := (1,3)` by rfl; path 3 = 37 verified ~90 s out of band; the other game gives 1,3,11) (quoted).
- **HYD-010** [E2] *Ordinal via Hessenberg sum, no second encoding* (`ordOfHydra`/`ordOfForest`/`insertExp`; `ordOfForest` needs no fuel).
- **HYD-011** [E0] *`insertExp` preserves normal form, nonzero* (`nfB_insertExp`, `insertExp_ne_zero`).
- **HYD-012** [E0] *Insertion strictly increases the ordinal* (`precB_insertExp_self`; `ordOfForest_cons_leaf_descends` = base case backwards).
- **HYD-013** [E0] *Insertion monotonicity lemmas* (`precB_insertExp_mono` the hard H3 lemma; `precB_insertIter_lt` — n copies of ω^a below one ω^b for *every* n, n untouched in the induction).
- **HYD-014** [E0] *Ordinal assignment lands in normal form* (`nfB_ordOfHydra`) — precondition for any descent statement.
- **HYD-015** [E0] *`cutH_descends` — every legal move strictly decreases the ordinal* (three cases = cutH's own; insensitive to the copy count n).
- **HYD-016** [E0] *`olt_ordOfHydraN_step` — the single fact H4 imports* (descent on codes with side condition `code ≠ 0`; imported as `Deriv.hordCutLt`; analogue of `ordPredLt`).
- **HYD-017** [E4] *Design: Hydra definitions choice-free/kernel-computable* ("`#print axioms` … does not depend on any axioms"; a `Classical.choice` here would break every continuity budget) (quoted).
- **HYD-018** [E0] *First descent instances kernel-checked* (`ordOfHydraN 0..3 = (0,1,ω,3)`; ordinal descends at the widening step 2→3 where node count *increased*, `ω ≻ 2` by decide).
- **HYD-019** [E0] *Battle recursion equations named* (`hydraSeqN_zero/succ` for schemas `hydraZero/hydraSucc`).
- **HYD-020** [E4] *Three new symbols hcut/hydra/hord + four schemas* (`hydraZero/hydraSucc` honest recursion; `hcutNum` numeral graph; `hordCutLt` the one imported fact) (quoted).
- **HYD-021** [E4] *"The one imported mathematical fact" — `hordCutLt` design* (a property of one move symbol relative to one ordinal symbol, saying nothing about the battle; quantifies over regrown copies) (quoted).
- **HYD-022** [E2] *Fragment computes concrete battles* (`hydraComputeDeriv start t ⊢ hydra(start,t) = (hydraSeqN start t)̂`; chain dead after 3 moves through the widening step).
- **HYD-023** [E0] *Round trip proving the import faithful* (`hydra_descent_via_fragment` recovers H3's descent through soundness — "not a weaker or differently-quantified statement").
- **HYD-024** [E2] *`hydraGoal := ∀h. ∃t. hydra(h,t)=0`* — "Hercules wins" as a fragment formula; variable convention identical to GoodsteinTheorem.
- **HYD-025** [E0] *`hydraTheorem : Deriv [] (∀h ∃t. hydra(h,t)=0)`* — Kirby–Paris termination inside the fragment, by `tiEps0`, GoodsteinTheorem's shape line for line incl. the naming step.
- **HYD-026** [E4] *The naming step for naive substitution* (`hydraNamedIHDeriv`; descent = `hordCutLt` glued to `hydraSucc` by congruence of `hord`) (quoted).
- **HYD-027** [E4] *Negative: PA-independence NOT proved/claimed* ("does not prove that Peano arithmetic cannot derive it … no claim about it is made") (quoted).
- **HYD-028** [E0] *hydraTheorem certified* (soundness + generic continuity).
- **HYD-029** [E0] *`hydraBattleLength` + `_spec`* — reads the witness at ambient 12 (`derivBound = 12`, "the same 12 as Goodstein's"); `hydraSeqN h (hydraBattleLength h)=0` for every h from soundness; `hydraRealizesCtQ`.
- **HYD-030** [E4] *Limitation: `hydraBattleLength 2` doesn't finish (600 s), answer is only 3* — a limitation of *evaluating the extract* not the math; the D4 bottleneck (two `dropR`, `app₁`/`abs₁` duplication, no memo → exponential re-evaluation) (quoted). `#eval` reaches h=0,1.
- **HYD-031** [E2] *The general legal-move relation `Play`/`CutF`/`MoveF`* — any head at any position, n arbitrary; `PlayRel h' h := ∃n, Play n h h'`.
- **HYD-032** [E0] *`play_descends` — every legal play strictly descends* (each constructor → one H3 ordinal lemma; H3's `cutH_descends` is the leftmost special case).
- **HYD-033** [E0] *`hercules_wins : WellFounded PlayRel`* — every play finite for any choice/replication; `oLt_wf` pulled back along the ordinal assignment; entire content is `play_descends`.
- **HYD-034** [E4] *Negative: the fragment cannot state `hercules_wins` (no function variables)* ("a strategy is a function, and the fragment has no function variables — so it is proved here, in the metatheory") (quoted).
- **HYD-035** [E0] *`play_stuck_iff_leaf`* — the only terminal position is the bare head.
- **HYD-036** [E0] *`hydraStep_play`* — the fragment's battle is one of the general plays (H5 is an instance of `hercules_wins`, not a separate game).
- **HYD-037** [E0] *`play_two_choices`* — genuine nondeterminism (both choices legal, lead to different hydras, both descend; not accidentally the leftmost strategy).
- **HYD-038** [E0] *Battle on trees `battleLenH` — ~98 s→<1 s, certified equal to codes* (`battleLen_eq_battleLenH`; codes grow doubly exponentially).
- **HYD-039** [E3] *Published lengths 1,3,37 `#guard`ed at every build* (`battleLenH 200 1 (path 3) == 37`; 37 discriminates vs the other game's 11; formerly a hand-checked docs/first-order/STATUS.md claim).
- **HYD-040** [E3] *Bracket-notation battle trace with ordinals* (`battleTrace`; on the 4-node path the battle grows to 20 nodes, 5× starting size, while the ordinal falls at all 37 steps).
- **HYD-041** [E4] *`descendsAlong` — the descent watched (demonstration, not proof)* (`#guard`ed for the whole 37-move battle; the proof is `cutH_descends`+`hercules_wins`).
- **HYD-042** [E0] *Rightmost-head strategy as an instance of the general play* (`rightStep_descends := play_descends (rightStep_play …)` in one line; H3's three-case induction "absorbed into H7").
- **HYD-043** [E4] *Two strategies agree on lengths (checked at instances) but differ in states* (`battleLenR … path 3 == 37`; a `#guard` shows different trees after 3 moves; strategy-independence of length "is a known result which is not proved here") (quoted).

## HP — Hanoi + Pascal/Lucas (`Signature/{Hanoi,Pascal}`, `Theorems/Hanoi/*`, `Theorems/Pascal/{PascalTheorem,PascalExtraction,Lucas,PascalBinary}`)

- **HP-001** [E2] *Hanoi move `mvN src dst = src*3+dst`* — no new symbol; a move is the term `f×3+t`.
- **HP-002** [E2] *Move sequences use Hydra's cons coding over Epsilon0 pairing* ("no second scheme is introduced").
- **HP-003** [E2] *`hanoiAux` — difference-list solver with BRANCHING recursion* (two sub-calls per level, unlike Goodstein's/Hydra's linear chains).
- **HP-004** [E4] *Design: difference-list form keeps the module free of list theory* ("the correctness proof never needs associativity, only the two `hanoiAux` equations") (quoted).
- **HP-005** [E2] *`Solves` as a parser/validator `hcheck`* — validates arbitrary `k`, not "k equals the canonical answer" ("what makes the existence theorem say something").
- **HP-006** [E0] *The solver solves* (`solvesN_hanoiN`).
- **HP-007** [E0] *Concatenation + the recursion the fragment's step mirrors* (`hanoiN_succ`; `happN` needed to join two opaque sub-witnesses).
- **HP-008** [E0] *`solvesN_succ` — value-level step imported as schema `solvesSucc`.*
- **HP-009** [E4] *Limitation: "optimal" = unique-for-this-relation, NOT classical minimality* ("the classical `2^n−1` lower bound over that relation is not formalized and is not claimed") (quoted).
- **HP-010** [E0] *Move count subtraction-free — `succ(MoveCount k)=2^n`* (`hlen_hanoiN`; fragment has `pred` but no order).
- **HP-011** [E4] *Design: cons coding squares magnitudes → `#guard` not `rfl`* ("the code of a 7-move sequence is astronomically large and kernel reduction … is hopeless, while compiled evaluation takes microseconds") — grounds the "n=5 wall is the encoding, not the extraction" claim (quoted).
- **HP-012** [E3] *Hanoi value-level `#guard` values* (counts 0,1,3,7,15; validator genuinely rejects non-solutions, scoring 0).
- **HP-013** [E0] *`hanoiTheorem : ∀n∀f∀t∀v ∃k. Solves(...) ∧ MoveCount k = 2^n−1`* by ordinary `ind`.
- **HP-014** [E4] *Proved by ordinary `ind` — a PA theorem with a BRANCHING recursion* (no `tiEps0`/ordinals) (quoted).
- **HP-015** [E4] *Design: induction carries both conjuncts at once* (correctness + optimality; separately would need a second ∃-elim in a second induction; costs one `andI`) (quoted).
- **HP-016** [E4] *Design: subtraction-free count carried inside the fragment* (quoted).
- **HP-017** [E4] *`ihRenamed` — α-renaming the IH for a permuting recursion* ("with naive substitution *every* such instantiation captures … α-rename the induction hypothesis first"; reusable device; second instance renames witness 5→9) (quoted).
- **HP-018** [E2] *`expDoubleDeriv` — 2^x+2^x=2^(succ x)* via `y×2=y+y`, no induction of its own.
- **HP-019** [E0] *`hanoi_derivBound = 26`.*
- **HP-020** [E3] *`hanoiSolution`/`hanoiMoves` — extracted, decoded solver* (witness at ambient 26, decoded to `(src,dst)` pairs; `#eval hanoiMoves 1..4` = classical optimal solutions).
- **HP-021** [E0] *`hanoiSolution_spec` — correct and optimal from soundness* (valid solution ∧ length `2^n−1`, at every n and peg arrangement).
- **HP-022** [E3] *Extracted witness equals value-level solver* (`#guard hanoiSolution == hanoiN`, n=0..4; lengths 0,1,3,7,15) — "not something soundness by itself says."
- **HP-023** [E0] *Hanoi generic continuity + `CtQ 2` class.*
- **HP-024** [E2] *`xorN = (a+b)%2` as a fragment symbol* (total; standard XOR on {0,1}).
- **HP-025** [E4] *Design: why XOR is a symbol — `a+b−2ab` not expressible; `1−x` has no term* ("a composition of monotone operations under finitely many outer preds is monotone in x and 1−x is not") (quoted).
- **HP-026** [E2] *`pasN` — Pascal mod 2, branching recursion* (`pas(n+1,k+1)=xor(pas(n,k),pas(n,k+1))`; every entry 0 or 1).
- **HP-027** [E0] *`pasN_above`/`pasN_diag` at the value level* (derived, not axioms).
- **HP-028** [E0] *`pas_rows_small` — rows 0–4 kernel-checked* (`(1),(1,1),(1,0,1),(1,1,1,1),(1,0,0,0,1)`).
- **HP-029** [E0] *`pasZeroCol`/`pasAbove`/`pasDiag`/`pasTotal` by ordinary `ind`* — no TI(ε₀), no ordinals, no `∃` ("the lightest infrastructure in the development").
- **HP-030** [E4] *Design: no 0/succ case-split — `ind` with hypothesis discarded* ("the base and step cases of an induction are exactly the two cases of a 0/succ split … recurs three times") (quoted).
- **HP-031** [E4] *`Nat.choose` used nowhere in the fragment or proofs* (only in PascalExtraction #guards, "exactly the role `WilliamAngus/Goodstein` played in Phase B") (quoted).
- **HP-032** [E0] *`pas_derivBound = 8`* (lightest headline extraction).
- **HP-033** [E0] *The disjunction TAG is the decision — `pasTag`/`pasDecide`/`pasDecide_eq`* ("the extract of this theorem is a genuine decision function"; `pasDecide n k = pasN n k` at every (n,k)).
- **HP-034** [E3] *Sierpiński gasket — the drawn triangle* (`pasTriangle`; "every cell is one instance of the proved disjunction, resolved by the extracted realizer itself"; `#eval IO.println (pasTriangle 16)`).
- **HP-035** [E3] *Cross-check vs `Nat.choose` only in #guards* (`pasDecide n k == Nat.choose n k % 2`, rows 0–8; fragment symbol over 17 rows).
- **HP-036** [E0] *`pasFragment_eq`* — fragment symbol equals `pasN`; continuity + `CtQ 2`.
- **HP-037** [E0] *Kummer/Lucas at p=2 (metatheory)* (`pasN_eq_one_iff : pasN n k=1 ↔ ∀i, digit k i ≤ digit n i`; `pasN_eq_one_iff_land : … ↔ k &&& n = k`) — "makes the Sierpiński picture inevitable rather than merely observed."
- **HP-038** [E0] *Binary step identities (value level)* (`pasN_even/odd/lucas_step`; one simultaneous induction alternating even/odd rows — "exactly the alternation the gasket's self-similarity expresses").
- **HP-039** [E4] *Lucas is metatheory — no division/order in the fragment* (`digit m i = (m/2^i)%2`; "no hereditary representation is required, because … this recursion never has to look at a digit's own structure — only at its value") (quoted).
- **HP-040** [E3] *Lucas cross-checks* (`(pasN n k==1)==(k &&& n==k)` over 17 rows; row 8 = `[1,0,…,0,1]`, row 7 all ones).
- **HP-041** [E0] *`binEvenDeriv`/`binOddDeriv` — the four binary identities INSIDE the fragment* by ordinary `ind` ("only the final assembly — the induction down the bit positions — has to stay outside").
- **HP-042** [E4] *Design: doubling is `n+n`, not `2×n`* (fewer rewrites for `pasSuccSucc`) (quoted).
- **HP-043** [E0] *Round trips — fragment derivations equal Phase G's `pasN_even`/`pasN_odd`* ("the same mathematics, not a weaker syntactic shadow").
- **HP-044** [E0] *PascalBinary derivBounds* (`binEven = 18`, `binOdd = 22` w/ `maxRecDepth 8000`) + continuity.
- **HP-045** [E5] *Axiom-budget `#print axioms` present but budget lines not in-file* (inference; per CLAUDE.md realization = `[propext, Classical.choice, Quot.sound]`, continuity = `[propext, Quot.sound]`).

## ES — Euclid/gcd + Sperner (`Common/StrongInduction`, `Theorems/Euclid/*`, `Signature/Coloring`, `Theorems/Sperner/*`)

- **ES-001** [E4/E2] *Order is a defined `∃`+`+` notion, no order symbol* (`ltT d s t := ∃d. succ s + d = t`, `leT` similarly; "every order lemma is a derivation, not an imported schema — the honest opposite of adding a `leq` symbol") (quoted).
- **ES-002** [E0] *Associativity of `+` derived* (`plusAssocDeriv` by `ind`; α-variant `plusAssocDeriv'` binds 6,7,8; the strong-induction descent needs it).
- **ES-003** [E0] *Substitution-lemma library* (`Term.subst_self/notMem/notMem_self_subst`, `Formula.subst_self/notFree/notFree_self_subst`, `Deriv.wkNil`) — the syntactic facts a generic-in-φ former needs (unnecessary for concrete φ).
- **ES-004** [E0] *`ltStepDown` — descent through succ* (`z<y`, `y<succ v ⊢ z<v`, witness = sum of the two differences, landed by `plusAssoc`; + `ltZeroElim`, `ltSuccSelfV`).
- **ES-005** [E0] *`caseNatDeriv` — 0/succ split surrogate by `ind`* (`∀n. n=0 ∨ ∃m. n=succ m`, step ignores its hypothesis; negative fact: no primitive case-split rule).
- **ES-006** [E0] *`trichotomyDeriv : ∀a∀b. a≤b ∨ b<a`* by `ind` on `a`, case-splitting the ≤-difference via `caseNat`.
- **ES-007** [E0] *Strong induction DERIVED from `ind`* (`demoAuxDeriv`/`strongIndDemo`: run `ind` on `Aux(v):=∀y.y<v→φ(y)`, read φ(x) off `Aux(succ x)`; "the numeric-< analogue of `tiEps0`, but derived") — exercised at φ:=(x=x) → `∀v. v=v`.
- **ES-008** [E4] *Limitation: generic-in-φ strong-induction former not shipped* (concrete only; a generic former "would need a substitution-composition library"; flagged remaining E1 piece) (quoted).
- **ES-009** [E4] *StrongInduction certification + budgets* (`strongIndDemo_realized`, `trichotomy_realized` + continuity; budgets per header/CLAUDE.md).
- **ES-010** [E0] *`distribDeriv : d·(x+y)=d·x+d·y`* by `ind` on `y` (+ `congTimesR`).
- **ES-011** [E2] *`dvdT d a := ∃q. a = d·q` — divisibility as `∃` over `×`, no `dvd` symbol* (gcd deferred, stated existentially, so no `gcd` symbol either).
- **ES-012** [E0] *Divisibility laws* (`dvdReflDeriv`, `dvdZeroDeriv`, `dvdAddDeriv` = distributivity's payoff).
- **ES-013** [E0] *`cancelAddDeriv` / `addEqZeroDeriv`* (left cancellation by `ind`; zero-summand by `caseNat`).
- **ES-014** [E0] *`dvdSubDeriv : d∣a → d∣(a+c) → d∣c` — the "greatest" direction* (trichotomy on the two quotients; cancel in the ≤ branch, force c=0 in the < branch).
- **ES-015** [E4] *Euclid.lean certification + budgets* (`distrib_realized`, `dvdAdd_realized`, `dvdSub_realized` + continuity; 6 `#print axioms`).
- **ES-016** [E0] *`gcdTheorem : Deriv [] (∀a∀b. ∃g. g∣a ∧ g∣b ∧ ∀d.(d∣a→d∣b→d∣g))`* — the extracted `g` IS the gcd (no `gcd` symbol), subtractive Euclid via strong induction on the sum a+b, scaffold inlined at the concrete φ.
- **ES-017** [E4] *Measure is the SUM a+b* ("neither argument decreases every step, but the sum does: `a+(b−a)=b<a+b`"; the `b<a` branch recurses on `(b, succ s)` so recombination needs no commutativity) (quoted).
- **ES-018** [E4] *Design: NO positivity precondition (`gcd(0,0)=0`)* ("`spec(0,0,0)` holds — everything divides 0 … the delivered theorem is the stronger `∀a∀b. ∃g. spec`") (quoted; docs/internal/QUESTIONS.md item 17).
- **ES-019** [E4] *Design: recursion composes BOTH capture dodges* (name the sub-sum with a fresh `∀17` = Goodstein's device; α-rename φ's inner `∀a∀b` to 15/16 = Hanoi's device) (quoted).
- **ES-020** [E0] *`plusCommDeriv` — commutativity of `+`* (from `plusRightCommDeriv` at z=0; Arithmetic had only right-commutativity; used only for the two descents).
- **ES-021** [E1] *`gcd_realized` / `gcd_extract_continuous`* (full spec realized; the "greatest" clause is the third conjunct, formally proved).
- **ES-022** [E2] *`gcdWitness` — extracted gcd function* at ambient 41 (`derivBound gcdTheorem = 41` w/ `maxRecDepth 4000`, "the repository's deepest").
- **ES-023** [E0] *`gcdWitness_dvd` — extracted number is a common divisor* (first two conjuncts, from soundness "where evaluation cannot reach").
- **ES-024** [E4] *Limitation: NO `#eval` for gcd; ambient 41 too expensive* ("every `pairPT`/`up`/`down` at that level is a functional nested 40 deep, so even `gcdWitness 0 0` does not return") (quoted).
- **ES-025** [E4] *`gcdRealizesCtQ` + budgets* (spelled-out `#check` prevents drift).
- **ES-026** [E2] *`lookN` + `look` — the one genuinely-new symbol (data access)* ("`c k` for a bound `k` cannot be written as a term over the existing signature … structural in the index, hence kernel-computable and choice-free") (quoted); contrast order/divisibility which are ∃-encoded.
- **ES-027** [E0] *`colorCode` + `lookN_colorCode` — encode/decode round trip.*
- **ES-028** [E0] *`spernerTheorem : Deriv [] (∀n∀c. (c 0=0)→(c n=1)→ ∃k. k<n ∧ c k≠c(k+1))`* — 1D Sperner / discrete IVT by ordinary `ind` on the invariant `P(m):=(c m=0)∨∃k<m. crossing`; `k<n` is `ltT`, `≠` the negated equation, no TI(ε₀).
- **ES-029** [E4] *Proved for ARBITRARY ℕ colorings (binary is special case)* ("the `{0,1}` restriction is never used") (quoted).
- **ES-030** [E4] *Design: `spernerBody` leaves n,c FREE (keeps realizer shallow)* ("the two `∀`s would otherwise add two `app₁` layers of pure-type plumbing") (quoted).
- **ES-031** [E4] *Limitation: 2D Sperner / Brouwer OUT OF SCOPE* ("needs a genuine triangulation object") (quoted).
- **ES-032** [E0] *`ltWeakSucc` — order weakening `k<m → k<succ m`* (carries an already-found crossing past the new point).
- **ES-033** [E1] *`sperner_realized` / continuity* (full ∀n∀c theorem realized; budgets).
- **ES-034** [E0] *`spernerWitness` + `spernerWitness_spec` at ambient derivBound=11* (`< n` ∧ genuine crossing, from soundness, at every valid coloring).
- **ES-035** [E4] *Two-ambient trick — witness ambient-independent, `spernerScan` at ambient 5* ("the ambient-11 realizer … overflows the (macOS-capped, 8 MB) stack even at n=1 … the extracted witness numeral is ambient-independent … reading the same derivation at a lower ambient gives the same k (checked under `lean --run`)") (quoted); same pure-type wall as gcd.
- **ES-036** [E3] *`spernerScan` #guards — returns the FIRST crossing* (`[0,1]→0, [0,0,1]→1, [0,0,0,1]→2`; multiple crossings `[0,1,0,1]→0`, `[0,1,1,0,1]→0`).
- **ES-037** [E4] *`spernerRealizesCtQ` + budgets* (`spernerWitness_spec` axioms printed to confirm the realization budget).
- **ES-038** [E4] *Design: colorings reuse Hanoi's cons-list; no new object* ("No new *object* is constructed; the only genuinely new thing is the `look` accessor symbol") (quoted).

---

*End of dossier. Cross-cutting facts, synthesis (§FINAL SUMMARY), and ≈300 cluster
fact-entries above. Every entry traces to a Lean declaration or a quoted comment;
E4/E5 are marked; the axiom facts (CONST-*, KK-001/002) are the kernel's own
`#print axioms` verdicts from this session.*

