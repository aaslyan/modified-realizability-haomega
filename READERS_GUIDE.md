# Reader's guide

For a full manual read-through, start to finish.  This is a map, not a
substitute: every claim below is checkable against the Lean source.

**This repository contains two developments.**  Part I (§1–§4, inherited
from `modified-realizability-lean`) maps the first-order fragment kept
in-tree under `Realizability/` as the reference implementation.  **Part II
(§5–§7) maps the HA^ω library under `HAomega/`** — the current development,
whose README, `HAOMEGA.md`, and `HAOMEGA_DOSSIER.md` are its companion
documents.  If you are here for HA^ω, start at §5 and treat Part I as the
baseline the types are measured against.

The one-sentence version of what is proved: **the fragment derives
`∀m ∃t. good(m,t) = 0`, and modified realizability turns that derivation
into a program that computes the Goodstein stopping time, certified
correct at every input and continuous as a type-2 functional.**

Since the Hydra phases the same sentence holds a second time, for a
second theorem: **the fragment derives `∀h ∃t. hydra(h,t) = 0`** — every
Kirby–Paris hydra dies — **and the same pipeline extracts a
battle-length function from it, certified the same three ways.**  The
second run reused the first's machinery unchanged, which is the strongest
evidence available here that the pipeline is general rather than tuned to
Goodstein.  Neither *independence* result (unprovability in PA) is
formalized, and neither is claimed.

One scope point, stated up front because it is easy to read past.  The
fragment names *one* battle — leftmost head, `s + 1` copies at step `s`
— because a strategy is a function and the fragment has no function
variables.  The strategy-free statement ("every play terminates, whatever
Hercules chops and however many heads grow") is therefore proved in the
metatheory, in `HydraGeneral.lean`, and `hydraStep_play` shows the
fragment's battle is one of those plays.

Goodstein and Hydra are the two that need `TI(ε₀)`, which is why they
carry the narrative — but the map below covers **seven** theorems proved
inside the fragment, and the other five need no ordinals at all: Tower of
Hanoi (§1.8), Pascal mod 2 (§1.9), greatest common divisor (§1.10),
Sperner's lemma in 1D (§1.11), and the Fibonacci **on-ramp** (§1.12) —
the easy case, written last but meant to be read first.  §1.13 is how to
*look at* the programs all of them extract to.  Reading §1.12 → §1.8 →
§1.6 is a gentler route through the same machinery than reading
straight down.

§1.14 is the odd one out and the place to go if you want to see a
program *run* rather than be certified: a second, uncertified extraction
that deletes the ambient-level machinery, under which the gcd
program — certified since Phase E2 and executable at no input until
now — returns `gcd 12 18 = 6`.

---

## 1. Dependency-ordered theorem map

Read in this order.  Each entry is `declaration` — file — what it
establishes.  The order is logical, not chronological: phase labels are
noted only where they help.

### 1.1 The notation system and its order (read first — everything else consumes it)

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 1 | `tri`, `pr`, `pr1`, `pr2`, `pr_pr1_pr2` | `Epsilon0.lean` | A hand-rolled triangular pairing `ℕ ≅ ℕ²`, choice-free and kernel-computable.  Read `pr_pr1_pr2` (surjectivity) and move on. |
| 2 | `mkO`, `oE`, `oC`, `oR`, `mkO_oE_oC_oR` | `Epsilon0.lean` | Ordinal notations below `ε₀` **as natural numbers**: `mkO e c r` codes `ω^e·(c+1) + r`, and the destructors invert it exactly.  The coding is a bijection, so the fragment's `∀x` ranges over exactly the notations. |
| 3 | `precAux`, `precB`, `precB_pos` | `Epsilon0.lean` | Cantor-normal-form comparison, fueled.  `precB_pos` is the characterization you will use everywhere. |
| 4 | `nfB`, `nfB_pos`, `nfB_mkO` | `Epsilon0.lean` | The normal-form predicate (strictly decreasing exponents, hereditarily). |
| 5 | `precB_onePlus_omega`, `nfB_onePlus_omega`, `not_olt_onePlus_omega` | `Epsilon0.lean` | **Why normal forms are not optional**: `ω ≻ 1+ω ≻ 1+(1+ω) ≻ …` is an infinite descent in the bare comparison, through terms all denoting `ω`.  Machine-checked. |
| 6 | `oltB`, `OLt`, `oltN` | `Epsilon0.lean` | The order the rule actually uses: comparison **conjoined with** normality.  `oltN` is its characteristic function, the semantics of the `prec` symbol. |
| 7 | `acc_zero`, `acc_mkO`, `acc_of_nf`, **`oLt_wf`** | `Epsilon0.lean` | **Well-foundedness.**  `acc_mkO` is the heart: three nested inductions (head exponent's accessibility, coefficient, remainder's accessibility) matching the three ways one notation can precede another.  No ordinals, no `Classical`. |

### 1.2 The value-level Goodstein functions and the ordinal assignment

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 8 | `hlog`, `bumpN`, `goodN` | `OrdinalAssignment.lean` | The functions the fragment's symbols evaluate by (Phase B; moved here in Phase D).  All fueled, all kernel-computable. |
| 9 | `lt_pow_hlog_succ`, `one_le_digit`, `digit_lt`, `hlog_rem_lt`, `hlog_of_digits` | `OrdinalAssignment.lean` | Logarithm theory: maximality, the digit bounds, the exponent ordering, and uniqueness of a digit decomposition.  Phase B needed none of this; canonicity needs all of it. |
| 10 | `bumpN_pos_eq`, **`bumpN_mono_bound`** | `OrdinalAssignment.lean` | `bumpN` as a *function*: strictly monotone, and respecting the digit bound.  Proved together by one strong induction — the largest single proof in Phase D.  Read the docstring first. |
| 11 | `ordOf`, `ordOf_pos` | `OrdinalAssignment.lean` | **The ordinal assignment**: `ordOf k n` is the code of the ordinal of `n`'s hereditary base-`k` representation read at base `ω`. |
| 12 | `precB_ordOf_of_lt`, **`nfB_ordOf`**, `olt_ordOf_of_lt` | `OrdinalAssignment.lean` | D1 obligation 1: the assignment is monotone and lands in normal form. |
| 13 | **`ordOf_bumpN`** | `OrdinalAssignment.lean` | D1 obligation 2: bumping the base does not change the ordinal. |
| 14 | **`ordOf_descent`** | `OrdinalAssignment.lean` | D1 obligation 3: one Goodstein step strictly decreases the ordinal.  This is the mathematical content of the whole development. |

### 1.3 The fragment

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 15 | `Term`, `Term.eval`, `numeral` | `Syntax.lean` | Terms over the **21-symbol** signature: `{0, succ, +, ×, pred, exp, bump, good, prec, ord}` (through Phase C), `{hcut, hydra, hord}` (H4), `{hcons, happ, mvcount, solves}` (Hanoi E1–E2), `{xor, pas}` (F1–F2), `look` (S1, see §1.11), `fib` (Phase Fib) — plus `var`, giving `Term` 22 constructors. |
| 16 | `Formula`, `FreeIn`, `subst`, `SubstOK`, `FreshIn` | `Syntax.lean` | Formulas (`∧∨→⊥`, `∀`, and since D0 `∃`) and the substitution bookkeeping. |
| 17 | **`Deriv`** | `Syntax.lean` | The **76-rule** natural-deduction family (39 before Phase C; then `tiEps0`, `precNum`, `eqCongPrec`, `eqCongOrd`, `exI`, `exE`, D5's three, H4's seven, Hanoi's eight, F2's seven, S1's two, and Fibonacci's four `fibZero`/`fibOne`/`fibSucc`/`eqCongFib`).  Read the constructor list in order; the comments mark which phase added what.  Note it is an inductive in `Type`, not `Prop`, so `extract` can recurse on it. |

### 1.4 Realizability, extraction, soundness

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 18 | `PureType` (parent project), `up`/`down`, `pairPT`/`fstPT`/`sndPT`, `app₁`/`abs₁`, `app₁_abs₁` | `ModifiedRealizes.lean` | The pure-type devices.  Everything else is built from these five. |
| 19 | `lvl`, **`MR`** | `ModifiedRealizes.lean` | The flexible-ambient realizability relation.  Read the `∃` clause against the `∨` clause — they are the same shape. |
| 20 | `MR_congr`, `MR_subst` | `ModifiedRealizes.lean` | Environment congruence and the substitution lemma. |
| 21 | `liftR`, `dropR`, **`MR_liftR_dropR`**, `famOf`, `FR_famOf` | `Transport.lean` | The level transports and the family generator: how a binder's one-ambient realizer serves a body that uses it at many ambients. |
| 22 | `extract` (and its combinators), `derivBound` | `Extraction.lean` | One named combinator per rule.  The two that *recurse* are `indRecC` (along `succ`) and **`tiRecC`** (along `≺`) — read `tiRecC` and `tiRecC_eq` carefully; they are where the transfinite content lives. |
| 23 | `MR_indRecC`, **`MR_tiRecC`** | `Soundness.lean` | The two "small" inductions: closure of `MR` under primitive recursion, and under transfinite recursion along `≺`. |
| 24 | **`soundness`** | `Soundness.lean` | The big induction: every derivation's extract realizes its conclusion. |

### 1.5 Continuity

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 25 | `Tracked`, `abs₁_tracked`, `tracked_apply_nat` | `GenericContinuity.lean` | The oracle-parameterized logical relation, abstraction closure by β-reduction, and the closure fact both recursors need. |
| 26 | `tiRecC_tracked`, `tiC_tracked`, `exIC_tracked`, `exEC_tracked` | `GenericContinuity.lean` | The Phase-C and Phase-D preservation lemmas. |
| 27 | `extract_tracked`, **`extract_continuous`** | `GenericContinuity.lean` | Every closed derivation's extract is `Continuous2`. |
| 28 | `RealizesCtQ`, `collapse_demo` | `CollapseDemo.lean` | The extract's class in `CtQ 2`, total on closed derivations. |

### 1.6 What the fragment proves

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 29 | `plusZeroDeriv` … `timesSuccDeriv` | `Arithmetic.lean` | The four `+`/`×` equations as genuine `ind` theorems (Phase A). |
| 30 | `hrep`, `hrep_eval_self`, `hrep_eval_bump`, `goodComputeDeriv`, `goodN_four`, `goodN_three` | `Goodstein.lean` | Hereditary representations as terms of the fragment; the sequence computed inside the fragment; the cross-checks against `WilliamAngus/Goodstein`. |
| 31 | `ordTerm_hterm`, `ordOf_goodstein_three`, `ordOf_goodstein_three_descends` | `TransfiniteInduction.lean` | The notations *are* Phase B's `HTerm` grammar read at base `ω`; and the kernel-verified descent `9 ≻ 2 ≻ 10 ≻ 3 ≻ 1 ≻ 0` along `G(3)` — note it is not numerically decreasing. |
| 32 | `tiDemoDeriv` | `TransfiniteInduction.lean` | `tiEps0` exercised end to end. |
| 33 | `goodThreeExDeriv`, `good_three_ex_witness` | `Exists.lean` | The fragment's first existential theorem, and the witness read off its realizer. |
| 33½ | **`Deriv.ordDescent`**, `ord_descent_via_fragment` | `OrdinalDescent.lean` | The Goodstein descent **derived** in the fragment from three single-symbol schemas (D5), and the round trip showing the derivation recovers the semantic descent through `soundness`. Read this before the theorem — it is where the phrase "the fragment proves Goodstein" is cashed out or qualified. |
| 34 | `descentDeriv`, `namedIHDeriv`, `stepBranch`, `goodProgressive` | `GoodsteinTheorem.lean` | The four pieces of the induction step.  `namedIHDeriv` is the substitution trick — read its docstring. |
| 35 | **`goodsteinTheorem`** | `GoodsteinTheorem.lean` | `⊢ ∀m ∃t. good(m,t) = 0`. |
| 36 | `goodsteinStopTime`, **`goodsteinStopTime_spec`**, `goodstein_extract_continuous`, `goodsteinRealizesCtQ` | `GoodsteinExtraction.lean` | The extracted function, its correctness at every input, its continuity, and its class in `CtQ 2`. |

### 1.7 The Hydra layer (H1–H9) — the second theorem, on the same machinery

**`HYDRA.md` is the self-contained account of this layer**; the table
below is the dependency-ordered reading list.

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 37 | `encodeH`/`hydraOf`, `hydraOf_encodeH`, `encodeF_forestOf` | `Hydra.lean` | Finite rooted trees coded into `ℕ` through Phase C's pairing, with **both** round trips — so `∀h` ranges over exactly the trees, and `0` is the dead hydra. |
| 38 | `cutH`, `hydraStepN`, `hydraSeqN`, `hydraSeq_chain`, `battleLen_small` | `Hydra.lean` | The Kirby–Paris move and the battle, with the small battles kernel-checked and the published lengths `1, 3, 37` used to pin the rule down. |
| 39 | `insertExp`, `nfB_insertExp`, `precB_trans`, `precB_trichotomy` | `Hydra.lean` | The CNF sum `ω^e ⊕ c` on Phase C's codes, plus the order facts the notation layer never needed before: totality, transitivity, asymmetry. |
| 40 | `ordOfHydra`, `nfB_ordOfHydra`, **`cutH_descends`** | `Hydra.lean` | The ordinal assignment and the descent theorem: every legal move lowers it, at every replication factor — including the moves that make the tree bigger. |
| 41 | `Deriv.hordCutLt`, `hydra_descent_via_fragment`, `hydraComputeDeriv` | `HydraFragment.lean` | The single imported schema, the round trip proving the import faithful, and the fragment computing concrete battles. Read this before the theorem — it is where "the fragment proves Kirby–Paris" is cashed out or qualified. |
| 42 | `hydraDescentDeriv`, `hydraNamedIHDeriv`, `hydraProgressive` | `HydraTheorem.lean` | The pieces of the induction step; the same naming trick as `namedIHDeriv`. |
| 43 | **`hydraTheorem`** | `HydraTheorem.lean` | `⊢ ∀h ∃t. hydra(h,t) = 0`. |
| 44 | `hydraBattleLength`, **`hydraBattleLength_spec`**, `hydra_extract_continuous`, `hydraRealizesCtQ` | `HydraExtraction.lean` | The extracted battle-length function, correct at every tree, continuous, with its class in `CtQ 2`. |
| 45 | `Play`, `play_descends`, **`hercules_wins`**, `no_infinite_play`, `play_stuck_iff_leaf`, `hydraStep_play` | `HydraGeneral.lean` | The general game (H7): *any* head, *any* replication factor at every step. Every play is finite and ends at the bare head, and the fragment's battle is one of these plays. Read `play_two_choices` — it is what rules out the relation secretly being the leftmost strategy. |
| 46 | `battleLenH`, **`battleLen_eq_battleLenH`**, `battleTrace`, `sizeTrace`, `descendsAlong` | `HydraDisplay.lean` | The battle run on trees rather than codes (98 s → <1 s, proved to be the same battle), so `Hydra(3) = 37` is `#guard`ed at every build; and the trace that shows the tree growing while the ordinal falls. **Start here if you want to see the theorem rather than read it.** |
| 47 | `cutRightF`, `rightStep_play`, **`rightStep_descends`** | `HydraStrategies.lean` | A second strategy (rightmost head), whose descent and termination follow from H7 in one line each — the test that the general theorem is usable. Both strategies give `1, 3, 37`, `#guard`ed, through different intermediate states. |

### 1.8 The Hanoi layer (E1–E5) — the third theorem, on the *simplest* machinery

The point of this one is what it does **not** use: no `TI(ε₀)`, no
ordinals, only `ind`, `∃` and Phase A's arithmetic.  What it exercises
instead is a *branching* recursion — two sub-calls per level, where
Goodstein's and Hydra's were linear chains.

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 48 | `mvN`, `hconsN`, `hanoiAux`, `hanoiN` | `Hanoi.lean` | Moves as `src*3+dst`; sequences in the *same* cons coding as the Hydra layer; the solver in difference-list form, which is what keeps the module free of list theory. |
| 49 | `hcheck`, `solvesN`, **`solvesN_succ`** | `Hanoi.lean` | `Solves` as a **parser** — it validates an arbitrary `k` rather than comparing against the canonical answer, which is what makes the existence theorem say something. The `#guard`s check it rejects non-solutions. |
| 50 | **`solvesN_unique`**, `solvesN_length` | `Hanoi.lean` | The relation admits exactly one sequence, of length `2^n − 1` — the precise sense in which the result is optimal. Read the section header for what this is *not* (classical minimality over arbitrary legal sequences). |
| 51 | `expDoubleDeriv`, **`ihRenamed`** | `HanoiTheorem.lean` | `2^x + 2^x = 2^(x+1)` from Phase A, no induction; and the α-renaming device — a permuting recursion cannot instantiate its induction hypothesis at a permutation of the goal's own bound variables, and this is the fix. |
| 52 | **`hanoiTheorem`** | `HanoiTheorem.lean` | `⊢ ∀n∀f∀t∀v ∃k. Solves(n,f,t,v,k) ∧ MoveCount k = 2^n − 1`, by ordinary `ind`. |
| 53 | `hanoiSolution`, **`hanoiSolution_spec`**, `hanoiMoves` | `HanoiExtraction.lean` | The extracted solver, correct and optimal at every input, and its output decoded into readable `(src,dst)` pairs — the classical sequences, `#eval`ed at n=1..4. |

### 1.9 The Pascal layer (F1–F4) — the fourth theorem, and the one you can *see*

The lightest infrastructure of all: a decidable disjunction, so the
extract is a decision **function**, not a witness — and the picture it
draws is the theorem, not an illustration of it.

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 54 | `xorN`, `pasN` | `Pascal.lean` | The mod-2 recursion. Read the header for why `xor` must be a symbol: `a + b − 2ab` is not expressible in this signature. |
| 55 | `pasAbove`, `pasDiag`, `pasZeroCol` | `PascalTheorem.lean` | The characteristic clauses **derived**, not assumed. `pasAbove` is the real induction — it needs its hypothesis at two arguments. |
| 56 | **`pasTotal`** | `PascalTheorem.lean` | `⊢ ∀n∀k. pas(n,k) = 1 ∨ pas(n,k) = 0`, by nested `ind`. The header names the standing device: `ind` with the hypothesis discarded *is* the fragment's `0`/`succ` case split. |
| 57 | `pasTag`, **`pasDecide_eq`**, `pasTriangle` | `PascalExtraction.lean` | The disjunction's tag as a decision procedure, proved correct at every `(n,k)` from soundness — and the Sierpiński triangle it prints. **Start here if you want to see a theorem rather than read one.** |
| 58 | `pasN_even`, `pasN_lucas_step`, **`pasN_eq_one_iff`**, `pasN_eq_one_iff_land` | `Lucas.lean` | **Kummer/Lucas at p=2** (Phase G): `C(n,k)` is odd iff `k`'s bits are a submask of `n`'s. The one theorem in the Pascal work that is *about* the triangle rather than about `pas`'s definition — it is why the picture is the gasket. Metatheory, not fragment; the header and STATUS say precisely why the fragment cannot state it. |
| 59 | **`binEvenDeriv`**, `binOddDeriv`, `bin_even_via_fragment` | `PascalBinary.lean` | The four binary step identities — Lucas's core — derived **inside** the fragment by `ind`, with the round trip back to the value level. The induction alternates even/odd rows: the gasket's self-similarity as a proof term. |

### 1.10 The order + Euclid layer (Z0, Euclid E1–E2) — the fifth theorem, and the one with *no new symbols*

> **Phase-label warning.**  "E1"–"E5" are Hanoi's sub-phases (§1.8);
> "E1"/"E2" are *also* the labels of the order foundation and the Euclid
> work below.  They are different phases that happen to share letters.
> STATUS.md has both under separate `##` headings; when a label is
> ambiguous, go by the file.

The interesting constraint here is what this layer *refuses* to add.
Order (`<`, `≤`) and divisibility (`∣`) are not symbols and not axiom
schemas — they are **defined**, as existentials over `+` and `×` that the
fragment already had.  So every order and divisibility fact below is a
derivation rather than an import, and the layer costs the signature
nothing.  Contrast Sperner's `look` in §1.11, which is the one place the
discipline genuinely breaks.

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 60 | `ltT`, `leT`, `ltZeroElim`, `ltSuccSelfV`, **`ltStepDown`** | `StrongInduction.lean` | Numeric order as a *defined* notion: `y < t := ∃d. succ y + d = t`. `ltStepDown` (`z<y` and `y<succ v` give `z<v`) is the load-bearing one — it is what discharges the induction hypothesis everywhere below. `plusAssocDeriv` was added to land it. |
| 61 | `caseNatDeriv`, **`trichotomyDeriv`** | `StrongInduction.lean` | The `0`/`succ` case-split surrogate, and `⊢ ∀a∀b. a≤b ∨ b<a` — the comparison Euclid branches on. Recall the standing device from §1.9: the fragment cannot case-split a variable, so `ind` with the hypothesis discarded *is* the case split. |
| 62 | `demoAuxDeriv`, **`strongIndDemo`** | `StrongInduction.lean` | **Strong induction derived from `ind`** — the numeric-`<` analogue of `tiEps0`, but *derived*, not primitive, via `Aux(v) := ∀y. y<v → φ(y)`. **Read the header for the device that makes it work:** the fragment has no formula-level Leibniz, so `φ(y)` is never *transported* across an equation — it is *produced at `y`* by applying progressiveness there and discharging its premise from the IH through `ltStepDown`. Same flavour as Goodstein's naming trick and Hanoi's `ihRenamed`: routing around naive substitution. Shipped **concretely** (`φ := x=x`) through the full scaffold; a generic-in-`φ` former is deliberately deferred. |
| 63 | `distribDeriv`, `dvdT`, `dvdReflDeriv`, `dvdZeroDeriv`, `dvdAddDeriv` | `Euclid.lean` | Divisibility, likewise defined: `d ∣ a := ∃q. a = d·q`. `distribDeriv` (`d·(x+y) = d·x + d·y`) is a genuine `ind` theorem and the algebraic engine of the rest. |
| 64 | `cancelAddDeriv`, `addEqZeroDeriv`, **`dvdSubDeriv`** | `Euclid.lean` | The subtraction side: `d∣a → d∣(a+c) → d∣c`. This is what makes *subtractive* Euclid go through without a monus symbol. |
| 65 | **`gcdTheorem`** | `GcdTheorem.lean` | `⊢ ∀a∀b. ∃g. g∣a ∧ g∣b ∧ ∀d.(d∣a→d∣b→d∣g)`. The extracted `g` **is** the gcd — there is no `gcd` symbol. **Measure: strong induction on the sum `a+b`**, since neither argument decreases at every subtractive step but the sum does. Two things to read for: **no positivity precondition** (dropped as unnecessary — `gcd(0,0)=0` realizes the spec), and **both naive-substitution dodges composed** — the sub-sum is *named* by a fresh `∀` (Goodstein's device) *and* φ's inner `∀a∀b` is α-renamed (Hanoi's device). The `b<a` branch recurses on `(b, succ s)` so recombination needs no commutativity. |
| 66 | `gcdWitness`, `gcdWitness_dvd`, `gcd_derivBound` | `GcdExtraction.lean` | The extract, and a certified-but-**unrunnable** one: `derivBound gcdTheorem = 41` (the repository's deepest derivation, against Goodstein's 12), so pure-type operations nested 40 deep mean even `gcdWitness 0 0` does not return. `gcdWitness_dvd` still proves from soundness that it is a common divisor at *every* `(a,b)`. Read this next to §1.11's Sperner entry: the same wall, and there it is worked around. |

### 1.11 The Sperner layer (S1) — the sixth theorem, and the one that forced a symbol

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 67 | `lookN`, `colorCode`, `lookN_colorCode` | `Coloring.lean` | The `k`-th colour of the coloring coded by `w`, over `Hanoi.lean`'s cons-list and Phase C's choice-free pairing. Sits before `Syntax.lean` because `Term.eval` evaluates `look` by it — so, like Hydra's and Hanoi's value layers, it is inside `extract` and must stay choice-free. |
| 68 | `look` — **the one genuinely new symbol** | `Coloring.lean`, `Syntax.lean` | Worth stopping on, because it is the exception to the discipline §1.10 illustrates. Order and divisibility could be *defined* as existentials; `c k` for a bound `k` cannot. It is **data access** — a decode recursion, not a relation — so no `∃`-encoding reaches it. The fragment has no function variables either, so the arbitrary coloring `c` is a `ℕ` **code**. Added through all ~16 sites; every pre-existing `#print axioms` line is unchanged. |
| 69 | `invP`, `spernerInduction` | `SpernerTheorem.lean` | The forward scan: `ind` on the invariant `P(m) := (c m = 0) ∨ ∃k<m. c k ≠ c(k+1)`. The step compares `c(m+1)` to `0` by `eqDec` and either stays left or reports the crossing at `m`. |
| 70 | **`spernerTheorem`** | `SpernerTheorem.lean` | `⊢ ∀n∀c. (c 0=0) → (c n=1) → ∃k. k<n ∧ c k ≠ c(k+1)` — Sperner's lemma in 1D, the discrete intermediate value theorem. **No `TI(ε₀)`**: an ordinary PA-strength theorem by `ind`, reusing §1.10's `ltT`. Note the delivered generality: it is proved for **arbitrary `ℕ`-valued** colorings — the `{0,1}` restriction is never used, so binary Sperner is the special case. 2D Sperner and Brouwer are **explicitly out of scope** (they need a triangulation object). |
| 71 | `spernerWitness`, `spernerWitness_spec`, **`spernerScan`** | `SpernerExtraction.lean` | The extract is a genuine **linear scan returning the *first* crossing** — forced by the invariant, which carries the minimal crossing once found and never revises it, and `#guard`ed on multiple-crossing colorings (`[0,1,0,1] → 0`). **Read `spernerScan` for the general workaround to §1.10's wall:** the ambient-11 realizer overflows the interpreter, but the witness numeral is **ambient-independent**, so the *same* derivation is read at ambient 5 — checked to agree — and that one evaluates. |

### 1.12 The Fibonacci on-ramp (Phase Fib) — chronologically last, but **read it first**

Deliberately the easy case: the most recognizable recursive function,
extracted by the pipeline **unchanged**, with no ordinals anywhere.  It
was written after everything else but is meant to sit *before* Goodstein
in the narrative — if §1.6 was heavy going, start here and go back.

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 72 | `fibPair`, `fibN`, `fibN_succ_succ` | `Signature/Fibonacci.lean` | `fib` as a value symbol, via a *structural* paired recursion `(a,b) ↦ (b, a+b)` — so it reduces in the kernel (`fibN 10 = 55` by `rfl`) and the `fibSucc` schema is `rfl`-sound. |
| 73 | **`fibPairedTheorem`**, `fibBody`, `fib_lvl` | `FibonacciTheorem.lean` | `⊢ ∀n. (∃y. fib n = y) ∧ (∃z. fib(n+1) = z)`, by **ordinary `ind` on a paired invariant**. Two design points worth the read. *Why paired:* `fib(n+2)` needs two previous values — the course-of-values snag — dodged by carrying the pair, so the step is exactly `(y,z) ↦ (z, y+z)`. *Why `∧`-of-`∃` and not `∃y∃z`:* both are `lvl 0`, but nested existentials let the step's outer `exI` witness capture the inner binder's variable, restarting the renaming dance; written as a conjunction each body is atomic and nothing captures. `fib_lvl := rfl` confirms `lvl 1` on the nose. |
| 74 | `fibonacci`, `fibonacci_spec`, `fibNext`, **`fib_pair_spec`**, `fibonacci_ten` | `FibonacciExtraction.lean` | `derivBound = 5`, so unlike gcd and Sperner it *runs* — but exponentially (≈ ×4/step, the D4/D6 wall), so `#guard`s stop at `n=3`. **`fib_pair_spec` is the one to look at:** reading *both* witnesses recovers the iterative loop's exact pair-state, `(0,1) → (1,1) → (1,2) → (2,3)` — the `(a,b) ↦ (b,a+b)` iteration falling out of a proof that never mentions a loop. The headline `fibonacci 10 = 55` is `fibonacci_ten`: **certified through `fibonacci_spec`, not evaluated**, exactly as Goodstein's `m = 4` and gcd are. Note `#print axioms fibonacci = [propext, Quot.sound]` — the extracted function itself, traced. |

### 1.13 Looking at the extracted program (Phase P) — read this when you want to *see* the artifact

Everything above proves things.  This layer shows you what was produced.
None of it is certified content: the two `Meta/` modules are `partial
def`s and macros with no theorems, and they add no axioms.

Start with the problem, because it is not obvious that there is one.
**The extracted realizer cannot simply be printed.**  `#reduce (extract
goodsteinTheorem …)` never returns — it forces `tiRecC`, the same wall
that stops `goodsteinStopTime 2`.  And where reduction *does* finish it
over-reduces: the repository's smallest realizer, `extract
goodThreeExDeriv`, collapses to `fun n z => 30` (that is `Nat.pair 5 0`),
so the witness `5` the proof supplies is not in the output.

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 75 | **`#realizer d`**, `toSkel` | `Meta/RealizerDisplay.lean` | The realizer's *structure*, by walking the **derivation** rather than the extracted value — so it never calls `extract`, never builds a `PureType`, and terminates exactly where `#reduce` cannot. `goodsteinTheorem` and `hydraTheorem` come out as 29-line skeletons. Read the collapse rule in the header: a sub-derivation whose *conclusion* is an equation or `⊥` is contentless, so it becomes one `·` leaf — which is why 29 lines is the whole computational scaffolding and none of the equational chain. |
| 76 | `toSkel`, again — as **a per-rule site** | `Meta/RealizerDisplay.lean` | It matches every `Deriv` constructor with no wildcard, so a new rule breaks its build, exactly like `extract` / `derivBound` / `soundness` / `extract_tracked` — and, since §1.14, `emit` and `hsEmit`. Seven sites in total. If you are extending the fragment, these are the files people forget. |
| 77 | **`#realizerCH d`**, `toCH` | `Meta/RealizerDisplay.lean` | The same walk as `program-op — logic-rule ⟦proposition⟧`, one line per node: the Curry–Howard extraction map made legible instead of asserted. `paper/curry-howard.tex` is a standalone figure of it. **Caveat, and STATUS Phase P records it as a gap:** `toCH` *does* use a wildcard, so a newly added content-bearing rule is silently mislabelled `· — axiom (proof-irrelevant)` rather than breaking the build. |
| 78 | `#program d` | `Meta/RealizerDisplay.lean` | Pseudocode rendering of the same skeleton. Explicitly a generated **display view, not the certified artifact** — the artifact remains `extract D`, correct by `soundness`, continuous by `extract_continuous`. It dispatches on `toSkel`'s display strings, so treat its output as illustrative. |
| 79 | `witness₁…₄`, `tag₂`, `extractedAt`, `extractedCtQ` | `Meta/ProgramExtraction.lean` | The "apply the realizer to numerals, read the witness or tag" boilerplate, factored. It **re-proves nothing** — and it is *not* a compiler from Lean theorems: a Lean theorem must first be written as a `Formula` and proved as a `Deriv`. `EXTRACTED_PROGRAMS.md` is the index of the resulting programs. |
| 80 | **`stopBySearch`** vs **`minStop`** vs `goodsteinStopTime` | `Theorems/Goodstein/GoodsteinSearch.lean` | **The clearest single statement of what extraction buys.** The μ-search `stopBySearch` must be `partial`: nothing bounds it, and its totality *is* Goodstein's theorem. `minStop := Nat.find (goodReachesZero m)` is the same search made *total* — and it type-checks only because `goodReachesZero` **is** `goodsteinStopTime_spec`, so the μ-operator literally consumes the theorem as its termination argument. "The search halts iff the theorem holds" becomes the type of `Nat.find`. Two honesty notes in the header: the proof is erased at runtime (so the certificate buys termination, *not* speed — `minStop 4` is as unreachable as the naive loop), and its `Classical.choice` is metatheory, not an extracted-program budget. |
| 81 | `Deriv.bumpNeZeroNumeral`, `Deriv.neZeroOfEqSucc` | `Theorems/Goodstein/OrdinalDescent.lean` | Every **closed numeral** instance of `bumpNeZero` derived *without* the schema, from `bumpNum` + equality + `succNeZero`. The first dent in the import ledger, aimed at the smallest remaining Goodstein import. The uniform open-term schema is still imported — nothing was removed. |

### 1.14 The level-free emitter (Phase X) — where the certified programs finally *run*

The uncomfortable fact this section answers: the repository contains a
**certified program that has never been executed.**  `derivBound
gcdTheorem = 41`, so `gcdWitness 0 0` does not return at any input at all.

The fix is a second extraction rather than an optimization, and it turns
on one observation: the realizers' cost is not their computational
content.  It is the `PureType` tower and the transports — scaffolding
that exists so `MR` can be stated at a flexible ambient and
`extract_continuous` can quantify over all derivations at once, and that
computes nothing.  Delete it and what remains is System T plus one
well-founded recursor.

**Read the scope note first.**  Nothing here is certified: there is no
theorem relating `emit` to `extract`, and no soundness theorem for
`emit`.  These are generated views, exactly like `#program`'s pseudocode.
What *is* checked, every build, is agreement with the certified extracts
wherever those terminate.

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 82 | **`tyOf`**, `defaultOf`, `tyOf_subst` | `Meta/EmitLean.lean` | The type translation, and the whole of the design: `⟦∀x φ⟧ = ℕ → ⟦φ⟧`, `⟦∃x φ⟧ = ℕ × ⟦φ⟧`, equations `Unit`. Note what is **absent** — no level index and no dependence on `ρ`, which is exactly why a realizer's type only ever depended on `lvl`. `tyOf_subst` is the one lemma the module needs, and every `cast` in `emit` is it. |
| 83 | **`emit`** | `Meta/EmitLean.lean` | `Deriv Γ φ → Ctx Γ → tyOf φ` — a total Lean function, not a string generator, so Lean type-checks it. Choice-free (`[propext, Quot.sound]`). **Read the `tiEps0` case:** the premise `y ≺ x` is an equation, so its realizer is contentless and carries no evidence of descent; `emit` re-*decides* `OLt` at the recursive call and falls back to a default, which is exactly what `tiRecC` does and for the same reason. |
| 84 | **`emGcd`**, and the `#guard`s | `Meta/EmitDemo.lean` | **Start here.** `emGcd 12 18 = 6`, from the derivation whose certified realizer evaluates at no input whatsoever. The module runs two kinds of check at every build: *agreement* with the certified extract wherever it terminates (Fibonacci `n≤3`, Goodstein `m≤1`, Hydra code ≤1, Hanoi's decoded move lists, all of Pascal row 6), then *reach* past that point. The agreement checks are evidence in `spernerScan`'s sense — read the same derivation a cheaper way and verify the readings match — not proof. |
| 85 | the reach table | `Meta/EmitDemo.lean` header | Goodstein `m=1 → 3`, Fibonacci `n=3 → 25`, gcd nothing → hundreds. And **Hanoi `n=4 → n=4`, unchanged** — which is a result, not a disappointment: STATUS has claimed since E4 that Hanoi's wall is the *encoding*, not the extraction, and deleting the entire ambient tower moved it not at all. |
| 86 | `hsTy`, `hsEmit`, **`#haskell`** | `Meta/EmitHaskell.lean` | The same walk emitted as Haskell, mirroring `tyOf`/`emit` clause for clause. Verified end to end — the generated modules compile under GHC and run, including `gcd 1071 462 = 21`, which the *Lean* emitter times out on. Output is small (gcd is 6 KB from a 531-line derivation) because the collapse rule prints equational sub-derivations as `()`. |
| 87 | `hsPrelude` | `Meta/EmitHaskell.lean` | The second trusted boundary, split explicitly rather than papered over: arithmetic/`fibN`/`pasN`/`xorN` are **implemented**; everything decoding Phase C's pairing is a **stub** naming its Lean source, deliberately an `error` rather than a re-implementation that might silently diverge. So gcd, Fibonacci and Pascal emit to runnable Haskell; the rest emit structurally complete programs awaiting the prelude. **Also read the `tiRec` warning:** Haskell cannot express well-founded recursion along `≺`, so an emitted Goodstein program is one Haskell cannot certify halts — epistemically back beside `stopBySearch` (§1.13, row 80), which is exactly the distinction Phase P4 draws. |

---

## 2. The four sub-phases in plain language

**D0 — the existential quantifier.**  The fragment had no `∃`, so
Goodstein's theorem could not even be stated.  Adding it was cheap
because modified realizability treats `∃y φ` almost exactly like a
disjunction: a realizer is a pair whose first component is the witness
and whose second realizes `φ` there, so the existing pairing devices did
all the work and no new ambient level was needed.  The two new rules are
the standard introduction and elimination, with elimination carrying the
usual freshness conditions that stop the witness escaping its scope.

**D1 — the three obligations.**  These are facts about numbers, not
about derivations: that the ordinal assignment always produces a *normal*
notation, that bumping the base leaves the ordinal unchanged, and that
one Goodstein step strictly decreases it.  The first two turned out to be
the substantial work of Phase D — they need real logarithm theory (that
`hlog` is maximal, hence that digits are bounded and exponents strictly
decrease) and a proof that `bumpN` is strictly monotone and bound-
respecting, which Phase B had never needed.  The third is then short: given
base-change invariance, the descent is just monotonicity applied to
"subtract one".

**D5 — closing the descent gap.**  D2's proof imported its core step as
an axiom; D5 splits that into three properties of individual symbols and
has the fragment derive the step itself.  The imported facts no longer
mention the Goodstein sequence, and reading the derived step back through
soundness recovers the semantic theorem, so the derivation is not
vacuous.  What remains imported is three general facts about the ordinal
assignment, which the fragment cannot yet prove because it has no
division, logarithm, or order relation.

**D2 — Goodstein's theorem.**  Transfinite induction along `≺` on the
formula "every state of the sequence whose ordinal is `x` eventually
reaches `0`", with the start value as a parameter.  If the current value
is `0` we are done and the step count is the witness; otherwise the next
state's ordinal is strictly smaller, so the induction hypothesis applies
to it and hands back a witness.  The only fact imported from the
metatheory is D1's descent, which enters as the axiom schema
`ordDescent`; the case analysis, the gluing with `goodSucc`, the
induction and the witness are all the fragment's own work.

**D3 — the extracted function.**  Because the realizer of an existential
carries its witness, the derivation *is* a program: apply the extracted
realizer to a start value and read the first component.  That function is
proved correct for every input by instantiating soundness — no
computation involved — and it is continuous by the generic continuity
theorem with no new argument.  It also literally runs, though only for
the smallest inputs: the extract re-evaluates its own recursive calls
through the transport towers, so cost explodes with the number of
Goodstein steps.

---

## 3. Design decisions made in this brief (apply extra scrutiny here)

These were *not* dictated by the brief.  Each is a place where a
reviewer should check that the choice is sound and that nothing was
quietly weakened.

1. **`∃` reuses `∨`'s machinery rather than getting its own** (the
   expected example).  `exIC`/`exEC` are built from `pairPT`/`fstPT`/
   `sndPT`, and `lvl (∃y φ) = lvl φ`.  Check: is the `MR` clause for `∃`
   the standard one, and does the level assignment make `derivBound`
   sound?  (`Exists.lean` header; `ModifiedRealizes.lean` `MR`.)
2. **`∃`-elimination's side conditions.**  I chose `FreshIn x Γ` and
   `¬ ψ.FreeIn x` — the standard pair.  Check they are strong enough in
   the soundness case (`Soundness.lean`, `exE`).
3. **The `ord` symbol was added to the signature.**  Phase D2 needs to
   *speak* about the ordinal of a state, and the fragment has only
   equations between terms, so the assignment had to become a function
   symbol.  Check: does anything in the theorem depend on `ord` having
   properties beyond the one axiom below?
4. **The descent: three schemas, composite derived** (revised in D5; D2
   had it as one imported schema).  `ordBump`, `ordPredLt`, `bumpNeZero`
   are imported — each discharged by exactly one D1 theorem — and
   `Deriv.ordDescent` derives their composite inside the fragment.  Check
   three things: that each schema is *true* as stated (base `≥ 2` is
   built into its shape); that none of them is secretly the descent
   itself; and that `ord_descent_via_fragment` really goes through
   `soundness` rather than quietly invoking `ordOf_descent`.
5. **The "name the ordinal" trick** instead of adding α-renaming to the
   fragment.  This is the subtlest choice in Phase D.  Check that the
   capture it avoids is genuine (it is: the substituted term mentions `s`,
   which φ binds) and that the extra `∀z` does not weaken the theorem.
   (`GoodsteinTheorem.lean`, `namedIHDeriv`.)
6. **`2 ≤ k` on D1 obligations 2 and 3.**  Not in the brief; forced,
   because base change is not ordinal-preserving at `k = 1`.  Check that
   every use site supplies a base of the form `s + 2`.
7. **Moving `hlog`/`bumpN`/`goodN`/`ordOf` into `OrdinalAssignment.lean`.**
   A structural move with no content change, forced by the module order
   (`Soundness.lean` needs D1's theorems).  Check that nothing was
   silently altered in transit.
8. **Removing `noncomputable` from the transports and the extraction
   combinators.**  Required for D3 to run at all.  Check that the
   definitions are otherwise untouched.
9. **Formula abbreviations in `GoodsteinTheorem.lean` are `abbrev`, not
   `def`.**  Needed so `decide` can discharge the side conditions.  A
   reviewer should confirm the side conditions really are being *proved*
   (they are — by `decide +kernel` on decidable predicates), not assumed.
10. **Reusing variable `5` for both the transfinite-induction binder and
    the naming variable.**  Deliberate: it is what keeps the `allE` at
    `var 5` capture-free.  Check the variable convention table at the top
    of `GoodsteinTheorem.lean`.

Carried over from earlier phases, restated because they bear on Phase D:
`bumpNum`/`precNum` are numeral-graph axioms (Phases B/C), and Phase C's
order is only well-founded on normal forms.

---

## 4. Reproducing every claim from a fresh clone

```bash
# 1. This repository alone — it is standalone (the Kleene–Kreisel subset it
#    uses is vendored under Realizability/Core/ContinuousFunctionals/).
git clone https://github.com/aaslyan/modified-realizability-lean.git
cd modified-realizability-lean

# 2. Build everything.  Toolchain (leanprover/lean4:v4.26.0) is pinned in
#    lean-toolchain; elan fetches it automatically.  Mathlib (pinned in
#    lakefile.lean) is downloaded on first build.
lake build

# 3. Zero placeholders.  Note the scoping: since the layered reorg the
#    sources live in subdirectories, so a `Realizability/*.lean` glob
#    matches nothing and would "pass" vacuously.  Recursive, word-boundary,
#    and excluding the vendored read-only mirror:
grep -rnw "sorry\|admit" Realizability/ --include="*.lean" \
     --exclude-dir=ContinuousFunctionals                # expect: no matches

# 4. The authoritative check, since Lean reports `sorry` as a *warning*
#    rather than an error: no extracted or certified declaration may
#    depend on `sorryAx`.  It would appear in the `#print axioms` lines
#    the build already prints.
lake build 2>&1 | grep sorryAx                          # expect: no matches
```

`lake build` already prints every `#print axioms` result and every
`#eval` in the development.  To check the Phase-D claims individually:

```bash
cat > /tmp/check.lean <<'EOF'
import Realizability.Theorems.Goodstein.GoodsteinExtraction
namespace Realizability

-- D2: the theorem, at exactly the claimed type
#check (goodsteinTheorem :
  Deriv [] (Formula.all 2 (Formula.ex 4
    (Formula.eq (Term.good (Term.var 2) (Term.var 4)) Term.zero))))

-- D1: the three obligations
#print axioms nfB_ordOf
#print axioms ordOf_bumpN
#print axioms ordOf_descent

-- D0/D2/D3: realization, continuity, extraction
#print axioms good_three_ex_realized          -- D0
#print axioms goodstein_realized              -- D2
#print axioms goodsteinStopTime_spec          -- D3, correctness at every input
#print axioms goodstein_extract_continuous    -- D3, continuity
#print axioms extract_continuous              -- the generic theorem
#print axioms soundness

-- D3: the extracted function, running
#eval goodsteinStopTime 0                     -- 0    (<1 s)
#eval goodsteinStopTime 1                     -- 1    (<1 s)
-- #eval goodsteinStopTime 2                  -- does NOT finish; see STATUS.md
end Realizability
EOF
lake env lean /tmp/check.lean
```

And the Hydra claims (H1–H6):

```bash
cat > /tmp/hcheck.lean <<'EOF'
import Realizability.Theorems.Hydra.HydraExtraction
namespace Realizability

-- H5: the theorem, at exactly the claimed type
#check (hydraTheorem :
  Deriv [] (Formula.all 2 (Formula.ex 4
    (Formula.eq (Term.hydra (Term.var 2) (Term.var 4)) Term.zero))))

-- H4: the value-level functions are choice-free (they sit inside `extract`)
#print axioms hydraStepN
#print axioms hydraSeqN
#print axioms ordOfHydraN

-- H1/H3: the coding is a bijection; the descent is general
#print axioms hydraOf_encodeH
#print axioms cutH_descends

-- H4/H5/H6: the import is faithful, the theorem, the program
#print axioms hydra_descent_via_fragment
#print axioms hydraTheorem
#print axioms hydraBattleLength_spec
#print axioms hydra_extract_continuous

-- H6: the extracted function, running
#eval hydraBattleLength 0                     -- 0    (a few s)
#eval hydraBattleLength 1                     -- 1    (a few s)
-- #eval hydraBattleLength 2                  -- does NOT finish; see STATUS.md
end Realizability
EOF
lake env lean /tmp/hcheck.lean
```

Expected output, in order (measured, ~6 s in total):

```
hydraTheorem : Deriv [] hydraGoal
'Realizability.hydraStepN'   does not depend on any axioms
'Realizability.hydraSeqN'    does not depend on any axioms
'Realizability.ordOfHydraN'  does not depend on any axioms
'Realizability.hydraOf_encodeH'            … [propext, Quot.sound]
'Realizability.cutH_descends'              … [propext, Quot.sound]
'Realizability.hydra_descent_via_fragment' … [propext, Classical.choice, Quot.sound]
'Realizability.hydraTheorem'               … [propext, Quot.sound]
'Realizability.hydraBattleLength_spec'     … [propext, Classical.choice, Quot.sound]
'Realizability.hydra_extract_continuous'   … [propext, Quot.sound]
0
1
```

Two lines are worth pausing on.  The three *does not depend on any
axioms* results are load-bearing, not decoration: those functions sit
inside `Term.eval`, hence inside `extract`, so if any of them ever
acquired `Classical.choice` every continuity theorem's budget would break
at once.  And as with `goodsteinTheorem`, Lean *displays* the abbreviation
(`hydraGoal`), but the ascription in the `#check` is the spelled-out
`Formula.ex 4 (Formula.eq (Term.hydra …) …)`, so what was checked is the
unfolded type.

Expected output, in order: the `#check` echoing
`goodsteinTheorem : Deriv [] (Formula.all 2 goodTerminates)` — note Lean
*displays* the abbreviation `goodTerminates`, but the ascription in the
`#check` is the spelled-out `Formula.ex 4 (Formula.eq …)`, so what was
checked is the unfolded type;
`nfB_ordOf … [propext, Quot.sound]`; the other two obligations and every
`_realized` at `[propext, Classical.choice, Quot.sound]`; both
`_continuous` at `[propext, Quot.sound]`; then `0` and `1`.

The build itself is the strongest check: it fails if any `#print axioms`
line disagrees only in the sense that a reviewer reading the log will see
it, so read the log rather than trusting this file.

And the Phase-P claims — the display commands, the search/descent
contrast, and the first internalized piece of `bumpNeZero`:

```bash
cat > /tmp/pcheck.lean <<'EOF'
import Realizability.Meta.RealizerDisplay
import Realizability.Theorems.Goodstein.GoodsteinSearch
namespace Realizability

-- P1: the realizer you cannot print, printed.  The witness `5` is visible
-- here and is exactly what `#reduce` loses to `fun n z => 30`.
#realizer goodThreeExDeriv

-- P2: the same derivation as the Curry-Howard map.
#realizerCH goodThreeExDeriv

-- P1 again, on a realizer `#reduce` cannot evaluate at all.
#eval (Realizability.RealizerDisplay.realizerSkeleton goodsteinTheorem).splitOn "\n" |>.length

-- P4: search versus descent.  Same column, two termination guarantees.
#eval [stopBySearch 0, stopBySearch 1, stopBySearch 2, stopBySearch 3]
#eval [minStop 0, minStop 1, minStop 2, minStop 3]
#print axioms minStop

-- P5: the extraction helpers are choice-free.
#print axioms witness₁
#print axioms tag₂

-- P6: closed numeral instances of `bumpNeZero`, without the schema.
#print axioms Deriv.bumpNeZeroNumeral
end Realizability
EOF
lake env lean /tmp/pcheck.lean
```

Expected output, measured and quoted verbatim:

```
exI  ⟨witness = 5, ·⟩
   · ⟨contentless⟩  good(3,5) = 0

PROGRAM  —  LOGIC RULE  ⟦ PROPOSITION ⟧
return ⟨5, ·⟩  — ∃-intro  ⟦∃x1.good(3,x1) = 0⟧
   ·  — equation (proof-irrelevant)  ⟦good(3,5) = 0⟧

30
[0, 1, 3, 5]
[0, 1, 3, 5]
'Realizability.minStop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Realizability.witness₁' depends on axioms: [propext, Quot.sound]
'Realizability.tag₂' depends on axioms: [propext, Quot.sound]
'Realizability.Deriv.bumpNeZeroNumeral' depends on axioms: [propext, Quot.sound]
```

Four lines are worth pausing on.

The `30` is the Goodstein skeleton's line count (29 rendered lines plus
the trailing newline's empty segment).  It is the point of P1: that
derivation's extracted realizer is one `#reduce` never returns from, and
this prints its whole computational scaffolding in 29 lines because every
equational sub-proof collapses to a `·` leaf.

The two `[0, 1, 3, 5]` columns are the *same* stopping times computed by
the naive `partial` μ-loop and by `Nat.find`.  The second is total only
because it consumes `goodsteinStopTime_spec` as its termination
argument — that is the whole content of P4, and it is a typing fact, not
a comment.

`minStop`'s `Classical.choice` is **not** a regression in the extracted
program budget.  It is metatheory: `minStop` reasons *about* an extract
and inherits choice through `soundness`.  Every extracted program in the
repository is still `[propext, Quot.sound]` — which the two helper lines
below it show for the reading API itself.

`Deriv.bumpNeZeroNumeral` is a derivation *of the fragment*, so its
budget is the ordinary one; what matters is what is absent from its
proof, namely the `bumpNeZero` schema.  It is built from `bumpNum`,
equality reasoning, and `succNeZero` alone.  The uniform open-term schema
is still imported — see STATUS.md Phase P6 and `RESEARCH_PLAN.md` §2.

---

# Part II — The HA^ω library (`HAomega/`)

The one-sentence version: **the same modified-realizability pipeline,
rebuilt over Heyting arithmetic in all finite types, where the realizer is a
term of the object language — twelve extracted programs, four of them from
theorems the fragment cannot even state, and (since the typed layers) with
neither ordinals nor hydra trees encoded into `ℕ` anywhere.**  Every fact below is
evidence-tagged in `HAOMEGA_DOSSIER.md`; this section is the reading order.

## 5. Dependency-ordered map

### 5.1 The machinery (read in this order)

| # | Declaration | File | What it gives you |
|---|---|---|---|
| H1 | `Ty`, `Ty.interp` | `Syntax.lean` | Finite types over ℕ with a `unit` for erased certificates. Note it is *not* the vendored pure-type tower — continuity later bridges by a logical relation instead of matching it. |
| H1b | `Eps0`, `olt`/`nf`, `oLtE_wf`, `ordE` | `OrdCnf.lean` | **The typed ordinal layer**: ε₀-notations as an inductive type, structural comparison and normal form, well-foundedness *inherited* from the coded order through `toCode` (proofs only — no coding in any computation), and the Goodstein assignment mirrored constructor for constructor. Read the size table in the header: a notation whose code is a 1,412-digit integer is a 67-node tree. |
| H1c | `ordEOfHydra`, `Eps0.insert`, `isLeafN`, `oltE_ordEOfHydra_step` | `HydraTyped.lean` | **The typed hydra layer**: trees as the base type `.hyd`, with the ordinal assignment landing in `.ord` rather than a code. `Eps0.insert` is `insertExp` with the fuel deleted; the descent is H7's `play_descends` on trees with no coding round trip. This is what moves the battle wall. |
| H2 | `Tm`, `Tm.eval` | `Syntax.lean` | Intrinsically-typed de Bruijn System T — recursor **at every type** — plus the primitives (`add`, `prec`, `pred`, `bump`, `good`, `ord`, `hcut`, `hydra`, `hord`) evaluated by the first-order repo's proven choice-free value layers, and **`tiRec`**, recursion along `≺`. `Tm.eval` depends on **no axioms** and stays computable (read the `OrdCode`/`termination_by` note: a bare `WellFounded.fix` would not compile). |
| H3 | `Ren`/`Sub` kit, `eval_rename`, `eval_subst1` | `Syntax.lean` | The two-stage substitution treatment. Capture is impossible by construction — the fragment's `namedIHDeriv`/`ihRenamed` dodges have no analogue here. |
| H4 | **`Formula`** | `Formulas.lean` | Formulas **indexed by their realizer type** — `tyOf` as an index, not a function. This is the load-bearing redesign: substitution preserves the index by construction, so `MR_subst` states without a cast and `extract` contains none. Read the header's account of why the unindexed first design stalled soundness. |
| H5 | `eqAt`, **`interp_eqAt`** | `Formulas.lean` | Equality primitive at every type; extensional equality *definable* from it, proved correct. One Leibniz rule (`eqSubst`) replaces the fragment's ~20 congruence schemas. |
| H6 | **`MR`**, `MR_subst`, `MR_subst1` | `Realizability.lean` | Modified realizability with **no ambient level and no transports** — `Transport.lean`'s 330 first-order lines have no counterpart. Note the recorded non-theorem: `MR φ e x → φ.interp e` fails at `→`, deliberately. |
| H7 | **`Deriv`** — 39 rules | `Realizability.lean` | No rule carries a side condition. `tiEps0`'s order premise is an *equation* (contentless), which is why `tiRec` re-decides `≺` at each call. The Goodstein/Hydra schemas (`ordBump`, `ordPredLt`, `bumpNeZero`, `hordCutLt`) are single-symbol imports, D5-style, each discharged in soundness by exactly one value-layer theorem. |
| H8 | **`extract`** | `Extraction.lean` | `Deriv Δ φ → Tm (as ++ Γ) a` — the realizer is an object-language term: printable, runnable, emittable. **Zero casts, no axioms.** `eqDec` is the one content-bearing axiom; its emitted decision procedure (`eqTest`) is verified in Soundness. |
| H9 | `Realizes`, **`soundness`** | `Soundness.lean` | Every extracted term realizes its conclusion; one case per rule, no wildcard. Footprint `[propext, Classical.choice, Quot.sound]` — the choice enters through the value-layer *theorem proofs* for the ordinal schemas, exactly as first-order; every derivation and running extract stays choice-free. |
| H10 | `Tracked`, `eval_tracked`, **`extract_continuous2`** | `Continuity.lean` | The continuity bridge: an oracle-parameterized logical relation over `Ty`, base case the vendored `Continuous2` — no associates constructed, so the pure-tower shape never has to be matched. 11-constructor induction where the first-order proof needed ~40 combinator lemmas. Read the `tracked_dflt` docstring: "constant families are tracked" is *false* at arrow types. |

### 5.2 Proof engineering (what makes derivations writable)

| # | Declaration | File | What it gives you |
|---|---|---|---|
| H11 | **`deriv_norm`** | `GcdDvd.lean` | The normalization tactic: reduces every `Ctx.wk`/`Formula.wk`/substitution in a `Deriv` goal — context index included — to ground form. The fix for whnf-vs-metavariable unification failures in nested eliminations. |
| H12 | **`deriv_assumption`** | `GcdDvd.lean` | Context search over normalized goals; retired the pinned `ax1`–`ax7` accessors in goal positions. |
| H13 | the term-form kit (`plusAssocT`, …, `trichotomyT`) | `GcdFull.lean` | ∀-lemmas cannot be `allE`-instantiated at use sites (the unifier cannot invert `Formula.subst1`); each lemma gets a term-parameterized form via one KIT-`simp`. |
| H14 | the explicit-chain discipline | `PascalTheorem.lean` header | Conversion chains written with holes make the elaborator symbolically execute substitution (20+ min/declaration); every intermediate named + every reduction its own `rfl`/`simp` link elaborates in milliseconds. |

### 5.3 The twelve extracted programs

| # | Theorem | File | Read it for |
|---|---|---|---|
| H15 | `fibDeriv`, `fibRealizer` | `Fib.lean` | The on-ramp; the three-view printers (`pretty`, `pretty'`); realizer **axiom-free**; extract runs to `n = 1000`. The header's historical note on the unary-addition wall is the record of why `+` is primitive. |
| H16 | `hiDeriv`, `hiProgram_continuous` | `HigherType.lean` | The type-2 theorem the fragment cannot state — where continuity has content. |
| H17 | `notAllZero_not_extractable`, `hiProgram_has_associate`, `hiModulus` | `Collapse.lean` | The evidence continuity is not vacuous: a discontinuous type-2 functional **no derivation extracts to**, and the collapse of a continuous one to its type-1 associate with an explicit computable modulus. |
| H18 | `pasT`, **`pasTotal`**, `pasTag` | `Pascal.lean`, `PascalTheorem.lean` | The first proof-computed extract: the decision tag comes from `eqDec` through two inductions. Row recursion **at type ℕ→ℕ** — what forced first-order `pas`/`xor` to be axiomatized symbols. Gasket `#guard`ed. |
| H19 | `hanoiT`, `hanoiSpec` | `Hanoi.lean` | Sequences as **functions** `(len, moves)` — the encoding-wall experiment concluded: `n = 10` where the fragment died at 5. First `∃` over a function. |
| H20 | `gcdT` … **`gcdTheoremD`**, `gcdFull` | `Gcd.lean` → `GcdStage2/Full/Dvd/Cases/Main/Theorem.lean` | The full specification by **fueled induction with slack** (`(a+b)+c = m` — plain `ind`, no strong-induction scaffold). Six landed layers; the first-order extract ran at *no* input, this one runs. |
| H21b | **`goodsteinOD`**, `goodsteinOX` | `GoodsteinTyped.lean` | H21's statement *verbatim*, proved by `tiEps0O` on structural notations — same derivation shape, three symbol replacements. The two extracts are build-guarded to agree; the typed one mentions no coded ordinal. Two proofs of one theorem with the **representation** as the variable, the way Sperner (H24) varies the proof. |
| H21 | **`goodsteinD`**, `goodsteinX` | `Goodstein.lean` | `tiEps0` used in anger; the first-order derivation line for line **minus the naming dodge**. Extract returns the published `[0,1,3,5]`; certificate `good(m, stop m) = 0` guarded. |
| H22b | **`hydraHD`**, `hydraHX` | `HydraTree.lean` | H22's theorem with **nothing encoded**: tree states, notation measures, one new rule instead of three (the battle is a term, so the recursor's conversions suffice). The payoff is measurable — it computes the published Kirby–Paris length **37** at a hydra where the coded extract overflows the interpreter without taking a step. |
| H22 | **`hydraD`**, `hydraX` | `Hydra.lean` | Goodstein's mirror with a shorter descent; one import (`hordCutLt`). Published lengths `[0,1,3]`. |
| H23 | `playT`, **`herculesD`** | `Hercules.lean` | `∀h ∀f^(ℕ→ℕ) ∃t. play(f,h,t) = 0` — strategy-quantified, unstatable first-order; `play` is a *term*, the descent needs *no new import*. Replication only; the head choice is quantified in H23b. |
| H23b | `moveF`/`playAtN`, **`herculesAnyD`** | `HydraSurgery.lean`, `HerculesAny.lean` | **The fully general game**: `∀h ∀f ∀g ∃t. playAt(g,f,h,t) = 0`. The surgery layer is `cutH` with a position argument — every in-range move a legal H7 `Play`, descent = `play_descends` on codes; one new primitive (`hcutAt`) + one new schema (`hordCutAtLt`); the derivation transcribes H23 with the head strategy threaded through. Extract agrees with H23's at the leftmost strategy. |
| H24 | **`spernerD`**, `spernerX` | `Sperner.lean` | Colorings as function variables — no `look`. **The fingerprint finding**: this proof extracts the *last* crossing where first-order S1 extracts the first (`[0,1,0,1] ↦ 2` vs `0`) — same theorem, different proof, measurably different program. |
| H25 | `R1`–`R7`, `showAll` | `ShowAll.lean` | Renders every realizer in three views and **writes `EXTRACTED_HAOMEGA.md` at each build**. |

## 6. The five design decisions to scrutinize

1. **Realizer-type indexing of `Formula`** (H4) — bought cast-free
   `MR_subst`, hence soundness; cost: `tyOf`'s clauses live in constructors.
2. **Equality and conversion at every type** — a *revision* of the
   type-0-only first design; Pascal's row equations forced it.  `eqAt`
   remains as the proof the narrow design was semantically sufficient.
3. **De-coding by inheritance.**  Both `OrdCnf.lean` (ordinals) and
   `HydraTyped.lean` (trees) give a coded object its own base type and then
   *inherit* every certified fact through an encoding used only in proofs
   (`toCode`).  No new descent argument, no new mathematics — and the coding
   disappears from every computation.  Hanoi's move sequences are the one
   coded object left.
4. **Primitives over definability** for the case-study symbols — definable
   in principle (System T is closed under their recursions), primitive in
   practice, evaluated by proven choice-free layers.  The numeral-graph
   *schemas* of the fragment are gone; the trade is recorded in
   `HAOMEGA.md`'s compromise table.
5. **`tiRec` re-decides `≺`** — the order premise's realizer is
   contentless, so the recursor cannot receive descent evidence; the
   `dite` fallback mirrors the first-order `tiRecC` exactly.

## 7. Reproducing the Part II claims

```bash
lake build          # 749 jobs; every #print axioms / #guard runs here
```

Spot checks (each was run for the dossier; expected outputs quoted there):

```bash
cat > /tmp/check.lean <<'EOF'
import HAomega.Sperner
open HAomega
#print axioms extract          -- (no axioms)
#print axioms soundness        -- [propext, Classical.choice, Quot.sound]
#print axioms extract_continuous2  -- [propext, Quot.sound]
#eval (goodsteinX 0, goodsteinX 1, goodsteinX 2, goodsteinX 3)  -- (0,1,3,5)
#eval (goodsteinOX 0, goodsteinOX 1, goodsteinOX 2, goodsteinOX 3) -- same, typed ordinals
#eval (hydraX 0, hydraX 1, hydraX 2)                            -- (0,1,3)
#eval hydraHX (Realizability.hydraOf 4)   -- 37: the published length, on trees
#eval herculesX (· + 1) 2                                       -- 3
#eval herculesAnyX 2 (· + 1) (fun _ => 0)                       -- 3 (leftmost head = hydraX)
#eval spernerX 3 (fun k => [0,1,0,1].getD k 0)                  -- 2 (last crossing)
EOF
lake env lean /tmp/check.lean
```

Known evaluation boundaries (measured, `HAOMEGA_DOSSIER.md` §5):
`goodsteinX 4` is cost-bound (astronomical value, no crash); the **coded**
`hydraX` covers codes 0–3, 5, 6 and stack-overflows on 4 and 7 — but the
**tree** `hydraHX` runs all of them, so that wall was the coding, now gone;
`fibExtracted` has no wall through `n = 1000`.
