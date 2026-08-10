# HA^ω — Heyting arithmetic in all finite types

This repository is a **copy** of `modified-realizability-lean`, taken at the
point where the first-order development was complete (716 jobs green, seven
theorems, the level-free emitter). It exists to try one thing:

> Redo the realizability pipeline over **HA^ω** — Heyting arithmetic in all
> finite types, with a typed λ-calculus term language — instead of over a
> one-sorted first-order fragment.

The original repository is untouched and remains the publishable artifact.
Nothing here is expected to flow back into it.

## Provenance and safety

* Branch: `haomega`. The `master` history is the original repository's.
* The `origin` remote was renamed to `upstream` and its **push URL disabled**,
  so HA^ω work cannot be pushed to the original repo by accident. Fetching
  from upstream still works.
* The first-order development under `Realizability/` is **kept, building, and
  untouched** — as the reference implementation to compare against, not as a
  dependency. `lake build` builds both libraries.
* The new work is a separate library, `HAomega/`, declared in `lakefile.lean`.
  It imports nothing from `Realizability` except the proven choice-free value
  layers its primitives evaluate by (`Signature.OrdinalAssignment`,
  `Signature.Hydra`, and through them `Ordinals.Epsilon0`).

## Why

Three documented compromises in the original all trace to a single cause —
the object language has one sort, `ℕ`, so everything else is *coded* into a
number:

| compromise | where it is recorded | what HA^ω does to it |
|---|---|---|
| `hercules_wins` proved in the metatheory, because a strategy is a function and the fragment has no function variables | `HydraGeneral.lean` (H7), README scope note | **fully derived**: `Hercules.lean`'s `herculesD` quantifies the replication strategy, and `HerculesAny.lean`'s `herculesAnyD` quantifies the head choice too — `∀h ∀f ∀g. ∃t. playAt(g,f,h,t) = 0`, on the computable surgery move `hcutAt` (`HydraSurgery.lean`) whose descent is H7's `play_descends` on codes. Both extracts run |
| `look` added as a symbol, the one place "no new symbols" was forced | `Coloring.lean` (S1), STATUS | dissolves — a coloring *is* a function |
| `bump`/`prec`/`hcut`/`xor`/`look` enter by **numeral graph** rather than open-term schemas | CLAUDE.md "documented compromise" | the numeral-graph *schemas* are gone; the symbols themselves were kept **primitive** (evaluated by the proven first-order value layer) rather than defined in System T — definable in principle, primitive in practice |
| ordinal notations **coded into `ℕ`** by triangular pairing, with decode/normal-form side conditions everywhere | `Epsilon0.lean` (C) | **dissolved**: `OrdCnf.lean` gives them the base type `.ord` with structural comparison and normal form; `GoodsteinTyped.lean` re-proves Goodstein on it, and the extract contains no coded ordinal at all |
| hydra trees **coded into `ℕ`**, doubly exponentially — the measured cause of the battle extract's interpreter overflow | `Hydra.lean` (H1–H3), dossier §5 | **dissolved**: `HydraTyped.lean` gives trees the base type `.hyd` with the ordinal landing in `.ord`; `HydraTree.lean` re-proves Kirby–Paris, and the extract runs the published 37-step battle the coded one cannot start |

And two costs measured during the emitter work (Phase X of the original):

* **Ambient levels** — `PureType` tower, `liftR`/`dropR`, `lvl`, `derivBound`.
  Pure bookkeeping for the proofs; computes nothing. `derivBound gcdTheorem =
  41` is why `gcdWitness` evaluates at no input at all. HA^ω has none of it,
  because a realizer's type is computed from its formula.
* **Data encoding** — the triangular pairing. Deleting the ambient tower did
  not move Hanoi's wall at all (`n = 4` before and after), which is what
  proved the encoding is a *separate* cost. HA^ω removes it at the root.

## Status (re-verified 2026-08-09 — see `HAOMEGA_DOSSIER.md` for evidence)

**751 jobs green**, zero `sorry`/`admit`, 7,994 lines in `HAomega/` (34
files). Machinery complete and **thirteen extracted programs run** — the
first-order repo's seven, plus three theorems that repo cannot state (the
higher-type Fibonacci, the strategy-quantified Hercules, and the fully
general any-head Hercules), plus Goodstein, Kirby–Paris and the general
Hercules game a second time each over the **typed** ordinal and hydra layers;
`EXTRACTED_HAOMEGA.md` renders every realizer in three views (raw object /
collapsed program / Haskell).

**Nothing is encoded any more.**  Every case study that ever coded an
object into `ℕ` now has a typed twin — Goodstein, Kirby–Paris, and the
fully general Hercules game — and Hanoi's move sequences were functions
from the start.  With `OrdCnf.lean` (ordinals) and
`HydraTyped.lean` (trees), both objects the first-order development had to
code into `ℕ` have their own base types, and the coding survives only inside
alignment *proofs*.  The measurable consequence: `hydraHX` computes the
published Kirby–Paris battle length **37** at the hydra where the coded
extract `hydraX` overflows the interpreter without taking a step.

Axiom footprints, run fresh (the earlier "`[propext]`-only continuity" claim
is stale — `tiRec`'s tracking case brought in `Quot.sound`; and `soundness`
carries `Classical.choice` since the Goodstein/Hydra rules, inherited from
the value-layer *theorem proofs*, exactly as in the first-order repo):

    Tm.eval, eval_tracked, extract_tracked, extract_continuous2,
    goodsteinD, goodsteinX, hydraD, hydraX      [propext, Quot.sound]
    extract, fibRealizer                        (no axioms)
    soundness                                   [propext, Classical.choice, Quot.sound]

| part | state |
|---|---|
| System T + primitives (`add`,`prec`,`tiRec`,`pred`,`bump`,`good`,`ord`,`hcut`,`hcutAt`,`hydra`,`hord`) | ✅ |
| **Typed ordinal layer**: base type `.ord`, `Eps0` notations, `ordᵒ`/`≺ᵒ`/`tiRecᵒ`, rule `tiEps0O` (`OrdCnf.lean`) | ✅ no coding in any computation |
| **Typed hydra layer**: base type `.hyd`, trees as values, `cutᴴ`/`deadᴴ?`/`hordᴴ` (measure lands in `.ord`), rule `hordCutLtH` (`HydraTyped.lean`) | ✅ battle at the published length 37, where the coded extract overflows |
| Formulas indexed by realizer type; equality+conversion at every type | ✅ |
| `MR`, **45 rules**, extraction (axiom-free), soundness (all cases) | ✅ |
| Continuity (`Tracked`, `extract_continuous2`) | ✅ choice-free |
| `tiEps0` + `tiRec` | ✅ used by Goodstein and Hydra |
| Case studies: Fib, Fib-type-2, Pascal, Hanoi, gcd (full spec), Goodstein, Hydra, **Sperner**, **Hercules (∀-strategy)**, **Hercules (any head)**, **Goodstein on typed ordinals**, **Kirby–Paris on trees**, **Hercules on trees** | ✅ all extracted and running |
| Proof engineering: `deriv_norm`, `deriv_assumption`, term-form kit | ✅ |
| **Certified emission**: target syntax + big-step semantics, `hsOf_correct` (logical relation across the type erasure); the shipped emitter is *defined* as `hsPrint ∘ hsOf` (`HsSemantics.lean`) | ✅ 6 of 13 programs (all that avoid `TI(ε₀)`) |

### What is next

Of the five items on the original research track, three are done: the
fully general any-head Hercules, the typed ordinal and hydra value layers
(the de-coding programme, now **finished** — the coded
`Goodstein`/`Hydra`/`Hercules` modules are kept only as the baselines their
typed twins are measured against), and certified semantics for the emitted
Haskell.  Two remain:

* **automatic associates / moduli for extracted type-2 programs** —
  *partially done*.  `Modulus.lean` supplies `HasMod` (the continuity
  existential with its witness given) and an algebra for building the bound
  compositionally; the type-2 Fibonacci modulus is now *derived* rather than
  written by hand, and comes out strictly tighter than the hand-written one
  (`f 0 + 1` against `max (f 0) (f (f 0)) + 1`).  `no_constant_modulus`
  additionally proves the bound cannot be a number.  What remains is the
  **metatheorem**: extraction is not yet proved to yield a modulus for every
  derivation, and the file records why that is research rather than an
  oversight — at arrow types a single number does not suffice (one needs a
  modulus whose *type* is computed from the finite type, i.e. an associate,
  which the continuity proof was designed to avoid), and `tiRec` has no
  compositional modulus because a notation can have infinitely many
  `≺`-predecessors.
* **upstreaming the deriv-authoring kit into reusable tactics.**
  `deriv_norm` and `deriv_assumption` live in `GcdDvd.lean`; the term-form
  kit and the explicit-chain discipline are conventions, not tooling.

One further item emerged during the work and is not on the original list:
**extending certified emission to `tiRec`**, which would make the chain
derivation → extract → target term → running code complete for the
$\mathrm{TI}(\varepsilon_0)$ theorems as well.  It needs the *target* to
have a transfinite recursor; the prelude currently emits `error`, which
`hsOf` models faithfully as a stuck term.

## What this branch will *not* deliver

* **Not "the same results, better."** Strictly more in three places (above),
  and one at risk (part 5).
* **A weaker audit story.** The original's appeal is partly that the fragment
  is *small*: 76 enumerable rules, seven per-rule sites, a short
  imported-schema ledger. HA^ω is a bigger system and that story gets harder
  to tell as crisply — even though the ledger itself gets shorter.
* **Not a port.** Parts 1–4 are new Lean, not translated Lean.

## Building

```bash
lake build              # both libraries
lake build HAomega.Syntax
```

The `.lake` build cache came across from the original by APFS copy-on-write,
so builds are warm from the first invocation.
