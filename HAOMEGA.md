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
| `hercules_wins` proved in the metatheory, because a strategy is a function and the fragment has no function variables | `HydraGeneral.lean` (H7), README scope note | **partially derived**: `Hercules.lean`'s `herculesD` states and proves `∀h ∀f^(ℕ→ℕ). ∃t. play(f,h,t) = 0` — quantified over every *replication* strategy, with the extracted battle length running. The **any-head** theorem (arbitrary head choice) is still open |
| `look` added as a symbol, the one place "no new symbols" was forced | `Coloring.lean` (S1), STATUS | dissolves — a coloring *is* a function |
| `bump`/`prec`/`hcut`/`xor`/`look` enter by **numeral graph** rather than open-term schemas | CLAUDE.md "documented compromise" | the numeral-graph *schemas* are gone; the symbols themselves were kept **primitive** (evaluated by the proven first-order value layer) rather than defined in System T — definable in principle, primitive in practice |

And two costs measured during the emitter work (Phase X of the original):

* **Ambient levels** — `PureType` tower, `liftR`/`dropR`, `lvl`, `derivBound`.
  Pure bookkeeping for the proofs; computes nothing. `derivBound gcdTheorem =
  41` is why `gcdWitness` evaluates at no input at all. HA^ω has none of it,
  because a realizer's type is computed from its formula.
* **Data encoding** — the triangular pairing. Deleting the ambient tower did
  not move Hanoi's wall at all (`n = 4` before and after), which is what
  proved the encoding is a *separate* cost. HA^ω removes it at the root.

## Status (re-verified 2026-08-09 — see `HAOMEGA_DOSSIER.md` for evidence)

**743 jobs green**, zero `sorry`/`admit`, 5,454 lines in `HAomega/` (23
files). Machinery complete and **all nine case studies done** — the
first-order repo's seven, plus two theorems that repo cannot state (the
higher-type Fibonacci and the strategy-quantified Hercules) — each with a
running extracted program; `EXTRACTED_HAOMEGA.md` renders every realizer in
three views (raw object / collapsed program / Haskell).

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
| System T + primitives (`add`,`prec`,`tiRec`,`pred`,`bump`,`good`,`ord`,`hcut`,`hydra`,`hord`) | ✅ |
| Formulas indexed by realizer type; equality+conversion at every type | ✅ |
| `MR`, **39 rules**, extraction (axiom-free), soundness (all cases) | ✅ |
| Continuity (`Tracked`, `extract_continuous2`) | ✅ choice-free |
| `tiEps0` + `tiRec` | ✅ used by Goodstein and Hydra |
| Case studies: Fib, Fib-type-2, Pascal, Hanoi, gcd (full spec), Goodstein, Hydra, **Sperner**, **Hercules (∀-strategy)** | ✅ all extracted and running |
| Proof engineering: `deriv_norm`, `deriv_assumption`, term-form kit | ✅ |

### What is next

* the **any-head** `hercules_wins` (the replication-strategy quantification
  is done — `herculesD`, `Hercules.lean`; the general head choice needs a
  tree-surgery move + descent the value layer does not provide);
* an `MR`-soundness bridge for the emitted Haskell;
* upstreaming the deriv-authoring kit into reusable tactics.

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
