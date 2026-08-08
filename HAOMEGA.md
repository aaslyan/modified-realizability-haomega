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
  It imports nothing from `Realizability`.

## Why

Three documented compromises in the original all trace to a single cause —
the object language has one sort, `ℕ`, so everything else is *coded* into a
number:

| compromise | where it is recorded | what HA^ω does to it |
|---|---|---|
| `hercules_wins` proved in the metatheory, because a strategy is a function and the fragment has no function variables | `HydraGeneral.lean` (H7), README scope note | dissolves — quantify over strategies directly |
| `look` added as a symbol, the one place "no new symbols" was forced | `Coloring.lean` (S1), STATUS | dissolves — a coloring *is* a function |
| `bump`/`prec`/`hcut`/`xor`/`look` enter by **numeral graph** rather than open-term schemas | CLAUDE.md "documented compromise" | dissolves — course-of-values recursion is definable in System T |

And two costs measured during the emitter work (Phase X of the original):

* **Ambient levels** — `PureType` tower, `liftR`/`dropR`, `lvl`, `derivBound`.
  Pure bookkeeping for the proofs; computes nothing. `derivBound gcdTheorem =
  41` is why `gcdWitness` evaluates at no input at all. HA^ω has none of it,
  because a realizer's type is computed from its formula.
* **Data encoding** — the triangular pairing. Deleting the ambient tower did
  not move Hanoi's wall at all (`n = 4` before and after), which is what
  proved the encoding is a *separate* cost. HA^ω removes it at the root.

## Status

**724 jobs green**, zero `sorry`, 1639 lines of new Lean. **The machinery is
complete**: modified realizability, extraction, soundness, and continuity.

| part | file | state |
|---|---|---|
| 1. Finite types + System T | `Syntax.lean` | ✅ `Tm.eval` axiom-free |
| 2. Formulas, indexed by realizer type | `Formulas.lean` | ✅ equality at type 0, `eqAt` + `interp_eqAt` |
| 3. `MR` + 28 rules | `Realizability.lean` | ✅ `MR_subst`/`MR_subst1` cast-free |
| 4. `extract` | `Extraction.lean` | ✅ zero casts, **axiom-free** |
| 5. **`soundness`** | `Soundness.lean` | ✅ **28/28 cases** |
| 6. **continuity** | `Continuity.lean` | ✅ **`[propext]` — choice-free** |
| demo | `Fib.lean` | ✅ extracts, prints, `fib 1000` runs |

### The headline theorems

```lean
soundness  : (D : Deriv Δ φ) → Realizes Δ e ε → MR φ e ((extract D).eval ε)
extract_tracked     : (D : Deriv Ctx.nil φ) → Tracked a (fun _ ↦ (extract D).eval Env.nil)
extract_continuous2 : (D : Deriv Ctx.nil φ) → Continuous2 ((extract D).eval Env.nil)
```

### How the continuity bridge was solved

The obstruction was that `Ct` is indexed by *pure-type level* (`ℕ`, `ℕ→ℕ`,
`(ℕ→ℕ)→ℕ`, …) with no products and no general arrows, while HA^ω realizers live
at arbitrary `Ty`. Indexing `Ct` by `Ty` would have meant generalising `Assoc`
upstream.

It was avoided entirely, using the device the first-order development already
relies on: an **oracle-parameterized logical relation**, `Tracked τ X`, whose
base case is the vendored `Continuous2` and whose finite-type structure is
carried by the relation rather than by `Ct`'s index. No associate is ever
constructed, so the pure tower's shape never has to be matched. Products and
general arrows get their own clauses.

Two consequences worth recording:

* **The induction is small.** The first-order `GenericContinuity.lean` is 1304
  lines because it needs a preservation lemma per extraction combinator (~40).
  Here the realizer is a System T *term*, so the induction runs over the **11
  constructors of `Tm`**, and `extract_continuous2` is a corollary of
  `eval_tracked`. `Continuity.lean` is 195 lines.
* **It is choice-free** — `[propext]`, tighter than the first-order
  development's `[propext, Quot.sound]`. Getting there required using
  `Nat.le_max_left` / `Nat.lt_of_lt_of_le` rather than the order-class lemmas,
  which drag in `Classical.choice`.

### Two constraints on "just feed proofs to the machinery"

1. **Statements can go trivial.** `∀n ∃y. y = fib n` is a one-line proof once
   `fib` is a definable term, and its extract is just the witness handed to
   `exI`. Specifications must be written so the algorithm is not already
   supplied.
2. **Goodstein's realizer cannot be a System T term.** System T defines exactly
   the provably-total functions of PA; Goodstein's stopping time is not one of
   them (Kirby–Paris — literature, not formalized here). So `tiEps0` needs a
   matching *term former*, a recursor along `≺`, added to `Tm`. Proof rule and
   program construct come in a matched pair.

### What is next

The machinery is done, so the remaining work is extensions, not foundations:
`tiEps0` + its recursor (for Goodstein/Hydra), and non-trivial specifications
whose extracted algorithm the proof actually synthesises.

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
