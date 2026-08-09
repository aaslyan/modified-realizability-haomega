# Modified realizability for Heyting arithmetic in all finite types

A Lean 4 formalization of Tait/Kreisel-style modified realizability over
**HA^ω**: an intrinsically-typed System T term language, formulas indexed by
their realizer type, an extraction function whose output is a **term of the
object language**, a soundness theorem, and a continuity theorem placing
every extracted type-2 realizer among the Kleene–Kreisel continuous
functionals.  The rule set includes **transfinite induction to `ε₀`**
(`tiEps0`), with its recursor `tiRec` as a matching term former.

Thirteen extracted programs come out of the object theory, each with its realizer
extracted, certified, and **run** at every build:

| | statement | notes |
|---|---|---|
| **Goodstein** | `∀m ∃t. good(m,t) = 0` | by `tiEps0`; extract returns the published stop times `[0,1,3,5]` |
| **Kirby–Paris (Hydra)** | `∀h ∃t. hydra(h,t) = 0` | by `tiEps0`; extract returns the published battle lengths `[0,1,3]` |
| **Hercules, ∀-strategy** | `∀h ∀f^(ℕ→ℕ) ∃t. play(f,h,t) = 0` | replication-strategy quantified — *unstatable* first-order |
| **Hercules, any head** | `∀h ∀f^(ℕ→ℕ) ∀g^(ℕ→ℕ) ∃t. playAt(g,f,h,t) = 0` | the fully general game: head choice *and* replication quantified |
| **gcd, full spec** | `∀a∀b ∃g. g∣a ∧ g∣b ∧ ∀d.(d∣a→d∣b→d∣g)` | fueled induction; proof-computed program |
| **Pascal mod 2** | `∀n∀k. pas(n,k)=1 ∨ pas(n,k)=0` | proof-computed decider; draws the Sierpiński gasket |
| **Sperner 1D** | `∀n ∀c^(ℕ→ℕ). c 0=0 → c n=1 → ∃k<n. c k≠c(k+1)` | colorings are function variables — no coding |
| **Tower of Hanoi** | `∀n ∃len ∃moves^(ℕ→ℕ). …` | function-valued move sequences; runs at `n = 10` |
| **Fibonacci** | `∀n ∃y. y = fib n` | the on-ramp; extract runs to `n = 1000` |
| **Fibonacci, type 2** | `∀f^(ℕ→ℕ) ∃y. y = fib(f(f 0))` | proved continuous, with associate and explicit modulus |
| **Goodstein, typed ordinals** | `∀m ∃t. good(m,t) = 0` | the same statement again, by `tiEps0O` on **structural** ε₀-notations — the extract contains no coded ordinal |
| **Kirby–Paris, typed trees** | `∀h^hyd ∃t. deadᴴ?(play(h,t)) = 0` | hydras as a base type; computes the published battle length **37** where the coded extract overflows |
| **Hercules any-head, typed trees** | `∀h^hyd ∀f ∀g ∃t. deadᴴ?(playAt(g,f,h,t)) = 0` | the fully general game with nothing encoded anywhere |

Zero `sorry`/`admit`.  `lake build` is the test suite: every correctness
claim is a theorem and every evaluation claim an embedded `#guard`.

## Why all finite types

This repository grew out of
[`modified-realizability-lean`](https://github.com/aaslyan/modified-realizability-lean),
which does the same programme over a **minimal first-order fragment** — one
sort, everything coded into ℕ.  That development is kept in-tree
(`Realizability/`) as the reference implementation; the HA^ω library
(`HAomega/`, ~8,000 lines) imports nothing from it except the proven
choice-free value layers (ε₀ notations, Goodstein and Hydra arithmetic).
What the types buy, each verified here rather than asserted:

* **statements the fragment cannot write** — quantification over strategies
  (`herculesD`) and over colorings (`spernerD`), and higher-type theorems
  where the continuity apparatus has actual content;
* **no ambient-level tower** — the first-order gcd extract was certified but
  evaluable at *no* input; here it runs;
* **capture-free binders** — the fragment's naive-substitution workarounds
  (`namedIHDeriv`, `ihRenamed`) do not exist here;
* **one Leibniz rule** replaces ~20 per-symbol congruence schemas.

## The three-view artifact

`EXTRACTED_HAOMEGA.md` (regenerated at every build) renders each realizer
three ways: the raw high-level object with its erased certificates visible,
the collapsed functional program, and generated Haskell.  Goodstein's
collapsed program is worth reading — the `ε₀` descent is visible in it.

## Where to start

* **`HAOMEGA.md`** — the roadmap and current status.
* **`HAOMEGA_DOSSIER.md`** — the evidence-tagged audit: exact axiom
  footprints, measured evaluation limits, and the honest scopes (what is
  proved, what is only statable, what is stale-and-fixed).
* **`HAOMEGA_PROGRAMS.md`** — the program ledger, case study by case study.

## Axiom footprints (audited)

    extract, fibRealizer                         no axioms
    continuity, all derivations and extracts     [propext, Quot.sound]
    soundness                                    [propext, Classical.choice, Quot.sound]

`soundness`'s choice enters through the value-layer theorem proofs (as in
the first-order development); every derivation and every running extract is
choice-free.

## Building

```bash
git clone https://github.com/aaslyan/modified-realizability-haomega
cd modified-realizability-haomega && lake build
```

Toolchain pinned in `lean-toolchain`; Mathlib pinned in `lakefile.lean`.
The build is standalone.

## Scope, stated once

Independence results are **not** formalized: Goodstein and Kirby–Paris are
proved as termination theorems; that PA cannot prove them is claimed
nowhere.  The Haskell renderings are **certified against a formal semantics
of the target** (`hsOf_correct`), for the 6 of 13 programs that avoid
`TI(ε₀)`; the hand-written prelude, the printer, and GHC itself remain the
trusted base.
