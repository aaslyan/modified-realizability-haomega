# Modified realizability over finite-type arithmetic

A Lean 4 framework in which a formal derivation is turned into a program by a
verified extraction map — and, because the same mechanism is applied to two
object languages, a setting in which the *consequences* of proving something
one way rather than another can be measured rather than argued about.

The extracted realizer is a **term of the object language**: it prints, it
runs, and a verified translation lowers it to a functional target. Extraction
is proved sound, every extracted realizer is proved continuous, and the object
theory is extended by a *matched* proof/program pair — transfinite induction
to ε₀ together with a recursor along the induced ordinal order — so theorems
beyond arithmetical induction still yield running programs.

## Three things you can vary, and what happens

This is the part that is not just an implementation. Hold the extraction
mechanism fixed and move one feature of the setup at a time:

| vary… | and the extracted program… | measured |
|---|---|---|
| **the proof** | changes strategy | two derivations of Sperner's lemma — same theorem, same invariant — return the *first* and the *last* crossing |
| **the representation** | changes what it can finish | the same derivation computes a 37-step hydra battle from trees that it cannot begin from ℕ-codes |
| **the logical strength** | changes the shape of its recursion | ordinary induction emits `rec`; TI(ε₀) emits `tiRec`, and the ordinal descent is visible in the program text |

A fourth axis is semantic: continuity is vacuous while every extract takes a
number, and acquires content exactly when a realizer first takes a *function*
as input — at which point the development also exhibits a discontinuous
functional that **no derivation can extract to**.

## Start here

1. **[`paper/how-a-proof-becomes-a-program.pdf`](paper/)** — the full account.
   Part I walks the minimal first-order system end to end; Part II rebuilds the
   machine over finite types and runs the comparisons above.
2. **[`HAOMEGA_DOSSIER.md`](HAOMEGA_DOSSIER.md)** — the evidence. Every claim
   tagged `[run]`, `[src]` or `[git]`, with exact axiom footprints, measured
   evaluation limits, and the claims this project walked back.
3. **[`EXTRACTED_HAOMEGA.md`](EXTRACTED_HAOMEGA.md)** — the demos. All fifteen
   realizers, each rendered three ways: raw object, collapsed program, Haskell.
   Regenerated at every build, so it cannot drift.
4. **[`READERS_GUIDE.md`](READERS_GUIDE.md)** — the declaration-by-declaration
   map, if you want to read the Lean.
5. **[`docs/haomega/STATUS.md`](docs/haomega/STATUS.md)** — the ledger: what is
   proved, what is only *stated*, and what is blocked on what.

## The fifteen extracted programs

Each is derived in the object theory, extracted, certified, and **run** at
every build.

| | statement | notes |
|---|---|---|
| **Goodstein** | `∀m ∃t. good(m,t) = 0` | by `tiEps0`; returns the published stop times `[0,1,3,5]` |
| **Kirby–Paris (Hydra)** | `∀h ∃t. hydra(h,t) = 0` | by `tiEps0`; returns the published battle lengths `[0,1,3]` |
| **Hercules, ∀-strategy** | `∀h ∀f^(ℕ→ℕ) ∃t. play(f,h,t) = 0` | strategy quantified — *unstatable* first-order |
| **Hercules, any head** | `∀h ∀f ∀g ∃t. playAt(g,f,h,t) = 0` | the fully general game: head choice *and* replication |
| **gcd, full spec** | `∀a∀b ∃g. g∣a ∧ g∣b ∧ ∀d.(d∣a→d∣b→d∣g)` | fueled induction; proof-computed program |
| **Pascal mod 2** | `∀n∀k. pas(n,k)=1 ∨ pas(n,k)=0` | proof-computed decider; draws the Sierpiński gasket |
| **Sperner 1D** | `∀n ∀c^(ℕ→ℕ). c 0=0 → c n=1 → ∃k<n. c k≠c(k+1)` | colorings are function variables — no coding |
| **Tower of Hanoi** | `∀n ∃len ∃moves^(ℕ→ℕ). …` | function-valued move sequences; runs at `n = 10` |
| **Fibonacci** | `∀n ∃y. y = fib n` | the on-ramp; runs to `n = 1000` |
| **Fibonacci, type 2** | `∀f^(ℕ→ℕ) ∃y. y = fib(f(f 0))` | continuous, with associate and explicit modulus |
| **Goodstein, typed ordinals** | `∀m ∃t. good(m,t) = 0` | same statement, by `tiEps0O` on **structural** notations — no coded ordinal in the extract |
| **Kirby–Paris, typed trees** | `∀h^hyd ∃t. deadᴴ?(play(h,t)) = 0` | hydras as a base type; computes **37** where the coded extract overflows |
| **Hercules, typed trees** | `∀h^hyd ∀f ∀g ∃t. deadᴴ?(playAt(g,f,h,t)) = 0` | the general game with nothing encoded anywhere |
| **Square roots** | `∀q^ℚ ∀n ∀K. col(0)=0 → col(K)=1 → ∃k<K. col(k)≠col(k+1)` | the discrete IVT applied to squaring; `√2` to `2⁻⁸` returns `181/128` |
| **Uniform continuity** | `∀f^(ℚ→ℚ) ∀j. Lip(f,j) → ∀n ∃M ∀x∀y. close(M,x,y) → close(n,f x,f y)` | the extracted realizer **is** the modulus: `n+j` |

Zero `sorry`/`admit`. `lake build` **is** the test suite: every correctness
claim is a theorem and every evaluation claim an embedded `#guard`.

## Axiom footprints (audited, reprinted at every build)

```
extract, fibRealizer                         no axioms
continuity, all derivations and extracts     [propext, Quot.sound]
soundness                                    [propext, Classical.choice, Quot.sound]
```

`soundness`'s choice enters through the value-layer theorem proofs; **every
derivation and every running extract is choice-free.**

## Scope, stated once

Independence from PA is **not** formalized — Goodstein and Kirby–Paris are
proved here as termination theorems, and that PA cannot prove them is claimed
nowhere. The typed-ordinal result is about representation **size**; no
reproducible speed difference was found, and none is claimed. The Haskell
translation is certified against a formal semantics of the target for all 13
programs; the hand-written prelude, the printer, and GHC's failure to check
that the emitted transfinite recursion terminates (it does, by the ε₀ descent
proved on the Lean side) remain the trusted base. The case-study symbols are imported primitives
evaluated by verified value layers, not System T definitions — so the object
theory is finite-type Heyting arithmetic *extended*, not the bare system.

## Building

```bash
git clone https://github.com/aaslyan/modified-realizability-haomega
cd modified-realizability-haomega && lake build
```

Toolchain pinned in `lean-toolchain`, Mathlib in `lakefile.lean`. Standalone.

## Repository map

```
HAomega/          the development (~8,000 lines)
Realizability/    the first-order system, kept as the reference implementation
                  Part I of the paper walks it; Part II measures against it
paper/            the paper and its figures
docs/haomega/     roadmap, status, program ledger
docs/first-order/ the first-order system's own status, dossier and evidence
docs/internal/    working notes, open questions, plans
```
