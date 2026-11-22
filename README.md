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
3. **[`EXTRACTED_HAOMEGA.md`](EXTRACTED_HAOMEGA.md)** — the demos. All thirty-seven
   realizers, each rendered three ways: raw object, collapsed program, Haskell.
   Regenerated at every build, so it cannot drift.
4. **[`READERS_GUIDE.md`](READERS_GUIDE.md)** — the declaration-by-declaration
   map, if you want to read the Lean.
5. **[`docs/haomega/STATUS.md`](docs/haomega/STATUS.md)** — the ledger: what is
   proved, what is only *stated*, and what is blocked on what.

## Fifteen of the extracted programs

The catalog in [`EXTRACTED_HAOMEGA.md`](EXTRACTED_HAOMEGA.md) holds
thirty-seven programs. The table below shows the thirteen discrete ones and
the first two from analysis; the rest are covered in the analysis strand
below. Each is derived in the object theory, extracted, certified, and
**run** at every build.

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

## The analysis strand

The last two rows above are where the analysis strand begins. It has since
grown into the larger part of `HAomega/`. The question it answers: once realizers
take rationals and functions as inputs, how much of calculus still extracts to
running programs, and what data does each step need?
[`EXTRACTED_ANALYSIS.md`](EXTRACTED_ANALYSIS.md) shows the analysis programs,
and [`docs/haomega/STATUS.md`](docs/haomega/STATUS.md) §3–§8 is the ledger.

**Numeric base.** `rat` and `dyad` are hand-rolled base types. Mathlib's
`Rat` arithmetic depends on `Classical.choice` (measured, not assumed), and
using it would put choice inside every running extract.

**Moduli as programs.**
- **Uniform continuity:** the extracted realizer *is* the modulus (`n + j`).
- **Jet moduli:** the Cauchy, continuity and differentiability moduli have
  proof-computed versions (`JetCauchyComputed.lean`, `JetModuliComputed.lean`).
  The extracted modulus is a `rec` assembled by `Deriv.ind`.
- **Square roots:** these are the discrete IVT, i.e. Sperner 1D applied to
  squaring.

**One derivation, every polynomial ODE.** `genSolveND`
(`PolyODESystemN.lean`) proves, by `Deriv.ind`, that every well-formed
polynomial–integral system `Y_v = A_v + ∫F_v(Y)` has a solution below every
degree `k`. Its specification names no algorithm. Its extract is provably the
Picard iteration (`extractClosed_genSolveND_fst`), and uniqueness
(`genSolveN_unique_val`) makes those coefficients *the* Taylor coefficients.
`exp`, `y' = y²`, Riccati/`tan`, Duffing, sine/cosine and Fourier modes are
instances. The extract is `[propext, Quot.sound]`.

**The universe.** `InGPAC` is the class of components of such systems with
constant data. It is proved closed under the following (`UniverseGPAC.lean`,
`UniverseInv.lean`, `UniverseComp.lean`, `UniverseInvFun.lean`,
`UniverseImpFun.lean`):
- `+`, `−`, `×`, `∫` and `d/dx`;
- reciprocals (when `f(0) ≠ 0`);
- composition;
- **local inverse functions** (`InGPAC_invFun`);
- **implicit functions** (`InGPAC_impFun`).

The expression language `UExpr` compiles into it (`UExpr.compile_correct`).
Every member gets a syntax-computed geometric coefficient bound
(`solN_geom_bound`, `sysParams`) and a certified evaluator: past a
proof-computed truncation degree, partial sums are within `2⁻ᵏ` on an explicit
disk (`UExpr.approx_spec`, `GPACSys.approxFast_spec`).

**Operators built on the evaluator.** Each is certified, and each is run by
`#guard` against floating point:

| operator | theorem | example |
|---|---|---|
| root finding by extracted bisection | `UExpr.root_spec` | `ln(41/40)`, `arcsin(1/5)` to `10⁻¹⁰` |
| definite integral / Newton–Leibniz | `defIntegral_spec` | `∫₀^{1/2} cos = sin(1/2)` |
| critical points (approximate Rolle) | `critical_spec` | minimum of `eˣ − 1 − (21/20)x` |
| Newton, Kantorovich-type | `UExpr.newton_spec` | `ln(41/40)` to `10⁻²⁸` in four steps |
| shooting for two-point BVPs | `shootBVP_certified` | harmonic and Duffing BVPs to `10⁻¹⁰` |
| re-centering / analytic continuation | `recenter_overlap`, `stepIter_cauchy` | `tan` stepped twice agrees to `10⁻²⁵` |

**Newton–Leibniz, and where it stops.** Both directions of the effective
fundamental theorem of calculus are proved for every representation in their
class (`eftc2_thm`, `eftc1` in `QAnalysis.lean`). The boundary sections record
what each operation *needs as data*:
- **Inversion:** a modulus of strict monotonicity, i.e. a rational lower bound
  on `f′`.
- **Limits:** a modulus of uniform convergence.
- **Composition:** a range condition.

The negative halves (Myhill, Specker) are cited, not formalized: they
quantify over procedures, and this model has no computability predicate.

**Most recent layers.** These are not yet entered in the STATUS ledger:
- **Bridge to Mathlib's real analysis** (`RealCalculusBridge.lean`): series
  values on `ℝ`, `HasDerivAt`, `intervalIntegral`.
- **Extraction–evaluation adequacy** (`ComputationalAdequacy.lean`): the
  proof-extracted coefficients equal the fast evaluator's
  (`extraction_to_fast`).
- **Certified simplification** (`CertifiedOptimization.lean`): a `UExpr`
  normalizer that preserves coefficients.
- **Validated numerics** (`ValidatedNumerics.lean`): dyadic ball arithmetic
  (`approxDyadic_spec`) and 1D/ND Krawczyk operators.

**Scope.** The solver and the extracts live in the object logic and are
choice-free. The closure theorems, evaluator certificates and operator
specifications are *metatheory* about `Q.val` and carry `Classical.choice`.
Several of them are marked in STATUS as written by an outside agent and
audited. The object language still has no rule base for computing with `Q`
(STATUS §6). The certified disks are conservative, and nonlinear or
compositional evaluation is slow. STATUS records the measured costs.

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
HAomega/          the development (~61,000 lines)
Realizability/    the first-order system, kept as the reference implementation
                  Part I of the paper walks it; Part II measures against it
paper/            the paper and its figures
docs/haomega/     roadmap, status, program ledger
docs/first-order/ the first-order system's own status, dossier and evidence
docs/internal/    working notes, open questions, plans
```
