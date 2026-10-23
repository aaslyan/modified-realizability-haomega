# Extracted programs — the HA^ω branch

The counterpart of `docs/first-order/EXTRACTED_PROGRAMS.md`, which indexes the **first-order**
development's seven programs. This file indexes this branch's, and says plainly
what is and is not claimed.

**Read this first: machinery and case studies are both complete.**
Extraction, soundness and continuity hold for every derivation, and **twenty-six
extracted programs run**: thirteen discrete programs (the first-order repo's
seven, plus three theorems that repo cannot state — `herculesD`,
`herculesAnyD`, and the higher-type Fibonacci — plus `goodsteinOD`, `hydraHD`
and `herculesTD`: Goodstein, Kirby–Paris and the fully general Hercules game
re-proved over the typed ordinal and hydra layers, with nothing encoded
anywhere) and thirteen analysis & formal-power-series jet programs (including
the discrete-IVT square-root search, uniform continuity, the three $E_1$ jet
moduli, Order-1 Picard jet solvers, and Newton–Schulz jet inversion). The
three-view rendering of every realizer (raw object / collapsed program /
Haskell) is `EXTRACTED_HAOMEGA.md`, regenerated at each build; the detailed
sections below cover the first six, and the coverage table covers all
twenty-six with an explicit **proof-computed** vs. **witness-style** split.

## The uniform core

```lean
extract      : Deriv Δ φ → Tm (as ++ Γ) a      -- a term of the object language
soundness    : Realizes Δ e ε → MR φ e ((extract D).eval ε)
extract_tracked     : Tracked a (fun _ ↦ (extract D).eval Env.nil)
extract_continuous2 : Continuous2 ((extract D).eval Env.nil)
```

The realizer is a **System T term**, not an opaque closure, so it prints, runs
and normalises. `Tm.pretty` shows it raw; `Tm.pretty'` elides the contentless
(`unit`-typed) parts left by equational subproofs.

**The Haskell renderings are no longer wholly uncertified.**
`HsSemantics.lean` gives the target a syntax and a big-step semantics, proves
`hsOf_correct` — the translation preserves meaning across the type erasure,
via a logical relation — and the shipped emitter is now *defined* as
`hsPrint ∘ hsOf`, so the strings come from the AST the theorem is about.
Outside the theorem: the printer, GHC's parse of it, the hand-written prelude,
and the 7 programs that use `TI(ε₀)` (for which the emitter has never produced
running code).

---

## 1. Fibonacci — `HAomega/Fib.lean`

Theorem `∀n^ℕ. ∃y^ℕ. y = fib n`. Realizer type `(N→(N×1))`.

**Extracted program**, contentless parts elided:

```
(λx0. ((λx1. fst ((λx2. rec[⟨0, S 0⟩ |
     (λx3. (λx4. ((λx5. ⟨snd x5, (fst x5 + snd x5)⟩) x4))) | x2]) x1)) x0))
```

Raw, it ends `…, ★⟩)` — the `★` is the erased equational certificate, which is
visible *in the type* as the `1` (`unit`) component.

**Runs:** `fibExtracted 0…15` = `0,1,1,2,3,5,8,13,21,34,55,89,144,233,377,610`;
`fibExtracted 100 = 354224848179261915075`; `fibExtracted 1000` is the 209-digit
value (checked mod 1e9+7). `#print axioms fibRealizer` — **no axioms**.

**Where the algorithm came from.** The proof is `allI (exI (fib n) (eqRefl))`:
the statement `∃y. y = fib n` is answered with the term `fib n`, so the
extracted program contains `fibT` because the proof was handed it.  Fully
constructive, fully extracted — the remark is only that the *statement*
already named the algorithm.  Contrast Pascal (§4), whose statement names no
algorithm and whose extract was assembled by extraction from the proof's case
analyses.

**`fib` is a term, not a symbol.** The first-order development needs `fib` as a
signature symbol with three axiom schemas (`fibZero`/`fibOne`/`fibSucc`) added
through ~16 sites. Here it is `fibT`, a paired System T recursion — no new
syntax, no new axioms.

---

## 2. Fibonacci at higher type — `HAomega/HigherType.lean`

Theorem `∀f^(ℕ→ℕ). ∃y^ℕ. y = fib (f (f 0))`. Realizer type `((N→N)→(N×1))`.

**This one the first-order fragment cannot even state** — it has no function
variables. It is also the only place continuity has anything to say.

**Extracted program:**

```
(λx0. ((λx1. fst ((λx2. rec[⟨0, S 0⟩ |
     (λx3. (λx4. ((λx5. ⟨snd x5, (fst x5 + snd x5)⟩) x4))) | x2]) x1))
   (x0 (x0 0))))
```

`x0` is the function argument `f`; `x0 (x0 0)` is `f (f 0)`, feeding the
Fibonacci pair-iteration.

**Runs on function arguments:** `hiProgram (·+5) = 55`,
`hiProgram (fun _ ↦ 30) = 832040`, `hiProgram (2·+7) = 10946`.
`#print axioms hiRealizer` — **no axioms**.

**It is a continuous type-2 functional:**

```lean
theorem hiProgram_continuous : Continuous2 hiProgram      -- [propext]
```

---

## 3. What continuity actually excludes — `HAomega/Collapse.lean`

Not an extracted program, but the evidence that the continuity theorem is not
vacuous.

```lean
noncomputable def notAllZero (α : ℕ → ℕ) : ℕ := if ∀ n, α n = 0 then 0 else 1

theorem not_continuous2_notAllZero : ¬ Continuous2 notAllZero
theorem notAllZero_not_extractable (D : Deriv Ctx.nil φ) :
    (extract D).eval Env.nil ≠ notAllZero
```

A perfectly good inhabitant of `PureType 2` that **no derivation can extract
to**. And the collapse in the other direction:

```lean
theorem hiProgram_mem_ct2       : hiProgram ∈ Ct 2
theorem hiProgram_has_associate : ∃ a : ℕ → ℕ, Assoc 1 a hiProgram
def     hiModulus (f : Nat → Nat) : Nat := max (f 0) (f (f 0)) + 1
theorem hiProgram_modulus : (∀ i < hiModulus f, f i = g i) → hiProgram f = hiProgram g
```

The type-2 functional is represented by a **type-1** function (its associate),
and for this program the finite information needed is explicit and computable.

---

## 4. Pascal mod 2 — `HAomega/Pascal.lean`, `HAomega/PascalTheorem.lean`

Theorem **`pasTotal : ∀n ∀k. pas n k = 1 ∨ pas n k = 0`** — `[propext, Quot.sound]`.

**The first proof-computed extract in this branch.** The disjunction's tag is
decided by `eqDec` inside `flipTotal`/`parityTotal` and threaded through two
inductions (outer on the row, inner on the column with its hypothesis
discarded — the case-split device). Nothing is handed to an introduction rule.

```lean
def pasTag (n k : Nat) : Nat :=
  (((extractClosed pasTotal).eval Env.nil) n k).1
def pasDecide (n k : Nat) : Nat := if pasTag n k = 0 then 1 else 0
```

**Build-time guard:** the gasket drawn by `pasDecide` equals the gasket drawn
by the value-level `pas`, rows 0–7. Soundness certifies the agreement at every
input; the guard checks the corner the build can run.

`pasT` itself recurses **on the row at type `ℕ → ℕ`** — the recursor at a
function type, which is exactly what forced the first-order version to
axiomatize `pas`/`xor` as symbols. Here they are definitions.

Two machinery consequences, recorded in the file headers:
* the **conversion-at-every-type revision** (`Formula.eq` at arbitrary `τ`) —
  row-level equations (`rowZero`, `rowSucc`) are unstatable with equality at
  type 0 only;
* the **explicit-chain discipline** — conversion chains written with holes
  make the elaborator symbolically execute `Tm.subst` (20+ minutes per
  declaration); with every intermediate named and every reduction its own
  `rfl`/`simp only` lemma, the same chains elaborate in milliseconds at
  default heartbeats.

---

## 5. Tower of Hanoi — `HAomega/Hanoi.lean`

**The encoding-wall experiment, concluded.** The first-order version codes a
move sequence into a single ℕ and dies at `n = 5`; deleting the ambient tower
did not move that wall, proving the encoding was the cost. Here a sequence is
**`(len, moves)` with `moves : ℕ → ℕ`** — data as a function — and the build
runs `n = 10` (1023 moves, checked move-for-move against a plain-Lean
reference). No encoding, no wall; only the answer's own size limits it.

Two higher-type devices, neither available first-order:

* `hanoiT` recurses at type `ℕ → ℕ → ℕ → (ℕ × (ℕ→ℕ))` — **the carrier is a
  function of the pegs**, so the classic peg-permuting recursion is
  structural. First-order Hanoi needed an axiomatized `solves` relation
  precisely because its recursion cannot permute arguments.
* `appT` appends sequences by offset-shifted function merge.

Theorem `hanoiSpec`: `∀n ∃len ∃moves^(ℕ→ℕ). …` — the second existential
ranges over a **function**, and the extracted witness read off it *is* a
function (`hanoiExtracted 8` = 255 moves, guarded against the reference).
Equality at the arrow type is the every-type `Formula.eq`.

**Honest scope:** as with Fibonacci, the statement names the solver, so the
extract *is* the solver (constructive, extracted, runnable — just not
proof-invented).  The `Solves`-checker theorem (an induction proving the
produced sequence valid, which extraction would turn into its own object) is
future work and not claimed. `hanoiT` and `hanoiDeriv` depend on **no axioms**.

---

## 6. gcd — `HAomega/Gcd.lean` (stage 1)

**The headline is the contrast.** The first-order `gcdWitness` is that
repository's deepest extract (`derivBound = 41`), certified at every input and
**evaluable at none**. Here:

```lean
def gcdProgram (a b : Nat) : Nat :=
  (((extractClosed gcdSpecDeriv).eval Env.nil) a b).1
```

runs — `#guard`ed against `Nat.gcd` on all 400 pairs below 20 plus
`gcd 1071 462 = 21`. No ambient tower, no wall.

Contents: `mulT` (multiplication, *definable* — first-order needed `×`
primitive); `gcdT` (subtractive Euclid **fueled by `a+b`** on a state pair,
agrees with `Nat.gcd` on all 900 pairs below 30); the divisibility former
`Dvd d a := ∃q. a = d·q`; and the first **proof-computed** divisibility facts
`dvdZeroDeriv` (`∀d. d∣0`) and `dvdReflDeriv` (`∀d. d∣d`, whose certificate is
the five-link `mulOne` conversion chain). `gcdSpecDeriv` depends on **no
axioms**.

**Stage 2 (complete):** the full specification — common divisor + maximality
— is `gcdTheoremD` (`GcdTheorem.lean`), proved by fueled induction with slack
(`(a+b)+c = m`, plain `ind`, no strong-induction scaffold); `gcdFull` is the
proof-computed gcd read off it. Stage 1's `gcdSpec` names the algorithm, so
*that* extract is the solver (Fibonacci-style); stage 2's maximality realizer
is assembled by the induction (Pascal-style).

---

## Coverage against the first-order repo

| program | first-order repo | this branch | what it needs |
|---|---|---|---|
| Fibonacci | ✅ | ✅ | — |
| Fibonacci, higher type | ✗ (unstatable) | ✅ | — |
| **Pascal mod 2** | ✅ `pasDecide` | ✅ `pasTag`/`pasDecide` | — |
| **Tower of Hanoi** | ✅ `hanoiSolution` (wall at `n=5`) | ✅ `hanoiExtracted` (`n=10` guarded) | — |
| **gcd** | ✅ certified, **never ran** | ✅ **COMPLETE**: stage 1 runs; stage 2 all 7 layers — `gcdTheoremD : ∀a∀b. ∃g. g∣a ∧ g∣b ∧ ∀d.(d∣a→d∣b→d∣g)` proved by the fueled induction, `gcdFull` = the proof-computed gcd (`GcdTheorem.lean`) | — |
| **Sperner 1D** | ✅ (via the `look` symbol) | ✅ **`spernerD`** — colorings are function variables, no symbol, no coding; extracted `spernerX` returns a certified crossing (`Sperner.lean` — this proof extracts the *last* crossing where first-order S1 extracts the first: same theorem, different proof, different program) | — |
| **Goodstein** | ✅ `goodsteinStopTime` (walls at `m=2`) | ✅ **`goodsteinD` by `tiEps0`**; extracted `goodsteinX` returns the published stop times `[0,1,3,5]` and runs to `m=3` (`Goodstein.lean`) | — |
| **Hydra** | ✅ `hydraBattleLength` (walls at code 1) | ✅ **`hydraD` by `tiEps0`** — Goodstein's mirror with a shorter descent; extracted `hydraX` returns the published battle lengths `[0,1,3]` and its witness is verified to end each battle (`Hydra.lean`) | — |
| **Hercules (strategy-quantified)** | ✗ (unstatable — a strategy is a function) | ✅ **`herculesD`**: `∀h ∀f^(ℕ→ℕ). ∃t. play(f,h,t) = 0`, quantified over every replication strategy; extracted `herculesX` agrees with `hydraX` at the fragment's own strategy (`Hercules.lean`) | — |
| **Hercules any-head, typed trees** | ✗ (unstatable) | ✅ **`herculesTD`**: `∀h^hyd ∀f ∀g. ∃t. deadᴴ?(playAt(g,f,h,t)) = 0` — the fully general game with tree states and notation measures. Cost at the value level: **nothing** (`playAt` and its descent were already tree-level); one term former, one schema (`HerculesTree.lean`) | — |
| **Kirby–Paris, typed trees** | ✗ (one sort — trees must be coded) | ✅ **`hydraHD`**: `∀h^hyd ∃t. deadᴴ?(play(h,t)) = 0`, state a tree and measure an `Eps0`. The extract has **zero** coded operations and computes the published length **37** at the hydra where the coded `hydraX` overflows the interpreter (`HydraTyped.lean`, `HydraTree.lean`) | — |
| **Goodstein, typed ordinals** | ✗ (one sort — ordinals must be coded) | ✅ **`goodsteinOD`**: the same `∀m ∃t. good(m,t) = 0`, proved by `tiEps0O` on the structural notations of `OrdCnf.lean`; the extract contains **no coded ordinal** (`ordᵒ`/`tiRecᵒ` only) and returns the same stopping times, build-guarded against `goodsteinX` | — |
| **Hercules, any head (fully general)** | ✗ (unstatable) | ✅ **`herculesAnyD`**: `∀h ∀f ∀g. ∃t. playAt(g,f,h,t) = 0` — head choice *and* replication quantified, on the computable surgery `hcutAt` whose descent is H7's `play_descends` on codes (`HydraSurgery.lean`, `HerculesAny.lean`); extracted `herculesAnyX` agrees with `herculesX` at the leftmost strategy | — |
| **Square-root approximation** | ✗ | ✅ **`sqrtApproxD`** (`SquareRoot.lean`, proof-computed): discrete IVT applied to `x² ≤ q`; bound `K` discharged in `QAnalysis.lean` | — |
| **Uniform continuity** | ✗ | ✅ **`uniContD`** (`UniformContinuity.lean`, proof-computed): extracts modulus `M(n) = n + j` via `convQLipScale` | — |
| **Formal antiderivative & termwise FTC1** | ✗ | ✅ **`ftcAntiderivD`** (`ClosedCalculus.lean`, witness-style antiderivative + proof-computed cancellation `D(I c)(n) - c(n) = 0`) | — |
| **Cauchy product convolution** | ✗ | ✅ **`jetMulD`** (`MajorantDom.lean`, witness-style): `extractedJetMul` on `JetTy = nat → rat` | — |
| **Taylor polynomial evaluator** | ✗ | ✅ **`jetEvalPolyD`** (`MajorantDom.lean`, witness-style): `extractedJetEvalPoly` on `JetTy` | — |
| **Jet $E_1$ Cauchy convergence modulus** | ✗ | ✅ **`jetCauchyModulusGenuineD`** (`JetCauchyDeriv.lean`, proof-computed): proves geometric tail bound by `Deriv.ind` on $d_2$ from $N$-free per-term `jetTermPremise`, extracting $N(k) = k + (B + 3)$; discharged for `AnalyticJet` and `RadiusJet` | — |
| **Jet $E_1$ uniform continuity modulus** | ✗ | ✅ **`jetContModulusD`** (`MajorantDom.lean`, proof-computed): extracts $\omega(k) = k + (B_1 + 1)$ via `convQLipScale`; discharged for `AnalyticJet` and `RadiusJet` | — |
| **Jet $E_1$ uniform differentiability modulus** | ✗ | ✅ **`jetDiffModulusD`** (`MajorantDom.lean`, proof-computed): extracts $\delta(k) = k + (B_2 + 1)$ via `convQLipScale`; discharged for `AnalyticJet` and `RadiusJet` | — |
| **Order-1 Picard jet iteration ($y' = y$)** | ✗ | ✅ **`picardJetIterD`** (`HolonomicCS.lean`, proof-computed): `Deriv.ind` at arrow type `JetTy` | — |
| **Riccati ODE ($y' = 1 + y^2$) Picard solver** | ✗ | ✅ **`riccatiPicardD`** (`ClosedFourierODE.lean`, proof-computed): `Deriv.ind` with diagonal degree locking $\mathcal{P}(Y_k)(k) = Y_k(k)$, synthesizing $\tan x$ | — |
| **Quadratic blow-up ODE ($y' = y^2$) Picard solver** | ✗ | ✅ **`quadBlowupPicardD`** (`ClosedFourierODE.lean`, proof-computed): `Deriv.ind` with diagonal degree locking, synthesizing $\frac{1}{1-x}$ | — |
| **2D coupled Duffing Picard solver** | ✗ | ✅ **`duffingPicardD`** (`ClosedFourierODE.lean`, proof-computed): `Deriv.ind` with 2D diagonal degree locking on `JetTy × JetTy` | — |
| **Quadratic Newton–Schulz jet inverter** | ✗ | ✅ **`newtonJetInvD`** (`ClosedFourierODE.lean`, witness-style): `extractedNewtonJetInv`, linked to `RadiusJet.invOneSub` by `extractedNewtonJetInv_agree` | — |

## Honest summary

- **Machinery: complete.** 57 rules, `extract` (axiom-free, cast-free),
  `soundness` (one case per rule), continuity (`[propext, Quot.sound]`,
  choice-free), certified emission (`HsSemantics.hsOf_correct`) covering all
  26 extracted programs.
- **Case studies: twenty-six extracted programs** — 13 discrete programs and
  13 analysis & formal-power-series jet programs, rendered in three views in
  `EXTRACTED_HAOMEGA.md`.
- **The typed ordinal layer** (`OrdCnf.lean`) gives ε₀-notations their own
  base type: structural comparison and normal form, well-foundedness
  *inherited* from the certified coded order through `toCode`. Measured
  contrast at `n = 1000`: the code is a **1,412-digit** integer, the tree is
  **67 nodes**. No reproducible *speed* difference in the two extracted
  Goodstein programs — what the layer removes is the encoding, not cycles.
- **The typed hydra layer** (`HydraTyped.lean`) does the same for trees, and
  there the encoding *was* the bottleneck: `hydraHX` runs the published
  37-step Kirby–Paris battle at a hydra where the coded `hydraX` overflows
  the interpreter without taking a step.
- **Proof-computed vs. witness-style across all 26 programs.**
  - *Proof-computed (19):* Pascal's decision tag (`pasRealizer`), gcd's stage-2
    maximality realizer (`gcdTheoremD`), the six transfinite-induction
    termination realizers (`goodsteinD`, `hydraD`, `herculesD`, `herculesAnyD`,
    `goodsteinOD`, `hydraHD`, `herculesTD`), Sperner's last-crossing scan
    (`spernerD`) and square-root search (`sqrtApproxD`), the uniform-continuity
    modulus (`uniContD`), the three jet $E_1$ moduli (`jetCauchyModulusGenuineD`
    by `Deriv.ind` on $d_2$ over the $N$-free per-term majorant `jetTermPremise`,
    and `jetContModulusD`/`jetDiffModulusD` via `convQLipScale`), and the four
    Order-1 Picard jet solvers (`picardJetIterD`, `riccatiPicardD`,
    `quadBlowupPicardD`, `duffingPicardD`, with diagonal degree locking proved
    by `Deriv.ind`).
  - *Witness-style (7):* the two Fibonacci programs (`fibRealizer`,
    `hiRealizer`), Tower of Hanoi (`hanoiDeriv`), formal antiderivative
    (`ftcAntiderivD`, whose antiderivative witness `tmJetInteg c` is handed to
    `exI` while termwise cancellation $\mathcal{D}(\mathcal{I}c)(n) - c(n) = 0$
    is derived via `convQMulDivSubZero`), Cauchy product convolution (`jetMulD`),
    Taylor polynomial evaluation (`jetEvalPolyD`), and the Newton–Schulz jet
    inverter (`newtonJetInvD`).
