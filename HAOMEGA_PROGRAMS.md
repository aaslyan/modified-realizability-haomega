# Extracted programs — the HA^ω branch

The counterpart of `EXTRACTED_PROGRAMS.md`, which indexes the **first-order**
development's seven programs. This file indexes this branch's, and says plainly
what is not here yet.

**Read this first: the machinery is complete, the case studies are not.**
Extraction, soundness and continuity all hold for every derivation. What exists
as an actual extracted program is **six** things — and Pascal is the first
whose algorithm the proof computes rather than receives. Sperner,
Goodstein and Hydra are *not* ported; gcd is stage 1 of 2 — nothing blocks them, but nobody has
written the derivations.

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

**Not claimed (stage 2):** the full specification — common divisor +
maximality by strong induction on `a+b` — is real ported work, not blocked but
not done. `gcdSpec` names the algorithm, so this extract is the solver
(Fibonacci-style, not Pascal-style).

---

## What is **not** here

| program | first-order repo | this branch | what it needs |
|---|---|---|---|
| Fibonacci | ✅ | ✅ | — |
| Fibonacci, higher type | ✗ (unstatable) | ✅ | — |
| **Pascal mod 2** | ✅ `pasDecide` | ✅ `pasTag`/`pasDecide` | — |
| **Tower of Hanoi** | ✅ `hanoiSolution` (wall at `n=5`) | ✅ `hanoiExtracted` (`n=10` guarded) | — |
| **gcd** | ✅ certified, **never ran** | ✅ **COMPLETE**: stage 1 runs; stage 2 all 7 layers — `gcdTheoremD : ∀a∀b. ∃g. g∣a ∧ g∣b ∧ ∀d.(d∣a→d∣b→d∣g)` proved by the fueled induction, `gcdFull` = the proof-computed gcd (`GcdTheorem.lean`) | — |
| **Sperner 1D** | ✅ | ⬜ | A coloring is a **function** here, so the `look` symbol is not needed at all — the one place the first-order "no new symbols" discipline was forced. |
| **Goodstein** | ✅ `goodsteinStopTime` | ⬜ | `tiEps0` and its recursor now **exist** (rule 29, `Tm.tiRec`). What is still missing is the ordinal-assignment layer: `ordOf`, `nfB_ordOf`, `ordOf_bumpN`, `ordOf_descent`. That is mathematics, not machinery. |
| **Hydra** | ✅ `hydraBattleLength` | ⬜ | As Goodstein, plus hydras as an inductive type instead of codes. The general Kirby–Paris theorem (`hercules_wins`) becomes **statable inside** the object theory, since strategies are functions. |

## Honest summary

- **Machinery: complete.** 29 rules, `extract` (axiom-free), `soundness` (28/28
  cases + `tiEps0`), continuity (`[propext, Quot.sound]`, choice-free).
- **Case studies: 5 of 7 ported** (gcd at stage 1) (plus the higher-type Fibonacci, unstatable first-order).
- **Pascal is the one whose algorithm the proof computes** — the decision tag
  comes from `eqDec` through two inductions, not from a witness handed to
  `exI`. The two Fibonacci programs remain witness-style.
