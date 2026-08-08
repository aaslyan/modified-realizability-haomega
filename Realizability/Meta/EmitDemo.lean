/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Meta.EmitLean
import Realizability.Meta.EmitHaskell
import Realizability.Theorems.Goodstein.GoodsteinExtraction
import Realizability.Theorems.Hydra.HydraExtraction
import Realizability.Theorems.Hanoi.HanoiExtraction
import Realizability.Theorems.Pascal.PascalExtraction
import Realizability.Theorems.Euclid.GcdTheorem
import Realizability.Theorems.Fibonacci.FibonacciExtraction

/-!
# The level-free emitter, run on every case study

`Meta/EmitLean.lean` is the emitter; this module is its evidence.  Two kinds of
check run at every build:

* **agreement** — wherever the certified extract terminates at all, the emitted
  program returns the same answer;
* **reach** — the emitted program is then run *past* that point, at inputs the
  certified realizer cannot evaluate.

The agreement checks are what make the reach numbers worth anything.  They are
not a proof that `emit` and `extract` agree — that theorem does not exist (see
`EmitLean.lean`'s scope note) — but they are the same species of evidence as
`SpernerExtraction.lean`'s ambient-5-vs-ambient-11 check, and they are run by
the kernel on every build rather than asserted here.

## What the reach actually is

The emitted programs are not uniformly fast; they are fast wherever the *cost
was the ambient tower* and unchanged wherever the cost is real.  Measured:

| theorem | certified extract reaches | emitted reaches | what the remaining wall is |
|---|---|---|---|
| Fibonacci | `n = 3` | `n = 25` in ~1 s | none hit; cost is now linear |
| Goodstein | `m = 1` | `m = 3` | `m = 4`'s stop time is astronomical — the mathematics, not the encoding |
| Hydra | code `1` | code `3` | as Goodstein |
| gcd | **nothing at all** | inputs in the hundreds | subtractive Euclid through the strong-induction scaffold: cost grows with `a + b`, not with `log` |
| Pascal | row 7 | row 7+ | none hit |
| Hanoi | `n = 4` | `n = 4` | **unchanged, and that is the point** — STATUS.md diagnosed Hanoi's wall as the *encoding* (code bit-length squares per move), not the extraction. Deleting the ambient tower did not move it, which is independent confirmation of that diagnosis. |

The gcd row is the one worth pausing on: `derivBound gcdTheorem = 41` meant the
certified `gcdWitness 0 0` never returned, so the repository has always had a
*certified but never-executed* program.  It executes here.
-/

namespace Realizability

/-! ## Readers for the shapes the case studies have -/

/-- Fibonacci's theorem is an `∧`-of-`∃`, so the witness is under two
projections rather than one. -/
def emFib (n : ℕ) : ℕ := ((Emit.run fibPairedTheorem) n).1.1

/-- The emitted Goodstein stopping time. -/
def emGoodstein (m : ℕ) : ℕ := Emit.witness₁ goodsteinTheorem m

/-- The emitted Kirby–Paris battle length. -/
def emHydra (h : ℕ) : ℕ := Emit.witness₁ hydraTheorem h

/-- The emitted gcd. -/
def emGcd (a b : ℕ) : ℕ := Emit.witness₂ gcdTheorem a b

/-- The emitted Hanoi solution code, at the peg convention `hanoiMoves` uses. -/
def emHanoi (n : ℕ) : ℕ := Emit.witness₄ hanoiTheorem n 0 2 1

/-- The emitted Hanoi solution, decoded to `(from, to)` pairs by the
repository's own decoder. -/
def emHanoiMoves (n : ℕ) : List (ℕ × ℕ) := decodeMoves (n + 32) (emHanoi n)

/-- The emitted Pascal decision tag. -/
def emPasTag (n k : ℕ) : ℕ := Emit.tag₂ pasTotal n k

/-! ## Agreement with the certified extracts

Every one of these compares the emitted program against the *certified* one at
inputs where the certified one terminates.  A disagreement fails the build. -/

-- Fibonacci: against the certified `fibonacci`, which reaches `n = 3`.
#guard (List.range 4).map emFib == (List.range 4).map fibonacci

-- Goodstein: against the certified `goodsteinStopTime`, which reaches `m = 1`.
#guard [emGoodstein 0, emGoodstein 1] == [goodsteinStopTime 0, goodsteinStopTime 1]

-- Hydra: against the certified `hydraBattleLength`, which reaches code 1.
#guard [emHydra 0, emHydra 1] == [hydraBattleLength 0, hydraBattleLength 1]

-- Hanoi: the decoded move lists agree with the certified `hanoiMoves`.
#guard (List.range 4).map emHanoiMoves == (List.range 4).map hanoiMoves

-- Pascal: the whole of row 6, against the certified `pasTag`.
#guard (List.range 8).map (emPasTag 6) == (List.range 8).map (pasTag 6)

/-! ## Reach — past where the certified extract can go

`gcd` is checked against `Nat.gcd`, which appears here and in
`PascalExtraction.lean` only, and only inside `#guard`s. -/

-- Goodstein, at `m = 2, 3`, which the certified extract cannot evaluate.  The
-- answers are the published stopping times — and the same column `minStop`
-- computes by μ-search in `GoodsteinSearch.lean`.
#guard [emGoodstein 0, emGoodstein 1, emGoodstein 2, emGoodstein 3] == [0, 1, 3, 5]

-- Hydra, at codes the certified extract cannot evaluate.
#guard [emHydra 0, emHydra 1, emHydra 2] == [0, 1, 3]

-- Fibonacci, well past `n = 3`.
#guard (List.range 12).map emFib == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]
#guard emFib 25 == 75025

-- **gcd: the certified realizer evaluates at no input whatsoever.**
#guard [emGcd 12 18, emGcd 7 13, emGcd 0 0, emGcd 48 180, emGcd 100 75] ==
  [Nat.gcd 12 18, Nat.gcd 7 13, Nat.gcd 0 0, Nat.gcd 48 180, Nat.gcd 100 75]
#guard emGcd 12 18 == 6

-- Pascal row 7 is all-ones (7 = 0b111, so every `C(7,k)` is odd): every tag is
-- the left disjunct, `pas = 1`.
#guard (List.range 8).map (emPasTag 7) == [0, 0, 0, 0, 0, 0, 0, 0]

-- Hanoi at `n = 4`: the classical 15-move optimum, decoded.
#guard (emHanoiMoves 4).length == 15

/-! ## The Haskell backend

Pinned outputs for the smallest derivation, so a change in either emitter shows
up as a build failure rather than as silently different generated source.  The
two emitters are meant to mirror each other; these guards are what makes
"mirror" checkable. -/

-- The type translation agrees with `tyOf`'s shape on the smallest existential.
#guard Emit.hsTy (Formula.ex 1 (.eq (.good (numeral 3) (.var 1)) .zero))
  == "(Integer, ())"

-- The emitted body is the witness `5` paired with the erased certificate —
-- the same `5` that `#realizer` shows and that `#reduce` loses.
#guard Emit.hsEmit goodThreeExDeriv 0 == "(5, ())"

-- The generated gcd module is small: the collapse rule folds a 531-line
-- derivation's equational reasoning to `()`.
#guard (Emit.hsModule "Gcd" "gcdTheorem" gcdTheorem).length < 8000

#print axioms emGcd
#print axioms emGoodstein

end Realizability
