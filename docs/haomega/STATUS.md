# HA^ω status

**As of 2026-08-10, commit `ac56b0e`.** 761 jobs green, zero warnings, zero
`sorry`/`admit`. 9,894 lines across 44 files in `HAomega/`, 45 inference
rules, 15 extracted realizers rendered in `EXTRACTED_HAOMEGA.md`.

This is the "where does everything stand" document. `HAOMEGA.md` is the
roadmap, `HAOMEGA_DOSSIER.md` is the evidence with per-claim tags, and the
paper is the account. This file is the ledger: **what is proved, what is only
stated, and what is blocked on what.**

---

## 1. The machinery — complete

| part | state |
|---|---|
| Finite types, System T, `Formula` indexed by realizer type | done |
| `MR`, 45 rules, `extract` (axiom-free, cast-free) | done |
| `soundness`, one case per rule, no wildcard | done |
| Continuity (`Tracked`, `extract_continuous2`), choice-free | done |
| `tiEps0` + `tiRec`, and their typed twins `tiEps0O`/`tiRecE` | done |
| Certified emission to a functional target, **13 of 13 programs** | done |
| Derivation-authoring kit (`Kit.lean`), extensible normalizer | done |

**Axiom footprints**, reprinted every build:

```
extract, fibRealizer                        no axioms
Tm.eval, continuity, all derivations,
  all running extracts                      [propext, Quot.sound]
soundness                                   [propext, Classical.choice, Quot.sound]
```

Choice enters `soundness` only through value-layer *theorem proofs*. **Every
extracted program that runs is choice-free.** That invariant is the reason
several design decisions below went the way they did.

## 2. The de-coding programme — finished

Every case study that once coded an object into `ℕ` has a typed twin; the
coded modules are retained only as the baselines their twins are measured
against.

| object | was | is |
|---|---|---|
| ε₀ notations | naturals via pairing | base type `ord` (`OrdCnf.lean`) |
| hydra trees | naturals via pairing | base type `hyd` (`HydraTyped.lean`) |
| Hanoi move sequences | — | never coded here; functions from the start |

The template both ports used: an inductive type with structural operations,
an encoding `toCode` used **only in proofs**, and every certified fact
inherited through it. No new mathematics was imported by either.

**The measurement that justifies it:** at the hydra whose published
Kirby–Paris battle length is 37, the coded extract exhausts the evaluator
without taking a step; the tree extract returns 37.

## 3. The fifteen extracted programs

Discrete (13, all covered by certified emission):
Fibonacci · Fibonacci at type 2 · Pascal mod 2 · Tower of Hanoi · gcd (full
spec) · Goodstein · Kirby–Paris · Sperner 1D · Hercules (∀-strategy) ·
Hercules (any head) · Goodstein on typed ordinals · Kirby–Paris on trees ·
Hercules on trees.

Analysis (2): square-root approximation · uniform continuity.

## 4. The analysis strand

| phase | state |
|---|---|
| 0. numeric base types | **done** — `rat` (states) and `dyad` (computes), both hand-rolled, with the bridge `dtoq` |
| square roots | **done** — a corollary of Sperner 1D, which *is* the discrete IVT; `√2` at `2⁻⁸` returns `181/128` |
| uniform continuity | **done** — the extracted realizer *is* the modulus; doubling gives `n+1`, translation `n` |
| Newton–Leibniz (EFTC2, positive half) | **constructions only** — see §5 |

**Why the numeric layers are hand-rolled.** Mathlib's `Rat` arithmetic —
including `Rat.add`, `Rat.mul`, `mkRat`, `Rat.normalize` — depends on
`Classical.choice`. Measured, not assumed. Using it would put choice inside
`Tm.eval` and destroy the invariant in §1. Same trap `Epsilon0.lean` records
for `Nat.pair`.

## 5. What is stated but **not proved**

Listed here so it cannot be missed. Each is flagged in its own source file too.

| claim | file | status |
|---|---|---|
| `Lemma1Claim`, `Lemma2Claim`, `EFTC2Claim` | `EFTC.lean` | **stated, unproved.** The constructions run and are guarded at instances; the error analyses are not derived |
| Lipschitz premise of uniform continuity | `UniformContinuity.lean` | hypothesis, discharged by the caller — guarded by computation |
| bound `K` in the square-root theorem | `SquareRoot.lean` | hypothesis, discharged by the caller — guarded by computation |
| modulus metatheorem (extraction yields a modulus for *every* derivation) | `Modulus.lean` | not proved; two recorded obstructions, see §6 |

**One cause underlies the first three: there is no arithmetic rule base for
`Q`.** `Deriv` has no conversion equations for the numeric operations, and
the value layer has no ring or order theory. Three independent pieces of work
have now hit it.

## 6. Known limits, with reasons

* **No arithmetic rule base for `Q`** — the live blocker. See §7.
* **No modulus metatheorem.** At arrow types a single numeric bound does not
  suffice (one needs a modulus whose *type* is computed from the finite type,
  i.e. a Kleene associate — exactly what the continuity proof exists to
  avoid); and `tiRec` has no compositional bound, since a notation can have
  infinitely many `≺`-predecessors. Continuity survives there; compositionality
  of the *bound* is what fails.
* **Emitted code**: GHC does not check that the emitted transfinite recursion
  terminates. It does, by the ε₀ descent proved on the Lean side, and the
  theorem is relative to that. The prelude and printer are trusted.
* **Independence from PA is formalized nowhere.** Goodstein and Kirby–Paris
  are termination theorems here; that PA cannot prove them is not claimed.
* **Myhill's negative half (`A₀ ⊭ EFTC2`) is a citation**, not a formalization.
* **`Modulus.lean` does not apply to analysis.** `HasMod` is Baire-space
  continuity — how much of an *oracle* a functional inspects — while `ω`/`δ`
  are metric moduli on `ℚ`. Checked; no lemma transfers.
* Coded hydra extracts still overflow at codes 4 and 7. That is the
  measurement their typed twins are measured against, not an unrepaired bug.

## 7. The arithmetic rule base for `Q` — partially unblocked

**The quotient re-representation was planned, measured, and then abandoned as
unnecessary.** What follows is what happened, not what was intended.

### The measurement that decided it

The plan branched on whether the `Quotient.lift` respect proofs could be
choice-free, since under a quotient those proofs become part of the
*definition*. Measured, exactly as printed:

    crossTrans  via  mul_left_cancel₀            [propext, Classical.choice, Quot.sound]
    crossTrans  via  Int.eq_of_mul_eq_mul_left   [propext]
    addRespects via  ring                        [propext]

So `ring` is clean and the *generic* `mul_left_cancel₀` is not, while the
`Int`-specific cancellation is — a one-lemma swap, not the sign-case-split
fallback the plan anticipated.

### The finding that made the whole question moot

While checking the above: **the choice constraint never bound the lemmas at
all.** The rule base is consumed by `soundness`, whose footprint already is
`[propext, Classical.choice, Quot.sound]`. Only *definitions* reachable from
`Tm.eval` must be clean, and `Q.add`/`Q.mul`/`Q.div` are measured axiom-free
already. So the lemmas may use Mathlib freely, and neither the quotient
re-representation nor a hand-rolled `gcd` theory is needed. **`Q`'s
representation is unchanged.** The earlier reasoning in this document — that
the lemmas had to be choice-free too — was simply wrong.

### What landed: `HAomega/QArith.lean`

* `Q.of_eq_mkRat` — `Q.of` agrees with Mathlib's normalization.
* **`Q.of_eq_of`** — *the* lemma five pieces of work were blocked on:
  equivalent fractions normalize to the same `Q`. With it, a ring identity
  reduces to an `Int` polynomial identity that `ring` closes.
* `Q.add_comm`, `Q.mul_comm` — demonstrating the route composes.

All `[propext, Classical.choice, Quot.sound]`, which is harmless here for the
reason above.

### What did **not** land, and why

**The laws carry a `den ≠ 0` hypothesis, so they are not yet `Deriv` rules.**
`Q`'s denominator is a bare `Nat`, so `⟨5,0⟩` inhabits `Q` and the object
language's `∀x^rat` ranges over it. Removing the hypothesis needs positivity
made structural — store `den : Nat` meaning `den+1` — which ripples through
every site reading `.num`/`.den` (`EFTC.lean`'s `ceilNatQ`, `Dyadics.toQ`,
the guards). That refactor is the next step and is **not done**.

Consequently **none of §5's rows has moved yet**: `SquareRoot`'s `K`,
`UniformContinuity`'s Lipschitz premise, and `EFTC`'s three claims are all
still hypothesis-discharged-by-caller or stated-unproved. The blocker is now
one concrete refactor rather than an open mathematical question, which is the
real change.

*Cost note:* `QArith.lean` imports `Mathlib` wholesale — narrower imports were
tried and the module paths do not exist in the pinned version. Since the file
is proof-side only, the cost is build time (7,849 jobs, ~11 s warm), not
trust.

## 8. Not started

* Constructive analysis beyond uniform continuity: IVT proper, Banach fixed
  point, Picard. Banach needs completeness (Cauchy sequences of Cauchy
  sequences); Picard additionally needs function spaces and integration — a
  programme, not a next step.
* Bisection-versus-Newton as a quantitative fingerprint experiment. The
  square-root theorem does not exhibit it: its colouring is monotone, so first
  and last crossing coincide. It needs a genuinely different *proof*.
* Automatic associates for extracted type-2 programs (see §6).
* A related-work / novelty investigation across Coq, Agda, Minlog, Nuprl and
  Isabelle. Not begun; no priority is claimed anywhere on the basis of the
  Lean-only search done so far.
