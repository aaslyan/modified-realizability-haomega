# HA^ω status

**As of 2026-08-10, commit `b259874`+.** 761 jobs green, zero warnings, zero
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
`Q`.** `Deriv` has no conversion equations for the numeric operations. The
value layer now *does* have ring theory (§7) — that half is done — but no law
has been lifted to a rule, so all three rows are unchanged.

## 6. Known limits, with reasons

* **No arithmetic rule base for `Q`** — the value-level ring laws are now
  proved unconditionally, but none has been added to `Deriv` as a conversion
  rule, so the object language still cannot compute with `Q`. See §7.
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

## 7. The arithmetic rule base for `Q` — laws proved, rules not yet added

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

### The `den+1` refactor: the laws are now unconditional

`Q`'s denominator field stores its **predecessor**, so `den = denPred + 1` and
there is no inhabitant with denominator zero. Before that, `⟨5, 0⟩` inhabited
`Q`, the object language's `∀x^rat` ranged over it, and every law carried a
`den ≠ 0` hypothesis that kept it from being a `Deriv` rule. The refactor
touched the constructions in `Rationals.lean` only; `EFTC.lean`'s `ceilNatQ`
and `UniformContinuity.lean`'s `closeVal` read `.num`/`.den` and were unchanged,
because `den` became a function of the same name.

What is proved in `QArith.lean`, all with **no side conditions**:

| law | form |
|---|---|
| `Q.add_comm`, `Q.mul_comm` | commutativity |
| `Q.add_assoc`, `Q.mul_assoc` | associativity |
| `Q.mul_add` | distributivity |
| `Q.add_neg`, `Q.sub_self` | additive inverse |

The route is one indirection: `Q.val` sends a `Q` to the Mathlib rational it
denotes, each operation is shown to commute with it (`Q.val_add`, `Q.val_mul`,
`Q.val_neg`), and `Q.of_inj_val` turns equal values back into equal normal
forms. Proving the nested laws through `of_eq_of` directly does not work — the
inner `Q.of` has already normalized, so its numerator is not the
cross-multiplied one and the identity stops being polynomial.

All report `[propext, Classical.choice, Quot.sound]`, harmless for the reason
above. The invariants are unmoved, reprinted from the build:

    HAomega.Tm.eval    [propext, Quot.sound]
    HAomega.Q.add      does not depend on any axioms
    HAomega.Q.mul      does not depend on any axioms
    HAomega.Q.div      does not depend on any axioms

### What the refactor did **not** buy: the identity laws

Positivity is now structural. **Coprimality is not**, and `x + 0 = x` needs
it. `⟨2, denPred := 3⟩` — the fraction `2/4` — inhabits `Q`, `Q.of` never
produces it, and adding zero reduces it:

    Q.add ⟨2,3⟩ Q.zero = ⟨1,1⟩ ≠ ⟨2,3⟩

`Q.add_zero_not_id`, by `decide`. So that law is **false in this model** and
must not become a `Deriv` rule; its honest form is `Q.add_zero_norm`: adding
zero normalizes. The dividing line is whether both sides of a law pass through
`Q.of` — the seven above do, which is why they hold on the nose for every
inhabitant, and a law with a bare variable on one side does not.

Closing that gap means a subtype carrying a coprimality proof, or a quotient —
a change of a different size from `den+1`, and one that has to keep the proof
component out of `Tm.eval`'s axiom footprint. **Not attempted.**

### What has still not moved

**None of §5's rows has changed state.** `SquareRoot`'s `K`,
`UniformContinuity`'s Lipschitz premise and `EFTC`'s three claims are still
hypothesis-discharged-by-caller or stated-unproved. What changed is the
blocker beneath them: there is now a hypothesis-free law suite to build object
rules from, where before there was none. Turning these lemmas into `Deriv`
rules — which needs conversion equations in `Syntax.lean` and cases in
`extract`/`soundness`/`eval_tracked`/`hsOf` per the per-rule discipline — is
the next step and is not done.

*Cost note:* `QArith.lean` imports `Mathlib` wholesale — narrower imports were
tried and the module paths do not exist in the pinned version. Since the file
is proof-side only, the cost is build time (7,849 jobs), not trust.

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
