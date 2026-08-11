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
| square roots | **done** — a corollary of Sperner 1D, which *is* the discrete IVT; `√2` at `2⁻⁸` returns `181/128`; its bound `K` is now proved, not assumed |
| uniform continuity | **done** — the extracted realizer *is* the modulus; doubling gives `n+1`, translation `n` |
| Newton–Leibniz (EFTC2, positive half) | **constructions only, and the correctness claims are refuted as stated** — see §7 |

**Why the numeric layers are hand-rolled.** Mathlib's `Rat` arithmetic —
including `Rat.add`, `Rat.mul`, `mkRat`, `Rat.normalize` — depends on
`Classical.choice`. Measured, not assumed. Using it would put choice inside
`Tm.eval` and destroy the invariant in §1. Same trap `Epsilon0.lean` records
for `Nat.pair`.

## 5. What is stated but **not proved**

Listed here so it cannot be missed. Each is flagged in its own source file too.

| claim | file | status |
|---|---|---|
| bound `K` in the square-root theorem | `SquareRoot.lean` | **discharged** — `sqrt_premises` (`QAnalysis.lean`) proves both colouring premises for every `q ≥ 0` at every precision |
| Lipschitz premise of uniform continuity | `UniformContinuity.lean` | **discharged at the three guarded maps**, for all `x`, `y`, `m`; an arbitrary `f` still owes its own |
| `Lemma1Claim`, `Lemma2Claim`, `EFTC2Claim` | `EFTC.lean` | **refuted as stated** — see §7. Repaired statements exist; one half of Lemma 1 is proved, the rest is not |
| modulus metatheorem (extraction yields a modulus for *every* derivation) | `Modulus.lean` | not proved; two recorded obstructions, see §6 |

The first three rows were all blocked on the same missing thing — an
arithmetic rule base for `Q` — and that is what §7 records the resolution of.
Two of them moved. The third turned out not to be blocked on arithmetic at
all.

## 6. Known limits, with reasons

* **No arithmetic rule base for `Q` at the object level.** The value-level
  ring *and order* laws are now proved unconditionally (§7), and they were
  enough to discharge two of §5's rows. But no law has been added to `Deriv`
  as a conversion rule, so the object language still cannot compute with `Q`;
  everything in `QAnalysis.lean` is meta-level Lean.
* **Nothing about `A1.integral` can be proved by computation.** `sumQ` is a
  `do`-loop — chosen so the Riemann sums survive `N = 32768` in the
  interpreter — and the loop **does not reduce in the kernel**. Measured on
  the smallest instance: `sumQ (fun _ ↦ Q.ofNat 1) 2 = Q.ofNat 2` fails by
  `rfl`. So `decide` is unavailable for any statement mentioning `integral`,
  and the `Lemma2Claim` refutation is evaluator-checked rather than a
  theorem. Same `WellFounded.fix` wall the first-order development records
  for its value-level recursions, reached from the opposite direction.
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

### The order bridge, and what it unblocked

Ring laws alone were not enough: every obligation in the analysis files is an
*inequality*, and `Q.ltN` is a `0`/`1` numeral rather than a `Prop`. The
bridge `Q.ltN_eq_one_iff : Q.ltN a b = 1 ↔ a.val < b.val` (with the `= 0`
companion, `Q.val_abs`, `Q.val_div`, `Q.val_ofNat`) turns each one into an
inequality between Mathlib rationals, where `linarith`/`nlinarith` apply.
That is what made the two discharges below mechanical rather than manual
cross-multiplication.

All of it lives in `QAnalysis.lean`, a **leaf** module importing the analysis
chain rather than sitting inside it, so no certified module changed shape and
`Mathlib` stays out of `Tm.eval`'s import graph.

### Step 4: what the payoff actually reached

**Square-root bound `K` — discharged.** `sqrtBound q n := (⌊q⌋+1)·2ⁿ`, with
`sqrt_lower_premise` and `sqrt_upper_premise` proving both of `sqrtApproxD`'s
hypotheses for every `q ≥ 0` at every precision. `#guard`s confirm the
extracted search run at the computed bound returns the same roots the
hand-picked bounds gave. `q ≥ 0` is genuinely necessary, not an artefact.

**Lipschitz premise — discharged for the guarded maps.** `doubling_lipschitz`,
`translation_lipschitz`, `quadrupling_lipschitz`, each for *all* `x`, `y`, `m`
rather than at sampled points. Stated precisely: the *general* theorem
`uniContD` was already proved; what these close is the side condition at each
instance. A caller supplying some other `f` still owes the obligation for that
`f`, and there is no general theorem that every definable `f` contracts —
that is false.

**EFTC — refuted as stated, not proved.** This is the result that did not go
as planned, and the reason has nothing to do with arithmetic. `A1` is a bare
structure — `a`, `b`, `f`, `ω`, `δ` with **no fields relating them**. Nothing
says `ω` is a modulus of continuity, nothing says `δ` is a modulus of uniform
differentiability, nothing says `a < b`. Those conditions live in the
docstrings and in the manifesto's definition of `A₁`, not in the type, and
`Lemma1Claim`/`Lemma2Claim` quantify over an arbitrary `A : A1`. So they are
false:

    'HAomega.Lemma1Claim_false'  does not depend on any axioms
    'HAomega.EFTC2Claim_false'   depends on axioms: [propext, Quot.sound]

The witness `lyingEx` is `sqEx` — `x²` on `[0,1]`, where the constructions are
guarded and correct — with `ω` and `δ` replaced by the constant `0`. Then `ω'`
collapses to the constant `1`, `intN k = 2` at every precision, `integral k`
is stuck at `3/4`, and Lemma 1 fails already at `k = 0`, `x = 0`, `y = 1/2`
(quotients `1/4` and `5/4`, gap `1`, target `1`). Both are checked by the
kernel except the `Lemma2Claim` half, for the `sumQ` reason in §6.

`IsA1` supplies the missing hypotheses — including the **interval
restriction**, which `Lemma1Claim` also drops and the manifesto's Lemma 1 has.
Under it, **Lemma 1's computable half is proved**:

    'HAomega.derivEval_approx'  depends on axioms: [propext, Classical.choice, Quot.sound]

i.e. `|derivEval k x − f' x| < 2⁻⁽ᵏ⁺³⁾` at every `x ∈ [a,b]` — the fact that
makes the `EFTC2` witness a statement about `f'` rather than about the numeral
`f b − f a`. The endpoint-safe sign is what the proof spends its effort on.

**The rest of Lemma 1 is not proved, and the §5.2 argument does not give it.**
Three obstructions, each found by attempting the proof and each recorded in
`QAnalysis.lean` so it can be checked: (1) §5.2's cancellation needs `x` and
`y` to use the *same* step, but `stepRight` picks the sign pointwise, so
points either side of the midpoint use opposite steps and nothing cancels;
(2) when `(b−a)/4` is the smaller half of `h₀`, the estimate divides by
`4/(b−a)` and `ω'` contains no term bounding it — so `omega'` **as
implemented** is not large enough in general, a statement about the code, not
the proof; (3) the repaired route needs `ω` at `k+4+δ(k+4)` where the
construction supplies `k+5+δ(k+3)`, and nothing requires `ω`, `δ` monotone.
**Lemma 2 is further off**: §5.2 imports `∫f' = f(b)−f(a)` from classical
FTC2, and there is no real integral here for that to be imported into; the
mesh `L/N` and the step `h₀` are unrelated, so no discrete telescoping
replaces it.

### What has still not moved

Turning any of these lemmas into `Deriv` rules — conversion equations in
`Syntax.lean` plus cases in `extract`/`soundness`/`eval_tracked`/`hsOf` per
the per-rule discipline — is **not done**; everything above is meta-level.
`EFTC`'s claims are refuted rather than proved, and repairing them needs
changes to `A1` and to `omega'`, not more arithmetic. The `Modulus.lean` row
of §5 is untouched.

*Audit note:* the site list this document previously gave for the `den`
refactor (`ceilNatQ`, `Dyadics.toQ`, "the guards") was not accurate.
A repo-wide `grep` for `.num`/`.den` finds readers in exactly four files —
`Rationals.lean`, `QArith.lean`, `EFTC.lean` (`ceilNatQ`), and
`UniformContinuity.lean` (`closeVal`). `Dyadics.toQ` does **not** read either
field; it calls `Q.of`, so it was never a touch point.

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
