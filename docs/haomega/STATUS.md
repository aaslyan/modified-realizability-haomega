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
| Newton–Leibniz (EFTC2, positive half) | **done** — `eftc2_thm : ∀ A : A1, EFTC2Claim A`; see §7 |
| Newton–Leibniz (EFTC1, integration direction) | **done** — `eftc1 : ∀ A : A0, EFTC1Claim A`; `δ := ω`, no new data |

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
| `Lemma1Claim`, `Lemma2Claim`, `EFTC2Claim` | `EFTC.lean` | **proved** — `lemma1`, `lemma2`, `eftc2_thm` in `QAnalysis.lean`, for every `A1`. See §7 for the six construction fixes this required |
| `EFTC1Claim` | `EFTC.lean` | **proved** — `eftc1`, for every `A0`. The "`∫f` is `A₁`-adequate" phrasing is *not* stated; see §7 for why that is a representation limit |
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

**EFTC — the claims were false, and the cause is now fixed in the code.**
This is the result that did not go as planned. `A1` was a bare structure —
`a`, `b`, `f`, `ω`, `δ` with **no fields relating them**. Nothing said `ω` was
a modulus of continuity, nothing said `δ` was a modulus of uniform
differentiability, nothing said `a < b`. Those conditions lived in the
docstrings and in the manifesto's definition of `A₁`, not in the type, and
`Lemma1Claim`/`Lemma2Claim` quantified over an arbitrary `A : A1`. So they
were refutable, and were refuted: `sqEx` (`x²` on `[0,1]`, where the
constructions are correct) with `ω` and `δ` replaced by the constant `0` makes
`ω'` collapse to `1`, `intN k = 2` at every precision, `integral k` stick at
`3/4`, and Lemma 1 fail already at `k = 0`, `x = 0`, `y = 1/2` — quotients
`1/4` and `5/4`, gap `1`, target `1`.

**Both fixes are now in.** `A1` carries `ivl`, `cont` and `diff`, so that
counterexample **can no longer be constructed** and the refutation theorems are
gone — their absence is the deliverable. Two design points are load-bearing:

* `diff` is **existential** (`∃ F : Q → Q, …`). Putting `f'` in as *data*
  would be a different representation, one that hands the derivative over for
  free, and would trivialise the theorem the file exists to state.
* All three fields are written in `Q`'s own vocabulary (`Qle`, `Q.ltN`,
  dyadic `2⁻ᵏ`), not through `Q.val`. That is not style: stating them with
  `Q.val` puts `Rat`'s order instances into `A1`'s *type*, and then every
  construction taking an `A1` reports `Classical.choice`. Measured, and
  reverted. The footprints are unchanged from before the hypotheses existed:

      'HAomega.A1.derivEval'  does not depend on any axioms
      'HAomega.A1.omega''     does not depend on any axioms
      'HAomega.A1.integral'   depends on axioms: [propext, Quot.sound]
      'HAomega.A1.eftc2'      depends on axioms: [propext, Quot.sound]

**`omega'` is fixed.** It was `max(ω(k+5+δ(k+3)), η₂)`; it is now

    max(ω(k + 5 + max(δ(k+3), η₂+1)), η₂)

The estimate divides by `h₀ = min(2⁻ᵟ⁽ᵏ⁺³⁾, (b−a)/4)`, so it multiplies by
`1/h₀`, and when the *second* term is the minimum that factor is `4/(b−a)`,
which a `δ`-only index cannot see. Since `2⁻ᵑ² ≤ (b−a)/2`, the added
`max(…, η₂+1)` bounds it in both branches.

**Two things the proof obligations caught.** `sqEx`'s `δ` was off by one:
the difference quotient for `x²` is `2x + h`, so its error *is* `|h|`, and
`|h| ≤ 2⁻ᵟ⁽ᵏ⁾` has to give `|h| < 2⁻ᵏ` **strictly** — with `δ k = k` the
admissible step `|h| = 2⁻ᵏ` meets the bound with equality and misses. It is
now `k+1`. (`sqEx`'s `ω k = k+1` checks out as it stood: `x + y < 2` strictly
whenever `x ≠ y` in `[0,1]`, so the estimate is strict.) `linEx` needed no
change.

**Cost of the two fixes:** every Riemann sample count doubles —
`sqEx.intN` `8192 → 16384`, `linEx.intN` `2048 → 4096` at `k = 0` — paid in
constant factors, not in the growth rate, which is still `2^ω'(m)`. Guards
updated: `sqEx.derivEval 8` now lands within `2⁻¹²`, `sqEx.integral 0` is
`524257/524288` (error `31/524288`), `linEx.integral 0..3` still exactly `6`.

**`EFTC2Claim` is proved for every `A₁`:**

    'HAomega.lemma1'     depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.lemma2'     depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.eftc2_thm'  depends on axioms: [propext, Classical.choice, Quot.sound]

Lemma 1: `derivEval` computes the derivative to `2⁻⁽ᵏ⁺³⁾` on `[a,b]`, with one
`F` drawn from `diff` uniformly in `k` and `x`, and is uniformly continuous
with modulus `ω'`. Lemma 2: the Riemann sums built *from `derivEval`* converge
to `f b − f a` at the stated rate.

**Nothing in the analysis was missing. Six things in the constructions and
statements were**, each found by a proof failing rather than by inspection:

1. **`omega'` was too small.** The Lemma 1 estimate divides by
   `h₀ = min(2⁻ᵟ⁽ᵏ⁺³⁾, (b−a)/4)`; when the second term is the minimum the
   factor is `4/(b−a)`, which a `δ`-only index cannot bound. It now carries
   `max(δ(k+3), η₂+1)`.
2. **`A1` carried no hypotheses**, so `ω` and `δ` were moduli of nothing and
   the claims were refutable. `ivl`, `cont`, `diff` are now fields, stated in
   `Q`'s own vocabulary so `A1`'s *type* stays free of `Rat`'s order instances
   — with `Q.val` in the field types, every construction taking an `A1` reports
   `Classical.choice`. Measured, and reverted.
3. **`etaAux` returned `0` on fuel exhaustion** — precisely a value failing the
   property it searches for, wrong for any interval shorter than about `2⁻⁶³`.
   Fixed, with data-derived fuel; `ceilLog2Aux` likewise, since Lemma 2 needs
   `L ≤ 2ˡ`. `eta2_spec` and `ceilLog2Q_spec` now prove both outright.
4. **`Lemma1Claim` was missing its interval premises**, so it ranged over
   points where `A1` says nothing about `f`.
5. **`intN` fixed the mesh by `ω'` alone.** That is right for the classical
   argument — Riemann sum against `∫f'` — and wrong here. With no `∫` in a
   shallow embedding, what is available is the *exact* telescoping
   `f b − f a = Σᵢ (f xᵢ₊₁ − f xᵢ) = h·Σᵢ DQ_h(xᵢ)`, and that needs the **mesh
   itself** to be an admissible `δ`-step. Hence `intN`'s new `δ` term. This is
   the substantive mathematical difference between §5.2's Lemma 2 and the one
   proved here.
6. **`sqEx.δ` was off by one.**

**Two enabling facts.** `f` must not distinguish two `Q`s denoting the same
rational — samples are `a + i·h`, and `a + 0·h` is a different `Q` from `a` —
and `f_val_congr` *derives* this from `cont` at every precision rather than
assuming it. And `sumQ`, the `do`-loop chosen because a structural recursion
exhausts the interpreter stack at `4096` (measured), had to be reasoned about:
it does not reduce in the kernel, so `decide` is unavailable, but it unfolds to
a `foldl` over `List.range'` and a step lemma is one rewrite from there. **No
`implemented_by`, no trusted swap** — the theorems are about the same `sumQ`
the guards run.

**Cost.** The index fixes double every Riemann sample count relative to the
original code (`sqEx.intN 8192 → 16384`); the growth rate is unchanged, still
`2^ω'(m)`, which is §8's optimal-adequacy question rather than this one.

### `EFTC1` — the integration direction

**Proved: `eftc1 : ∀ A : A0, EFTC1Claim A`**, footprint
`[propext, Classical.choice, Quot.sound]`. Stated in exactly `A1.diff`'s shape,
with `δ` instantiated to `ω` and the derivative instantiated to the integrand:
the difference quotients of the Riemann sums of `f` over `[x, x+h]` are within
`2⁻ᵏ` of `f x` whenever `|h| ≤ 2⁻ω⁽ᵏ⁾`, **uniformly in the subdivision count**
and consuming only `A₀`-data.

The proof is short because the mathematics is: a difference quotient of a
Riemann sum is the *average* of `f` at points all within `|h|` of `x`, and an
average of values each within `2⁻ᵏ` of `f x` is within `2⁻ᵏ` of `f x`. That is
the whole of the asymmetry — `EFTC2` needed `δ` supplied from outside and, by
Myhill, could not manufacture it from `A₀`-data; integration needs nothing
supplied.

Refactor this required: `ivl` and `cont` moved from `A1` to `A0`, where they
belong — they are conditions on `A₀`'s data alone, and `EFTC1`'s hypothesis is
an `A₀`. `A1` now adds exactly `δ` and `diff`.

### Approximating evaluators

`A0.f : Q → Q` is an *exactly rational-valued* evaluator, and `∫f` is not
rational-valued — which is why `EFTC1` could prove its differentiability
content but not say "`∫f` is `A₁`-adequate": `∫f` was not an inhabitant of the
theory at all. The `E0` layer fixes that.

    structure E0 where a b : Q; ev : Nat → Q → Q; cm : Nat → Nat; ivl; conv

`ev n x` is the `n`-th approximation at `x`. There is no real number here for
the approximations to converge *to*, so what `conv` asserts is that they
converge to **each other**: past level `cm k`, successive levels agree to
`2⁻ᵏ`. That is what "represents a real" means constructively.

**Proved:**

    'HAomega.A0.toE0'   depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.A0.intE0'  depends on axioms: [propext, Classical.choice, Quot.sound]

`A0.toE0` is **conservativity** — every exact representation is an
approximating one (the constant family), so the generalization admits more
functions and loses none. `A0.intE0` is the payoff: `∫f` *is* an `E0`, with
`cm k := ω (k + ℓ)` built from `f`'s own modulus of continuity.

**The engine is `riemann_refine`**: doubling a Riemann sum's subdivision count
moves it by at most `|h|·2⁻ᵏ`. Comparing Riemann sums at *arbitrary* counts
needs a common refinement and an index bijection; comparing `N` with `2N` needs
only that the even fine points are the coarse points, which is an induction
(`sum_range_two_mul`). That is why the evaluator's levels double — the
indexing is chosen to make the estimate provable. `f_val_congr` is needed again
here: the even fine points equal the coarse points as *values*, not as terms.

### The `E₁` layer

`E1 extends E0` with `ω`, `δ` and the two conditions transposed to the
approximating setting, plus one field `A1` did not need: **`dq : Nat → Q → Nat`**,
the level at which a difference quotient at step `h` is good to `2⁻ᵏ`. A
difference quotient divides by `h`, so an evaluator error `ε` contributes
`2ε/|h|`, and no fixed level works for every `h`. That dependence is the whole
difference between `A1.diff` and `E1.diff`.

    'HAomega.A1.toE1'  depends on axioms: [propext, Classical.choice, Quot.sound]

**Conservativity again**: every exact `A₁` is an `E₁` via the constant family,
with `dq := 0` — an exact evaluator has no error for the quotient to amplify.

### A correction to `E0`, found while building `E1`

`E0.conv` as shipped in the previous commit bounded only **successive** levels:
`|ev n x − ev (n+1) x| ≤ 2⁻ᵏ` past level `cm k`. That is too weak to make the
family Cauchy — `j` consecutive gaps of `2⁻ᵏ` sum to `j·2⁻ᵏ`, which is
unbounded, so the condition does not say the approximations converge. It was
not false, and `A0.intE0` proved a true statement; the *structure* was simply
weaker than a representation needs. `conv` now quantifies over all later
levels:

    conv : ∀ k n m, cm k ≤ n → n ≤ m → … |ev n x − ev m x| ≤ 2⁻ᵏ

Reproving `A0.intE0` at that strength needed a better estimate than the
doubling one. Chaining doublings **accumulates** — `j` steps give `j·|h|·2⁻ᵏ` —
so `riemann_refine_gen` proves the classical form instead: refining a Riemann
sum by *any* factor moves it by at most `|h|·2⁻ᵏ`, with no dependence on the
factor, because every fine sample lies within the **coarse** mesh of its
block's left endpoint however many fine samples there are. The block
decomposition is `sum_range_mul_block`, an induction on the outer count.

### Additivity without tagged partitions

The obstacle to lifting `∫f` from `E₀` to `E₁` was additivity — the grids for
`[a,x]` and `[a,x+h]` are incommensurate, so the difference of the two sums is
not the sum over `[x,x+h]` — and the plan of record was to generalize to
tagged partitions and redo the refinement estimate at that generality.

**Tagged partitions turned out not to be needed.** The split point is a
*rational*, so `h/(x−a)` is a ratio of integers, and cell counts in that ratio
make the concatenated grid uniform again. Two lemmas do what a common
refinement of two arbitrary partitions would have done:

    'HAomega.riemann_split'          depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.riemann_uniform_close'  depends on axioms: [propext, Classical.choice, Quot.sound]

`riemann_split` is **exact**: a uniform grid of `[x, x+h₁+h₂]` with `N₁+N₂`
cells splits at `x+h₁` into the grids of `[x,x+h₁]` and `[x+h₁,x+h₁+h₂]`
whenever the two cell widths agree. `riemann_uniform_close` is grid
independence: two uniform grids with mesh at most `2⁻ω⁽ᵏ⁾` agree to `2|h|·2⁻ᵏ`,
by comparing each to the product grid. No partition objects, no sortedness, no
merge.

### What `∫f` still needs to be an `E₁`

Of the three items recorded last round, **two are now done**.

    'HAomega.split_widths'     depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.split_mesh'       depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.A0.fBound_spec'   depends on axioms: [propext, Classical.choice, Quot.sound]

**The counts.** `splitScale`, `splitLo`, `splitHi` take the numerator `p` and
denominator `q` of `h/d` and use cells in the ratio `q : p`, scaled until the
mesh is fine. `split_widths` proves the cell widths agree — which is exactly
`riemann_split`'s hypothesis — and `split_mesh` proves the mesh target. They
are **sign-agnostic**: `natAbs` makes them describe the interval of length
`|h|`, whichever side of the point it lies on, so `h < 0` needs no separate
construction. What the *assembly* still has to do is orient that interval,
since `riemann_split` is stated for two lengths laid end to end.

**The bound on `|f|`.** `A0.fBound := |f a| + bnd`, where `bnd` counts
`2⁻ω⁽⁰⁾`-steps across `[a,b]`. `A0.fBound_spec` proves it bounds `|f x|` at
every `x ∈ [a,b]`: `ω` says `f` moves by less than `1` per step, and the walk
from `a` to `x` telescopes.

**The assembly is done.**

    'HAomega.A0.intEv_cont'  depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.A0.intEv_diff'  depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.A0.intE1'       depends on axioms: [propext, Classical.choice, Quot.sound]

**`A0.intE1 : A0 → E1`** — the integral of an `A₀` is an approximating
evaluator carrying a modulus of continuity *and* a modulus of uniform
differentiability, with the derivative being `f` itself and both moduli built
from the `A₀`-data alone. That is `EFTC1` as a single statement: integration
upgrades `A₀` to `A₁` and nothing is supplied that was not already there.

`cont` is `intEv_cont` (§ above). `diff` is `intEv_diff`, which chains

    intEv n (x+h) − intEv n x  ≈  riemann a (x−a+h) (N₁+N₂) − riemann a (x−a) N₁
                               =  riemann x h N₂
                               ≈  h · f x

with `riemann_uniform_close` twice, `riemann_split` via `split_widths` and
`split_mesh`, and `eftc1_quotient`. Three things the chain needed:

* `A0.intEv_split_close` produces its cell count rather than naming it, because
  the degenerate case `x = a` has an empty lower piece where `splitHi` would be
  `0` and the evaluator's own grid serves instead.
* Both **orientations**. A negative step splits `[a,x]` at `x+h` and the
  quotient is then moved from `f (x+h)` to `f x` by one more use of `cont` —
  the only asymmetry between the cases.
* **Congruence** — `riemann_val_congr` and `A0.intEv_val_congr`, since the two
  sides of the chain produce `riemann` at equal-valued but distinct `Q` terms.
  This is `f_val_congr` one level up, and it is needed because a `Q` carries
  more than the rational it denotes.

`E1.dq` is what absorbs the `4L·2⁻ᴷ/|h|` that dividing by `h` costs:
`A0.intDq k h = ω(k+4+ℓ+⌈log₂(1/|h|)⌉)`, growing as the step shrinks. That
dependence on `h` is the one field `A₁` had no analogue of, and this is where
it earns its place.

### Reals in the object language

A real is a Cauchy family of rationals with a rate, and the object language
**already has the type**: `Ty` is closed under `→`, so a real is a term of type
`nat → rat`. No new base type, no new rule.

    'HAomega.realCauchy_sound'  depends on axioms: [propext, Classical.choice, Quot.sound]

`realUpperF`/`realLowerF` are the Cauchy formulas (two one-sided `qlt` bounds
rather than an absolute value, so no `recNat`-defined `abs` is involved; the
bound is a parameter, and the gap `d` is quantified instead of `m ≥ n`, so no
order on `nat` is needed). `realCauchy_sound` carries a closed derivation of
them down to the value layer — **`HAomega`'s first use of `soundness` to obtain
an analytic fact**, and the join between the object language and the `E₀`/`E₁`
machinery.

### The fork this exposes — option 2 measured, and it splits

Three options were on record for giving `Deriv` arithmetic rules for `Q`:
Mathlib in the core, hand-rolled choice-free laws, or conversion-by-evaluation.
Option 2 has now been measured against a concrete target — `qsub t t = 0`, the
first thing the constant real needs — rather than estimated.

**The finding: option 2 is not one size.** It splits, and the dividing line is
the same one the `den+1` refactor found: *whether both sides feed `Q.of`
arguments that already agree.*

**Cheap — no normal-form theory at all.** Measured, in the core, with no
Mathlib:

    'HAomega.Q.sub_self'  depends on axioms: [propext]

`sub a a = zero` needs no gcd reasoning because the numerator collapses to `0`
*before* `Q.of` reaches a gcd, and `Nat.gcd 0 d = d` then short-circuits the
normalization. Four lines. The same holds for anything where the two sides give
`Q.of` equal arguments up to `Int`/`Nat` commutativity — probed, not assumed:

    Q.add_comm  (congr + Int.add_comm + Nat.mul_comm)   [propext]
    Q.mul_comm  (congr + Int.mul_comm + Nat.mul_comm)   [propext]
    Q.ltN_self  (Int.lt_irrefl)                         [propext]

**Not cheap — unchanged in size.** Associativity and distributivity are *not*
in that class and gain nothing from this route. There an inner operation's
output is fed to an outer one, so the inner `Q.of` has already normalized, and
relating the results needs uniqueness of normal forms — `Q.of_eq_of`, which is
exactly where the gcd theory lives. That is the original quotient-plan-sized
work, undiminished.

So option 2 buys a characterizable class of laws very cheaply and does not
scale past it. It is not a path to a general arithmetic rule base; it is a way
to add particular rules when the identity degenerates.

**What landed.** One rule, at the three sites a `Deriv` rule needs:

    Realizability.lean   | convQSubSelf (t : Tm Γ .rat) : Deriv Δ (.eq (.qsub t t) (.qnat .zero))
    Extraction.lean      | .convQSubSelf _ => .star
    Soundness.lean       | convQSubSelf t => … exact Q.sub_self _

Invariants unmoved, reprinted from the build:

    'HAomega.extract'    does not depend on any axioms
    'HAomega.soundness'  depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.Tm.eval'    depends on axioms: [propext, Quot.sound]

**The positivity rule, added second.** `0 < eps` is an *order* fact about a
particular bound rather than an identity, so it needed its own rule. The bound
chosen is `1/(t+1)`, not `2⁻ᵗ`, for two reasons: it is built only from
constructors the core already has (`qnat`, `qdiv`, `succ`), whereas `2⁻ᵗ` would
need a `recNat` term added to the core; and its normalization degenerates the
same way `sub_self`'s does, one step later — the gcd is `Nat.gcd 1 _`, so `of`
divides through by `1`. `1/(t+1) → 0`, so it is a genuine Cauchy rate.

    'HAomega.Q.recip_eq'        depends on axioms: [propext]
    'HAomega.Q.ltN_zero_recip'  depends on axioms: [propext]

    Realizability.lean   | convQPosRecip (t : Tm Γ .nat) :
                             Deriv Δ (.eq (.qlt (.qnat .zero)
                               (.qdiv (.qnat (.succ .zero)) (.qnat (.succ t)))) (.succ .zero))
    Extraction.lean      | .convQPosRecip _ => .star
    Soundness.lean       | convQPosRecip t => … exact Q.ltN_zero_recip _

Invariants unmoved: `extract` *does not depend on any axioms*, `soundness`
`[propext, Classical.choice, Quot.sound]`, `Tm.eval` `[propext, Quot.sound]`.

Note the same degeneracy is doing the work a third time — this route reaches
exactly the identities and order facts whose normalization collapses, and no
further. It is still not a general arithmetic rule base.

**The two rules do suffice — now checked, not predicted.**

    'HAomega.constReal_upper'   depends on axioms: [propext, Quot.sound]
    'HAomega.constReal_cauchy'  depends on axioms: [propext, Classical.choice, Quot.sound]

`constReal_upper`/`constReal_lower` derive, **inside `Deriv`**, that
`fun _ ↦ 0` is Cauchy with rate `1/(n+1)`. The footprint is the one every
derivation in this development reports, `[propext, Quot.sound]` — this is a
derivation, not a meta-level proof about one. `constReal_cauchy` then runs it
through `realCauchy_sound` to the value layer, picking up `Classical.choice`
from `soundness` as every use of soundness does.

The shape is four `eqSubst` rewrites run *backwards* from `convQPosRecip`: the
reciprocal is rewritten into its application, `0` into `0 − 0`, and each `0`
into the beta-redex that produced it, with `convBeta` supplying the redexes and
`convQSubSelf` the middle step.

**The derivation was harder than the rules.** The rules were three sites each;
this needed the weakenings normalized by hand (`simp only [Tm.wk, Tm.rename,
Ren.ext]`) before `convBeta` would unify, explicit context annotations at every
step because `Ctx.nil`'s object context is not inferable from the goal, and a
`deriv_norm` after each rewrite because `Formula.subst1` of a weakened term is
only *propositionally* equal to the term — `eqSubst` chains cleanly only once
both sides are in normal form. Worth recording, since it is the cost of every
future object-language derivation about reals, not a one-off.

Options 1 and 3 remain open and untouched; the choice between them is not
defaulted into.

### The negative half — not formalizable here, and the reason is measurable

`A₀ ⊭ EFTC2` (Myhill: a computable `C¹` function with non-computable
derivative) has been a citation throughout. Looking at it directly gives a
sharper answer than "not attempted":

**As it would be phrased here, the statement is false**, and that is proved:

    'HAomega.A0.toA1'               depends on axioms: [Classical.choice]
    'HAomega.A0.eftc2_of_unifDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]

`A₀ ⊭ EFTC2` quantifies over *procedures*, and this development has no notion
of one at the analysis layer: `A0.f : Q → Q` is an arbitrary Lean function, and
`A1`'s only content over `A0` is the datum `δ` plus a `Prop`. So whenever the
analytic content holds — `f` genuinely uniformly differentiable —
`A0.toA1` builds the `A₁`, and `eftc2_of_unifDeriv` applies `eftc2_thm` to it.
`A0.toA1_toA0` confirms the `A₀`-part is untouched, so this is a collapse of
the separation on the *same* data, not a change of subject.

The footprint of `A0.toA1` is exactly `[Classical.choice]` — nothing else. That
is the negative half's content stated in the one language this development can
state it in: **the `A₀`/`A₁` separation is a computability phenomenon, and a
model with no computability predicate cannot see it.**

**What formalizing it would take**, on the record: a model of computation
attached to the analysis layer. Either computable analysis in Mathlib, which
does not exist there, or real functions represented inside this development's
own object language, where `extract` would supply the notion of procedure. The
second fits the project but is a programme, not a task: `Deriv` has no reals,
and Myhill's `f` is built from a computably-enumerable non-computable set that
the object language cannot name. Neither is started.

So the boxed asymmetry in the manifesto's §5 still rests on a citation for its
lower half, and now the repository says precisely why.


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
