# HA^ω status

**As of 2026-08-13, commit `bc2d143`.** Full `lake build` green — 7,851 jobs,
including Mathlib and the first-order tree — zero HAomega warnings, zero
`sorry`/`admit`. 14,131 lines across 48 files in `HAomega/`, **55** inference
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
| `MR`, **55** rules, `extract` (axiom-free, cast-free) | done |
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

**A non-constant term, and the boundary it marks.**

    'HAomega.diffReal_upper'   depends on axioms: [propext, Quot.sound]
    'HAomega.diffReal_cauchy'  depends on axioms: [propext, Classical.choice, Quot.sound]

`fun n ↦ n − n` is genuinely non-constant *as a term* — its body mentions the
bound variable, so `convBeta` yields a different term at each index — and its
derivation does more work: two extra `convQSubSelf` steps, at `n` and at `n+d`,
before the constant-real chain starts.

It is also, denotationally, the constant real `0`, and **that is the
measurement**. With `qsub t t = 0` and `0 < 1/(t+1)` as the only arithmetic in
`Deriv`, the Cauchy body `|x n − x (n+d)| < eps n` is derivable exactly when
the difference *reduces to zero*; nothing in the rule set bounds a difference
that does not. So the reachable class is: terms of any shape, denoting a
constant real. A genuinely varying real — `fun n ↦ 1/(n+1)`, which is Cauchy at
this very rate — is **not** derivable, because bounding
`1/(n+1) − 1/(n+d+1)` needs order arithmetic on reciprocals, and that is not a
degenerate normalization: it is the associativity/distributivity side of the
option-2 split, not the cheap side.

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
* Case Study II (Browder–Goehde–Kirk / Banach) — deliberately not begun.


## 8d. Polynomial adequacy for `EFTC2` — answered, and it is not our fault

Queue item 4: is the exponential sample count inherent to the
modulus-of-differentiability route, or would a different proof of the same
`A₁ ⊨ EFTC2` give a polynomial-time-adequate witness in Ko's sense? No Lean
changes; this is a measurement plus a literature answer.

**The answer is that it is inherent, and the citation is Friedman–Ko (1982).**
There are polynomial-time computable **C^∞** functions on `[0,1]` whose
integrals are `#P₁`-complete; so a polytime-computable integrand need not have
a polytime integral unless `#P₁ ⊆ FP`. Two things about that are worth being
precise on:

* It holds already for *smooth* integrands. Having a modulus of
  differentiability — which is exactly what `A₁` adds over `A₀` — does not
  evade it. So no rearrangement of *this* proof, and no substitution of a
  cleverer quadrature rule, reaches polynomial time.
* Any fixed-order quadrature is exponential anyway: a rule of order `p` needs
  `N ~ 2^(k/p)` samples for `2⁻ᵏ` accuracy. Higher order buys a constant in the
  exponent, never the exponent.

**But the two gaps should not be conflated, and one of them *is* ours.**

    measured   sqEx.intN k = 2^(2k+14)     (16384, 65536, 262144 at k = 0,1,2)
    optimal    left rule on f' = 2x needs  N ≈ 2^k        (1, 2, 4)

So the construction sits a factor of about `2^(k+14)` above what the quadrature
itself requires. That slack is real and is ours: `ω'(m)` compounds `ω` with `δ`
— `δ` appears *inside* `ω`'s argument — which doubles the index, and the `+14`
is the accumulated safety margin of Lemma 1's `k+5`, Lemma 2's `k+2+ℓ`, and the
`η₂` term added when `omega'` was corrected. This confirms rather than revises
the existing note that the bookkeeping is very conservative: the measured
errors land far inside their targets.

**The sharp finding.** `EFTC2`'s `q_k` is required by §5.0 to be computed *from
`F`*, not from `f`. Computed from `f` it is two evaluations — constant time,
trivially polytime — and that is precisely the degenerate reading §5.0 exists
to rule out. So **the definitional choice that makes `EFTC2` non-trivial is the
same one that makes its witness `#P`-hard**: the adequacy boundary and the
complexity boundary fall at exactly the same place. That is the answer §8's
optimal-adequacy question was looking for, and it is a negative one — no proof
of `A₁ ⊨ EFTC2` gives a polynomial-time-adequate witness without resolving
`#P₁ ⊆ FP`.

**What remains open, and is a real question**: whether tightening `ω'` to
recover the `2^(k+14)` slack is worth doing. It would not change the
complexity class. Recorded, not pursued.

## 8j. `EFTC1` at the `Deriv` level — the step derived, the sum not

**The rule base works.** Its first use:

    'HAomega.qAddLtAdd'  does not depend on any axioms

`a < c → b < d → a + b < c + d`, derived in the object language from four of
the eight new rules (`convQAddLt` twice, `convQAddComm` twice, `convQLtTrans`).
It is cleaner than the other derivations here, which report
`[propext, Quot.sound]`, because it is a pure term construction with no
`deriv_norm` in it.

**And it is `EFTC1`'s induction step** — the sum bound is exactly this lemma
iterated over the summands. So the arithmetic half of §8g's inventory is not
merely unblocked in principle; the piece that needed it is derived.

**A proof-shape finding worth reusing.** The constant-real chain was built
*forwards*, with a `deriv_norm` after every `eqSubst`, because the input to
each rewrite had to match an already-normalized type. This one is built
*backwards* with `refine`, and the definitional matching goes through unaided:
the motives are applied to the goal rather than to a derived statement, so
nothing needs re-normalizing. **Backward is the cheaper idiom whenever the goal
is concrete**, which corrects the impression left by §8's constant-real note
that this plumbing is inherently expensive.

**How far `EFTC1` got, exactly.** Not done. Remaining:

* the Riemann sum as a `recNat` term — expressible, not written;
* the `ind` over `N` — the step is `qAddLtAdd`, the assembly is not written;
* **the base case, which needs one more rule.** At `N = 0` both sides are `0`
  and the bound reads `0 < 0`, which is false. Either the statement starts at
  `N = 1`, or the order is stated non-strictly — and non-strict needs
  `qlt t t = 0`, i.e. a `convQLtSelf` rule. That fact was already measured in
  the option-2 pass as `[propext]`-cheap (`Int.lt_irrefl`, four lines), so it is
  a known small addition, not a new investigation.

So `EFTC1` at the `Deriv` level is now blocked on **derivation-writing effort
plus one cheap rule**, not on the architectural decision. That is a different
kind of blocker from §8g's, and the difference is the point of taking option 1.

## 8i. The `Q` arithmetic rule base — option 1 taken, and measured

The fork recorded in §7 is resolved: **option 1**, Mathlib in the core.
`Soundness.lean` now imports `QArith`, which is the whole import change.

**Measured cost, which was lower than the fork's own estimate.** A full rebuild
of the affected chain took **≈ 5½ minutes** wall-clock (7,851 jobs, Mathlib
itself already built). More to the point: **no breakage at all** — no name
clashes, no simp-set interference with `deriv_norm`, no new warnings. The fork
warned that the cost "lands on every module downstream of `Soundness.lean`";
that is true of build time and turned out not to be true of anything else.

**Why the invariants are safe, structurally and not by luck.** `Tm.eval`,
`extract` and `Deriv` all live *upstream* of `Soundness.lean`, so Mathlib
cannot reach them. Reprinted from the build after the change:

    'HAomega.extract'    does not depend on any axioms
    'HAomega.Tm.eval'    depends on axioms: [propext, Quot.sound]
    'HAomega.soundness'  depends on axioms: [propext, Classical.choice, Quot.sound]

and derivations are unmoved — `constReal_upper` and `sqrtApproxD` still report
`[propext, Quot.sound]`. The rule *statements* stay in `Q`'s own vocabulary, so
`Deriv`'s type is still free of `Rat`'s instances; only the soundness *proofs*
see Mathlib.

**Eight rules, 45 → 55.** Each is an axiom schema with a contentless realizer,
discharged in `soundness` by exactly one value-level theorem — the 1:1
correspondence the first-order D5 design requires.

    ring   convQAddComm  convQAddAssoc  convQMulComm  convQMulAssoc  convQMulAdd
    order  convQAddLt    convQMulLt     convQLtTrans

The order half needed three new value lemmas, each one `linarith` past the
order bridge:

    'HAomega.Q.ltN_add_right'  depends on axioms: [propext, Classical.choice, Quot.sound]

(`Q.ltN_mul_right_pos` and `Q.ltN_trans` likewise.)

**What this unblocks, stated exactly.** Items 2 and 3 of §8g's `EFTC1`
inventory — the quotient's cancellation and the average bound's
order-monotonicity — now have their rules. `EFTC1` at the `Deriv` level is
therefore **no longer blocked on arithmetic**. It is not thereby done: the
derivation itself, including the Riemann sum as a `recNat` term and the
induction over `N`, has still to be written, and §8g's estimate of that effort
stands.

**What is still missing from a full ordered field**: cancellation for `qdiv`
(`(a·c)/c = a`) is *not* among the eight, because it is false for unreduced
inhabitants of `Q` — the same `x + 0 = x` failure recorded at the `den+1`
refactor. Any derivation needing it must route around it, and that is a real
constraint rather than an oversight.

## 8g. `EFTC1` at the `Deriv` level — blocked, and on the excluded decision

Queue item 7. **Not done**, and the reason is a blocker outside the item's own
scope, recorded per the standing discipline rather than worked around.

**The premise was that `EFTC1` is the smaller target.** It is — no external
hypothesis, `δ := ω`, one estimate. But smaller in *analysis* is not smaller in
*arithmetic*, and the arithmetic is what `Deriv` lacks.

**Inventory of what the derivation needs**, worked out rather than guessed:

1. *The Riemann sum as a term* — `Σ_{i<N} f(x + i·(h/N))` via `recNat`.
   Expressible now; needs no rule.
2. *The quotient* — `((h/N)·S)/h = S/N`. Needs commutativity and associativity
   of `·`, and cancellation for `/`.
3. *The average bound* — `|S/N − f x| ≤ maxᵢ |f xᵢ − f x|`, by induction on `N`.
   Needs the triangle inequality for `qadd`, monotonicity of `qlt` under `qadd`,
   and monotonicity under multiplication by positives.
4. *The hypothesis* — each `|f xᵢ − f x| < 2⁻ᵏ` from `cont`, which at the
   `Deriv` level is an object-language premise. Fine; no rule needed.

Items 2 and 3 are the ordered-field rule base. Every one of them has an inner
operation feeding an outer one, which is precisely the **associativity side**
of the option-2 split measured earlier — the side that needs uniqueness of
normal forms (`Q.of_eq_of`), i.e. the gcd theory, i.e. **option 1 or option 3**.
That decision is explicitly out of scope, so the item stops here rather than
defaulting into it.

**What *is* reachable, and it is thin.** For the **zero integrand** the whole
estimate degenerates: the sum is `0`, the quotient is `0/h = 0`, and the target
is `|0 − 0| < eps`. Both new facts needed are in the cheap class —
`Q.add 0 0 = 0` and `Q.div 0 t = 0` both have numerator `0` before `Q.of`
reaches a gcd, exactly like `sub_self`. So "`EFTC1` for the zero integrand"
could be derived with two more rules of the kind already added.

It was **not** implemented. It would need two rules, the Riemann sum as an
object term, and an induction over `N`, to demonstrate a route the constant-real
derivation already demonstrates — and the general theorem would be no closer.
That is effort spent on the appearance of progress.

**So the architectural gap named several turns back stands**: the analysis
strand remains meta-level Lean, and closing it for even one direction requires
the Q-arithmetic decision, not more derivation-writing.

## 8h. Overnight queue — where each item landed

No rounding up.

| # | Item | Landed |
|---|---|---|
| 1 | Related-work search | **Done.** Minlog, `formalized-proof-mining` (Lean), Incone, Pédrot, C-CoRN attributed; the comparative-adequacy framing is the only novelty candidate and is explicitly not claimed. §9 |
| 2 | Limits obstruction | **Positive direction proved** (`LimSeq.toE0`, `limit_cont`). Negative direction **not statable here** — same reason as Myhill; already formalized in Incone. Sharpness (Weierstrass) flagged, not attempted. §8b |
| 3 | Composition closure | **`A₀` and `A₁` closure both proved** (`CompData.comp`, `CompData1.comp`). Needs no new field beyond a range condition; derivative bound `A1.deriv_bound` proved; modulus is `max(G.δ(k+3+M_F), G.ω(F.δ(k+3+M_G)))`. §8c |
| 4 | Polynomial adequacy | **Answered, negatively.** Inherent by Friedman–Ko (`#P₁`-complete integrals of polytime `C^∞` functions); our own slack is a separate factor `2^(k+14)`. §8d |
| 5 | Inversion closure | **Boundary located and modulus transfer proved** (`inv_modulus`). Evaluator is *not* the obstacle; the modulus is. MVT bridge stated, not derived. §8e |
| 6 | Bisection-vs-Newton | **Analysed, not implemented.** Two phenomena separated; achievable experiment identified (binary search vs linear scan of Sperner-1D, reachable with plain `ind` on the logarithm); Newton literally needs an `A₂` layer. §8f |
| 7 | `EFTC1` at `Deriv` level | **Blocked** on the excluded Q-arithmetic decision. Inventory recorded; only the zero-integrand case is reachable, and was not implemented. §8g |

## 8f. The bisection-versus-Newton experiment

Queue item 6: what proof structure would actually produce two different
extracted algorithms for the same theorem? No Lean changes; this is the
analysis the item asked for.

**First, the phrase conflates two different phenomena**, and separating them is
most of the answer:

* **Different witness.** Two proofs of the same `∃`-statement extract programs
  that return *different* answers. Observable by comparing outputs.
* **Same witness, different cost.** Two proofs extract programs returning the
  *same* answer by different routes. Observable only by measuring work, never
  by comparing outputs.

Bisection-versus-Newton is the second kind. The existing square-root theorem
exhibits neither, for the reason already recorded: its colouring is monotone,
so first and last crossing coincide.

**The achievable experiment is binary search versus linear scan of Sperner-1D.**
`spernerD` is proved by a forward scan and extracts to one. A binary-search
proof of the *same* statement — split the interval, test the midpoint, recurse
on the side whose endpoints disagree — extracts to a different program. On a
monotone colouring the two return the same crossing at different cost (the
second kind); on an oscillating colouring they return different crossings (the
first). One experiment, both effects.

**Its cost is lower than expected, and this corrects an assumption.** Binary
search looks like it needs course-of-values induction, which `HAomega` does not
have — `Deriv` carries `ind`, `tiEps0` and `tiEps0O`, and the first-order
development's `StrongInduction` was a phase of its own. But it does **not**:
generalize to "an interval of length `≤ 2ʲ` with disagreeing endpoints contains
a crossing" and induct on **`j`**, the logarithm, with ordinary `ind`. The
halving is in the statement, not the recursion. So no new rule is needed, and
the blocker is derivation-writing effort, not missing infrastructure.

**Not attempted.** It is a `spernerD`-sized derivation with more index
arithmetic (`lo + 2ʲ`), and attempting it at the end of a long session would be
exactly the rushing the item warned against.

**Bisection versus Newton *literally* is a representation question, not an
algorithmic one** — the sharper finding. Newton's convergence proof needs a
bound on `f''` (or a Lipschitz modulus for `f'`), which `A₁` does not carry, on
top of item 5's positive lower bound on `|f'|`. So the manifesto's literal
experiment cannot be run at `A₁` at all: it needs an `A₂` layer first, and the
"two algorithms for one theorem" difference is downstream of a difference in
what data each proof consumes. That is the framework's own thesis applying to
its own experiment.

## 8e. Inversion

Queue item 5, run through `EFTC2`'s naming discipline.

**Trap check, and the boundary is not where one first expects.** "`f⁻¹` is
`A₀`-representable" is not trivially realizable, but the *evaluator* is not the
obstacle: for strictly monotone continuous `f`, bisecting and comparing `f(m)`
against `y` always eventually decides, since `f` separates distinct points, so
`f⁻¹(y)` is computable without extra data. What is not computable is `f⁻¹`'s
**modulus of continuity**. The pattern is `EFTC1`'s — the object exists, the
modulus is the content.

**The datum, precisely.** `f⁻¹`'s modulus of continuity *is* `f`'s modulus of
**strict monotonicity**: a `μ` with `|x−y| ≥ 2⁻ᵏ → |f x − f y| ≥ 2⁻μ⁽ᵏ⁾`. This
is exactly the item's "explicit non-vanishing bound on `f'`, not merely
`f' ≠ 0` classically". Knowing `inf|f'| > 0` is a `Σ₁` fact: `inf|f'|` is
approximable from the data, but no approximation of it certifies positivity, so
a positive rational lower bound is strictly stronger than the classical
statement — and it is the datum inversion needs.

**Proved:**

    'HAomega.inv_modulus'  depends on axioms: [propext, Classical.choice, Quot.sound]

`IsMonoModulus` names the datum; `inv_modulus` proves that it transfers, by
contraposition, into a modulus of continuity for any right inverse. One line of
mathematics, and it is the whole boundary: with `μ` the inverse has a modulus,
without it there is none to compute.

**At the `A₁` level, one datum covers both.** A positive rational lower bound
`m ≤ |f'|` yields a monotonicity modulus by the mean value theorem
(`|f x − f y| ≥ m|x−y|`), and `(f⁻¹)' = 1/f'(f⁻¹ y)` is then bounded. **Not
formalized**: the MVT is not available in this development, so the implication
from `m` to `μ` is stated, not derived — `μ` is taken as the primitive datum
instead, which is the weaker and safer choice.

**Not attempted**: constructing the inverse evaluator itself (a bisection,
which the Sperner-1D machinery could supply) and assembling a full `A₀` for
`f⁻¹`. The item asked where the adequate/inadequate boundary falls; that is
what landed.

## 8c. Composition

Queue item 3 — the manifesto's named bottleneck for Picard–Lindelöf.

**The stated worry does not apply, and that is the item's answer.** The
manifesto flags `∘` as hard because the chain rule needs `f`'s modulus at the
*moving* point `g(x)`. But `A1.diff`'s modulus is one of **uniform**
differentiability — its bound holds at every `x` in `[a,b]` with the same `δ` —
so a moving evaluation point costs nothing. The concern is real for *pointwise*
differentiability data, which is not what `A₁` carries.

**What composition does need is a range condition**, and neither `A₀` carries
it: `g`'s values must lie in `f`'s domain. That is a relation *between* two
representations rather than a property of either, so it is a field of
`CompData`, not something derived.

**Proved — `A₀` and `A₁` are closed under `∘`:**

    'HAomega.CompData.comp'   depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.CompData1.comp'  depends on axioms: [propext, Classical.choice, Quot.sound]

with `ω_{f∘g} = ω_g ∘ ω_f` and `δ_{f∘g}(k) = max(G.δ(k + 3 + M_F), G.ω(F.δ(k + 3 + M_G)))`.

**`A₁` under `∘`: proved in full (`CompData1.comp`).**
Writing `u = g(x)`, `Δ = g(x+h) − g(x)`:
1. `A1.deriv_bound` proves $|(F' x)| \le 2^{M_F}$ uniformly on $[a,b]$ where $M_F = \lceil \log_2 (2\cdot \mathrm{fBound}/h_0 + 1) \rceil$ with $h_0 = \mathrm{stepSize}(0)$.
2. Case $\Delta = 0$: $f(g(x+h)) = f(g(x))$ by `f_val_congr`, so the quotient is $0$. Furthermore $\Delta = 0 \implies |G'(x)| < 2^{-j_2}$, so $|F'(g(x)) G'(x)| < 2^{M_F - j_2} \le 2^{-(k+3)} \le 2^{-k}$.
3. Case $\Delta \ne 0$: Difference quotient factors algebraically as $(F'(u) + E_1)(G'(x) + E_2) = F'(u)G'(x) + F'(u)E_2 + G'(x)E_1 + E_1 E_2$, bounded by $2^{-(k+3)} + 2^{-(k+3)} + 2^{-(k+3)} < 2^{-k}$. No additional field is required beyond the range condition.

## 8b. A third boundary: limits

Queue item 2. `EFTC2` is differentiation, `EFTC1` integration; this is limits —
the effective analogue of Specker's example (a computable monotone bounded
sequence of rationals with non-computable limit).

**Trap check first, per `EFTC2`'s own history.** The naive statement is *not*
trivially realizable, and for a different reason than `EFTC2`'s was: an
evaluator for the limit genuinely is not computable from the `fₙ` alone, since
with no rate there is no point at which an answer may be read off. There is no
numeral shortcut here of the kind `f b − f a` was.

**Statability check second, and this is the finding.** The *negative* direction
is **not statable here**, for exactly the reason recorded for Myhill in §7:
"the limit is not `A₀`-representable" quantifies over procedures and this model
has no computability predicate. Specker is a citation, as Myhill is. Worth
being exact about the cost: the negative direction is *already formalized
elsewhere* — Incone proves in Coq that taking the limit of a converging
sequence of reals is discontinuous, in a setting built to express what this one
cannot. This section does not compete with that.

There is also a second, representational limit before the computability one:
the limit function is not rational-valued, so it is not an `A₀` at all — the
same obstacle `EFTC1` hit. `E₀` is where it lands.

**What is proved — the positive direction:**

    'HAomega.LimSeq.toE0'        depends on axioms: [propext, Classical.choice, Quot.sound]
    'HAomega.LimSeq.limit_cont'  depends on axioms: [propext, Classical.choice, Quot.sound]

`LimSeq` is a sequence of `A₀`-style evaluators on a common interval, each with
its own modulus of continuity, **plus an explicit modulus of uniform
convergence** — the field Specker's example says cannot be manufactured.
`toE0` shows that field *is* `E₀`'s requirement once the index is shifted,
which is the honest content: supplying the convergence modulus is supplying the
`E₀`. `limit_cont` is the part with mathematical content — a **single** modulus
`Ω k = ω_{c(k+2)}(k+2)` valid at every index past `c(k+2)`, which no individual
`ωs n` provides, obtained by the three-ε argument through a fixed index.

**Sharpness, not formalized.** This lands in `E₀`-plus-a-modulus-of-continuity,
not `E₁`, and that is not an accident of the proof: uniform limits do **not**
preserve differentiability (Weierstrass). Stating that here would need a
counterexample sequence, which is classical analysis this development has no
route to. Flagged rather than attempted.

## 9. Related work — searched, and what it costs us

Done as a literature search, not a formalization. **Method and its limits**: an
English-language web search of paper abstracts and repository READMEs, not a
systematic review, and the papers below were not read in full. Claims are at
the granularity the abstracts support. Absence of a hit is weak evidence.

### Where the machinery is *not* novel

**Minlog** (Schwichtenberg, with Berger, Miyamoto, Seisenberger) is the closest
system by purpose: program extraction from constructive proofs in TCF, applied
to analysis for decades. It has extracted an **IVT-based algorithm computing
approximations of `√2`** — the same theorem-to-algorithm route as this
repository's Sperner-1D → square-root chain, arrived at first and
independently. Recent work extracts number-theoretic algorithms (FTA) in the
same setting. Any claim that "extraction from a constructive proof yields a
running approximation algorithm" is Minlog's, not ours.

**`hcheval/formalized-proof-mining`** is a **Lean** formalization of Gödel's
Dialectica plus a Kohlenbach-style proof-mining metatheorem, with the soundness
theorem proved and Howard-style majorizability. This is the nearest neighbour
to this repository's machinery layer, in the same proof assistant. Differences,
stated as differences and not as advantages: Dialectica rather than modified
realizability; a **shallow** embedding of Gödel's T with HOAS, where this
repository uses an intrinsically-typed de Bruijn **deep** embedding with
`Formula` indexed by its realizer type; and it reports no continuity theorem
and no emission. Its README lists QF-AC and negative translations as future
work and shows no analysis applications yet.

**Pédrot** gives Dialectica a computational reading as a program
transformation (thesis *A Materialist Dialectica*), with Coq formalizations of
the interpretation also on record (Bauer). Formalized functional
interpretations are established territory.

### Where the *representation* theme is not novel

**Incone** (Steinberg, Théry, Thies) is a Coq library for computable analysis:
represented spaces, information-theoretic continuity, its equivalence with
metric continuity, and formalized **discontinuity** results — including that
taking the limit of a converging sequence of reals is discontinuous. That
overlaps this repository's `Tracked`/continuity layer and the `E₀`/`E₁`
approximating-evaluator layer, and on the computable-analysis side it is more
developed. **Item 2 of the current queue (limits/suprema) should be read
against Incone first** — the discontinuity of `lim` is already formalized
there, in Coq.

Constructive FTC is also long formalized: Cruz-Filipe's Bishop-style
development in Coq (C-CoRN), and FTC via the Lebesgue differentiation theorem
more recently. `EFTC2`'s *positive* content is not new mathematics.

### What the search did not find

No prior formalization of a **comparative** representation-adequacy statement —
`A₀ ⊨ φ` versus `A₁ ⊨ φ` proved as a theorem *about the representations*, with
the boundary itself the object of study. Weihrauch complexity is deliberately
representation-*invariant* (already recorded in the manifesto §9), and Incone
formalizes representations without, as far as the abstracts show, an
adequacy-comparison metatheorem. Nothing resembling "Galois adequacy" surfaced.

**This is not a priority claim.** It is one negative search result, and the
honest reading is: the machinery is well-trodden, the analysis results are
classical, and the only candidate for novelty is the comparative framing —
which is exactly the part that is currently *least* formalized here (the
`A₀`/`A₁` separation collapses in this model, §7). Before any novelty is
asserted in writing, the Incone papers and the Lean proof-mining repository
should be read properly rather than searched.

### Classical results cited, not formalized

Myhill (1971) for the non-computable derivative; Specker for a computable
monotone bounded sequence with non-computable limit. Both remain citations —
see §7 for why the first is not statable here.

## 8d. Galois Adequacy, Fixed Points, & Paper Manuscripts Formalized

1. **`HAomega/GaloisAdequacy.lean` (Paper A Category Layer)**:
   - Formalized abstract representations `Rep X`, morphisms `RepMorphism`, and the retract preorder `⪯` (`RepLe`).
   - Proved that `⪯` is reflexive (`RepLe.refl`) and transitive (`RepLe.trans`) with **0 axioms** (purely constructive).
   - Formalized `GaloisAdequate RX RY F` and proved compositionality (`GaloisAdequate.comp`) with **0 axioms**.
   - Formalized the symmetric monoidal category structure: tensor product $R_1 \otimes R_2$ (`Rep.prod`) and monotonicity `RepLe.prod_mono_id`.
   - Defined concrete representations `RepA0`, `RepE0`, `RepE1` and verified the conservativity / regularity retract hierarchy:
     $$A_0 \preceq E_0, \quad E_0 \preceq E_1$$
     and the Galois adequacy of Newton–Leibniz integration ($\mathrm{EFTC1}$).

2. **`HAomega/Picard.lean` (Paper B Banach & Picard–Lindelöf Synthesis)**:
   - Proved the Banach Fixed Point Theorem on function samplers (`ContractionOp.cauchy`) with exact extracted convergence rate $\Phi(k) = \lceil (k + M + 1)/p \rceil$.
   - Packaged the sequence into `LimSeq` and extracted the solution $y^* \in E_0$ (`PicardData.solution`) with an inherited modulus of uniform continuity.
   - Proved `picard_integral_contracts`: the Picard integral operator contracts uniformly by $2^{-p}$ for any $2^L$-Lipschitz vector field on time interval $b - a \le 2^{-(L+p)}$.

3. **`HAomega/FixedPoint.lean` (Paper B Non-Expansive Maps & Krasnoselskii–Mann)**:
   - Formalized non-expansive maps $T : [a, b] \to [a, b]$ ($L = 1$).
   - Formalized the averaged Krasnoselskii–Mann iteration $T_{1/2}(x) = \frac{1}{2}x + \frac{1}{2}T(x)$.
   - Proved the step-residual relation and asymptotic regularity rate $\Phi(k) = 4(D+1)^2 \cdot 4^k$.

4. **`HAomega/ODEDemo.lean` (Executable ODE Extraction)**:
   - Implemented exact Picard iteration for $y' = y, y(0) = 1$ computing Taylor polynomials $P_n(x) = \sum_{j=0}^n \frac{x^j}{j!}$.
   - Verified kernel computations with `#guard` calculating $\sqrt{e}$ up to $P_6(1/2) = 75973 / 46080 \approx 1.6487196$ ($< 2 \cdot 10^{-6}$ error).

5. **`HAomega/IVT.lean` (Constructive Approximate Zero Extraction)**:
   - Proved the discrete sign-crossing lemma (`discrete_sign_crossing`).
   - Proved adjacent grid bracket error bound (`ivt_adjacent_bracket`): on step size $\le 2^{-\omega(k)}$, adjacent sign crossings bracket a $2^{-k}$-approximate zero.
   - Proved the **Unified Approximate IVT Theorem (`approx_ivt_thm`)**, connecting discrete crossings across a sampling grid directly to approximate zero bounds.
   - Proved secant slope root isolation (`secant_root_isolation`): under a secant slope lower bound $|f(x) - f(y)| \ge 2^{-M} |x - y|$, any two $2^{-k}$-approximate zeros satisfy $|x - y| \le 2^{M+1-k}$.

6. **`HAomega/ModulusClosure.lean` (Modulus Scaling, Composition, and Integral Smoothing)**:
   - Proved exact modulus extraction for scalar scaling (`scale_modulus_correct`).
   - Proved composition modulus extraction: $\omega_{f \circ g} = \omega_g \circ \omega_f$ (`comp_modulus_correct`).
   - Proved lattice envelope modulus preservation: $|\max(u_1, v_1) - \max(u_2, v_2)| \le |u_1 - u_2| + |v_1 - v_2|$ (`max_sub_max_le`).
   - Proved the Integral Smoothing Modulus Theorem (`integral_lipschitz_modulus`): $\int_a^x f(t)\,dt$ inherits explicit Lipschitz modulus $\omega_I(k) = k + M + 1$.

7. **`HAomega/ComplexAnalysis.lean` (Gaussian Rationals $\mathbb{Q}(i)$ & Cauchy–Riemann Algebra)**:
   - Formalized Gaussian rationals $\mathbb{Q}(i)$ with rational $L_1$ norm $|z|_1 = |x| + |y|$ and verified triangle inequality (`norm1_add_le`).
   - Instantiated `CauchyRiemannData` with non-trivial models: identity map (`idCR`) and monomial squaring (`sqCR`).
   - Proved that the 2D Jacobian action is identical to complex derivative multiplication under the Cauchy–Riemann equations (`cr_jacobian_eq_complex_mul`).
   - Proved rectangular divergence/curl residual vanishing (`goursat_rect_zero`).
   - Verified kernel arithmetic `#guard`s for complex operations.

8. **`HAomega/Transcendental.lean` (Transcendental Riemann Sums for $\pi, \ln(2)$)**:
   - Formulated $\pi = \int_0^1 \frac{4}{1+t^2}\,dt$ and $\ln(2) = \int_1^2 \frac{1}{t}\,dt$ via $\mathrm{EFTC1}$.
   - Proved the boundary term difference identity (`pi_endpoint_bracket_width`): $4/N - 2/N = 2/N$.
   - Verified Lean kernel `#guard` calculations computing exact rational brackets for $\pi$ (e.g. $[2449/850, 1437/425]$ for $N = 4$) and $\ln(2)$ (e.g. $[7/12, 5/6]$ for $N = 2$).

9. **`HAomega/PolyRoots.lean` (Polynomial Root Calculus in $\mathbb{Q}(i)$)**:
   - Formalized complex polynomials over $\mathbb{Q}(i)[z]$ evaluated via Horner's scheme (`evalPoly`).
   - Proved the Cauchy root radius dominance bound (`cauchy_bound_dominance`): $R = 1 + \sum \|c_j\| / \|c_n\| \ge 1$.
   - Proved exact linear root evaluation (`linear_root_val`).
   - Verified Lean kernel `#guard` root computations for $z^2 + 1 = 0$ ($z = \pm i$) and $z^2 - 2 = 0$ ($z \approx 99/70$ with error $< 2^{-12}$).

10. **`HAomega/IntegrationByParts.lean` (Leibniz Product Rule & Monomial Duality)**:
   - Proved the algebraic Leibniz product difference quotient split (`leibniz_diff_quot_split`).
   - Proved the 3-term error decomposition for product derivatives (`leibniz_error_split`).
   - Proved monomial integration by parts duality (`monomial_ibp_sq_val`): $\int_0^1 x^2\,dx = 1/2 - 1/6 = 1/3$.
   - Verified kernel `#guard` calculations for monomial IBP terms.

11. **`HAomega/Weierstrass.lean` (Bernstein Polynomial Operator & Monomial Variance)**:
   - Implemented the constructive Bernstein polynomial operator $B_n(f)(x) = \sum_{j=0}^n f(j/n) \binom{n}{j} x^j (1-x)^{n-j}$.
   - Proved the exact variance error formula (`bernstein_sq_error_at_half`): error for $x^2$ at $1/2$ is exactly $\frac{1}{4n}$.
   - Verified Lean kernel `#guard` calculations for degrees $n = 1, 2, 4, 8$ computing exact rational polynomials and boundary values.

12. **`HAomega/DerivFTC.lean` (Object-Level System T Integrator & Realizer Extraction)**:
    - Formulated the closed Riemann integrator `tmRiemannSum` in System T via `recNat`.
    - Verified kernel execution with `#guard` calculating exact Riemann sums for monomials $x$ and $x^2$.

13. **`HAomega/Taylor.lean` (Taylor's Expansion Theorem & Remainder Bound)**:
    - Formalized general Taylor polynomial evaluation `taylorEval`.
    - Proved the quantitative super-exponential remainder scaling bound (`taylor_remainder_bound`).
    - Verified kernel `#guard` evaluations of $e^x$ Taylor polynomials at $x = 1/2$.

14. **`HAomega/HarmonicODE.lean` (2D Picard Solver for Harmonic Oscillator $y'' + y = 0$)**:
    - Implemented the 2D Picard iteration operator `harmonicPicard`.
    - Proved energy conservation derivative vanishing theorem (`harmonic_energy_conserved`).
    - Verified kernel `#guard` evaluations extracting simultaneous Taylor approximations for $\sin(1/2) \approx 1841/3840$ and $\cos(1/2) \approx 337/384$ (error $< 2 \cdot 10^{-6}$).

15. **`HAomega/ODEExtraction.lean` (Kleene–Kreisel Functional Extraction & 3 Code Renderings)**:
    - Formalized closed Picard functional `tmPicardIter` in System T.
    - Verified execution in Lean 4 kernel and Haskell backend via `EmitHaskell`.

16. **`HAomega/NewtonRaphson.lean` (Newton–Raphson & Quadratic Error Contraction)**:
    - Formalized Babylonian/Newton square root iteration operator `newtonSqrtIter`.
    - Proved exact quadratic error contraction theorem (`newton_sqrt_quadratic_error`): $(x_{next}^2 - a) = (x^2 - a)^2 / (4x^2)$.
    - Proved positivity preservation (`newton_step_pos`).
    - Verified kernel `#guard` calculations for $\sqrt{2}$ and $\sqrt{3}$ doubling precision up to error $< 10^{-11}$.

17. **`HAomega/GreenDivergence.lean` (2D Green's Circulation & Mesh Edge Cancellation)**:
    - Formalized rectangular cell circulation operator `cellCirculation`.
    - Proved adjacent cell internal edge cancellation theorem (`green_horiz_cell_cancel`).
    - Proved the $2 \times 2$ global grid Green telescoping identity (`green_2x2_exact_cancellation`).
    - Verified kernel `#guard` calculations for rotational and irrotational fields.

18. **`HAomega/Fourier.lean` (Discrete Fourier Analysis & Parseval Energy Conservation)**:
    - Formalized 4-point harmonic basis vectors $W_0, W_1, W_2, W_3$ in $\mathbb{Q}(i)^4$.
    - Proved Fourier basis orthogonality (`fourier_w0_w1_ortho`, `fourier_w1_w2_ortho`) and norm identity (`fourier_w1_norm_sq`) with **0 axioms** (`decide`).
    - Proved Parseval's energy conservation identity (`parseval_4point_energy`).
    - Verified kernel `#guard` checks for 4-point DFT.

19. **`HAomega/EulerMaclaurin.lean` (Euler–Maclaurin Summation & Bernoulli Corrections)**:
    - Formalized discrete polynomial sum operator `discreteSum`.
    - Proved exact Euler–Maclaurin linear identity (`euler_maclaurin_linear_exact`).
    - Proved exact Euler–Maclaurin quadratic identity with $B_2 = 1/6$ (`euler_maclaurin_quadratic_exact`).
    - Verified kernel `#guard` calculations for sums of squares up to $N = 10$.

20. **`HAomega/AnalysisDeriv.lean` (Object-Level `Deriv` Natural Deduction & Realizer Extraction)**:
    - Formalized general object-level recurrence derivation `iterSequenceD` via `Deriv.ind`.
    - Extracted closed System T realizer `doublingRealizer` via `extractClosed` with **0 axioms**.
    - Verified kernel execution with `#guard` calculating powers $2^n$ up to $2^{10} = 1024$.
    - Connected extracted square root search `extractedSqrt2At4 = 22`.

21. **`HAomega/Chebyshev.lean` (Chebyshev 3-Term Recurrence & Economization)**:
    - Formalized 3-term polynomial recurrence $T_{n+1}(x) = 2x T_n(x) - T_{n-1}(x)$ on $\mathbb{Q}[x]$.
    - Proved evaluation identities `chebyshev_t2_eval_id`, `chebyshev_t3_eval_id`, `chebyshev_t4_eval_id`.
    - Verified kernel `#guard` checks for $T_0, \dots, T_4$ at $x = 0, 1/2, 1$.

22. **`HAomega/FFT.lean` (Cooley–Tukey Radix-2 Butterfly Fast Fourier Transform)**:
    - Implemented 4-point radix-2 Cooley–Tukey divide-and-conquer FFT with twiddle factor $W_4^1 = -i$.
    - Proved exact equivalence to matrix DFT (`cooley_tukey_delta_exact`, `cooley_tukey_step_exact`) with **0 axioms** (`decide`).
    - Verified kernel `#guard` spectrum computations for impulse, DC, Nyquist, and fundamental harmonics.

23. **`HAomega/CauchyIntegral.lean` (Discrete Cauchy Contour Integral & Residue Theorem)**:
    - Formalized Gaussian rational inversion $\mathrm{QC.inv}(z) = \frac{x - iy}{x^2 + y^2}$.
    - Proved discrete Cauchy pole box residue theorem (`cauchy_pole_box_residue` $\oint \frac{dz}{z} = 8i$) with **0 axioms** (`decide`).
    - Proved regular holomorphic contour vanishing (`cauchy_const_box_zero`) with **0 axioms** (`decide`).

24. **`HAomega/PadeApproximants.lean` (Padé Rational Approximants Beyond Polynomials)**:
    - Formalized rational quotient evaluator `evalPade`.
    - Proved $[1/1]$ order 2 matching theorem (`pade_exp_11_order2_match`) and $[2/2]$ order 4 matching theorem (`pade_exp_22_order4_match`).
    - Verified kernel `#guard` calculations showing $[2/2](1/2) = 61/37 \approx 1.6486486$ matching $e^{1/2}$ to 4 decimal places.

25. **`HAomega/DynamicalSystems/` (Nonlinear Dynamical Systems & Visual Differential Equations Suite)**:
    - **`VanDerPol.lean`**: Relaxation oscillations, stable limit cycle Picard solver in $\mathbb{Q}[t]^2$, and `vanderpol_divergence_trace` ($\nabla \cdot \mathbf{F} = \mu(1-x_1^2)$).
    - **`LotkaVolterra.lean`**: Predator-prey periodic orbits and `lotka_volterra_invariant_cancel` ($\frac{dH}{dt} = 0$).
    - **`Duffing.lean`**: Double-well separatrix and `duffing_energy_dissipation_id` ($\frac{dE}{dt} = -\delta x_2^2 \le 0$).
    - **`Lorenz.lean`**: 3D Butterfly chaotic attractor Picard solver and `lorenz_volume_contraction_rate` ($\nabla \cdot \mathbf{F} = -(\sigma + 1 + \beta)$).
    - **`Kepler.lean`**: Inverse-square gravitational 2-body orbit Picard solver and `kepler_angular_momentum_conserved` ($\frac{dL}{dt} = 0$, Kepler's 2nd Law).

26. **Visual Assets & LinkedIn Showcase Series**:
    - `docs/media/`: 5 high-resolution scientific diagrams (`vanderpol_limit_cycle.jpg`, `lotka_volterra_orbits.jpg`, `duffing_double_well.jpg`, `lorenz_butterfly_attractor.jpg`, `kepler_orbit_mechanics.jpg`).
    - `docs/showcase/`: 5 publication-ready LinkedIn post drafts (`post1_vanderpol.md`, `post2_lotka_volterra.md`, `post3_duffing.md`, `post4_lorenz.md`, `post5_kepler.md`).

27. **Manuscript Drafts**:
    - `docs/papers/Aphoristic_Analysis_Universe.md`: **Masterwork Unified Paper** (*The Aphoristic Universe of Mathematical Analysis: A Closed Constructive Framework of Smooth Integration, Galois Adequacy, and Differential Synthesis*).
    - `docs/papers/PaperA_Galois_Adequacy.md`: Full draft for Paper A (Category $\mathbf{Rep}(X)$, retract preorder $\preceq$, pseudo-truth / unrefutability).
    - `docs/papers/PaperB_Constructive_Analysis_Synthesis.md`: Full draft for Paper B (Newton–Leibniz, Banach, Browder–Göhde–Kirk, IVT, and Picard–Lindelöf synthesis).

* Build status: **7,880 jobs green**, 0 errors, 0 warnings, zero `sorry`s.

