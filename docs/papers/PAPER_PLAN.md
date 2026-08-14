# Plan: a paper on the analysis results

**Status:** planning document, not a draft. Written against the repository as
measured in `CLAIMS_AUDIT.md` §§0–11. Every artifact named below has been
verified to exist and to have the footprint stated. Nothing here may be written
up before the P0 items in §5 are closed.

---

## 1. The thesis

The repository has, without quite saying so, built a **calibration framework**
for constructive analysis. It does not ask *"is analysis constructive?"* — that
question is a century old and settled in several directions. It asks a sharper
and more mechanizable question:

> **How much data must a representation of a real function carry before a given
> classical theorem becomes provable about it?**

The answer is a *ladder* of representations, and the classical theorems sort
themselves along it. That sorting is the paper.

Three measured facts carry the argument:

1. **Integration is cheap.** `eftc1 (A : A0) : EFTC1Claim A` — the first
   fundamental theorem holds with *only* a modulus of uniform continuity, with
   `δ := ω`. No derivative data.
2. **Differentiation is expensive.** `eftc2_thm (A : A1) : EFTC2Claim A` — the
   second fundamental theorem needs `A₁`, which carries a modulus of
   differentiability `δ` and derivative data `diff`.
3. **The gap between them is exactly `Classical.choice`.**
   `A0.toA1 (A : A0) (h : HasUnifDeriv A) : A1` is `noncomputable` with
   footprint **exactly `[Classical.choice]`**, and `eftc2_of_unifDeriv` shows
   EFTC2 becomes provable once choice supplies the missing datum.

The unifying observation, which recurred independently across limits,
inversion, integration and composition:

> **The object is never in doubt. The modulus is the content.**

Constructively the integral, the limit and the inverse all *exist* — what
varies from theorem to theorem is the quantitative data needed to compute them
to a given precision. A representation is exactly a choice of which moduli to
carry, and the calibration is the map from theorems to minimal representations.

### 1.1 The methodological contribution

The measuring instrument is unusual and is worth stating as a contribution in
its own right: **`#print axioms` used quantitatively.**

`A0.toA1`'s footprint is not incidental bookkeeping. It says that in this
model, the step from "a derivative exists uniformly" to "here is the modulus"
is *precisely* the strength of choice — no more, no less. Myhill proved there
is a genuine computability obstruction there. This development cannot restate
Myhill (see §3), but it can **exhibit the obstruction as an axiom dependency**,
mechanically, in a way that is checked on every build.

That is a reusable technique: in a development whose core is axiom-free by
construction, the axiom footprint of a bridging lemma becomes a measurement of
how non-constructive the bridge is.

---

## 2. What the paper can claim, with the artifact behind each claim

Every row is verified. Footprints are as measured in `CLAIMS_AUDIT.md` §2, §11.

| Claim | Artifact | Footprint |
|---|---|---|
| EFTC1 holds at `A₀`, `δ := ω` | `eftc1` | `[propext, Classical.choice, Quot.sound]` |
| EFTC2 holds at `A₁`, both conjuncts | `eftc2_thm` (via `lemma1`, `lemma2`) | same |
| The `A₀`→`A₁` bridge costs exactly choice | `A0.toA1`, `eftc2_of_unifDeriv` | **exactly `[Classical.choice]`** |
| `∫f` is `E₀`- and `E₁`-adequate | `A0.intE0`, `A0.intE1` | same |
| The layers are conservative | `A1.toE1`, `A0.toE0` | same |
| Uniform limits land in `E₀`, with modulus | `LimSeq.toE0`, `limit_cont` | same |
| `A₀` is closed under composition | `CompData.comp` | same |
| Inversion, given a monotonicity modulus | `inv_modulus` | same |
| Reals are derivable *inside* the object language | `constReal_upper/lower`, `diffReal_upper` | `[propext, Quot.sound]` |
| Object-language reals are sound | `realCauchy_sound` | `[propext, Classical.choice, Quot.sound]` |
| **Proof → realizer → running program, axiom-free** | `doublingDeriv` → `extractClosed` → `Tm.eval` = 2ⁿ | **no axioms at all** |
| The core extractor is axiom-free | `extract`, `fibRealizer` | no axioms |

### 2.1 The limitative results — do not bury these

Negative and limitative findings are usually the most durable part of a paper
like this, and this repository has unusually crisp ones:

- **Polynomial adequacy for EFTC2 is unreachable.** Friedman–Ko: there exist
  polytime-computable **C^∞** functions with `#P₁`-complete integrals. Since it
  bites already for smooth integrands, carrying a modulus of differentiability
  does not evade it. Cite as a *limit on the whole programme*, not a defect.
- **This construction's own slack is separable from that.** `sqEx.intN =
  2^(2k+14)` against an optimal `≈2^k` — about `2^(k+14)` of overhead that is
  ours, not the complexity class's. Reporting both is what makes the first
  citation honest.
- **Baire-space continuity does not transfer to metric moduli.** `HasMod`
  measures how much of an *oracle* a functional inspects; `ω`/`δ` are metric
  moduli on `ℚ`. **No lemma transfers**, and the modulus metatheorem is
  unproved with two recorded obstructions (arrow types need a Kleene associate;
  `tiRec` has no compositional bound). This is a real negative result about
  the higher-type layer and should be stated as one.
- **`qdiv` cancellation is false** for unreduced inhabitants of `Q`. Small, but
  it is the kind of thing that makes a formalization paper trustworthy.

---

## 3. What the paper must not claim

These are hard constraints, each traceable to a measurement.

1. **Not "`A₀ ⊭ EFTC2`".** Myhill's negative half is **not statable** here: it
   quantifies over *procedures* and this model has no computability predicate.
   The correct sentence is *"the axiom footprint exhibits the gap Myhill
   proved; it does not reprove it."* Anything stronger is false.
2. **Not "`E₁ ≅ A₁`".** Not proved, and false in the direction that matters:
   `A₁`'s evaluator is exactly rational-valued and `∫f` is not. That asymmetry
   is *why* the `E` layer exists; asserting the isomorphism erases the paper's
   own subject.
3. **Not "0 axioms".** True of `extract`, `fibRealizer`, the `GaloisAdequacy`
   preorder core and the `AnalysisDeriv` chain. False of every analysis
   theorem. Use the true and stronger statement: the core is axiom-free, every
   *running* extract is `[propext, Quot.sound]`, and choice enters only through
   `soundness`.
4. **Not a novelty claim for constructive FTC, IVT, or modulus extraction.**
   All have prior art (§6). The novelty candidate is the *comparative
   calibration*, and even that is not safe until §6 is done.
5. **Not "the Picard operator is extracted".** It is hand-written as
   `tmPicardIter` and compiled by the emitter. What *is* extracted is
   `doublingRealizer`. Claim that instead — it is axiom-free, which is stronger.

---

## 4. Section outline

**Title (working):** *How Much Data Does a Theorem Need? Representation
Adequacy for Constructive Analysis, Mechanized in Lean 4*

**§1. Introduction.** The calibration question. The three headline facts from
§1 above. Explicit statement of what is and is not proved — put the honesty up
front; it is a selling point in this genre.

**§2. The setting.** HA^ω, modified realizability, intrinsically-typed System T
(`Tm`), `Deriv`, `extract`, `soundness`. Keep short; cite rather than re-derive.
State the standing axiom discipline here — it is the measuring instrument, so
it belongs in the setup, not an appendix.

**§3. The representation ladder.** `A₀`, `A₁ extends A₀`, `E₀`, `E₁ extends E₀`.
What each carries and *why*: `A` = exactly rational-valued evaluator, `E` =
approximating, because `∫f` of a rational-valued function is not
rational-valued. This section motivates the whole hierarchy from one honest
failure, which is the best possible motivation.

**§4. Calibration results.**
- 4.1 EFTC1 at `A₀` (`eftc1`), with `δ := ω` — integration is cheap.
- 4.2 EFTC2 at `A₁` (`eftc2_thm`, `lemma1`, `lemma2`) — differentiation is not.
- 4.3 The bridge and its price (`A0.toA1`, `eftc2_of_unifDeriv`). **The
  flagship.** Present the footprint as the measurement; state the Myhill
  caveat from §3.1 in the same breath.
- 4.4 Where the integral lands (`A0.intE0`, `A0.intE1`) and why not `A₁`.
- 4.5 Closure: composition (`CompData.comp`), limits (`LimSeq.toE0`,
  `limit_cont`), inversion (`inv_modulus`) — and the honest gap that inversion
  takes `μ` as primitive because the MVT is absent.

**§5. The category of representations.** `Rep`, `RepMorphism`, `RepLe` (`⪯`),
`GaloisAdequate`; `RepA0`/`RepA1`/`RepE0`/`RepE1` and the retract order among
them. **This section cannot be written until P0.2 and P0.3 (§5 below) are
done** — at present the order is announced but no concrete instance is proved.

**§6. From proof to program.** `AnalysisDeriv`: `Deriv.ind` derivation →
`extractClosed` → `Tm.eval` → 2ⁿ, **axiom-free end to end**. Then the emitter
(`EmitHaskell`, `tmPicardIter`, the Haskell output) presented honestly as
compilation of a hand-written term. The Picard/Taylor computation as a worked
demonstration.

**§7. Limitative results.** §2.1 above, as a section rather than a footnote.

**§8. Related work.** Mandatory; see §6 below. Cannot be written from memory.

**§9. What is not proved.** A standing section listing §3's items plus the
open gaps. This repository already keeps such a record; publishing it is a
differentiator, not an admission.

---

## 5. Gaps to close before writing

### P0 — blocking

| # | Item | Why blocking | Rough size |
|---|---|---|---|
| P0.1 | **Read the related work** (§6) | §9 of STATUS explicitly forbids the novelty claim until this is done. The paper's contribution is a *positioning* claim; it cannot be made from memory. | days, not code |
| P0.2 | **Prove one concrete `⪯`** — e.g. `RepE1 ⪯ RepE0`, by supplying the section `E1_to_E0_morphism` lacks | §5 of the paper is about an order of which **no instance is currently proved**. Without this the central object does not exist. | small–medium; `RepRetract` needs morphism + section + `retract_id` |
| P0.3 | **Define `RepA1`, place it in the order** | The flagship result is the `A₀`/`A₁` gap. It is currently *invisible* inside the framework meant to organize representations. | small, given P0.2's pattern |

### P1 — strongly desirable

| # | Item | Payoff |
|---|---|---|
| P1.1 | `A₁` closure under `∘` | Analysed already: needs **no new field**, only a range condition. Completes §4.5's closure story. |
| P1.2 | Extend `AnalysisDeriv` beyond 2ⁿ — derive an *analysis* statement in `Deriv` and extract it | Turns §6 from "the pipeline works on a toy" into "the pipeline works on the paper's subject". Highest scientific value of any item here. |
| P1.3 | `#print axioms` in `AnalysisDeriv.lean` | Its footprint is the paper's strongest single number and is currently measured only externally. One line. |

### P2 — optional

| # | Item | Note |
|---|---|---|
| P2.1 | EFTC1 at `Deriv` level | Blocked only on one cheap rule (`qlt t t = 0`, measured `[propext]`); the induction step `qAddLtAdd` is already derived. |
| P2.2 | Tighten `ω'` to recover the `2^(k+14)` slack | Does not change the complexity class. Report the slack either way. |
| P2.3 | Sharpness of the limits result | Needs a Weierstrass-type counterexample sequence; likely out of scope. |

---

## 6. Related work — mandatory reading, with what each threatens

The single largest risk to this paper is a novelty claim that prior art
defeats. Each item below must be read, not summarized from memory, and the
paper must say precisely how it differs.

| Work | What it does | What it threatens |
|---|---|---|
| **Incone** (Steinberg, Théry, Thies), Coq | Represented spaces, information-theoretic continuity, **discontinuity of `lim`** | Closest known relative. May already contain the represented-space comparison this paper calls novel. **Read first.** |
| **Weihrauch degrees** (Brattka, Gherardi, Pauly) | A rich, established reducibility order on problems-with-representations | The `⪯` preorder is Weihrauch-flavoured. The paper must say how representation-adequacy calibration differs from Weihrauch reduction — or adopt the vocabulary and position as a mechanization. |
| **Kohlenbach**, proof mining | Extraction of moduli and rates from proofs | "The modulus is the content" is close to proof mining's founding observation. Position as *calibration of representations* rather than *extraction of rates*. |
| **`hcheval/formalized-proof-mining`**, Lean | Dialectica + a Kohlenbach-style metatheorem, soundness proved | Same language, adjacent goal. Must be compared directly. |
| **Minlog** (Schwichtenberg, Berger, Miyamoto, Seisenberger) | Extracted an **IVT-based algorithm computing `√2`** | Defeats any novelty claim for the theorem-to-algorithm route as such. |
| **C-CoRN** (Cruz-Filipe et al.), Coq | Constructive FTC, long formalized | Defeats novelty for constructive FTC as such. |
| **Bishop; Weihrauch** | The two classical frameworks | Currently dismissed in one sentence in the draft. Needs a real paragraph each. |

**Outcome required before writing §8:** a one-paragraph statement of the
delta against each of Incone, the Lean proof-mining repository, and Weihrauch
degrees. If no delta survives, the paper becomes a *mechanization* paper —
still publishable, differently framed — and the framing must change before
§1 is written, not after.

---

## 7. Staging

1. **Stage 0 — positioning.** P0.1. Produces either a defensible novelty claim
   or a decision to reframe as mechanization. *Everything downstream depends on
   which.*
2. **Stage 1 — close the framework.** P0.2, P0.3, P1.3. Makes §5 writable and
   the flagship result visible inside the framework.
3. **Stage 2 — strengthen.** P1.1, P1.2. Each independently improves a section;
   neither blocks writing.
4. **Stage 3 — write.** §§2–4 and §7 can be drafted from what exists today;
   §5 after Stage 1; §§1 and 8 last, once positioning is fixed.
5. **Stage 4 — audit the draft** against the repository the way
   `CLAIMS_AUDIT.md` audited the previous one. Every claim gets an artifact and
   a footprint, or it is cut.

---

## 8. Risk register

| Risk | Severity | Mitigation |
|---|---|---|
| Novelty defeated by Incone or Weihrauch degrees | **High** | Stage 0 before any writing. Reframe as mechanization if needed — that is a fine outcome, not a failure. |
| Overclaiming the Myhill result | **High** | §3.1's sentence is the only permitted formulation. It is a nice result *as an exhibition*; it does not need inflating. |
| §5 written about an order with no proved instance | High | P0.2 is blocking for a reason. |
| Recurrence of name-vs-statement inflation | Medium | Apply the §7.6 test from the audit to every theorem cited: *if the statement does not mention the objects in the name, it is misnamed.* |
| Stale build figures | Low | Quote one figure, measured at submission, in one place. The audit has already caught three inconsistent counts. |
| Decorative files padding the contribution | Medium | Cite only Category (A) artifacts (`CLAIMS_AUDIT.md` §0.2). Most of the 18 recent files are not paper material and citing them weakens it. |

---

## 9. One-paragraph abstract to aim at

> We ask not whether classical analysis can be made constructive, but how much
> data a representation of a real function must carry for a given classical
> theorem to become provable about it. Working in HA^ω with modified
> realizability, mechanized in Lean 4, we define a ladder of representations
> and calibrate the fundamental theorems of calculus against it: the first
> fundamental theorem holds given only a modulus of uniform continuity, while
> the second requires a modulus of differentiability. We show that the bridge
> between the two levels has an axiom footprint of exactly `Classical.choice`,
> exhibiting — though not reproving — the computability obstruction identified
> by Myhill. Throughout, we use axiom footprints as a quantitative instrument:
> in a development whose extractor is axiom-free by construction, the footprint
> of a bridging lemma measures how non-constructive that bridge is. We report
> our limitative findings, including a Friedman–Ko barrier to polynomial
> adequacy, and the failure of Baire-space continuity to transfer to metric
> moduli.
