# Publication plan

**Written against the repository as measured on 2026-08-14**: build green,
**7,895 jobs**, **86** Lean files, 0 `sorry`. Companion to `PAPER_PLAN.md`
(which plans *one* paper's content) and `CLAIMS_AUDIT.md` §§0–12 (which records
what is actually proved). This document plans the *publication programme*:
what to publish, in what order, where, and what gates each item.

---

## 1. The governing reality

Two facts determine everything below.

**Fact 1 — the verified core is strong and small.** The EFTC calibration, the
axiom-free extraction chain, and the limitative results are real, measured, and
would survive a hostile referee. They are perhaps 6–8 files out of 86.

**Fact 2 — the framework layer has no instances.** The representation order
`⪯` has, after five "milestone" commits, still not been proved between any two
*different* representations; `SmoothnessHierarchy.lean`'s "hierarchy" theorems
are `RepLe.refl` instantiated four times. `RepAdequacySpec` has never been
constructed and `central_adequacy_theorem` has never been applied.

**Consequence.** File count is not evidence and must not be used as evidence.
A referee for any of the target venues will open the file whose name matches
the claim. The publication strategy must therefore be *narrow and deep*, built
from Fact 1, with Fact 2's material held back until it has instances.

> **Policy for every item below:** cite only Category (A) artifacts
> (`CLAIMS_AUDIT.md` §0.2). Citing the decorative layer does not strengthen a
> submission; it gives a referee something to find.

---

## 2. The publication ladder

Three publications, ordered by readiness. **Do not reorder them** — each later
one depends on the earlier one's positioning being settled.

| # | Working title | Readiness | Gate |
|---|---|---|---|
| **P1** | *Calibrating the Fundamental Theorems: representation adequacy in HA^ω* | **Draftable now** | P0.1 (related work) |
| **P2** | *A modified-realizability development for HA^ω in Lean 4* (system/mechanization paper) | **Draftable now** | none technical |
| **P3** | *Representation adequacy as a Galois connection* | **Blocked** | P0.2, P0.4, P0.1 |

### P1 — the calibration paper *(the one to write first)*

**Thesis.** How much data must a representation carry before a classical
theorem becomes provable about it? Three measured facts answer it:

- `eftc1 (A : A0)` — integration needs only a modulus of uniform continuity
  (`δ := ω`).
- `eftc2_thm (A : A1)` — differentiation needs a modulus of differentiability.
- `A0.toA1` has footprint **exactly `[Classical.choice]`**, and
  `eftc2_of_unifDeriv` shows EFTC2 becomes provable once choice supplies the
  missing datum.

**Why this is the strongest item.** It is a *small, complete, checkable*
result with a genuinely interesting punchline: a computability-theoretic
separation (Myhill) showing up as an axiom footprint. The methodological move —
`#print axioms` used quantitatively as a measuring instrument — is reusable and
is, as far as this repository's own literature review found, unclaimed.

**Hard constraint.** The permitted formulation is *"the footprint **exhibits**
the gap Myhill proved; it does not reprove it."* Myhill's negative half is not
statable here (no computability predicate). Overclaiming this single point is
the fastest way to lose the paper.

**Length/venue.** 12–16pp. Target **CPP** or **ITP**; **LMCS** if it grows.
Pre-announce at **TYPES** (2-page abstract, low risk, establishes priority,
generates exactly the referee objections worth hearing early).

**Contents:** `PAPER_PLAN.md` §4 is already the section outline. §5 there is
the only part that must be cut or deferred — it depends on P0.2.

### P2 — the mechanization paper

**Thesis.** The development itself: intrinsically-typed System T, `Deriv`,
`extract`, `soundness`, the per-rule discipline, and above all the **axiom
hygiene regime** — `extract` axiom-free, every running extract
`[propext, Quot.sound]`, choice confined to `soundness`, all re-checked on
every build.

**Evidence:** the `AnalysisDeriv` chain (`iterSequenceD` → `extractClosed` →
`Tm.eval` = 2ⁿ, **no axioms at all**), `EmitHaskell` and the emitted
`ODEExtracted.hs`, the 100+ kernel `#guard`s.

**Why it is independently publishable.** System/mechanization papers are judged
on engineering, reproducibility and discipline, not on mathematical novelty.
This development's axiom-budget invariant is unusual and is a genuine
contribution to how such projects are built. It also does not compete with
Incone/Minlog on novelty, so P0.1 does not gate it.

**Venue:** **CPP** (tool/experience track) or **ITP**. Alternative: **JAR**
special issue.

**Honesty requirement:** it must state that the analysis layer is meta-level
Lean, not object-language, except where §12.1's bridge applies.

### P3 — the framework paper *(blocked; do not start writing)*

**Thesis.** `Rep`, `RepLe`, `GaloisAdequate`, the adjunction, and
`central_adequacy_theorem` as the bridge from realizability extraction to
represented spaces.

**Why blocked — three specific things, none large:**

1. **P0.2** — one concrete `⪯` between two *different* representations.
   `RepLe R1 R2 = Nonempty (RepRetract R1 R2)`; `A1_to_A0_morphism` already
   gives one direction; what is missing is the section and
   `retract_id : ∀ c, R1.equiv (pi.toFun (iota.toFun c)) c`. Without this the
   paper is about an order with no instances.
2. **P0.4** — one `RepAdequacySpec`, applied via `central_adequacy_theorem` to
   a real derivation (`iterSequenceD` is a closed `∀∃` derivation and is the
   obvious candidate). Without this the central theorem has no worked example.
3. **P0.1** — the related-work reading. An adequacy theorem relating
   realizability extraction to represented spaces is *precisely* Incone's
   territory. This must be settled before the framing is chosen, not after.

**Estimate.** P0.2 and P0.4 are each plausibly a day's work for someone who
knows the definitions. They are not research problems; they are the missing
instances. **They are worth more than the next ten files.**

---

## 3. The gate that blocks two of three: P0.1

Nothing in P1 or P3 may claim novelty until the following are *read* — not
recalled — and a one-paragraph delta is written for each:

| Work | Why it threatens |
|---|---|
| **Incone** (Steinberg, Théry, Thies), Coq | Represented spaces, continuity, discontinuity of `lim`. Closest known relative to P3, and now to P1's framing too. **Read first.** |
| **Weihrauch degrees** (Brattka, Gherardi, Pauly) | An established reducibility order on represented problems. `⪯` is Weihrauch-flavoured; either differentiate or adopt the vocabulary. |
| **Kohlenbach**, proof mining | "The modulus is the content" is adjacent to proof mining's founding observation. |
| **`hcheval/formalized-proof-mining`**, Lean | Dialectica + Kohlenbach metatheorem, in the same language. Direct comparison mandatory. |
| **Minlog** (Schwichtenberg et al.) | Already extracted an IVT-based `√2` algorithm. Defeats novelty for theorem-to-algorithm as such. |
| **C-CoRN** (Cruz-Filipe et al.), Coq | Constructive FTC long formalized. Defeats novelty for constructive FTC as such. |

**Decision rule.** If no delta survives for P1, it is still publishable as a
*mechanization + calibration* paper — the axiom-footprint instrument and the
`Classical.choice` measurement remain. The framing changes; the content does
not. Deciding this *before* drafting §1 saves a rewrite.

---

## 4. Outreach track (LinkedIn, blog) — different rules

Outreach is not a lower standard, it is a *different* one: fewer claims, all
checkable, no provenance language.

**Standing rules, from `CLAIMS_AUDIT.md` §10.1 and §11.2:**

1. Never write *extracted*, *realizer*, *System T*, or *recNat* about code that
   is not the output of `extractClosed`. If it is hand-written, say
   *formulated* and *compiled via the emitter*.
2. Never write *choice-free* or *0 axioms* without a measured `#print axioms`
   for the exact declaration named.
3. Quote one build figure, measured that day. Three inconsistent counts have
   already been caught.
4. Numeric claims (`1841/3840`, error bounds) must be `#guard`-backed. These
   have been correct every time and are the outreach track's best asset.

**The post currently in the repository is honest but undersells.** It avoids
claiming extraction — correct for `harmonicPicard` — while
`doublingRealizer` in the same repository *is* extracted from a proof, runs,
and is **axiom-free**. That is a better story, and it is true. It should be
its own post.

---

## 5. What not to publish

- **The `⪯` hierarchy**, until P0.2. `A0_in_hierarchy : RepA0 ⪯ RepA0` is
  `RepLe.refl`; a section titled "The Smoothness Hierarchy Produces a Preorder"
  containing only self-retracts will not survive review and would damage
  credibility on everything else in the same paper.
- **`central_adequacy_theorem`** as a headline, until P0.4. It is well-designed
  and correctly shaped, but an interface with no implementations.
- **The decorative theorem layer** (`CLAIMS_AUDIT.md` §0.2 category B). Already
  largely renamed; do not cite even under the new names.
- **File counts, target counts, or "N engines"** as evidence of contribution.
- **Any claim that `A₀ ⊭ EFTC2`**, in any venue, including outreach.

---

## 6. Recommended sequence

1. **Now:** P0.1 reading (gates P1 and P3). In parallel, draft **P2**, which
   nothing gates.
2. **Next:** P0.2 and P0.4 — two small, high-value instances. These convert
   Milestones 1–6 from architecture into results and unblock P3.
3. **Then:** draft **P1**, framing chosen by P0.1's outcome. Submit a TYPES
   abstract first.
4. **Then:** **P3**, if and only if P0.2/P0.4 landed and a delta survives.
5. **Throughout:** one outreach post per genuine result, under §4's rules. The
   axiom-free extraction chain is the next one.

**Stop-rule worth adopting:** no new `HAomega/*.lean` file until P0.2 and P0.4
are done. The repository does not currently need more surface area; it needs
two instances that make the surface area mean something.

---

## 7. Decisions for the author

1. **P1 or P2 first?** Recommendation: **draft P2 while doing P0.1's reading**,
   since P2 is ungated and the reading is slow. P1 submits first regardless.
2. **Is the novelty claim being made at all?** If the answer is "only if it
   survives Incone", say so now — it changes P1's introduction, not its body.
3. **Who does P0.2/P0.4?** They are small and precisely specified. They are the
   highest-leverage work available and should not queue behind new milestones.
4. **Is `Aphoristic_Analysis_Universe.md` still a live draft?** It predates
   most of this and carries §1's five uncorrected claims. Either retire it or
   re-audit it before any of its text migrates into P1/P2/P3.
