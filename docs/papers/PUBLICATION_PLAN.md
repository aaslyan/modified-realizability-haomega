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

### P3 — the framework paper *(unblocked on instances; gated by P0.1)*

**Thesis.** `Rep`, `RepLe`, `GaloisAdequate`, the adjunction, and
`central_adequacy_theorem` as the bridge from realizability extraction to
represented spaces.

**Status of prerequisite gates:**

1. **P0.2 ✅ DONE** — Retract order $\preceq$ instantiated across representations:
   `A1_le_A0diff`, `A0diff_le_A1`, `A1_equiv_A0diff`, `E1_le_E0diff`, `E0diff_le_E1`, `E1_equiv_E0diff`
   proved and verified in `GaloisAdequacy.lean` / `SmoothnessHierarchy.lean`.
2. **P0.4 ✅ DONE** — Concrete `RepAdequacySpec` and `central_adequacy_theorem` instances:
   `doubling_central_adequacy` / `doublingGaloisRealizer` and `exp_doubling_central_adequacy` /
   `expDoublingGaloisRealizer` proved and verified in `CentralAdequacy.lean`.
3. **P0.1** — the related-work reading. An adequacy theorem relating
   realizability extraction to represented spaces is *precisely* Incone's
   territory. This must be settled before the framing is chosen, not after.

---

## 3. The gate that blocks two of three: P0.1 ✅ DONE

The related-work reading and technical delta analysis have been completed and formalized in [`docs/papers/RELATED_WORK_DELTA.md`](file:///Users/araaslyan/modified-realizability-haomega/docs/papers/RELATED_WORK_DELTA.md).

| Work | Why it threatened | Delivered Technical Delta |
|---|---|---|
| **Incone** (Steinberg, Théry, Thies), Coq | Represented spaces, continuity, discontinuity of `lim`. | Incone is shallow/classical on names without deep object-logic; we provide deep $\mathrm{HA}^\omega$ embedding + automated extraction + `central_adequacy_theorem` bridging derivations to $\mathbf{Rep}$. |
| **Weihrauch degrees** (Brattka, Gherardi, Pauly) | Reducibility order on represented problems. | Weihrauch $\le_W$ orders *multi-valued problems*; our $\preceq$ orders *represented spaces* via retracts, inducing a Galois connection on operation theories ($\operatorname{Req} \dashv \operatorname{Th}$). |
| **Kohlenbach**, proof mining | "The modulus is the content". | Proof mining uses Dialectica/majorization for classical systems; we formalize modified realizability for constructive $\mathrm{HA}^\omega$, an extensional $\mathbf{Rep}$ category, and kernel-verified axiom budgets. |
| **`hcheval/formalized-proof-mining`**, Lean | Dialectica + Kohlenbach metatheorem in Lean. | Cheval formalizes Dialectica translations; we formalize modified realizability, a full code emission compiler (Haskell/Scheme), category $\mathbf{Rep}$, and numerical dynamical system instances. |
| **Minlog** (Schwichtenberg et al.) | Program extraction from proofs (e.g. $\sqrt{2}$). | Minlog extraction is an external unverified Lisp program; our entire pipeline is verified inside Lean 4's trusted kernel, with category $\mathbf{Rep}$ and retracts. |
| **C-CoRN** (Cruz-Filipe et al.), Coq | Constructive FTC formalized in Coq. | C-CoRN is shallow constructive analysis; we deeply embed $\mathrm{HA}^\omega$ with realizability, and quantitatively calibrate the axiom cost of EFTC1 vs EFTC2 (`A0.toA1` costs exactly `[Classical.choice]`). |

**Conclusion:** Clear, non-overlapping technical deltas survive for **P1**, **P2**, and **P3**.

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

- **The decorative theorem layer** (`CLAIMS_AUDIT.md` §0.2 category B). Already
  largely renamed; do not cite even under the new names.
- **File counts, target counts, or "N engines"** as evidence of contribution.
- **Any claim that `A₀ ⊭ EFTC2`**, in any venue, including outreach.

---

## 6. Recommended sequence

1. **All Gates Cleared:** **P0.1** (Related work delta), **P0.2** (Retract preorder), and **P0.4** (Central adequacy instances) are complete.
2. **Next:** Draft **P2** (Mechanization paper: intrinsically-typed System T, `Deriv`, zero-axiom extraction, compiler).
3. **In Parallel / Next:** Draft **P1** (Calibration paper: EFTC1 vs EFTC2, `A0.toA1` measured as `[Classical.choice]`, axiom-footprint instrument).
4. **Next:** Draft **P3** (Framework paper: category $\mathbf{Rep}$, Galois connection $\operatorname{Req} \dashv \operatorname{Th}$, retract preorder $\preceq$, `central_adequacy_theorem`).
5. **Throughout:** Outreach posts highlighting verified zero-axiom extraction (`doublingRealizer`).

---

## 7. Decisions for the author

1. **P1 or P2 first?** Recommendation: **draft P2 while doing P0.1's reading**,
   since P2 is ungated and the reading is slow. P1 submits first regardless.
2. **Is the novelty claim being made at all?** If the answer is "only if it
   survives Incone", say so now — it changes P1's introduction, not its body.
3. **P0.2/P0.4 status:** Fully completed and verified (7,895 jobs, 0 errors, 0 sorry).
4. **Is `Aphoristic_Analysis_Universe.md` still a live draft?** It predates
   most of this and carries §1's five uncorrected claims. Either retire it or
   re-audit it before any of its text migrates into P1/P2/P3.
