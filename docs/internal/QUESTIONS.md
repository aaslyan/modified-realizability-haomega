# Open questions and pending decisions

A running record of decision points I have raised, with options and my
recommendations.  Items get moved to "Resolved" when you answer them.

## Resolved

1. **Which not-yet-proved piece to attack next?**
   *Asked 2026-07-27; answered: "Generic continuity."*
   *Reopened 2026-07-27 after design analysis (sizing concern:
   continuity seemed to need hereditary countability at every ambient —
   the full countability chapter).*
   ***Closed 2026-07-28: generic continuity is proved***
   (`extract_continuous` in `GenericContinuity.lean`), per the brief's
   direction to thread a compositional logical relation through the
   derivation.  The sizing concern dissolved: the invariant is the
   oracle-parameterized continuity relation (`Tracked`), under which
   abstraction closure holds by β-reduction — no associates are
   constructed, so the countability chapter is not needed for this
   theorem.  The finding's residue that *does* stand: associate-level
   abstraction closure remains open and remains the hard core of the
   parent repo's finite-types chapter.  Bonus: the brief's `lvl φ ≤ 1`
   hypothesis proved unnecessary — every closed derivation's extract is
   continuous, so `RealizesCtQ` is now total on closed derivations.

2. **Push `Realizability` to GitHub?**
   *Answered 2026-07-27: pushed to
   `github.com/aaslyan/modified-realizability-lean`.*

3. **Rename the local `ContinuousFunctionals` directory?**
   *Done 2026-07-27: now `/home/aaslyan/kleene-kreisel-lean`; the
   Realizability path dependency and manifest updated, both repos
   rebuilt green.*

3¾. **How to consume `ContinuousFunctionals` — symlink, git-pin, or
   vendor?**  The layered-reorg symlink
   (`Realizability/Core/ContinuousFunctionals` → `../kleene-kreisel-lean`)
   was explicitly interim, pending this decision.  *Resolved 2026-08-01:
   **vendor.***  The transitive closure of the two direct imports
   (`Hierarchy`, `CtQ`) — **12 files** — is copied verbatim into
   `Realizability/Core/ContinuousFunctionals/ContinuousFunctionals/` and
   built by an in-package `lean_lib «ContinuousFunctionals»`.  The symlink
   and its `require` are gone; Mathlib is now required directly at the same
   `v4.26.0` (manifest regenerated, no dependency-rev drift), and the repo
   builds **standalone** — verified by a clean clone with no
   `kleene-kreisel-lean` anywhere nearby.  `Density/` and `KleeneTree/` are
   unreachable from anything imported here and were not copied; the vendored
   files are a **read-only mirror**, so fixes go upstream, not here.

6. **Induction axiom (long-term plan).**  *Closed: delivered as Phase 2
   (see docs/first-order/STATUS.md), and now exercised on new content by Phase A — the
   four `+`/`×` defining equations are `ind` theorems (five inductions,
   `Arithmetic.lean`).*

7. **Phase A: Option 1 vs Option 2 for `+`/`×`** (the brief delegated
   the choice, to be recorded with rationale).  *Resolved 2026-07-29:
   Option 2, in "mirror recursion" form* — the defining axioms recurse
   on the **first** argument, so all four briefed (second-argument)
   equations are genuine `ind` theorems; the brief's own Option-2
   sketch (second-argument axioms) would have collapsed into Option 1
   with `ind` never firing, and a term-level recursion binder was the
   "deeper syntactic machinery" wall the brief itself flagged.  Full
   rationale in docs/first-order/STATUS.md's Phase-A section.  Also settled there: the
   equational-logic kit as per-symbol implication schemas rather than
   a single Leibniz replacement rule.

8. **Phase B: encoding of hereditary base-`k` representations** (the
   brief named this the single most consequential design decision and
   delegated it).  *Resolved 2026-07-29: a representation is a term of
   the fragment's own syntax in one distinguished free variable (the
   base, variable `0`)* — so bumping the base is evaluating the same
   term at `k + 1` (the reference repo's base-replacement `f` made
   definitional), existence is a *derivable* fragment equation
   produced by a certifying evaluator (no axiom about `hrep` exists),
   and uniqueness/canonicity is deferred with an explicit safety
   argument.  One compromise flagged: `bump` enters the fragment by
   its numeral graph (`bumpNum`), since its course-of-values recursion
   through the exponent structure is not a first-order schema.  Full
   rationale in docs/first-order/STATUS.md's Phase-B section.

9. **Phase C: how `tiEps0`'s quantifiers range, and whether canonicity
   of notations is load-bearing** (the brief delegated the first and
   demanded a direct answer to the second).  *Resolved 2026-07-29.*
   Quantifiers range over **natural-number codes** of Cantor-normal-form
   trees — forced, since the fragment has one sort and only equations, so
   `y ≺ x` is the equation `prec y x = 1` for a new function symbol.  The
   tempting reuse of Phase B's hereditary base-2 representation as the
   coding was rejected because it *trivializes* the rule (that coding is
   order-isomorphic to `(ℕ, <)`, so `tiEps0` would follow from `ind`).
   And canonicity **is** load-bearing, decisively: on arbitrary notations
   the comparison has an infinite descending chain
   `ω ≻ 1 + ω ≻ 1 + (1 + ω) ≻ …` of terms all denoting `ω`, so the order
   is the comparison conjoined with a normal-form predicate — Phase B's
   deferred `NF` layer, now built.  Full rationale, with the
   machine-checked witnesses, in docs/first-order/STATUS.md's Phase-C section.

10. **Phase C: does the recursor need a well-foundedness theorem?**  The
   brief said no (structural recursion on the notation's subterms) and
   asked that the finding be recorded either way.  *Resolved
   2026-07-29: it does* — `≺`-descent is not subterm descent (from `ω^ω`
   one descends to the larger tree `ω^2·2 + ω·2 + 2`), so `Epsilon0.lean`
   proves `oLt_wf` and `tiRecC` is `WellFounded.fix` on it.  The brief's
   philosophical point survives in sharper form: that proof is
   elementary and `Classical`-free (`[propext, Quot.sound]`, strictly
   less than the realization theorems' budget).  Recorded in docs/first-order/STATUS.md,
   together with the two things this forced — a hand-rolled pairing
   (Mathlib's `Nat.pair` theory is choice-dependent) and a ban on
   `by_cases` in that module.

11. **The fragment has no `∃`** (item 3½, raised in Phase B, deferred by
   Phase C).  *Resolved 2026-07-29 as Phase D0*: added, and it needed no
   new machinery — its realizability clause is `∨`'s with the tag
   generalized to a numeral, so `exIC`/`exEC` reuse the existing pairing
   devices and `lvl (∃y φ) = lvl φ`.  Goodstein's theorem is now stated
   and proved (`goodsteinTheorem`).  The original item is preserved
   below for the record.

## Open

*(nothing blocking; the roadmap's phases and the Hydra project's six are
all delivered, as are Phases E and F.  Item 12 is engineering, not
mathematics; items 13–16 are design points, recorded rather than silently
chosen.)*

16. **Lucas: should it be internalized in the fragment?**  *Raised and
   answered 2026-07-30, on delivering Phase G.*  Phase G proves
   Kummer/Lucas in the metatheory.  Internalizing it is blocked twice
   over, and precisely: the fragment cannot **state** the submask
   condition (it needs binary digits, i.e. division, which the signature
   lacks — or a new bitwise symbol), and even given the statement it
   could not **prove** it, because the proof recurses `n → n/2` and
   deriving course-of-values recursion from `ind` needs an order on `ℕ`
   that the fragment does not have (`prec` is the ordinal-notation order,
   which on codes is not the numeric one).
   **Done, in part: Phase G2 (2026-07-30) derives the four binary step
   identities inside the fragment**, with round trips recovering the
   value-level versions through `soundness`.  They are the mathematical
   core; what remains outside is only the final bit-position induction,
   which needs division (to state) and an order on `ℕ` (to justify the
   `n → n/2` recursion).  Adding a division symbol would fix the first
   and not the second.  Recommendation for the remainder: leave it.

15. **Pascal: how should `XOR` enter the fragment?**  *Raised and
   answered 2026-07-30, in Phase F, since the brief delegated the
   choice.*  The brief offered `a + b − 2·a·b` or a case-split axiom.
   **Neither is used**: `a + b − 2ab` is *not expressible* in this
   signature at all, because `pred` is the only non-monotone operation
   and it subtracts constants from terms, so nothing built from
   `+`/`×`/`exp` under outer `pred`s can be `1 − x`.  `xor` therefore
   enters by its **numeral graph**, like `bump`, `prec` and `hcut`, and
   the case analysis lands in the proofs (driven by `pasTotal`) rather
   than in four conditional axioms.  Recorded because the alternative
   the brief suggested first looks available and is not.

14. **Hanoi: is "optimal" the same as "shortest"?**  *Raised and
   answered 2026-07-30, at the close of Phase E.*  The brief's formal
   goal (`∃k. Solves ∧ MoveCount k = 2^n − 1`) is proved, and E5 adds
   that the relation admits **exactly one** sequence (`solvesN_unique`),
   so every solution it accepts has that length.  But the brief's prose
   ("prove it's shortest") reads as classical minimality — no *legal*
   sequence is shorter — and that is a different theorem over a
   different relation: legality on arbitrary sequences with a
   tower-state semantics, plus a counting argument for the lower bound.
   **Recommendation: leave it, and keep saying so.**  Adding the state
   semantics is a phase of its own; docs/first-order/STATUS.md's E5 section states the gap
   in the same words as this entry, so the two claims cannot drift apart.

13. **Should the Hydra descent be *derived* the way D5 derived the
   Goodstein one?**  *Raised 2026-07-30, at the close of H4/H5.*
   H4 imports exactly one mathematical fact, `hordCutLt`: from `c ≠ 0`,
   `hord(hcut(n,c)) ≺ hord(c)`.  It follows D5's `ordPredLt` pattern —
   one property of one move symbol relative to one ordinal symbol, silent
   about the battle, quantified over the replication factor — so it is
   already at D5's granularity, not at the pre-D5 "one composite step"
   granularity.  There is no analogue of D5's split available: the
   Goodstein step decomposed because it *is* `pred ∘ bump`, two symbols
   with separate ordinal properties, whereas a Hydra move is one
   operation and its descent is one theorem (`cutH_descends`) whose three
   cases are cases of the *tree*, not of a composition of symbols.
   Going further would mean internalizing tree surgery and Cantor normal
   forms in an equations-only first-order language — strictly harder than
   the Goodstein internalization D5 already scoped as research-scale and
   declined.
   **Recommendation: leave it.**  `hydra_descent_via_fragment` checks the
   import is faithful (it returns exactly H3's theorem through
   `soundness`), and docs/first-order/STATUS.md's H4 section states the gap plainly.  If
   this is ever revisited, the first genuine sub-step would be giving the
   fragment `hord` of a *node in terms of its children* — i.e. `insertExp`
   as a symbol with its four defining equations — which is a phase of its
   own, not a refactor.

18. **Phase S1 Sperner: arbitrary `ℕ` colors, and a two-ambient
   extraction.**  *Raised and resolved 2026-07-31 while building 1D
   Sperner.*  Two choices, both recorded:
   (a) **Arbitrary `ℕ`-valued colorings, not `{0,1}`.**  The brief framed
   the coloring as `{0,1}`, but the crossing argument never uses binariness
   — "endpoints differ ⇒ some adjacent pair differs" holds for any
   `ℕ`-coloring, and `≠` (the negated equation) needs no binary test.  So
   the delivered theorem is the general discrete IVT; binary Sperner is the
   special case.  This also *avoided* forcing colors binary (which would
   have needed either an extra `∀j. c j ∈ {0,1}` hypothesis — more `app₁`
   depth — or a normalizing `lookN`).  Using `xor(c k)(c(k+1)) = 1` (an
   equation, reusing the Pascal symbol) was considered and rejected: it
   only means "differ" for binary colors, so it would have *required* the
   restriction it was meant to save.
   (b) **The extract is read at two ambients.**  `spernerWitness_spec` is
   certified at `derivBound = 11` (soundness), but the ambient-11 pure-type
   realizer overflows the interpreter stack (the `gcd` wall).  The witness
   numeral is ambient-independent, so the *runnable demonstration*
   (`spernerScan`) reads the same derivation at ambient 5 — checked under
   `lean --run` to agree with ambient 11 wherever both terminate.  The
   agreement is *checked*, not *proved* (proving ambient-independence of a
   realizer's witness component is out of scope); flagged as such.  A
   cleaner single-ambient run would need `derivBound ≤ ~5`, which the
   essential `impI`/`ind`/`allI` nesting (`+1` each) rules out.

17. **Phase E2 gcd: the positivity precondition, dropped.**  *Raised and
   resolved 2026-07-31 during the gcd existence proof.*  The roadmap
   handoff stated the theorem as `∀a∀b. (a>0 ∨ b>0) → ∃g. spec`.  While
   building it I found the precondition is **unnecessary**: `spec(0,0,0)`
   holds — `0∣0`, and `∀d. d∣0→d∣0→d∣0` is trivial because everything
   divides `0` — so `gcd(0,0)=0` (the standard convention, `Nat.gcd 0 0 =
   0`) realizes the predicate at the origin.  The delivered `gcdTheorem`
   is therefore the strictly stronger `∀a∀b. ∃g. spec`, and dropping the
   precondition is *simpler* throughout (the `a=0` base returns `g:=b`
   unconditionally; the recursion never re-establishes a precondition; the
   extract takes `(a,b)` not `(a,b,precond-realizer)`).  **Chosen: no
   precondition.**  A precondition-carrying variant, if ever wanted, is a
   four-line `impI`-that-ignores wrapper over `gcdTheorem`.  Flagged here
   per the "record design forks" discipline; the user may still prefer the
   documented form.

12. **The extracted program is correct but not efficient.**  *Diagnosed
   2026-07-29 in Phase D4; the authorized memoization fix was built,
   proved and measured in Phase D6 (2026-07-30) and **does not help** —
   see docs/first-order/STATUS.md's D6 section for the numbers.*  The one-line summary:
   memoizing the recursor by notation code achieves a 100 % hit rate
   (2376 hits, 0 misses at `m = 1`) and changes the wall clock by nothing
   (4693 ms against 4614 ms), because `app₁` returns a *closure* — so
   producing the recursor's value at a code is `O(1)`, and the cost is in
   *applying* it, once per consumer, with a different argument each time.
   A table that would collapse the tree must be keyed by
   `(code, argument)`, and arguments are `PureType` functions with no
   decidable equality.  D4's entry count was therefore never a cost
   proxy.  Recommendation unchanged: leave it; the correctness theorem
   carries the content at every input.  *Original D4 entry follows.*  The profile:
   at `m = 1` the recursor's body is entered 2377 times at only **two**
   distinct notation codes — 2376 of them at the same code — so the cost
   is re-evaluation of an identical recursive call, ≈ 2400× per Goodstein
   step, independent of the ambient level.  `WellFounded.fix` is *not* to
   blame: the compiled code contains no `Acc` references at all (proofs
   are erased for `#eval`, unlike for kernel reduction, which is what
   Phase B was avoiding).  Three proof-backed `@[csimp]` sharing variants
   were written, compiled and measured: **exactly zero effect**.  The
   reason no `csimp` can help is structural — it changes what a function
   computes, not how often the surrounding term calls it — and the fix
   that would work (memoization keyed by the code) is not expressible as
   a provably-equal pure function.  Full evidence in docs/first-order/STATUS.md's Phase-D4
   section.  Recommendation unchanged: leave it; the correctness theorem
   carries the content at every input.  Original entry: `goodsteinStopTime` evaluates at `m = 0, 1`
   in under a second and does not finish at `m = 2`, because every
   recursive value passes through two `dropR` transports and `app₁`/
   `abs₁` duplicate their argument, so recursive calls are re-evaluated
   exponentially often in the number of Goodstein steps.  Nothing is
   memoized.  Options if this is ever worth pursuing: sharing in the
   combinators, a transport-free realizer for this derivation shape, or
   a compiled evaluator for `PureType`.  Recommendation: leave it —
   `goodsteinStopTime_spec` carries the mathematical content at every
   input, and efficiency was never a roadmap goal.  Flagged rather than
   fixed.

### Historical record of item 3½

3½. **The fragment has no `∃` — now a Phase-D blocker.**  Flagged during
   Phase B (2026-07-29); *Phase C deliberately did not fold it in*
   (2026-07-29): the transfinite-induction work turned out to be
   self-contained, while `∃` touches `Formula`, `MR`, both transports and
   the tracking relation — a phase-sized change of its own that would
   have been entangled with the notation/well-foundedness work for no
   benefit.  It is now the **first** thing Phase D needs, before any
   descent argument, since without it the target cannot be stated.  The
   original analysis stands:
   the target `∀m ∃s. G(m, s) = 0` is Π₂, and the fragment's formulas
   have only `∀` (plus `∧∨→⊥` over equations).  Phase B is unaffected
   (its deliverables are equations and their certifications), but
   Phase D cannot even state termination without either (a) an `∃`
   clause added to `Formula`/`MR` — the natural choice for this
   project, since modified realizability of `∃` carries the witness,
   and *extracting the Goodstein stopping-time function is presumably
   the point of the roadmap* — or (b) a negative translation, which
   would gut the extraction payoff.  Recommendation, updated for the
   post-Phase-C state: make `∃` **Phase D's first deliverable**, before
   the descent argument (its `MR` clause is the `orI` pattern — pair a
   witness numeral with a realizer — and it needs a `liftR`/`dropR` case,
   a `Tracked` case, and intro/elim rules with their four machinery
   cases each).

4. **Next chapter in `kleene-kreisel-lean`.**  Per the stated pipeline:
   Kreisel's density theorem is next (completing the Kleene-tree pairing
   into both machine-checked halves of "restriction costs everything /
   nothing"), awaiting its brief.  Standing alternatives: the
   countability / arbitrary-finite-types chapter (its associate-level
   abstraction closure is still the hard core there, though it is no
   longer needed for `RealizesCtQ` — see item 1); Mathlib upstreaming
   of the type-2 core.

5. **The draft paper (`paper/main.pdf`) awaits your read-through.**  It
   predates the Kleene tree module and this realizability project; when
   the dust settles, decide whether to extend it, write a separate note,
   or leave it as the type-2/collapse snapshot.

