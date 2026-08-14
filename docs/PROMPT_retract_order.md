# Task prompt: establish the retract order on representations (P0.2)

## 0. What this is

`HAomega/GaloisAdequacy.lean` defines a preorder `⪯` on representations and
`SmoothnessHierarchy.lean` claims a "smoothness hierarchy" over it. **No
instance of `⪯` between two *different* representations has ever been proved.**
Every concrete `⪯` theorem in the repository today is `RepLe.refl` instantiated:

```lean
theorem A0_in_hierarchy (a b : Q) : (RepA0 a b) ⪯ (RepA0 a b) := RepLe.refl _
theorem A1_in_hierarchy (a b : Q) : (RepA1 a b) ⪯ (RepA1 a b) := RepLe.refl _
theorem E0_in_hierarchy … theorem E1_in_hierarchy …          -- all RepLe.refl
```

These carry no information beyond `RepLe.refl`, which is already proved for
**all** `R`. This task is to replace that with real content.

This is the single highest-value item in the repository. It unblocks the
framework paper, and — see §3 — its likely answer is itself a publishable
result.

---

## 1. The exact definitions you are working against

From `HAomega/GaloisAdequacy.lean`:

```lean
structure RepMorphism {X : Type} (R1 R2 : Rep X) where
  toFun     : R1.Carrier → R2.Carrier
  map_equiv : ∀ c1 c2, R1.equiv c1 c2 → R2.equiv (toFun c1) (toFun c2)
  shift     : Nat → Nat
  map_approx : ∀ c k x, R1.approx c (shift k) x → R2.approx (toFun c) k x

structure RepRetract {X : Type} (R1 R2 : Rep X) where
  iota : RepMorphism R1 R2
  pi   : RepMorphism R2 R1
  retract_id : ∀ c, R1.equiv (pi.toFun (iota.toFun c)) c

def RepLe {X : Type} (R1 R2 : Rep X) : Prop := Nonempty (RepRetract R1 R2)
infix:50 " ⪯ " => RepLe
```

So **`R1 ⪯ R2` requires a morphism *both ways* plus a round-trip identity.** A
one-directional morphism is not enough. This is exactly why the existing
morphisms do not already give the order.

**Morphisms that already exist** (all one-directional, all in
`GaloisAdequacy.lean`):

```lean
A1_to_A0_morphism : RepMorphism (RepA1 a b) (RepA0 a b)   -- forgets δ, diff
A1_to_E1_morphism : RepMorphism (RepA1 a b) (RepE1 a b)   -- conservativity
A0_to_E0_morphism : RepMorphism (RepA0 a b) (RepE0 a b)   -- conservativity
E1_to_E0_morphism : RepMorphism (RepE1 a b) (RepE0 a b)   -- forgets diff data
```

**The map in the missing direction** (`HAomega/QAnalysis.lean`):

```lean
noncomputable def A0.toA1 (A : A0) (h : HasUnifDeriv A) : A1 :=
  { toA0 := A, δ := h.choose, diff := h.choose_spec }
```

Note both properties: it is `noncomputable` (uses `h.choose`) **and partial**
(requires `HasUnifDeriv A`, an existential over `δ` and `F`, defined in
`HAomega/EFTC.lean`).

---

## 2. A fact that makes this tractable — read before designing anything

**The `equiv` relations are blind to the extra data.**

- `RepA0.equiv` and `RepA1.equiv` are the *same formula*: `A₁.a = A₂.a ∧
  A₁.b = A₂.b ∧ ∀ x in range, (A₁.f x).val = (A₂.f x).val`. Neither mentions
  `δ` or `diff`.
- `RepE0.equiv` and `RepE1.equiv` are likewise identical to each other, and
  `RepE0.approx` and `RepE1.approx` are identical too.

**Consequence:** for `RepA1 ⪯ RepA0`, the `retract_id` obligation is
```lean
∀ (A : A1), RepA1.equiv (pi.toFun (A1_to_A0_morphism.toFun A)) A
```
and since `A0.toA1` sets `toA0 := A` — preserving `a`, `b` and `f` exactly —
the round trip changes only `δ`/`diff`, which `equiv` cannot see. **So
`retract_id` is nearly free.**

**The whole difficulty is therefore concentrated in one place: defining `pi`,
i.e. a *total* `RepMorphism (RepA0 a b) (RepA1 a b)`.** `A0.toA1` is not total.

---

## 3. What to determine, and why the answer matters either way

For each ordered pair among `RepA0`, `RepA1`, `RepE0`, `RepE1`, classify as:

- **(H) Holds** — construct the `RepRetract`, prove the theorem.
- **(C) Holds only with choice** — construct it, and report the measured
  `#print axioms` showing `Classical.choice`.
- **(R) Holds only on a restricted representation** — e.g. after restricting
  `A₀`'s carrier to `{A : A0 // HasUnifDeriv A}`. Define the restricted
  representation, then construct the retract.
- **(O) Obstructed** — you cannot construct it, and you can say *precisely
  which field* fails and why.

**Both outcomes are valuable, so do not force a positive result.** If
`RepA1 ⪯ RepA0` is obstructed because `A0 → A1` is partial and noncomputable,
that obstruction *is* the Myhill gap appearing as a structural separation in
the order — which is a stronger form of this project's flagship result
(`A0.toA1` has footprint exactly `[Classical.choice]`). Reporting a clean
obstruction is a success, not a failure.

**Priority target:** `RepA1 ⪯ RepA0restricted`, where `RepA0restricted` has
carrier `{A : A0 // HasUnifDeriv A}` (or equivalent). This is the most likely
(C)/(R) win and it directly serves the paper. Expected footprint:
`[propext, Classical.choice, Quot.sound]` — and **the presence of
`Classical.choice` is the point**, not a defect.

**Second target:** any `⪯` among `RepE0`/`RepE1`. Note their `approx` and
`equiv` are identical, so the only obstacle is constructing `E0 → E1`
(adding differentiability data) or `E1 → E0` (already exists as
`E1_to_E0_morphism`) in the direction you need.

---

## 4. Hard constraints

1. **No `RepLe.refl` at concrete representations.** `R ⪯ R` is already proved
   for all `R`. Restating it four times is not progress and has now been
   submitted twice. Any new `⪯` theorem must relate **two syntactically
   different** representations.
2. **Do not prove a negative by asserting it.** You cannot prove `¬(R1 ⪯ R2)`
   by failing to construct a retract. If you claim (O), *document the
   obstruction in prose* — name the field, say why it cannot be filled — and do
   **not** state a Lean theorem claiming impossibility unless you have a real
   argument (e.g. an invariant preserved by all morphisms that the two
   representations differ on).
3. **Name every theorem for what it proves.** The repository's standing test:
   *if the statement does not mention the objects in the name, the name is
   wrong.* A theorem called `..._hierarchy` must relate two representations.
4. **`#print axioms` every new theorem**, in the file, and quote the output
   verbatim in your report. Do not describe anything as "choice-free" without
   the measurement for that exact declaration.
5. **No new files beyond what this task needs.** Work in
   `GaloisAdequacy.lean` / `SmoothnessHierarchy.lean` or one new focused file.
   The repository has 86 Lean files and does not need more surface area; it
   needs this instance.
6. **Zero `sorry`, zero `admit`.** Build must stay green (currently 7,895
   jobs).
7. **Do not weaken the definitions to make it go through.** If `RepRetract`
   or the `Rep` fields need changing for a retract to exist, that is a finding
   to report, not a change to make unilaterally.

---

## 5. Deliverable

1. **The classification table** — all ordered pairs, each marked (H)/(C)/(R)/(O)
   with one sentence of justification.
2. **At least one proved cross-representation `⪯`**, with its `#print axioms`
   output quoted verbatim.
3. **For each (O): the precise obstruction** — which field of `RepMorphism` or
   `RepRetract` cannot be constructed, and why.
4. **Replace or delete** the four `*_in_hierarchy` / `*_retract_self`
   reflexivity theorems, or keep them but rename so they cannot be mistaken
   for hierarchy results.
5. **A short report** stating what was achieved, not what was attempted. If the
   priority target turned out obstructed, say so plainly — that is a real
   result and the paper wants it.

---

## 6. Context you may need

- Build: `lake build`. Currently green, 7,895 jobs, 0 `sorry`.
- Axiom discipline: `extract` is axiom-free; `Tm.eval` and derivations are
  `[propext, Quot.sound]`; anything through `soundness` is
  `[propext, Classical.choice, Quot.sound]`. A `Classical.choice` in a
  *bridging* lemma is informative, not a bug — this project reads axiom
  footprints as measurements.
- Relevant files: `HAomega/GaloisAdequacy.lean` (definitions, `RepA0`–`RepE1`,
  morphisms), `HAomega/SmoothnessHierarchy.lean` (the reflexivity theorems to
  replace), `HAomega/EFTC.lean` (`A0`, `A1`, `E0`, `E1`, `HasUnifDeriv`),
  `HAomega/QAnalysis.lean` (`A0.toA1`, `A1.toE1`, `A0.toE0`).
- Background on why this matters: `docs/papers/PAPER_PLAN.md` §5,
  `docs/papers/PUBLICATION_PLAN.md` §2 (P3), `docs/papers/CLAIMS_AUDIT.md`
  §§8.4, 12.4.

---

## 7. If this lands, the next task is

Instantiate `RepAdequacySpec` once and apply `central_adequacy_theorem`
(`HAomega/CentralAdequacy.lean`) to a real derivation — `iterSequenceD` in
`HAomega/AnalysisDeriv.lean` is already a closed `∀∃` derivation and is the
obvious candidate. That theorem is currently an interface with zero
implementations. Do not start this until the retract task is reported.
