# Constructivity Audit — `modified-realizability-lean`

**Question.** *Can every extracted computational artifact be trusted to arise
entirely from constructive reasoning?*

**Verdict (short).** **Yes for the computational content.** Every executable
object in the repository — the extraction function `extract`, all realizer
combinators, and every extracted program (`goodsteinStopTime`,
`hanoiSolution`, `gcdWitness`, `spernerWitness`, …) — depends on **no
`Classical.choice`**. The only classical axiom in the development lives in
(i) Prop-level *correctness proofs*, entering through two Mathlib
environment-update lemmas, and (ii) the semantic `CtQ` *collapse class*
inherited from the parent Kleene–Kreisel development. Neither is part of any
extracted program. In Lean's standard sense this is
**Verdict B — fully constructive except for proof packaging**, with the
strengthening that the *packaging* itself never touches a computed value.

Every claim below is verified with `#print axioms` (the kernel's own
verdict), not assumed. All quoted axiom sets are literal `#print axioms`
outputs against the current tree (708 jobs green).

---

## The constructivity criterion used

Lean 4's kernel type theory contains three axioms beyond its inductive/`Quot`
primitives:

- **`propext`** — propositional extensionality, `(a ↔ b) → a = b`. About
  `Prop` only; proof-irrelevance-compatible; **does not imply excluded
  middle**.
- **`Quot.sound`** — the soundness rule for the primitive quotient type
  former; part of Lean's constructive core.
- **`Classical.choice`** — Hilbert choice. With `propext` + `funext` it
  yields excluded middle (Diaconescu). **This is the one genuinely
  nonconstructive axiom.**

The operative criterion, therefore, is the standard one for Lean
developments:

> An object is **constructive** iff `#print axioms` reports **no
> `Classical.choice`** (i.e. at most `propext`, `Quot.sound`).

Accordingly this report treats `propext`/`Quot.sound` as the trusted
*kernel* base and focuses the "is it constructive?" question on the presence
or absence of `Classical.choice`.

---

## STEP 1 — Object → Axioms (ground truth)

Literal `#print axioms` outputs. `∅` = *"does not depend on any axioms."*

### Executable layer — the extraction framework (all `def`s)

| Object | Axioms |
|---|---|
| `extract` | `[propext, Quot.sound]` |
| `derivBound` | `∅` |
| `indRecC`, `indC`, `allIC`, `axiomC` | `∅` |
| `up`, `down`, `pairPT`, `fstPT`, `app₁`, `abs₁`, `natPT`, `defaultPT` | `∅` |
| `liftR`, `dropR` | `∅` |
| `tiRecC`, `tiRecC_eq`, `tiC` | `[propext, Quot.sound]` |
| `oLt_wf` (ε₀ well-foundedness) | `[propext, Quot.sound]` |
| `MR` (the relation, a `def` into `Prop`) | `∅` |
| `Function.update` (Mathlib def, used by `extract`) | `∅` |
| `WellFounded.fix` (used by `tiRecC`) | `∅` |

### Executable layer — the extracted programs (all `def`s)

| Object | Axioms |
|---|---|
| `goodsteinStopTime` | `[propext, Quot.sound]` |
| `hanoiSolution` | `[propext, Quot.sound]` |
| `gcdWitness` | `[propext, Quot.sound]` |
| `spernerWitness`, `spernerScan` | `[propext, Quot.sound]` |

**None depend on `Classical.choice`.**

### Proof-object layer — the derivations (`Deriv [] φ`, in `Type`)

| Object | Axioms |
|---|---|
| `goodsteinTheorem`, `hydraTheorem`, `hanoiTheorem`, `gcdTheorem`, `spernerTheorem` | `[propext, Quot.sound]` |
| `hercules_wins` (metatheory Hydra termination) | `[propext, Quot.sound]` |

These are the **certificates** `extract` consumes. Choice-free.

### Proof layer — soundness, continuity, specifications (`Prop`)

| Object | Axioms |
|---|---|
| `MR_congr` | `[propext, Quot.sound]` |
| `Term.eval_subst` | `[propext]` |
| `Term.eval_congr` | `[propext, Quot.sound]` |
| **`extract_continuous`** (generic continuity) | **`[propext, Quot.sound]`** |
| `MR_subst` | `[propext, Classical.choice, Quot.sound]` |
| `soundness` | `[propext, Classical.choice, Quot.sound]` |
| `MR_indRecC`, `MR_tiRecC` | `[propext, Classical.choice, Quot.sound]` |
| `goodsteinStopTime_spec`, `hanoiSolution_spec`, `spernerWitness_spec`, `gcdWitness_dvd` | `[propext, Classical.choice, Quot.sound]` |

### Semantic-packaging layer

| Object | Axioms |
|---|---|
| `RealizesCtQ` (class in the extensional collapse) | `[propext, Classical.choice, Quot.sound]` |

### The imported Kleene–Kreisel dependency

| Object | Axioms |
|---|---|
| `ContinuousFunctionals.Continuous2` (the continuity predicate) | `∅` |
| `ContinuousFunctionals.PureType` (the realizer hierarchy) | `∅` |
| `ContinuousFunctionals.Ct`, `CtQ`, `Assoc`, `CtPer` | `[propext, Classical.choice, Quot.sound]` |

The two pieces of the dependency that the *executable* pipeline touches —
`PureType` (where realizers live) and `Continuous2` (the continuity
statement) — are **axiom-free**. The classical part of the dependency
(`Ct`/`CtQ`/`Assoc`/`CtPer`, the extensional collapse) enters **only**
through `RealizesCtQ`.

---

## STEP 2 — Every `Classical.choice` traced to its source

There are exactly **two independent entry points**, found by bisection
(checking `#print axioms` on the intermediate lemmas until the classical
carrier is isolated).

### Source ① — Mathlib environment-update lemmas (→ soundness / specs)

```
soundness, MR_indRecC, MR_tiRecC
      │  (all three use MR_subst; MR_indRecC also uses Function.update_idem directly)
      ▼
MR_subst                                    [propext, Classical.choice, Quot.sound]
      │  (ModifiedRealizes.lean:291,306,319,343)
      ▼
Function.update_comm , Function.update_idem  [propext, Classical.choice, Quot.sound]
      │  (Mathlib.Logic.Function.Basic, imported by Ordinals/Epsilon0.lean:6)
      ▼
Classical.choice
```

- **Why present.** `MR_subst` (the substitution lemma for the realizability
  relation) must re-associate and idempotently collapse updates of the
  environment `ρ : ℕ → ℕ` — `Function.update_comm` and
  `Function.update_idem`. Mathlib *proves* these two equalities classically.
- **Local or inherited?** Inherited from Mathlib. `MR_subst` (and therefore
  `soundness`) contains **no** `Classical.*` construct of its own; the file
  `Soundness.lean` imports nothing but `Extraction`. The `by_cases` in
  `Soundness.lean`/`ModifiedRealizes.lean` are all on **decidable** `Nat`
  equalities (e.g. `z = y`, `fstPT … = 0`) and resolve through the
  `Decidable` instance — they are **not** a choice source (confirmed: the
  choice-free `MR_congr` uses the same `by_cases` style).
- **The discriminating fact.** `MR_congr` (which does *not* touch
  `Function.update_comm/idem`) is `[propext, Quot.sound]`; `MR_subst` (which
  does) gains `Classical.choice`. That isolates the two lemmas as the sole
  carriers.
- **Reaches the `_spec` theorems** only because each `_spec` is literally
  `soundness` instantiated (e.g. `spernerWitness_spec := … soundness …`), so
  it inherits `soundness`'s axioms verbatim.

### Source ② — the extensional-collapse types (→ `RealizesCtQ` only)

```
RealizesCtQ                                 [propext, Classical.choice, Quot.sound]
      ▼
ContinuousFunctionals.CtQ / Ct / Assoc / CtPer   [propext, Classical.choice, Quot.sound]
      ▼
Classical.choice
```

- **Why present.** `CtQ` is the *extensional collapse* of the continuous
  functionals (a quotient by extensional equality, presented via associates
  `Assoc`/`Ct`). The parent Kleene–Kreisel development defines these
  classically.
- **Local or inherited?** Entirely inherited from the dependency, and used in
  this repository at exactly one place: forming the `CtQ 2` class of an
  extracted realizer (`RealizesCtQ`, and the per-theorem `…RealizesCtQ`
  wrappers).

**Both sources are absent from every `def` in Step 1's executable layer.**

---

## STEP 3 — Classification of every classical occurrence

Categories: **A** computational (affects executable code) · **B** proof-only
(lives in `Prop`) · **C** packaging (quotients/extensionality/semantic
presentation) · **D** unknown.

| Occurrence | Class | Justification |
|---|---|---|
| `Classical.choice` in `soundness`, `MR_indRecC`, `MR_tiRecC`, `MR_subst`, `…_spec` | **B** | These are `Prop`-valued theorems. Their statements quantify over the *already-built* `extract` term; the proofs never reconstruct or alter it. Proof-irrelevance means the choice term is erased and cannot influence any computed value. |
| `Classical.choice` in `RealizesCtQ` / `Ct`/`CtQ`/`Assoc`/`CtPer` | **C** | `CtQ` is a semantic *presentation* (the extensional-collapse class of a realizer). It packages an already-extracted `PureType`/`Continuous2` object into a quotient; the quotient is never executed. |
| `propext` everywhere it appears | **C** | Propositional extensionality; used only in proof terms and definitional equalities of `Prop`s. No computational content (Prop is proof-irrelevant, erased at runtime). |
| `Quot.sound` in `extract`, `tiRecC`, `oLt_wf`, derivations | **C** | Enters through (a) `oLt_wf`, the ε₀ well-foundedness *certificate* consumed by `WellFounded.fix`, and (b) `Term.eval_congr` and the `decide`-discharged side conditions of the derivations. In all cases it sits in a *proof* sub-term (a termination witness or a decidability certificate), erased in compiled code. |
| `by_cases` in `Extraction.lean` (`tiRecC`, `tiCFind`), `Transport.lean` (`liftR`/`dropR`) | *not classical* | On decidable props (`oltB … = true`, `k = j`, `m ≤ n`). Resolve through `Decidable` — confirmed by `extract`/`tiRecC`/`liftR`/`dropR` reporting no `Classical.choice`. |

There is **no category-A occurrence** anywhere in the repository.

---

## STEP 4 — The extraction pipeline, end to end

```
Deriv [] φ            (goodsteinTheorem, …)      [propext, Quot.sound]
   │  extract (def)                              [propext, Quot.sound]
   ▼
Fam / PureType realizer                          (built from ∅-axiom combinators)
   │  app₁ / fstPT / natPT / defaultPT (defs)    ∅
   ▼
extracted executable (goodsteinStopTime, …)      [propext, Quot.sound]
   │  soundness (proof, applied)                 [propext, Classical.choice, Quot.sound]
   ▼
correctness (…_spec)                             [propext, Classical.choice, Quot.sound]
```

- **Derivation → extract → executable:** every node is `[propext,
  Quot.sound]` — **no `Classical.choice` anywhere on this chain.**
- The `Classical.choice` appears **only** at the *last* arrow (the
  correctness statement), which is a `Prop` about the executable, not a step
  in building it.

**Explicit statement.** *No classical theorem is used at any point in the
construction of an extracted program. `Classical.choice` occurs strictly in
the `Prop`-level proof that the (already-constructed, choice-free) program is
correct, and in the separate `CtQ` semantic packaging.*

---

## STEP 5 — Executable definitions, inspected

- `goodsteinStopTime`, `hanoiSolution`, `gcdWitness`, `spernerWitness`,
  `spernerScan`: each unfolds to `fstPT (app₁ … (extract T ρ [] n) …) …`.
  Transitively: `extract` `[propext, Quot.sound]`; `app₁`/`fstPT`/`natPT`/
  `defaultPT` `∅`. **No classical constant in any unfolding.**
- The only non-`∅` axioms reachable are `propext`/`Quot.sound`, entering via
  `oLt_wf` (the ε₀ termination certificate behind `tiRecC`) and
  `Term.eval_congr`. Both are *proof* sub-terms: `WellFounded.fix` is `∅`, so
  the recursor adds nothing itself; its accessibility argument (`oLt_wf`) is
  irrelevant to the computed value and erased at runtime.
- **Notable:** `spernerWitness` is `[propext, Quot.sound]` even though the
  Sperner derivation is pure `ind` (no transfinite recursion). The
  `propext/Quot.sound` are a property of the shared `extract` *framework*
  (which contains the `tiRecC` case), not of the Sperner theorem. An
  `ind`-only extractor would be fully `∅` — evidence that these axioms are
  framework infrastructure, not per-program computational content.

Every extracted program has been executed (`#eval`/`#guard`): e.g.
`goodsteinStopTime 1 = 1`, `hanoiMoves 1..4`, `spernerScan` on five
colorings. Compiled execution carries no axiom (axioms are `Prop`/proof-level
and erased).

---

## STEP 6 — Imported libraries

- **Direct Mathlib surface is tiny.** Only three modules import Mathlib:
  `Ordinals/Epsilon0.lean` (`Mathlib.Logic.Function.Basic`),
  `Signature/OrdinalAssignment.lean`, and `Theorems/Pascal/PascalExtraction.lean`
  (`Nat.choose`, used only in `#guard` cross-checks).
- **The only Mathlib module that injects `Classical.choice` into the pipeline
  is `Mathlib.Logic.Function.Basic`**, via the two lemmas
  `Function.update_comm` / `Function.update_idem` (Source ①). The *definition*
  `Function.update` it also provides is `∅` and is what `extract` actually
  computes with.
- The Kleene–Kreisel dependency contributes `Classical.choice` through
  `Ct`/`CtQ`/`Assoc`/`CtPer` (Source ②), but its computational core
  (`PureType`, `Continuous2`) is `∅`.
- No `import`/`open Classical`, no excluded-middle or Hilbert-choice import
  anywhere; the classical axiom is only ever pulled in transitively by the
  two lemmas above and by the collapse types.

**Do these imports affect computation? No** — verified by the executable
layer's axiom sets in Step 1.

---

## STEP 7 — Quotients / `propext` / `Quot.sound`

- **`Quot.sound` / `propext`** are Lean *kernel* axioms, present in nearly
  every Mathlib-touching development. In this repository they are
  **packaging/infrastructure (class C)**, never computational:
  - in `extract`/`tiRecC`: inside `oLt_wf` (a termination certificate for
    well-founded recursion) — a `Prop` sub-term, erased at runtime;
  - in the derivations: inside `decide`-produced decidability certificates
    for the `SubstOK`/`FreshIn` side conditions — again `Prop`, erased;
  - in `MR_congr`/`Term.eval_congr`: ordinary `Prop` reasoning.
- **`Quotient`/`CtQ`** (the extensional collapse) is genuinely quotient
  *packaging*: it re-presents an extracted `PureType` object as its
  equivalence class. `Quot.sound` there is the quotient's computation rule,
  used to prove class equalities — never to *run* anything.

No quotient or `propext` use is computational.

---

## STEP 8 — Trusted Computing Base

For each layer, *what is trusted and why*.

### Kernel assumptions (unavoidable; trusted by every Lean development)
- Lean 4 kernel: inductive types, recursors, definitional equality, the
  `Quot` type former.
- **`propext`**, **`Quot.sound`** — the two kernel axioms the executables
  depend on. Constructively acceptable; do **not** imply excluded middle.
- *These are the entire TCB of the extracted programs.*

### Mathlib assumptions
- `Function.update` (def, `∅`) — trusted as a plain computable function.
- `WellFounded.fix` (`∅`), `Mathlib` `Nat`/ordinal lemmas underlying
  `oLt_wf` — contribute only `propext`/`Quot.sound`.
- `Function.update_comm` / `Function.update_idem` — trusted **only for
  proofs**; they inject `Classical.choice`, but into `Prop` (Source ①). Not
  in the TCB of any program.

### Classical assumptions
- **`Classical.choice`** — present, but **confined to**: (i) the `Prop`
  correctness proofs `soundness`/`MR_*`/`…_spec` (via Source ①), and (ii)
  the `CtQ` collapse class `RealizesCtQ` (via Source ②). **Not in the TCB of
  any extracted computation.**

### Repository assumptions
- Zero `sorry`/`admit` (build-enforced).
- The 20-symbol signature's value functions (`bumpN`, `goodN`,
  `hydraStepN`, `lookN`, …) are `∅`-axiom, kernel-computable, choice-free —
  a deliberate invariant (`Epsilon0.lean` is kept `Classical`-free precisely
  because `oLt_wf` feeds `extract`).
- The extraction/continuity discipline (`#print axioms` checks embedded in
  the source) enforces these budgets at every build.

**TCB of the extracted programs = { Lean kernel, `propext`, `Quot.sound` }.**
Nothing classical.

---

## STEP 9 — Can the nonconstructive dependencies be removed?

| Dependency | Removable? | Effort |
|---|---|---|
| Source ① — `Function.update_comm`/`update_idem` in `MR_subst`/`soundness`/`_spec` | **Yes** | **Easy–Moderate**. Both facts are constructively true for a `DecidableEq`-based `update` (prove by `funext` + decidable case split). Replacing the two Mathlib lemmas with local choice-free reproofs would bring `MR_subst`, hence `soundness` and every `_spec`, to `[propext, Quot.sound]` — making the *correctness proofs* constructive too. Purely mechanical; touches ~2 lemmas. |
| Source ② — `Ct`/`CtQ`/`Assoc`/`CtPer` in `RealizesCtQ` | **Probably not (here)** | **Hard**. This is inherited from the parent development's extensional collapse, which may be genuinely classical (extensional equality of continuous functionals via associates). Removing it means reworking the Kleene–Kreisel `CtQ`, out of this repository's scope. It is also *unnecessary* for computation: no extracted program depends on it. |
| `propext` / `Quot.sound` in executables | **No (and no need)** | **Probably impossible / not desirable.** They are kernel axioms; every non-trivial Lean development uses them, they are constructively acceptable, and they occur only in erased proof sub-terms (`oLt_wf`, `decide` certificates). |

The one worthwhile target is **Source ①** — a small, mechanical change that
would upgrade the *proofs* from "constructive-except-two-update-lemmas" to
fully `[propext, Quot.sound]`, matching the executables. Flagged for the
refinement phase.

---

## STEP 10 — Final verdict

**B — the extraction pipeline is constructive except for proof packaging** —
with the following precise strengthening, which is the publishable claim:

> **Every executable artifact of the development — the extraction function
> and every extracted program — depends only on `propext` and `Quot.sound`,
> never on `Classical.choice`. The single nonconstructive axiom,
> `Classical.choice`, is confined to (i) `Prop`-level correctness proofs,
> where it enters solely through Mathlib's `Function.update_comm/idem`
> environment lemmas and is proof-irrelevant and runtime-erased, and (ii) the
> `CtQ` extensional-collapse class inherited from the parent Kleene–Kreisel
> development, which no extracted program depends on. The Trusted Computing
> Base of every extracted computation is therefore { Lean kernel, `propext`,
> `Quot.sound` } — with no classical content.**

**Justification.** The kernel's own `#print axioms` (Step 1) shows the
executable layer is `Classical.choice`-free; the pipeline trace (Step 4)
shows no classical theorem participates in constructing a program; the two
choice sources (Step 2) are both isolated to `Prop` proofs or semantic
packaging (Step 3); and the runtime-executed programs carry no axiom at all.
The development does *not* reach Verdict A only because two Mathlib update
lemmas make the *correctness proofs* (not the programs) classical — a
condition that is easily removable (Step 9, Source ①).

---

### Reproduction

All axiom facts above are reproduced by `#print axioms <name>` against the
built library (`open Realizability ContinuousFunctionals`). The embedded
`#print axioms` blocks in `Arithmetic.lean`, `Goodstein*.lean`,
`GcdExtraction.lean`, `SpernerExtraction.lean`, etc. check the headline
budgets on every `lake build`.
