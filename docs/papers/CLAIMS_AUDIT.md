# Findings audit — `HAomega`

**Scope.** Everything below was measured against the repository, not inferred
from documentation. Axiom footprints are quoted verbatim from `lake build`
output. Where something is *stated but not proved*, or *not statable at all*,
it says so in those words.

**Build state at time of writing:** `lake build` green, **7,858 jobs**, 0
errors, 0 HAomega warnings, 0 `sorry`. This includes the six newly arrived
files (`GaloisAdequacy`, `UniformContinuityTheorem`, `IVT`, `ComplexAnalysis`,
`FixedPoint`, `ODEDemo`), which were untracked when this was written.

---

## 1. Audit of `Aphoristic_Analysis_Universe.md`

Five claims in the paper draft conflict with what the repository actually
contains. Listed worst-first.

### 1.1 "0 unproved axioms" / "0 Axioms" — **partly false as stated**

The header claims "0 unproved axioms"; §7's table assigns "0 Axioms" to
`GaloisAdequacy` and `ODEDemo`. Measured:

```
'HAomega.RepLe.refl'                 does not depend on any axioms   ✓
'HAomega.RepLe.trans'                does not depend on any axioms   ✓
'HAomega.RepLe.prod_mono_id'         does not depend on any axioms   ✓
'HAomega.GaloisAdequate.comp'        does not depend on any axioms   ✓
'HAomega.A0_to_E0_morphism'          [propext, Classical.choice, Quot.sound]   ✗
'HAomega.E1_to_E0_morphism'          [propext, Classical.choice, Quot.sound]   ✗
'HAomega.expPicard_succ'  (ODEDemo)  [propext, Quot.sound]                     ✗
'HAomega.approx_fixed_point_bound'   [propext, Classical.choice, Quot.sound]   ✗
```

So the *preorder core* of `GaloisAdequacy` is genuinely axiom-free, and that is
worth claiming precisely. The blanket header claim is not defensible, and
`ODEDemo` is not 0-axiom.

**The accurate general statement** for this project is the one STATUS §1 makes:

```
extract, fibRealizer                     no axioms
Tm.eval, all derivations, running extracts   [propext, Quot.sound]
soundness and everything through it          [propext, Classical.choice, Quot.sound]
```

Choice enters via `soundness`; every *extracted program that runs* is
choice-free. That is a strong, true claim. "0 axioms" is a weaker-sounding
claim that happens to be false.

### 1.2 "$E_1 \cong A_1$" — **not proved, and false in the direction that matters**

Asserted in §2, §3.1 and §5.2. What exists:

- `A1.toE1` — every exact `A₁` **is** an `E₁` (constant family, `dq := 0`).
- `A0.intE1` — the integral of an `A₀` is an `E₁`.

The converse fails, and the reason is the whole motivation for the `E` layer:
`A₁`'s evaluator is *exactly rational-valued* (`A0.f : Q → Q`), and `∫f` is not
rational-valued. That is why `EFTC1` could not say "`∫f` is `A₁`-adequate" and
why `E₀`/`E₁` were introduced. Writing `E₁ ≅ A₁` erases the distinction the
construction exists to make.

### 1.3 §6 on higher types — **contradicts a recorded negative result**

§6 reads as though `Collapse.lean`/`Modulus.lean` supply associates and moduli
supporting the analysis layer. STATUS §6 records the opposite, and it was
checked rather than assumed:

- the modulus metatheorem is **not proved**, with two recorded obstructions
  (arrow types need a Kleene associate; `tiRec` has no compositional bound);
- `HasMod` is **Baire-space** continuity — how much of an *oracle* a functional
  inspects — while `ω`/`δ` are **metric** moduli on `ℚ`. **No lemma transfers.**

### 1.4 Build figures — internally inconsistent

Header says "7,856 verified targets"; §7 says "7,858 targets green". Measured:
**7,858**. §7 is right, the header is wrong.

### 1.5 No related-work section — **the specific risk already documented**

STATUS §9 (a literature search done in this session) found:

- **Minlog** (Schwichtenberg, Berger, Miyamoto, Seisenberger) has extracted an
  **IVT-based algorithm computing `√2` approximations** — the same
  theorem-to-algorithm route as this repo's Sperner-1D → square-root chain,
  arrived at first and independently.
- **Incone** (Steinberg, Théry, Thies) formalises represented spaces,
  information-theoretic continuity, and **discontinuity of `lim`** in Coq.
- **`hcheval/formalized-proof-mining`** is a **Lean** formalization of Gödel's
  Dialectica plus a Kohlenbach-style proof-mining metatheorem, soundness proved.
- Constructive FTC is long formalised in Coq (Cruz-Filipe, C-CoRN).

§9 concludes that the **comparative representation-adequacy framing** is the
only novelty candidate, and states explicitly that it should not be claimed
until Incone and the Lean proof-mining repo are read properly. The draft claims
"A New Foundation for Mathematical Analysis" with no related work and one
dismissive sentence about Bishop and Weihrauch.

### 1.6 §3.1 wording

"The derivative of the integral evaluator is identically the original
continuous function" overstates slightly. What is proved (`A0.intE1`) is that
the integral satisfies `E₁`'s `diff` field — an approximation statement with
moduli, with `dq k h` absorbing the error that division by `h` amplifies. The
informal reading is fine in prose; "identically" is not.

---

## 2. What is proved (with footprints)

### Analysis layer (meta-level Lean, `QAnalysis.lean`)

```
eftc2_thm            [propext, Classical.choice, Quot.sound]   A₁ ⊨ EFTC2, both conjuncts
lemma1, lemma2       [propext, Classical.choice, Quot.sound]
eftc1                [propext, Classical.choice, Quot.sound]   δ := ω, A₀-data only
A0.intE0 / A0.intE1  [propext, Classical.choice, Quot.sound]   ∫f is E₀ / E₁-adequate
A1.toE1, A0.toE0     [propext, Classical.choice, Quot.sound]   conservativity
LimSeq.toE0/limit_cont  [propext, Classical.choice, Quot.sound]
CompData.comp        [propext, Classical.choice, Quot.sound]   A₀ closed under ∘
inv_modulus          [propext, Classical.choice, Quot.sound]
sqrt_premises, doubling_lipschitz, …
```

### Object language (`Deriv`)

```
constReal_upper/lower   [propext, Quot.sound]     a real, derived inside Deriv
diffReal_upper          [propext, Quot.sound]     non-constant term, constant denotation
qAddLtAdd               does not depend on any axioms
realCauchy_sound        [propext, Classical.choice, Quot.sound]   the soundness bridge
```

### Core invariants (unchanged by everything above)

```
extract     does not depend on any axioms
Tm.eval     [propext, Quot.sound]
soundness   [propext, Classical.choice, Quot.sound]
```

---

## 3. Not proved, and in two cases **not statable**

- **Myhill's negative half (`A₀ ⊭ EFTC2`).** Not statable here: it quantifies
  over *procedures*, and this model has no computability predicate. Proved
  instead: `A0.toA1` has footprint **exactly `[Classical.choice]`** — choice
  alone closes the gap Myhill says cannot be closed. The `A₀`/`A₁` separation
  is a computability phenomenon this model cannot see.
- **Specker / limits negative half.** Same reason. Already formalised elsewhere
  (Incone, in Coq, in a setting that *can* express it).
- **`A₁` closure under `∘`.** Analysed, not proved. Needs **no new field**
  beyond a range condition; the manifesto's "moving point" worry dissolves
  because `A1.diff` is a modulus of *uniform* differentiability.
- **Inversion at `A₁`.** The bridge from a positive lower bound `m ≤ |f'|` to a
  monotonicity modulus is by the mean value theorem, which this development
  does not have. `μ` is taken as primitive instead.
- **Sharpness of the limits result.** Uniform limits do not preserve
  differentiability (Weierstrass); stating it needs a counterexample sequence.
- **`EFTC1` at `Deriv` level.** The induction step (`qAddLtAdd`) is derived.
  Remaining: the Riemann sum as a `recNat` term, the `ind` over `N`, and a base
  case needing one further cheap rule (`qlt t t = 0`, measured `[propext]`).

---

## 4. Measured constraints on future work

- **Polynomial adequacy for `EFTC2` is unreachable.** Friedman–Ko: there are
  polytime-computable **C^∞** functions with `#P₁`-complete integrals. Holds
  already for smooth integrands, so a modulus of differentiability does not
  evade it. Separately, this repo's construction carries about `2^(k+14)` of
  *its own* slack above optimal quadrature (`sqEx.intN = 2^(2k+14)` vs `≈2^k`)
  — real, ours, and not a complexity-class issue.
- **The `Q` rule base splits.** Laws where both sides feed `Q.of` arguments
  that already agree are cheap and Mathlib-free (`sub_self`, `add_comm`,
  `mul_comm`, `ltN_self` — all `[propext]`). Associativity and distributivity
  are not: an inner operation feeds an outer one, so they need uniqueness of
  normal forms (`Q.of_eq_of`). **Option 1 (Mathlib in `Soundness.lean`) was
  taken**; measured cost ≈5½ min rebuild and **zero breakage**.
- **`qdiv` cancellation `(a·c)/c = a` is FALSE** for unreduced inhabitants of
  `Q` — the same failure as `x + 0 = x` at the `den+1` refactor. Not among the
  rules; derivations must route around it.
- **`sumQ` does not reduce in the kernel** (`do`-loop). No `decide`-style proof
  about `A1.integral` is possible; it *is* provable via `Std.Range.forIn` →
  `foldl`.
- **Derivation idiom.** Backward `refine` beats forward `have` + `deriv_norm`
  whenever the goal is concrete (`qAddLtAdd` vs `constReal_upper`).

---

## 5. Open decisions — do not resolve without the author

- Whether to add `convQLtSelf` (`qlt t t = 0`) to unblock `EFTC1`'s base case.
  Measured cheap; not added.
- Whether to tighten `ω'` to recover the `2^(k+14)` slack. Would not change the
  complexity class.
- Whether the comparative-adequacy framing is claimed as novel, and on what
  reading of Incone and the Lean proof-mining repository.

---

## 6. Repository hygiene — one outstanding problem

Commit **`42042df`**, message *"Fix stale headline counts caught by reviewing
the diff"*, actually contains **563 insertions across 4 files**: the entire new
`HAomega/Picard.lean` (302 lines) and 263 lines of `QAnalysis.lean`
(`ContractionOp`, `PicardData`, `VectorField`, `CompData1`, `A1.deriv_bound`,
`unifDistLe`), none of which the commit message mentions. Cause: `git add -A`
in a repository with concurrent in-progress work. It is pushed. The history is
misleading and should be corrected or annotated; the work itself is intact and
builds.
