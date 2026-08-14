# Findings audit — `HAomega`

**Scope.** Everything below was measured against the repository, not inferred
from documentation. Axiom footprints are quoted verbatim from `lake build`
output. Where something is *stated but not proved*, or *not statable at all*,
it says so in those words.

**Build state at time of writing:** `lake build` green, **7,858 jobs**, 0
errors, 0 HAomega warnings, 0 `sorry`. This includes the newly arrived files
(`GaloisAdequacy`, `UniformContinuityTheorem`, `IVT`, `ComplexAnalysis`,
`FixedPoint`, `ODEDemo`, and `Transcendental`, which appeared last), all
untracked when this was written.

**Read §7 first if you are deciding what to build on.** A green build with no
`sorry` establishes that those files' theorems are *true*. It does not
establish that they are the theorems their names claim, and for several of
them they are not.

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

---

## 7. Name-versus-statement audit of the seven new files

**Why this section exists.** The seven files compile, contain no `sorry`, no
`admit`, no `native_decide`, and declare no axioms. Every theorem in them is
*true*. But "compiles and is true" and "proves what the name says" are
different properties, and the gap between them is wide here. Several theorem
names, docstrings and file names assert results that their own statements do
not express. Anyone reading the declaration list — or a paper generated from
it — will substantially overestimate what has been established.

The check applied below is mechanical and reproducible: **does the statement
mention the objects the name is about?** A theorem called `pi_bracket_width`
that never mentions a Riemann sum is not a theorem about Riemann sums,
whatever its docstring says.

### 7.1 Grading

**Tier A — sound and honestly named.** No action needed.

- `discrete_sign_crossing` (`IVT`) — a real induction on `N` producing a sign
  crossing index. Elementary, correct, named exactly what it is.
- `expPicard_succ` (`ODEDemo`) — `expPicard` is a genuine computable Taylor
  polynomial; the recurrence is proved via `List.range_succ`/`foldl_append`.
  Backed by 7 `#guard`s that actually compute (`expPicard 5 (1/2) = 6331/3840`).
  Named "Taylor step recurrence", which is what it is. Note the *file* is named
  `ODEDemo` and this is `exp`'s Taylor series, not Picard iteration on a
  general ODE.
- `RepLe.refl` / `RepLe.trans` / `RepLe.prod_mono_id` / `GaloisAdequate.comp`
  (`GaloisAdequacy`) — measured genuinely axiom-free (§1.1). A preorder with a
  monotonicity lemma. Modest and real.
- The `#guard` blocks in `Transcendental` (14) and `ComplexAnalysis` (4).
  Executable checks are evidence in the `spernerScan` sense and are the
  strongest content in those two files.

**Tier B — real content, oversold name.**

- `ivt_adjacent_bracket` (`IVT`), billed as "The Galois Approximate IVT
  Theorem". It genuinely consumes `A.cont`, so it does connect to the `A₀`
  layer and is not vacuous. But it proves: *if you are handed `x, y` that are
  already within `2^{-ω(k)}` and already have opposite signs, then both values
  are within `2^{-k}` of zero.* The existence of such a pair — the actual IVT
  content — is not proved. See 7.2.

**Tier C — the hard hypothesis is assumed, not proved.**

- `root_isolation` (`IVT`) takes `h_secant` as a hypothesis: a lower bound on
  `|f(x) − f(y)|` in terms of `|x − y|`. That is the mean value theorem
  consequence, i.e. precisely the bridge §3 of this document already records as
  **absent from this development**. Confirming the gap: `TransverseA1`'s
  substantive field `h_slope` (the derivative lower bound) is used **0 times**
  in `root_isolation`'s proof — only `T.M` is. The structure's mathematics is
  inert; the conclusion rests on the assumed secant bound.
- `approx_fixed_point_bound` (`FixedPoint`), presented as a
  Krasnoselskii–Mann rate of asymptotic regularity. Statement:

  ```lean
  theorem approx_fixed_point_bound (diam : Rat) (k n : Nat) (hn : 0 < n)
      (h_sum : (n:Rat) * (1/2^(2*k+2)) ≤ diam^2) :
      1/2^(2*k+2) ≤ diam^2 / (n:Rat)
  ```

  `NonExpansiveMap` and `kmRate` do not occur. The proof is `le_div_iff₀` —
  dividing the hypothesis by `n`. The KM content is the hypothesis.

**Tier D — the statement does not mention its own subject.**

- `pi_bracket_width` (`Transcendental`): `(4:Rat)/N - (2:Rat)/N = 2/(N:Rat)`,
  by `norm_num`. `piLeftSum` and `piRightSum` do not occur. The docstring
  claims it is the telescoping difference of left and right Riemann sums for
  `π`. It is `4/N − 2/N = 2/N`. Nothing links it to `π`.
- `goursat_rect_zero` (`ComplexAnalysis`): `(CR.ux - CR.vy) * hx * hy = 0 ∧ …`,
  proved `rw [CR.cr1]; ring`. `CauchyRiemannData.cr1` *is* `ux = vy`, so this is
  `(a − a)·hx·hy = 0`. Goursat's theorem is that the contour integral of a
  holomorphic function over a rectangle vanishes, and needs a subdivision
  argument. There is no contour, no integral, and no subdivision in the file.
- `cr_jacobian_eq_complex_mul` (`ComplexAnalysis`): same shape — `rw [CR.cr2];
  ring` against the structure's own field.

### 7.2 Structural findings (these matter more than any single theorem)

**(a) `CauchyRiemannData` is never instantiated.** Zero occurrences outside its
own declaration and the two theorems above. No holomorphic function is ever
exhibited; the all-zeros assignment satisfies both fields. Every result about
it is therefore consistent with the structure having only the trivial model.

**(b) The IVT is proved in two halves that are never joined.**
`discrete_sign_crossing` and `ivt_adjacent_bracket` each occur exactly once —
at their own definition sites. No theorem mentions both. The missing bridge is
exactly the grid search, and the definitions written to perform it —
`IVTProblem`, `ivtGridPoint`, `isApproxZero` — are **defined and never used**
(one occurrence each, their own definition). So the file contains the two ends
of an IVT proof and the unused scaffolding for its middle.

**(c) Dead scaffolding is systematic.** Declarations occurring exactly once in
the entire repository, i.e. never used after definition: `kmRate`,
`IVTProblem`, `ivtGridPoint`, `isApproxZero`, `latticeModulus`. These are the
declarations whose names carry the most weight (`kmRate` is the advertised
Krasnoselskii–Mann rate; `latticeModulus` the advertised lattice-envelope
modulus). They contribute nothing to any proof.

**(d) Four of the seven files never reach the realizability core.** Grepping
`Deriv|extract|soundness`:

```
FixedPoint.lean        0
ODEDemo.lean           0
ComplexAnalysis.lean   0
Transcendental.lean    0
GaloisAdequacy.lean    3
UniformContinuityTheorem.lean  3
IVT.lean               1
```

In a development whose thesis is choice-free extraction from an object
language, these four files are free-floating Mathlib `Rat` algebra. They do not
extend the fragment, produce a `Deriv`, or invoke `soundness`. They can be true
without bearing on the project's claim.

**(e) `UniformContinuityTheorem.lean` asserts, in its header, the negative
result this project recorded.** The header states that the file concerns the
Heine–Borel / Fan Theorem principle that "every pointwise continuous functional
on a compact domain admits an explicitly extracted uniform modulus of
continuity". STATUS §6 records the opposite as a *measured* finding: the
modulus metatheorem is **not proved**, with two obstructions (arrow types need
a Kleene associate; `tiRec` has no compositional bound), and `HasMod` is
Baire-space continuity while `ω`/`δ` are metric moduli on `ℚ` — **no lemma
transfers**. The file's actual contents (`scale_modulus_correct`,
`comp_modulus_correct`, `integral_lipschitz_modulus`) are closure lemmas that
take moduli as *input* and build moduli as *output*. Nothing in the file
extracts a modulus from continuity. The file name and header claim the
project's hardest open problem; the contents are three modulus-arithmetic
lemmas. This is the most serious item in §7, because it is the one a reader is
most likely to believe on the strength of the file name alone.

### 7.3 On production speed

These seven files (~40KB of Lean) appeared in roughly 25 minutes. That is
consistent with their content: the Tier C and D proofs are one to three lines
(`ring`, `norm_num`, `le_div_iff₀`, `rw` against a hypothesis field), and the
elaborate docstrings are prose. Speed is not itself evidence of a problem — it
is explained by the difficulty of what was actually proved, which is low. For
calibration, `eftc2_thm`, `lemma1` and `A0.intE1` in `QAnalysis.lean` took
substantial work because their statements carry the content rather than
assuming it.

### 7.4 Second wave: `FundamentalTheoremAlgebra`, `IntegrationByParts`, `Weierstrass`

Three further files arrived while §7.1–7.3 were being written. They confirm the
pattern rather than departing from it, and they sharpen the diagnosis.

- `ibp_duality_algebra` (`IntegrationByParts`) — the purest Tier D instance in
  the repository:

  ```lean
  theorem ibp_duality_algebra (boundary_diff int_u'_v int_u_v' : Rat)
      (h_ftc : int_u'_v + int_u_v' = boundary_diff) :
      int_u_v' = boundary_diff - int_u'_v := by linarith
  ```

  Three arbitrary rationals carrying integral-shaped *names*. The content is
  `a + b = c ⊢ b = c − a`. No integral, no `u`, no `v`, no `∫`. Integration by
  parts is the hypothesis `h_ftc`, assumed.
- `bernstein_sq_error_at_half` (`Weierstrass`) — `1/4 + (1/4)/n − 1/4 =
  1/(4n)`, by `ring`. `bernsteinOp` is defined and does compute, but does not
  occur in the statement. Weierstrass approximation needs uniform convergence
  over the interval; this is an arithmetic identity.
- `linear_root_val` (`FundamentalTheoremAlgebra`) — **Tier A**. It genuinely
  evaluates `evalPoly [−z₀, 1] z₀` in `QC` and shows both components are zero.
  Modest, correct, and named exactly what it is: the root of a *linear*
  polynomial. The file, however, is named for the Fundamental Theorem of
  Algebra, which requires a root-existence argument for arbitrary degree and is
  nowhere present.

### 7.5 The consistent split — and what is actually worth keeping

Across all ten files the same division holds, and it is the most useful finding
in this section:

> **The computable definitions and the `#guard` blocks are real. The theorem
> layer is decoration.**

`bernsteinOp` genuinely computes Bernstein polynomials; `expPicard` genuinely
computes Taylor partial sums and is `#guard`ed to `6331/3840`; `evalPoly`
genuinely evaluates over `QC`; the `IntegrationByParts` guards compute real
boundary terms. That is executable, kernel-checked content of exactly the kind
this repository values elsewhere (the `spernerScan` sense of evidence). It cost
real work and should be kept.

The theorems sitting above those definitions largely do not mention them. Where
a file has both a computing definition and a headline theorem, the theorem is
typically an arithmetic identity about free variables named after the
definition's outputs. The `#guard`s are the load-bearing part; the `theorem`s
are the part that will mislead a reader.

This inverts the usual reliability ordering and is worth stating plainly to
anyone building on these files: **trust the `#guard`s, re-read every
`theorem`.**

### 7.6 Recommendation

Do not cite Tier C or Tier D results by name in any paper. Either restate them
to say what they prove (`approx_fixed_point_bound` → "dividing a summed
residual bound by `n`"; `goursat_rect_zero` → "the CR equations, multiplied
out"), or complete them:

- **IVT** is the closest to real. Joining (b)'s two halves through the unused
  grid definitions would produce a genuine approximate IVT for `A₀`. That is a
  well-scoped, worthwhile task.
- **`root_isolation`** needs the MVT bridge, which §3 records as absent. It is
  blocked, not nearly-done.
- **`ComplexAnalysis`** has no complex analysis in it; a rectangle contour and
  a subdivision argument would be new work of a different order.
- **`UniformContinuityTheorem`** should be renamed to what it contains
  (e.g. `ModulusClosure.lean`) regardless of any other decision, since its
  present name contradicts a recorded negative result.

The same renaming point applies to `FundamentalTheoremAlgebra.lean` (contains a
linear root evaluation), `Weierstrass.lean` (contains Bernstein computations at
a point), `ComplexAnalysis.lean` (contains the CR equations rearranged) and
`ODEDemo.lean` (contains `exp`'s Taylor series). In each case a file name
asserts a theorem the file does not contain, and in each case the *definitions*
inside would justify an honest name.

**Rule of thumb for any future file here:** if the statement of the headline
theorem does not mention the objects in the file name, the file is misnamed.
That test is mechanical, takes seconds, and would have caught every Tier C and
Tier D item above.
