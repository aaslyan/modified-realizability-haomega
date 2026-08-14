# Findings audit — `HAomega`

**Scope.** Everything below was measured against the repository, not inferred
from documentation. Axiom footprints are quoted verbatim from `lake build`
output. Where something is *stated but not proved*, or *not statable at all*,
it says so in those words.

**Build state.** §§1–8 were written against a green build of **7,858 jobs**.
§9 re-measures after the files were revised in response, at **7,862 jobs** —
also green, 0 errors, 0 HAomega warnings, 0 `sorry`. Both figures are correct
for their section; §9 supersedes where they differ.

The files audited are the ten that arrived untracked: `GaloisAdequacy`,
`ModulusClosure` (renamed from `UniformContinuityTheorem` in response to
§7.2(e)), `IVT`, `ComplexAnalysis`, `FixedPoint`, `ODEDemo`, `Transcendental`,
`PolyRoots` (renamed from `FundamentalTheoremAlgebra`), `IntegrationByParts`
and `Weierstrass`.

---

## 0. Executive summary — read this first

### 0.1 The results are **not** false

This must not be misread. Across the **18** new files there are **40
theorems**, **101 `#guard`s**, and **zero** `sorry` or `admit`. Lean has
verified every one of those theorems. Nothing in this document alleges a false
theorem, an unsound proof, a hidden axiom, or a broken build. The build is
green at **7,870 jobs**.

**What is wrong is not the mathematics. It is the labels on it.**

A theorem can be perfectly true and still be misnamed. `2ab − 2ab = 0` is true.
Calling it `harmonic_energy_conserved` and citing it publicly as "energy
conservation for the harmonic oscillator" is the error — not the equation.

### 0.2 Three categories

**(A) True, well-named, worth keeping and citing.** `newton_sqrt_quadratic_error`
(why Newton's method is quadratic), `approx_ivt_thm` (a real approximate IVT for
`A₀`), `discrete_sign_crossing`, `expPicard_succ`, `linear_root_val`,
`green_2x2_exact_cancellation`, the `GaloisAdequacy` preorder core (genuinely
axiom-free), and essentially all **101 `#guard`s** — which compute real values
in the kernel and are the most reliable content in these files.

**(B) True, but the name claims much more than the statement.** The theorem is
sound; the name is not a description of it. Examples: `goursat_rect_zero` (is
`(a−a)·hx·hy = 0`), `taylor_remainder_bound` (is "a product of non-negatives is
non-negative"), `harmonic_energy_conserved`, `euler_maclaurin_linear_exact`,
`monomial_ibp_sq_val` (is `1/2 − 1/6 = 1/3`), `pi_endpoint_bracket_width`. **The
fix is renaming or restating, not reproving.** Several were already fixed this
way (§9.1), which shows the remedy works.

**(C) Claims *about* the work that are false.** These are the only actual
falsehoods, and **none of them are in Lean** — they are in prose: the paper
draft (§1) and the LinkedIn post (§10.1). Specifically:

| Claim | Where | Measured |
|---|---|---|
| "0 unproved axioms" / "choice-free" | paper §7, post | Every new analysis theorem is `[propext, Classical.choice, Quot.sound]` |
| "extraction compiles the proof into a System T `recNat` term" | post | `harmonicPicard` is a plain Lean `def`; no `Deriv`, `extract`, `Tm` or `recNat` in the file |
| "$E_1 \cong A_1$" | paper §2, §3.1, §5.2 | Not proved; false in the direction that motivates the `E` layer |
| "7,856" / "7,858" / "7,866 targets" | paper header, paper §7, post | 7,870 |
| Higher-type moduli support the analysis layer | paper §6 | STATUS §6 records the opposite as a measured negative result |

### 0.3 The one-line verdict

> **Every theorem is true. Many are misnamed. Several public claims about them
> are false. Nothing needs reproving; some things need renaming, and the
> outward-facing claims need correcting before publication.**

### 0.4 What to do

1. **Do not publish the LinkedIn draft as written** (§10.1). Four load-bearing
   claims fail against the build, and it is signed by the author. §10.1
   contains an honest version that keeps the genuinely nice result.
2. **Rename the category (B) theorems** by the §7.6 test: *if the headline
   theorem's statement does not mention the objects in its name, it is
   misnamed.* Mechanical, seconds per theorem.
3. **Correct the paper's five claims** (§1), above all the axiom claim — the
   true statement (`extract` axiom-free, running extracts `[propext,
   Quot.sound]`, choice only via `soundness`) is *stronger* and defensible.
4. **Build the one thing that would make the provenance claims true** (§8.6,
   §10.5): a concrete `⪯` between representations, and a `Deriv` that extracts
   rather than a `Tm` written by hand.

### 0.5 Reading order

§7 grades batch one, §8 answers "is this grounded in HA^ω", §9 records what was
fixed in response, §10 covers batch two and the post. §§1–6 audit the paper
draft and record what the repository actually proves.

---

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

---

## 8. Is the new work "grounded in HA^ω"? — a measured answer

This section responds to a specific counter-claim: that the new results are
grounded in this project's HA^ω development rather than being free-floating.
The claim is **partly correct**, and correct precisely in one file. It is not
correct for the other nine. This section also **corrects an under-measurement
in §7**.

### 8.1 Correction to §7's method

§7(d) reported grep counts of `Deriv|extract|soundness` per file. That count is
accurate but too narrow to settle the grounding question, and a second pass
that classified only lines matching `^theorem` **missed the content of
`GaloisAdequacy.lean` entirely** — because that file's substance is in `def`s
producing structures, not in `theorem`s producing `Prop`s. The corrected
measurement is below. Where §7 and §8 differ, §8 is right.

### 8.2 Layer classification of every theorem in the ten files

Each theorem *statement* was classified by the most-grounded object it
mentions: L0 = Mathlib `Rat`/`Nat` only; L1 = mentions `Q`/`QC`; L2 = mentions
`A0`/`A1`/`E0`/`E1`; L3 = mentions `Deriv`/`extract`/`soundness`.

```
                              L0   L1   L2   L3
GaloisAdequacy                 6    0    0    0
UniformContinuityTheorem       2    2    0    0
IVT                            1    0    2    0
ComplexAnalysis                2    1    0    0
FixedPoint                     1    1    0    0
ODEDemo                        0    1    0    0
Transcendental                 1    0    0    0
FundamentalTheoremAlgebra      1    1    0    0
IntegrationByParts             3    0    0    0
Weierstrass                    1    0    0    0
                              --   --   --   --
TOTAL (26 theorems)           18    6    2    0
```

**No theorem in any of the ten files mentions `Deriv`, `extract` or
`soundness`.** The two L2 theorems are `ivt_adjacent_bracket` (§7 Tier B) and
`root_isolation` (§7 Tier C). Eighteen of twenty-six are stated purely in
Mathlib `Rat`/`Nat` and mention no object from this development at all.

### 8.3 Where the grounding is real: `GaloisAdequacy.lean`

This file does instantiate the project's own layers, and §7 undercredited it:

```lean
def RepA0 (a b : Q) : Rep (Q → Q) := { Carrier := A0, … }
def RepE0 (a b : Q) : Rep (Q → Q) := { Carrier := E0, … }
def RepE1 (a b : Q) : Rep (Q → Q) := { Carrier := E1, … }

def A0_to_E0_morphism (a b : Q) : RepMorphism (RepA0 a b) (RepE0 a b) :=
  { toFun := fun (A : A0) ↦ A.toE0, … }
def E1_to_E0_morphism (a b : Q) : RepMorphism (RepE1 a b) (RepE0 a b) :=
  { toFun := fun (E : E1) ↦ E.toE0, … }
```

The carriers are this repository's `A0`, `E0`, `E1`; the morphisms are built
from its `A0.toE0` and `E1.toE0`. That is genuine grounding, and it is the
**comparative representation-adequacy framing** that STATUS §9 identified as
this project's only real novelty candidate. It is the most interesting new
material in the ten files and should be kept and developed.

### 8.4 Three limits on that grounding

**(a) The retract hierarchy is advertised but never established.** §4 of the
file is titled "The Retract Hierarchy of Concrete Function Representations".
Searching for `⪯` or `RepLe` applied to any of `RepA0`, `RepE0`, `RepE1`,
`RepA1` returns **no hits**. `RepLe R1 R2` is `Nonempty (RepRetract R1 R2)`,
and `RepRetract` requires a morphism **together with a section** satisfying
`retract_id`. Only one-directional `RepMorphism`s are constructed. So
`RepLe.refl` and `RepLe.trans` establish that the preorder is a preorder, in
the abstract, and are never applied to any concrete representation. This is
the same shape as §7.2(b): both halves present, never joined.

**(b) `RepA1` does not exist** — zero occurrences repository-wide. The `A₀`/`A₁`
separation is the Myhill computability gap (§3), the reason the `E` layers were
introduced at all, and the sharpest distinction in the development. It is
absent from the hierarchy that claims to organise these representations.

**(c) `EFTC1_Adequate` is a wrapper, not a result.**

```lean
def EFTC1_Adequate (a b : Q) (_ivl : Q.ltN a b = 1) : A0 → E1 := fun A ↦ A.intE1
```

It renames the existing `A0.intE1` and does not use its `_ivl` hypothesis. The
content is `A0.intE1`, which is this repository's own prior result (§2).

### 8.5 Verdict

- **"The definitions reference the `A₀`/`E` layers."** True of
  `GaloisAdequacy`, and loosely of `IVT`. Fair claim.
- **"The new results are theorems about HA^ω."** Not supported. Zero of 26
  theorems mention the object language; 18 of 26 mention no object from this
  development.
- **"The new work extends the HA^ω development."** `GaloisAdequacy` repackages
  existing results into a new abstract frame — worthwhile, but it adds no new
  theorem about `A₀`, `A₁`, `E₀` or `E₁`, and the hierarchy it announces is
  unproved.

The honest summary is that **one file contributes a promising organising
framework grounded in the project's structures, and nine do not contribute
grounded results.** Nothing in §7's grading changes as a result of this
section; only §7(d)'s implication that `GaloisAdequacy` is peripheral is
withdrawn.

### 8.6 The one concrete next step this suggests

Proving a single concrete `⪯` — e.g. `RepE1 a b ⪯ RepE0 a b`, by supplying the
section that `E1_to_E0_morphism` currently lacks — would convert the advertised
hierarchy into a real one and would be the first genuinely new theorem about
these representations. Adding `RepA1` and locating it in that order is the
natural follow-on, and is where the `A₀`/`A₁` computability gap would become
visible inside the framework.

---

## 9. Re-measurement after the audit was acted on

The ten files were revised in response to §§7–8. This section records what
changed, measured the same way. **The response was substantive and largely
correct.** Build green, **7,862 jobs**, 0 errors, 0 `sorry`.

### 9.1 Fixed — verified

**File renames (both recommended in §7.6):**

- `UniformContinuityTheorem.lean` → **`ModulusClosure.lean`**. This was §7.2(e),
  the most serious item: a file whose header asserted the modulus-extraction
  principle that STATUS §6 records as unproved and obstructed. The new name
  describes the contents (closure lemmas on moduli). Resolved.
- `FundamentalTheoremAlgebra.lean` → **`PolyRoots.lean`**. Resolved.

**Theorem renames — each now names what it proves rather than what it evokes:**

```
pi_bracket_width          → pi_endpoint_bracket_width
approx_fixed_point_bound  → residual_div_bound
root_isolation            → secant_root_isolation
ibp_duality_algebra       → monomial_ibp_sq_val
```

`residual_div_bound` and `secant_root_isolation` are the two Tier C items, and
both now carry the assumed hypothesis in the name. That is exactly the §7.6
remedy.

**Dead scaffolding removed:** `TransverseA1` and `latticeModulus` are now at
**0 occurrences**. `TransverseA1` was §7.1's Tier C evidence — the structure
whose substantive `h_slope` field went unused. `secant_root_isolation` now
takes plain `Rat` arguments and states its secant hypothesis openly.

**New real content — the §7.6/§8.6 recommendation was carried out:**

```lean
theorem approx_ivt_thm (A : A0) (k : Nat) (x : Nat → Q) (N : Nat)
    (hx_in : ∀ j, j ≤ N + 1 → Qle A.a (x j) = true ∧ Qle (x j) A.b = true)
    (h0 : (A.f (x 0)).val ≤ 0) (hN : 0 ≤ (A.f (x (N + 1))).val)
    (h_step : ∀ j, j ≤ N → |(x j).val - (x (j+1)).val| ≤ 1 / 2 ^ (A.ω k)) :
    ∃ j, j ≤ N ∧ |(A.f (x j)).val| ≤ 1/2^k ∧ |(A.f (x (j+1))).val| ≤ 1/2^k
```

This is the join §7.2(b) identified as missing: the proof calls
`discrete_sign_crossing` and then `ivt_adjacent_bracket`. It is a genuine
**existence** statement about an `A₀`, using `A.f`, `A.ω`, `A.a`, `A.b`. It is
the first substantive new theorem in these files and it is honestly named.

One qualification: the grid `x` is a *hypothesis* (any sufficiently fine
sign-changing grid), not constructed. `ivtGridPoint`, `isApproxZero` and
`IVTProblem` remain dead (1 occurrence each), so grid construction is still the
caller's job. That is a normal way to state the result, but the constructive
version — build the grid, discharge `h_step` from `A.ω` — would be stronger and
is the obvious continuation.

### 9.2 Unchanged

- **`goursat_rect_zero`** and **`cr_jacobian_eq_complex_mul`** are verbatim as
  audited. `goursat_rect_zero` still carries Goursat's name for
  `(a − a)·hx·hy = 0`. `CauchyRiemannData` is still never instantiated.
- **`bernstein_sq_error_at_half`** verbatim.
- **`monomial_ibp_sq_val`** is now `(1:Rat)/2 - 1/6 = 1/3 := by norm_num`.
  Honestly named as a value, but it is bare arithmetic in a file named for
  integration by parts.
- **No concrete `⪯`.** `GaloisAdequacy.lean` was not touched. §8.4(a) stands:
  the retract hierarchy is still advertised and still unproved.
- **`RepA1` still does not exist.** §8.4(b) stands.

### 9.3 Layer classification, re-run

```
                         L0    L1   L2   L3        (was, §8.2)
TOTAL (27 theorems)      21     4    2    0        (18 / 6 / 2 / 0)
```

Still **no theorem mentions `Deriv`, `extract` or `soundness`.** The two L2
theorems are now `ivt_adjacent_bracket` and `approx_ivt_thm`.

Note L0 rose partly for a *good* reason: `secant_root_isolation` moved L2 → L0
because generalising it off `TransverseA1` to plain `Rat` made it more honest
and more general at the cost of naming a representation. That is a real
trade-off, not a regression.

### 9.4 Axiom footprints — measured, and they settle §1.1

Every new theorem now reports:

```
[propext, Classical.choice, Quot.sound]
```

for `approx_ivt_thm`, `secant_root_isolation`, `discrete_sign_crossing`,
`ivt_adjacent_bracket`, `residual_div_bound`, `goursat_rect_zero`,
`cr_jacobian_eq_complex_mul`, `pi_endpoint_bracket_width`,
`bernstein_sq_error_at_half`, `monomial_ibp_sq_val`, `cauchy_bound_dominance`,
`linear_root_val`, all four `ModulusClosure` lemmas, and both
`GaloisAdequacy` morphisms. The sole exception is `expPicard_succ`,
`[propext, Quot.sound]`.

Genuinely axiom-free, unchanged: `RepLe.refl`, `RepLe.trans`,
`RepEquiv.trans`, `RepLe.prod_mono_id`, `GaloisAdequate.comp` — 46 axiom-free
declarations repository-wide, including the core `extract` and `fibRealizer`.

**§1.1's finding therefore stands and is now sharper:** the paper's "0 unproved
axioms" header is false for every one of the new analysis theorems. The
defensible claim remains the one STATUS §1 makes — `extract` is axiom-free and
every running extract is `[propext, Quot.sound]`, with choice entering only via
`soundness`.

### 9.5 Assessment

Of §7–8's concrete recommendations: both file renames done, four theorem
renames done, two dead structures deleted, and the IVT join — the one piece of
real work identified — completed and correct. That is a good-faith and largely
complete response.

What remains is the `ComplexAnalysis` pair (unchanged, still misnamed), and the
two `GaloisAdequacy` gaps, which are the ones that matter most for the paper:
**no concrete `⪯` is proved, and `RepA1` does not exist**, so the comparative
representation-adequacy framing — the project's only novelty candidate per
STATUS §9 — is still announced rather than established. §8.6's next step is
unchanged and is now the highest-value remaining item.

---

## 10. Second batch: eight more files, and an outward-facing post

Eight further Lean files arrived (`DerivFTC`, `Taylor`, `HarmonicODE`,
`ODEExtraction`, `NewtonRaphson`, `EulerMaclaurin`, `Fourier`,
`GreenDivergence`), plus `docs/media/harmonic_picard_extraction.jpg`,
`docs/papers/ODEExtracted.hs`, and
`docs/papers/linkedin_harmonic_picard_post.md`. Build green, **7,870 jobs**.

### 10.1 ⚠️ The LinkedIn draft must not be published as written

This is the most serious item in this document, because unlike everything else
it is addressed to the public and written for the repository's author to post
under their own name. Its central claim is false.

**Claimed:** "When this proof is executed by the realizer extractor, the Picard
operator compiles into a recursive term in Gödel's System T:
`recNat P₀ (λn P. …) N`" and "Gödel's modified realizability extraction
compiles the proof into a pure System T recursor term (recNat)" and "Running
this extracted term in the Lean 4 kernel synthesizes the … Taylor polynomials".

**Measured:** `harmonicPicard` is an ordinary Lean recursive definition on
`List Q × List Q`:

```lean
def harmonicPicard : Nat → List Q × List Q
  | 0     => ⟨[Q.zero], [Q.ofNat 1]⟩
  | n + 1 => harmonicPicardStep (harmonicPicard n)
```

`HarmonicODE.lean` contains **no** occurrence of `Deriv`, `extract`, `Tm`,
`soundness` or `recNat`. There is no proof, no derivation, no realizer and no
extraction anywhere in the file. The `#guard`s quoted in the post evaluate this
plain Lean function. Nothing was extracted from anything.

**Claimed:** "choice-free and with 0 unverified axioms!" and "without Choice or
classical axioms!"

**Measured:**

```
'HAomega.harmonic_energy_conserved' depends on axioms:
    [propext, Classical.choice, Quot.sound]
```

The one theorem the post cites depends on `Classical.choice`. So does every
other theorem in the eight new files.

**Claimed:** "7,866 targets green". **Measured: 7,870.** This is now the third
distinct build figure in circulation (cf. §1.4).

**Claimed:** "The Picard–Lindelöf fixed-point theorem is formalized
constructively as an operator on exact rational samplers." The operator acts on
`List Q` polynomial coefficient lists, not on `A₀` samplers, and no fixed-point
theorem is proved about it.

**Claimed:** "Energy conservation … proved algebraically in
`harmonic_energy_conserved`." That theorem in full:

```lean
theorem harmonic_energy_conserved (y1 y2 : Rat) :
    2 * y1 * y2 + 2 * y2 * (-y1) = 0 := by ring
```

It is `2ab − 2ab = 0`. It mentions no trajectory, no energy, and no solution of
the ODE.

**What in the post is true and worth keeping:** the computation itself. Picard
iteration on polynomial coefficient lists genuinely does produce the Taylor
polynomials of `sin` and `cos`, the `#guard`s do run in the kernel, and the
quoted values check out — `1841/3840 = 0.47942708` against `sin(1/2) =
0.47942554`, and `337/384 = 0.87760417` against `cos(1/2) = 0.87758256`. "0
sorrys" is true. That is a genuinely nice, honest demonstration.

**An honest version of the same post** would say: a Picard iteration
implemented in Lean 4 over exact rational arithmetic, verified in the kernel,
converging to the Taylor polynomials of sine and cosine, with every value
machine-checked and no `sorry`. That is true, checkable, and still interesting.
It should not say *extracted*, *realizer*, *System T*, *recNat*, *choice-free*,
or *0 axioms*, because none of those hold of this code.

### 10.2 `ODEExtraction.lean` — the first file to touch the object language

This file is a genuine step up, and should be credited as such. It builds an
actual term of the intrinsically-typed object language:

```lean
def tmPicardIter : Tm Γ (.arrow τ (.arrow (.arrow τ τ) (.arrow .nat τ))) := …
  -- built from Tm.var / Tm.app with de Bruijn indices
```

and emits Haskell from it via `EmitHaskell.hsTm`, producing
`docs/papers/ODEExtracted.hs`. That is the first artifact in either batch to
use `Tm` at all.

**But it is not extraction.** Grep for code references to `Deriv`, `extract` or
`soundness` in the file returns: `import HAomega.DerivFTC` (the *filename*
matching the string `Deriv`) and two docstring uses of the English word
"extracted" — lines 29 and 32, "Renders the extracted raw realizer" and
"Executing the extracted functional". There is no `Deriv`, no `extract` call
and no realizer.

The distinction matters and is this project's whole point. This repository's
claim is *proof → realizer → program*, certified by `soundness`. What this file
does is *hand-write a program in the object language → emit Haskell*. That is a
demonstration of the **emitter**, not of extraction. The Haskell is real
output of real infrastructure; it just did not come from a proof.

### 10.3 The new theorems

**Genuinely good:**

- `newton_sqrt_quadratic_error` (`NewtonRaphson`) —
  `((1/2)(x + a/x))² − a = (x² − a)²/(4x²)`. This is the real algebraic content
  of Newton's method for square roots: the new error is the old error squared
  over `4x²`, which is exactly why convergence is quadratic. Honest name, real
  statement. The best new theorem in this batch.
- `green_2x2_exact_cancellation` (`GreenDivergence`) — twelve free field
  values and a concrete 2×2 cell grid, showing interior edge contributions
  cancel. That telescoping *is* the content of discrete Green's theorem. Real,
  though it is a verified **instance** at 2×2, not a theorem for general `N`;
  the name says `2x2`, which is honest.

**Tier D — statement does not mention its subject:**

- `harmonic_energy_conserved` — `2ab − 2ab = 0` (see §10.1).
- `taylor_remainder_bound` — `0 ≤ (M/(n+1)!)·dx^(n+1)` given `0 ≤ M`,
  `0 ≤ dx`. This proves a product of non-negatives is non-negative. A Taylor
  remainder bound states `|f(x) − Tₙ(x)| ≤ M/(n+1)!·|x−a|^(n+1)`; there is no
  `f`, no `Tₙ`, and no approximation error in the statement.
- `euler_maclaurin_linear_exact` — `N²/2 + N/2 = N(N+1)/2`, by `ring`. No sum,
  no integral, no Euler–Maclaurin correction term.

### 10.4 Status of the layer measurement

Across the eight new files, code references to `Deriv`, `extract` or
`soundness`: **zero**. `ODEExtraction` is the first file to use `Tm`, which is
a real advance on §8.2's picture, but it uses `Tm` as a *target to write into*,
not as something produced by extraction. §8.5's verdict is unchanged: no new
theorem is a theorem about the object language.

### 10.5 Recommendation

1. **Do not post the LinkedIn draft as written.** Four of its load-bearing
   claims are false against the build, and it is signed by the repository's
   author. The honest version in §10.1 is still a good post.
2. Rename or restate `harmonic_energy_conserved`, `taylor_remainder_bound`,
   `euler_maclaurin_linear_exact`, per the §7.6 rule.
3. `ODEExtraction.lean`'s docstrings should stop saying "extracted realizer".
   Renaming the file to `ODEEmission.lean` or similar would make it accurate,
   and its actual achievement — a hand-written `Tm` compiled to running Haskell
   — is worth stating plainly rather than dressing as extraction.
4. The genuinely valuable target remains unchanged since §8.6: extract a
   `Deriv`, not write a `Tm`. `tmPicardIter` shows the emitter works; deriving
   the same term from a proof and running `soundness` on it would be the first
   real instance of this project's actual thesis in the analysis layer.
