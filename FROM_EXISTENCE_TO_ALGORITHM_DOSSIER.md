# From Existence to Algorithm: fact-check dossier

**Scope:** `from-existence-to-algorithm-complete.md`, checked against the
local repository at commit `f424383` on 2026-09-02.

**Standard:** claims are tagged `[run]` when verified by command output in
this audit, `[src]` when verified by direct source read, `[doc]` when checked
against existing repository documentation, and `[ext]` when checked against
external background sources.

**Build checked:** `lake build HAomega.SquareRoot HAomega.UniformContinuity
HAomega.BanachModulus HAomega.IntegralModulus HAomega.QAnalysis` completed
successfully: 7,801 jobs. The build produced two warnings unrelated to the
drafted claims: unused variables / unused simp argument in Hydra code and an
unused variable `j` in `HAomega/IntegralModulus.lean`.

---

## Executive Verdict

The draft is broadly aligned with the repository's intended narrative, but it
is not correct enough to publish unchanged.

The main corrections are:

1. **Post 2 over-describes the proof.** `sqrtApproxD` is not currently a
   bespoke grid-walking induction; it is an instantiation of `spernerD` with
   the square-colouring function. The runtime facts `k = 362` and `181/128`
   are correct. `[src]` `[run]`
2. **Post 2's "bound is assumed rather than proved" is stale for the current
   full repository.** `SquareRoot.lean` itself leaves `K` to the caller, but
   `QAnalysis.lean` proves `sqrt_premises` for `q >= 0` using `sqrtBound`.
   If the post is intentionally about only the extracted derivation module,
   say so; if it is about the repository at `f424383`, say the bound has a
   meta-level discharge in `QAnalysis.lean`. `[src]` `[run]`
3. **Post 4's "no axiom" wording for the scale arithmetic is wrong.**
   `uniContLipD` and `uniModulus` are `[propext, Quot.sound]`; the supporting
   arithmetic theorem `Q_lip_scale` reports `[propext, Classical.choice,
   Quot.sound]`. The right claim is "choice-free for the extracted derivation
   and realizer; `Classical.choice` appears in the meta-level arithmetic
   proof layer." `[run]`
4. **Post 6 is stale and internally inconsistent with current code.**
   `riemannIntegralD` now uses the concrete System T Riemann upper-sum term as
   the existential arrow witness. It is no longer true that the arrow witness
   is merely supplied. What remains assumed is the Lipschitz premise about
   that Riemann-sum function; the module itself says the internal deduction of
   that premise is blocked by missing absolute-value, division, and finite-sum
   rules. `[src]` `[run]`
5. **Post 7's final audit claim is too broad.** The listed declarations in
   Posts 2-6 do report `[propext, Quot.sound]`, but many analysis support
   theorems in `QAnalysis.lean` report `[propext, Classical.choice,
   Quot.sound]`. Say "the extracted derivations/running realizers named here"
   if that is what is meant. Do not write "the whole chain" without separating
   the meta-level arithmetic discharge layer. `[run]`
6. **The draft calls the Post 5 theorem "Banach's fixed-point theorem."**
   The formal statement is a convergence-modulus theorem for consecutive
   iterate gaps under a dyadic `1/2` contraction plus seed premise. It does not
   construct a fixed point in a complete metric space or prove uniqueness.
   The prose should call it "the extracted Banach-style stopping rule" or
   "the contraction-iteration modulus" unless the classical Banach theorem is
   being discussed informally. `[src]`

---

## External Background Checks

The mathematical background claims are mostly standard, with two wording
risks.

* **Modified realizability evidence types.** The draft's mapping
  `forall n exists k` to a function producing witnesses matches the standard
  modified-realizability reading: atomic formulas have unit/trivial evidence,
  implication maps to function type, conjunction to product type, universal
  quantification to function type, and existential quantification to a product
  carrying the witness. `[ext]`
* **HA^omega / System T connection.** The draft's "HA^omega proofs extract
  System T terms at finite types" matches the standard setting. `[ext]`
* **Continuity of System T-definable functionals.** The draft's informal
  point that type-2 System T programs can only query finite information before
  terminating is directionally correct, but "continuity by its very existence
  as a program" should be read as a theorem of the formal model, not as a
  proof-free slogan. The local theorem is `extract_continuous2`, not a generic
  runtime observation. `[src]` `[ext]`
* **Constructive real numbers.** The representation of reals by rational
  approximation data with a modulus/preassigned convergence rate is standard
  Bishop-style constructive analysis. The draft's simplified `forall n exists
  k` grid-bracket is a specific representation of a nonnegative real
  approximation, not a complete general definition of all constructive reals.
  `[ext]`
* **Goodstein / hydra background.** It is externally correct that Goodstein's
  theorem is unprovable in PA and proved by ordinal methods below epsilon_0;
  Kirby-Paris hydra games are also standard PA-independence examples. The
  local HAomega code, however, formalizes termination/extraction, not PA
  independence. Keep the independence claim as background about the previous
  series, not as a claim formalized in this repository. `[doc]` `[ext]`
* **Proof mining.** The statement that Kohlenbach-style proof mining extracts
  effective bounds/moduli from proofs in analysis is standard. `[ext]`

External references consulted:

* Kreisel-style modified realizability and HA^omega evidence types:
  https://www.researchgate.net/publication/220368322_A_Type_Theory_which_is_complete_for_Kreisel%27s_Modified_Realizability
* Bishop constructive mathematics / computable analysis:
  https://www.sciencedirect.com/science/article/pii/S0304397598002850
* Stanford Encyclopedia of Philosophy on constructive mathematics:
  https://plato.stanford.edu/entries/mathematics-constructive/
* Stanford Encyclopedia of Philosophy on constructive reals:
  https://plato.stanford.edu/entries/continuity/
* System T definable functionals are continuous:
  https://www.sciencedirect.com/science/article/pii/S157106611300056X
* Goodstein theorem background:
  https://mathworld.wolfram.com/GoodsteinsTheorem.html
* Goodstein / incompleteness background:
  https://plato.stanford.edu/entries/goedel-incompleteness/
* Proof mining / uniform bounds:
  https://drops.dagstuhl.de/entities/document/10.4230/DagSemProc.05021.13

---

## Post 1: Opening Frame

### Correct

* The move from first-order arithmetic examples to higher-type analysis is a
  faithful high-level description of the HAomega branch. `[doc]`
* HA^omega is the right local framing: the code has finite types, function
  types, rational and dyadic base types, `Formula`, `Deriv`, `MR`, extraction,
  soundness, and continuity machinery. `[src]`
* "Function as rule plus modulus" is compatible with the repository's
  constructive-analysis strand: `UniformContinuity.lean` extracts a modulus,
  `IntegralModulus.lean` packages a function with a modulus, and `QAnalysis`
  later develops richer representation layers. `[src]` `[doc]`

### Needs Qualification

* "There is no datatype of reals. sqrt(2) will never be a value." Locally this
  is true for the object language in these posts: there are `rat` and `dyad`
  types, not a completed real-number base type. But later files introduce
  approximating representations such as `E0`, `E1`, and Cauchy-style data.
  Say "there is no completed real-number base type in the object language used
  by these posts." `[src]` `[doc]`
* "Every functional the machine can produce is continuous by its very
  existence as a program" is too compressed. Locally, the checked statement is
  `extract_continuous2` for extracted terms in the tracked/continuous
  machinery, with footprint `[propext, Quot.sound]`. `[run]`
* "No classical axioms anywhere in the chain" is too broad if "chain" includes
  meta-level analysis proofs in `QAnalysis.lean`; many of those use
  `Classical.choice`. It is accurate for the named extracted derivations and
  running extracts in Posts 2-6, which report `[propext, Quot.sound]`. `[run]`

---

## Post 2: Square-Root Approximation

### What The Code Actually States

`HAomega/SquareRoot.lean` defines:

```lean
sqrtApproxD :
  forall q n K,
    colour(q,n,0) = 0 ->
    colour(q,n,K) = 1 ->
    exists k, k < K and colour(q,n,k) != colour(q,n,k+1)
```

Source lines: `SquareRoot.lean` lines 12-18 and 70-88. The proof instantiates
`spernerD` at `sqColour`; it is not a separate arithmetic induction through
the grid. `[src]`

### Correct

* `sqrtApproxX (Q.ofNat 2) 8 512 == 362`. `[src]` `[run]`
* `sqrtApprox (Q.ofNat 2) 8 512 == Q.of 181 128`. `[src]` `[run]`
* The bracket guard checks the colour at the extracted crossing and just past
  it for `sqrt(2)` for `n = 0..5`. `[src]` `[run]`
* A wrong `k` can refute the specification. The conclusion contains both a
  strict bound below `K` and a colour disagreement at adjacent indices. `[src]`
* Axiom reports from the build:

```text
sqrtApproxD  [propext, Quot.sound]
sqrtApproxX  [propext, Quot.sound]
```

### Incorrect Or Stale

* "The derivation is an induction that walks the grid" is inaccurate for this
  declaration. The induction is in `spernerD`; `sqrtApproxD` reuses it by
  instantiation. Use "the extracted search comes from the one-dimensional
  Sperner scan." `[src]`
* "The Archimedean bound is discharged externally / supplied rather than
  proved inside it" is only true if "inside it" means inside
  `SquareRoot.lean`'s object-level derivation. At repository level,
  `QAnalysis.lean` proves `sqrt_premises` for every `q >= 0` with
  `sqrtBound`. Axiom report:

```text
sqrt_premises [propext, Classical.choice, Quot.sound]
```

This is a meta-level Lean proof, not a new object-level `Deriv` rule. `[src]`
`[run]`

### Suggested Rewrite

Say:

> `sqrtApproxD` is the one-dimensional Sperner theorem instantiated at the
> square-colouring. The object-level derivation still takes the endpoint
> colours as premises; in the full repository, `QAnalysis.sqrt_premises`
> discharges those premises for `q >= 0` by a meta-level rational-arithmetic
> proof.

---

## Post 3: Function-Variable Crossing Solver

### What The Code Actually States

`fnCrossingD` is in `HAomega/SquareRoot.lean`, lines 214-233. It quantifies
over `F : rat -> rat`, target `y`, precision `n`, and bound `K`, then assumes
endpoint colour premises and produces adjacent colour disagreement. `[src]`

### Correct

* The solver is a higher-type extracted term accepting a function argument.
  `[src]`
* It is an instantiation of one-dimensional Sperner, not an analysis-specific
  theorem. `[src]`
* The table entries in the draft are guarded in the source:
  `2x + 1 = 5 -> 2`, `x^3 + x = 10 -> 2`, `x^5 = 32 -> 2`, `x^2 = 2 ->
  181/128` at `2^-8`, and `x^4 = 2 -> 19/16` at `2^-4`. `[src]` `[run]`
* Axiom reports:

```text
fnCrossingD  [propext, Quot.sound]
fnCrossingX  [propext, Quot.sound]
```

### Needs Qualification

* The phrase "for any F supplied" needs the endpoint-colour premise. The
  formal theorem does not prove that arbitrary `F` crosses `y`; it says that
  if the supplied endpoint colours differ, a crossing index exists. `[src]`
* "A working inverse" is too strong as a global inverse-function theorem.
  Fixing `F` and varying `y` gives a callable pointwise solver under bracket
  premises. It does not prove injectivity, monotonicity, total inverse, or a
  modulus for `F^{-1}`. `[src]`
* "Some with no closed-form inverse" is not a formal claim in the repository.
  It is harmless mathematically as prose, but do not make it part of the
  certification claim.

---

## Post 4: Uniform Continuity And Modulus

### What The Code Actually States

`uniContLipD` is in `HAomega/UniformContinuity.lean`, lines 114-138. Its
premise is `ucLipBound`, an object-level formula expressing
`|f x - f y| <= 2^j |x-y|` via `qlt(...)=0`, and the conclusion is a modulus
statement with witness `M = n + j`. `[src]`

### Correct

* The theorem quantifies over `f : Q -> Q` and `j`. `[src]`
* The premise is a genuine Lipschitz-style bound, not the conclusion with the
  desired modulus already written into it. `[src]`
* The extracted `uniModulus` returns:
  doubling with `j=1`: `[1,2,3,4,5,6]`; translation with `j=0`:
  `[0,1,2,3,4,5]`; quadrupling with `j=2`: `[2,3,4,5]`. `[src]` `[run]`
* The mutation note "replace `M = n+j` with `M = n` fails to build" is present
  as a source comment and is consistent with the proof's use of
  `convQLipScale`. I did not run a mutation build in this audit. `[src]`
* Axiom reports:

```text
uniContLipD [propext, Quot.sound]
uniContD    [propext, Quot.sound]
uniModulus  [propext, Quot.sound]
```

### Incorrect Or Stale

* The draft says the arithmetic rule is "validated once, in Lean's model of Q,
  with no axiom." The build reports:

```text
Q_lip_scale [propext, Classical.choice, Quot.sound]
```

So the derivation/realizer is choice-free, but the meta-level arithmetic proof
uses `Classical.choice`. `[run]`
* The draft says "the smaller rules exist in the rule base; decomposing the
  big one into them is bookkeeping." `QAnalysis.lean` and `QArith.lean` do
  prove many rational arithmetic facts, but the object-level derivation still
  uses `convQLipScale` as a single rule. Do not imply the decomposition is
  already present in `Deriv`. `[src]` `[run]`
* The draft says Post 2's bound gap and Post 4's arithmetic rule are "the same
  gap." That is narratively fair, but technically they are different layers:
  `sqrt_premises` is now discharged in `QAnalysis.lean`; `uniContLipD` still
  uses an object-level scale-conversion rule. `[src]`

### Suggested Rewrite

Say:

> The extracted derivation uses one object-level conversion rule,
> `convQLipScale`. The rule's soundness rests on rational arithmetic proved in
> Lean; those meta-level arithmetic lemmas carry `Classical.choice`, while the
> extracted theorem and its running realizer remain `[propext, Quot.sound]`.

---

## Post 5: Banach / Stopping Rule

### What The Code Actually States

`banachContractionD` is in `HAomega/BanachModulus.lean`, lines 165-254. It
assumes:

* a function variable `T : Q -> Q`;
* a dyadic `1/2` contraction premise;
* a seed premise `close(k0, x0, T x0) = 1`;
* then proves `forall n exists N forall d, close(n, x_{N+d}, x_{N+d+1}) = 1`
  with witness `N = n`. `[src]`

### Correct

* The proof uses object-level induction (`Deriv.ind`) for an orbit invariant.
  `[src]`
* The contraction premise is used in the induction step. `[src]`
* The extracted stopping function returns `N(n) = n` in the guarded examples.
  `[src]` `[run]`
* The table for the three contractions is source-guarded:
  `1 + y/2` from `1`, `3 + y/2` from `5`, and `y/2` from `1`. `[src]` `[run]`
* Boundary checks for `T(y)=1+y/2` verify that the step just before `N=n`
  fails strict closeness for `n=1` and `n=4`. `[src]` `[run]`
* Axiom reports:

```text
banachContractionD [propext, Quot.sound]
banachStoppingN    [propext, Quot.sound]
```

### Needs Qualification

* This is not the full Banach fixed-point theorem as classically stated. It
  does not prove completeness, existence of a limit point, or uniqueness. It
  proves a certified convergence/stopping modulus for consecutive iterate gaps
  under a dyadic contraction and seed condition. `[src]`
* The phrase "fixed point 2/6/0" in the examples is a value-level observation
  about the displayed affine functions, not a theorem produced by
  `banachContractionD`. `[src]`
* The theorem certifies consecutive gap closeness from step `N` onward, not
  directly "distance to the fixed point" unless additional mathematics bridges
  gap convergence to point convergence. `[src]`

### Suggested Rewrite

Use "Banach-style contraction stopping rule" in the technical claims, and
reserve "Banach's fixed-point theorem" for the informal motivation.

---

## Post 6: Integral / Arrow-Type Witness

### What The Code Actually States

`riemannIntegralD` is in `HAomega/IntegralModulus.lean`, lines 104-139. It
quantifies over integrand `f`, scale `j`, and partition count `N`, assumes a
Lipschitz premise for the concrete Riemann upper-sum function, and then
exists-introduces:

```lean
G := riemannUpperSumClosed f N
M := n + j
```

Source lines 116-121 explicitly name the concrete System T witness. `[src]`

### Correct

* The existential is at arrow type and the realizer type is a pair
  `(Q -> Q) x (Nat -> Nat x ...)`. `[src]`
* `riemannUpperSumClosed` is an intrinsically typed System T term. `[src]`
* The kernel guards check:
  constant integrand `1` integrates to `x` at tested points;
  identity integrand at `x=1` gives `3/8`, `7/16`, `15/32` for `N=4,8,16`;
  `F(0)=0` at tested cases;
  `integralModulus` gives `n+j`. `[src]` `[run]`
* Axiom reports:

```text
riemannIntegralD [propext, Quot.sound]
integralF        [propext, Quot.sound]
integralModulus  [propext, Quot.sound]
```

### Incorrect Or Stale

* The draft says the witness is supplied rather than built from the integrator
  term. That is stale for `f424383`: the source now introduces
  `riemannUpperSumClosed f N` as the existential witness. `[src]`
* The real remaining gap is not "one strip induction" exactly as written. The
  module header lists the current blockers more concretely: object-level
  absolute-value conversion rules, rational division field equations, and
  finite-sum difference bounding rules for `tmRiemannSum`. `[src]`
* The draft's theorem shape omits the partition-count parameter `N` and the
  assumed Lipschitz premise on the Riemann-sum function. The formal theorem is
  about the finite Riemann-sum operator at a supplied `N`, not a completed
  integral as a limit object. `[src]`
* The sentence "the arrow-type theorem above -- every 2^j-Lipschitz function
  has a certified modulus, witness delivered as a function-with-certificate"
  describes the wrapper shape, but if presented as "the integral exists" it
  overclaims. The certified object is the finite upper-sum function under its
  Lipschitz premise. `[src]`

### Suggested Rewrite

Say:

> The arrow witness is now the concrete System T term
> `riemannUpperSumClosed f N`. The remaining unproved part is the internal
> derivation that this Riemann-sum function satisfies the required Lipschitz
> premise from usable assumptions on the integrand; today that premise is
> assumed by `riemannIntegralD`.

---

## Post 7: ODE Composition

### Correct

* For `y' = 1 + y/2 - y`, forward Euler with step `1` gives
  `y_{n+1} = 1 + y_n/2`. The fixed point of this affine update is `2`.
  `[src]`
* `picardT` in `BanachModulus.lean` is exactly `1 + y/2`, and the guarded
  orbit-related stopping table uses `x0 = 1`. `[src]`
* `fnCrossingD` can solve the fixed-point equation by instantiating a crossing
  problem with `F(x) = x/2`, target `1`, suitable precision, and bound. This
  is mathematically valid and fits the interface. `[src]`
* The composition point is structurally sound: both the crossing solver and
  the stopping rule accept functions as parameters. `[src]`

### Needs Qualification

* I did not find a dedicated source guard in the audited files that performs
  exactly the Post 7 composition in one declaration for this ODE. The pieces
  are guarded separately: `fnCrossingD` examples in `SquareRoot.lean` and
  `picardT` stopping examples in `BanachModulus.lean`. `[src]`
* "Ask for the steady state within `2^-n` and the stopping rule answers" is
  stronger than what `banachContractionD` states. It certifies consecutive
  iterate gaps, not direct distance to the fixed point. Add the missing bridge
  or phrase it as "prices the discrete contraction's consecutive-step
  convergence." `[src]`
* "The steady state is not computed and then trusted; it is bracketed by a
  theorem" is accurate for the crossing-solver half only under endpoint
  colour premises. `[src]`

---

## Cross-Cutting Axiom Audit

### Verified From This Audit's Build

Named extracted-analysis declarations:

```text
spernerD             [propext, Quot.sound]
spernerX             [propext, Quot.sound]
sqrtApproxD          [propext, Quot.sound]
sqrtApproxX          [propext, Quot.sound]
fnCrossingD          [propext, Quot.sound]
fnCrossingX          [propext, Quot.sound]
uniContLipD          [propext, Quot.sound]
uniModulus           [propext, Quot.sound]
banachContractionD   [propext, Quot.sound]
banachStoppingN      [propext, Quot.sound]
riemannIntegralD     [propext, Quot.sound]
integralF            [propext, Quot.sound]
integralModulus      [propext, Quot.sound]
```

Meta-level arithmetic / analysis support layer:

```text
sqrt_premises        [propext, Classical.choice, Quot.sound]
Q_lip_scale          [propext, Classical.choice, Quot.sound]
doubling_lipschitz   [propext, Classical.choice, Quot.sound]
translation_lipschitz [propext, Classical.choice, Quot.sound]
quadrupling_lipschitz [propext, Classical.choice, Quot.sound]
```

Core machinery:

```text
extract              no axioms
Tm.eval              [propext, Quot.sound]
soundness            [propext, Classical.choice, Quot.sound]
extract_continuous2  [propext, Quot.sound]
```

### Required Wording Discipline

Safe wording:

* "The named extracted derivations and running realizers in the series are
  choice-free: `[propext, Quot.sound]`."
* "`extract` itself is axiom-free."
* "`soundness` and meta-level arithmetic/analysis proofs may use
  `Classical.choice`; the build prints those footprints."

Unsafe wording:

* "No classical axioms anywhere in the chain."
* "The kernel says there was nothing to print."
* "Every theorem above depends only on `[propext, Quot.sound]`" if "above"
  includes `QAnalysis` discharges or richer analysis theorems.

---

## Checklist For Revising The Draft

1. Post 1: replace global "no classical axioms anywhere" with the axiom
   split above.
2. Post 2: say the proof is Sperner instantiation; mention `sqrt_premises`
   if claiming the full repository now proves the bound.
3. Post 3: keep the five examples, but qualify "inverse" as pointwise under
   bracket premises.
4. Post 4: keep `M(n)=n+j`, but correct the axiom wording around
   `convQLipScale` / `Q_lip_scale`.
5. Post 5: rename the formal result from "Banach fixed-point theorem" to
   "Banach-style contraction stopping rule" or explicitly explain the formal
   theorem is a convergence-modulus fragment.
6. Post 6: replace the stale "witness supplied" gap with the current
   "concrete finite Riemann-sum witness, Lipschitz premise still assumed"
   gap.
7. Post 7: qualify the stopping rule as consecutive-gap convergence unless a
   fixed-point-distance theorem is added.
8. Final audit: print the actual axiom split; do not collapse the support
   layer and the extracted-program layer into one sentence.

