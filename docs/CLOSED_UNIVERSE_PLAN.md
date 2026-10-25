# A Certified, Extraction-Backed Algebra of Exponential-Type Jets in $\mathrm{HA}^\omega$

**Subtitle:** *Closed Under Ring Operations, $\frac{d}{dx}$, and $\int_0^x$, with Kleene–Kreisel Causality, `E0`/`E1` Embeddings, and the Exponential-Type vs. Cauchy–Hadamard Trade-Off*

---

## 0. The Goal: a Minimal Closed Universe of Analysis

The target is a small, closed universe inside $\mathrm{HA}^\omega$ in which
$+, -, \times, \frac{d}{dx}, \int$, $\exp$, $\sin$, $\cos$, Taylor series and
Fourier series all live, with the algebraic laws among them *provable in the
object logic* and every existence statement yielding an extracted program.
The sections below record what is mechanized so far; this section records the
goal and where we stand (2026-10-23).

| Pillar | State |
| :--- | :--- |
| 1. **Objects and operations.** Jets $\mathbb{N}\to\mathbb{Q}$ with `tmJetAdd/Sub/Mul/Deriv/Integ`, exp/sin/cos jets, as System T terms | done |
| 2. **Generation by proof-computed ODE solving.** The universe as the closure of constants under $+,-,\times,\int$ and solving $y = A + \int F(y)$ | done for single equations (`genSolveD`), two-variable systems (`genSolve2D`) and systems of any size (`genSolveND`, `PolyODESystemN.lean`), every polynomial–integral right-hand side; sin/cos (#31), exp, tan, Duffing are instances |
| 3. **Algebra laws inside `Deriv`.** FTC2, product and chain rules, $\exp' = \exp$, $\sin' = \cos$, $\sin^2+\cos^2 = 1$ | Value equality `s ≈ t` (QUESTIONS.md item 18, resolved (b)): `Formula.qeqv`, laws by the one rule `Deriv.qlaw`. Derived (`QEquiv.lean`): $\exp' \approx \exp$, $\sin' \approx \cos$, $\cos' \approx -\sin$, FTC1 $D(\int c) \approx c$, FTC2 $\int(Dc)(n+1) \approx c(n+1)$, and the product rule $D(fg) \approx Df\cdot g + f\cdot Dg$ (`ProductRuleD.lean`, induction over the Cauchy sum), $\sin^2+\cos^2 \approx 1$ (`PythagorasD.lean`), and the chain rule $D(f\circ g) \approx Dg\cdot((Df)\circ g)$ over the System T composition `tmJetComp` (`ChainRuleD.lean`). Done 2026-10-25 |
| 4. **Closure under $\div$ and $\circ$.** $1/(1-G)$ and $F(G)$ for $G(0)=0$ | inverses done, proof-computed: `shiftSolveD` solves $Y = A + x\cdot F(Y)$, so $1/(1-xH)$ for every $H$ (#32: $1/(1-x-x^2)$, Fibonacci exactly). Composition with ODE-defined functions is a `genSolveD` instance (`ComposeSolve.lean`); its agreement with `Jet.compZero` is proved for every $G$ (`ComposeProof.lean`: chain rule + uniqueness) |
| 5. **Evaluation.** Bounds and moduli from jets to values at points | metatheory (`toE0`/`toE1`). In `Deriv`: the Cauchy modulus is now proof-computed (`JetCauchyComputed.lean`, #33: induction on the precision, the tail halving per step); so are the continuity and differentiability moduli (`JetModuliComputed.lean`, #34, #35). For the whole universe: every expression has an explicit disk on which the proof-computed modulus is correct, through `soundness` (`UniverseEval.lean`: `UExpr.certifiedEval`, runnable `UExpr.approx`, choice-free). Open: a majorant theorem for arbitrary `InGPAC` systems; speed of evaluation through composition Roots: `UExpr.root` (`RootOperator.lean`) composes the evaluator with the bisection operator extracted from `bisectD` (`Bisection.lean`); `root_spec` is the approximate IVT on the certified disk, and roots of `f − y` give inverse-function values (`arcsin(1/5)`). |
| 6. **Fourier layer.** Trigonometric series as coefficient streams, $\frac{d}{dx}$, $\int$, convolution, the Taylor $\leftrightarrow$ Fourier bridge via $\sin(kx), \cos(kx)$ | value level done (`TrigPoly.lean`): trigonometric polynomials over $\mathbb{Q}[i]$ with $+,\times,\frac{d}{dx},\int$ and the Taylor bridge `toJet`, proved to commute with $\frac{d}{dx}$ and $\times$ and to send the modes to `cosFreq`/`sinFreq`. Modes from the proof-computed solver done (`FourierModesSolve.lean`, agreeing with `toJet`). System T terms done (`TrigPolyTerms.lean`, axiom-free, each proved to implement its value-level operation). Open: `∫` is partial here ($\int 1 = x$) |
| 7. **The universe as a class.** Which functions are in, and closure of that class under every operation (QUESTIONS.md item 19, resolved: polynomial-ODE functions) | `InGPAC` (`UniverseGPAC.lean`): a component of the solution of a polynomial–integral system with constant data, so each member comes with the proof-computed solver `genSolveND`. Closed under $+,-,\times,\int,\frac{d}{dx}$ (`InGPAC_add/sub/mul/integ/deriv`). Members: rational constants, $x$, $\exp$, $\sin$, $\cos$ (`UniverseMembers.lean`), so every expression in them under these operations is in the universe. The permissive `InUniverse` (`UniverseTrial.lean`, arbitrary closed jets as data — so it contains every System T jet) is closed under $+$ (`InUniverse_add`), $\times$ (`InUniverse_mul`, via the product rule `jetMul_leibniz_val`), $-$, $\int$ and $\frac{d}{dx}$ (`UniverseOps.lean`; $\frac{d}{dx}$ by symbolic differentiation of the right-hand side). Reciprocals: `InGPAC_inv` ($f(0)\ne 0 \Rightarrow$ some member $h$ has $f h = 1$), hence $\div$. Composition: `InGPAC_comp` ($f \circ (g - g(0))$, via the general chain rule `compZero_deriv_val` and an $\int$-free normal form). The universe is closed under $+,-,\times,\div,\int,\frac{d}{dx},\circ$. Fourier: $\sin(kx)$, $\cos(kx)$ and every trigonometric polynomial (via `TrigPoly.toJet`) are members (`UniverseFourier.lean`). Compiler: `UExpr.compile` turns every expression of the universe into a system, `UExpr.compile_correct` (`UniverseExpr.lean`). Next: the remaining algebra laws inside `Deriv` (pillar 3) |

**Order of work.** Pillar 6 (Fourier definitions and operations) → pillar 3
(item 18 decided 2026-10-24: `≈`; product rule, `sin²+cos²=1` and the chain rule done,
the last 2026-10-25) → pillar 5 in the logic.

### 0.1 Next phase: the six rooms (decided 2026-10-24)

**The vision.** In the author's words: a *complete and brief* "toy house" of
mathematical analysis — a minimal closed universe inside HA^ω and System T in
which the classical theorems of first-year analysis (Newton–Leibniz, the
intermediate value theorem, critical points, differential equations, Taylor and
Fourier series) hold without pathology, one can actually work, and in practice
everything behaves like numerical analysis, because every object and every
existence proof is a certified algorithm.

Why this universe and not pointwise functions: for black-box `C⁰`/`C¹`
functions (`E0`/`E1` here) Myhill's obstruction blocks computable
differentiation unless derivative moduli are carried by hand, and integration by
Riemann sums needs `2^{ω(k)}` evaluations. On polynomial-ODE analytic jets
(`UExpr`, `InGPAC`):
- `d/dx` and `∫₀ˣ` are one-step structural operations on coefficient streams;
- Newton–Leibniz holds coefficientwise inside `Deriv` (up to `≈`) and, on the
  certified disk, as a certified computation: a definite integral costs `O(k)`
  series terms, not `2^k` samples;
- bisection, extracted from induction on the logarithm of the grid size,
  composes with the certified evaluator into root-finding and inverse functions;
- ODE solving is native: guarded Picard iteration locks one coefficient per step;
- Taylor and Fourier meet through the trigonometric-polynomial bridge `toJet`.
Explicit coefficient bounds `(M, R)` exist for every `UExpr`; for arbitrary
`InGPAC` systems they exist too (`solN_geom_bound`, `SystemBound.lean`), computed from the system's
syntax by `sysParams` with the certified evaluator `GPACSys.approx` (`SystemEval.lean`, 2026-10-25).

| Room | Classical content | Tool in the universe | Done | Remaining |
| :--- | :--- | :--- | :--- | :--- |
| 1. Differential algebra | linearity, product rule, chain rule, `sin²+cos²=1` | `tmJetDeriv`, `tmJetMul`, `tmJetComp` | in `Deriv`: `exp′≈exp`, `sin′≈cos`, `cos′≈−sin`, FTC1, FTC2 (`QEquiv.lean`), product rule (`ProductRuleD.lean`), `sin²+cos²≈1` (`PythagorasD.lean`); the chain rule `chainRuleLawD` over the System T composition `tmJetComp` (`ChainRuleD.lean`) | — |
| 2. Integral calculus | FTC1, FTC2; `∫ₐᵇ f′ = f(b) − f(a)` | definite integral through the evaluator | `UExpr.defIntegral`, `defIntegral_spec`, pointwise Newton–Leibniz `UExpr.newtonLeibniz` (`DefiniteIntegral.lean`) | optional: a benchmark against the Riemann sums of `EFTC.lean` |
| 3. Zeros and inverses | intermediate value theorem, inverse functions | `UExpr.root` (extracted `bisect` + `UExpr.approx`) | approximate IVT on the certified disk (`Bisection.lean`, `RootOperator.lean`; `ln(41/40)`, `arcsin(1/5)` to `10⁻¹⁰`) | Newton's method (order item 4) |
| 4. Extrema | approximate Rolle / mean value theorem | bisection on `f′` | `UExpr.critical`, `critical_spec` (`CriticalPoints.lean`) | constructively only `\|f′(x)\| < ε`; a max/min claim needs more data (e.g. the sign of `f″`) |
| 5. Differential equations | existence, uniqueness | `genSolveND`, `UExpr.compile` | scalar, 2-variable and n-variable solvers, uniqueness, `InGPAC` closure | the general majorant `solN_geom_bound` (`SystemBound.lean`), computed `(M, R)` and the evaluator `GPACSys.approx` (`SystemEval.lean`), perturbation `solN_perturb_bound` (`SystemPerturb.lean`), all 2026-10-25; re-centering / stepping past the initial disk |
| 6. Fourier analysis | orthogonality, Parseval, Fourier coefficients | `TrigPoly` algebra, bridge `toJet`, modes from `genSolve2D` | `TrigPoly` `+, ×, d/dx, ∫`, `toJet`, System T terms | mean and inner product, mode orthogonality, Parseval for trigonometric polynomials (cheap, finite coefficient algebra); Fourier coefficients of general universe functions need a whole period, hence re-centering |

**Order:**
1. ~~The chain rule (room 1)~~ — done 2026-10-25. ~~`solN_geom_bound`, computed `(M, R)`, evaluator `GPACSys.approx`, perturbation bound~~ —
   done 2026-10-25; open: a memoized coefficient table (nonlinear systems are exponential today) —
   certified values for every member of the universe, not only `UExpr`.
2. **Re-centering / stepping**: re-expand at `x₀` (composition with `x + x₀`,
   already in the universe). Turns the disk-limited evaluator and solver into a
   global Taylor integrator; prerequisite for ODE solutions on `[0, 1]` and for
   Fourier coefficients of universe functions.
3. ~~Definite integrals (room 2) and approximate critical points (room 4)~~ — done 2026-10-24.
4. Newton's method with certified quadratic contraction (`f′` is in the
   universe; the `f″` bound comes from the coefficient bounds). Today Newton
   exists only for square roots on ℚ (`NewtonRaphson.lean`).
5. Room 6: mean, inner product, orthogonality and Parseval for trigonometric
   polynomials (any time; small); Fourier projection of universe functions after 2.

**What the house will still not contain**, by design: non-analytic functions
(`|x|`, steps, `max`) and functions satisfying no polynomial ODE (Γ, ζ); a
decision procedure for equality (`f ≈ g` is provable, not decidable); exact
choices (exact roots of arbitrary `f`, exact argmax) — only approximations.
These are the walls numerical analysis lives within too.

**Claims not to make:** Newton–Leibniz holds up to `≈`, not "on the nose";
"automatic `(M, R)` bounds" hold for `UExpr`, not yet for every `InGPAC` system;
evaluation is certified only on the disk `|x| ≤ 2^{-(R+1)}`, so values such as
`∫₀^{1/4} e^{sin x}` are not covered until step 2 (and composition evaluation is
slow, ~7 min for `e^{sin x}/(1+x²)` at `k = 20`).

**Presentation of the finished parts.** Until the universe is complete, the
delivered pillars are presented as program extraction from proofs worked out in
practice: algorithm-free specifications, proofs by induction, certified
extracts, with the proof-computed / explicit-witness / witness-style
classification kept explicit. This is a way to present the parts, not a
replacement for the goal.

---

## 1. Prior Art and What Is Mechanized Here

### 1.1. Prior Art in Computable Analysis and Stream Calculus
1. **Pointwise vs. Analytic Representations & Parameterized Complexity:**
   - The contrast between pointwise $C^1$ representations—where differentiation loses a regularity level and encounters Myhill's (1971) non-computability obstruction—and power-series representations where differentiation is computable goes back to **Pour-El & Richards (1989)** and **Müller (1987, 1995)**.
   - Parameterizing bit-complexity of analytic and Gevrey-class operators by explicit $(M, R)$ amplitude/radius majorant data was developed by **Kawamura, Müller, Rösnick & Ziegler (2015)** (*"Computational Benefit of Smoothness: Parameterized Bit-Complexity of Numerical Operators on Analytic Functions and Gevrey's Hierarchy"*).
2. **Coinductive Stream Calculus & Guardedness:**
   - Viewing Taylor series as streams $c : \mathbb{N} \to \mathbb{Q}$ on which differentiation $\mathcal{D}$ and integration $\mathcal{I}$ are structural stream operations—and where $\mathcal{I}$ is causal/guarded so that Picard iteration $\mathcal{P}(y) = y_0 + \mathcal{I}(F(y))$ locks $k$ Taylor coefficients in $k$ steps—is classical stream calculus (**Pavlović & Escardó 1998**, *"Calculus in Coinductive Form"*; **McIlroy 1999**; **Rutten 2003**, *"Behavioural Differential Equations"*).

### 1.2. What This Mechanization Adds
The contribution of the five Lean 4 modules ([`HAomega/ClosedCalculus.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ClosedCalculus.lean), [`HAomega/HolonomicCS.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/HolonomicCS.lean), [`HAomega/MajorantDom.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/MajorantDom.lean), [`HAomega/JetCauchyDeriv.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/JetCauchyDeriv.lean), [`HAomega/ClosedFourierODE.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ClosedFourierODE.lean)) is the **certified mechanization inside $\mathrm{HA}^\omega$ and Gödel's System T**:
1. **Genuine System T Extraction (`Deriv` + `extractClosed`), classified by where the content comes from:**
   - **Explicit witness, derived correctness:** `jetCauchyModulusGenuineD` (the $E_1$ Cauchy modulus $N(k) = k + (B+3)$ is written at `exI`; its correctness — the multi-step tail bound — is derived by object-level induction `Deriv.ind` on $d_2$ from the $N$-free per-term majorant `jetTermPremise`, relative to four closed $\mathbb{Q}$-laws taken as the hypothesis `qGeomArithPremise` and proved in the metatheory), `jetContModulusD` and `jetDiffModulusD` (moduli written at `exI`, certified via `Deriv.convQLipScale`).
   - **Proof-computed:** `picardExpSolveD` (`HAomega/PicardExpSolve.lean`): for `y' = y`, the algorithm-free specification `∀k ∃Y. ∀i < k. P(Y)(i) = Y(i)` (integral form, `P(Y) = 1 + ∫Y`) is proved by `Deriv.ind` on `k`, and the extracted solver is the Picard recursion. `quadBlowupSolveD` (`HAomega/QuadBlowupSolve.lean`) does the same for the nonlinear `y' = y²` (`P(Y) = 1 + ∫(Y·Y)`), resting on `jetMulPrefixT`, the Cauchy-product prefix lemma derived inside `Deriv`. `riccatiSolveD` (`HAomega/RiccatiSolve.lean`) does the same for Riccati `y' = 1 + y²`, and `duffingSolveD` (`HAomega/DuffingSolve.lean`) for the Duffing system on pairs of jets. These four are the proof-computed jet programs; the others below are not. The scalar ones are instances of the general `genSolveD A F` (`HAomega/PolyODESolve.lean`): one derivation, for every closed initial jet `A` and every polynomial–integral right-hand side `F : JExpr`, whose extract is the Picard iteration.
   - **Witness-style realizers:** `ftcAntiderivD` (supplying `tmJetInteg c` to `exI` and deriving termwise cancellation $\mathcal{D}(\mathcal{I}c)(n) - c(n) = 0$ via `Deriv.convQMulDivSubZero`), `jetMulD`, `jetEvalPolyD`, `newtonJetInvD` (linked to `RadiusJet.invOneSub` by `extractedNewtonJetInv_agree`), and the four Picard iterations `picardJetIterD`, `riccatiPicardD`, `quadBlowupPicardD`, `duffingPicardD` (each is `iterSequenceD`: `exI (recNat Y₀ step k)` + `eqRefl`, with no degree-locking conjunct).
   - **Degree locking** is proved in the metatheory for all four extracted solvers (`HAomega/PicardLocking.lean`: `extractedPicardJet_lock`, `extractedRiccatiJet_lock`, `extractedQuadBlowupJet_lock`, `extractedDuffingJet_lock`, each `[propext, Quot.sound]`): iterate $k+1$ agrees with iterate $k$ below degree $k$, from per-step contractivity. Stating locking inside `Deriv` is open; for the nonlinear steps it needs prefix agreement and order on $\mathbb{N}$ in the object logic, because the Cauchy-product coefficient depends on the whole prefix.
2. **Proved Bounds as Data (`AnalyticJet` vs. `RadiusJet`):**
   - Every stream in `AnalyticJet` carries a proved factorial-scaled bound $|c_n|\cdot n! \le 2^M \cdot (2^R)^n$, with explicit propagation under `add`, `sub`, `mul` (via Pascal's identity $(a+b)! \le 2^{a+b}a!b!$), `deriv` ($(M, R) \mapsto (M+R, R)$), and `integ` ($(M, R) \mapsto (M, R)$).
3. **Formal Comparison of the Exponential-Type and Cauchy–Hadamard Closed Algebras:**
   - Mechanizes both `AnalyticJet` (entire functions of exponential type) and `RadiusJet` ($|c_n| \le 2^M (2^R)^n$, analytic germs of radius $\rho = 2^{-R}$) as complete closed differential-integral algebras (`RadiusJet.add`, `RadiusJet.sub`, `RadiusJet.neg`, `RadiusJet.mul`, `RadiusJet.integ`, `RadiusJet.deriv`, `RadiusJet.invOneSub`, `RadiusJet.compZero`, `RadiusJet.riccatiODE`, `RadiusJet.quadBlowupODE`, `RadiusJet.duffingU`, `RadiusJet.duffingV`, `RadiusJet.toE0`, `RadiusJet.toE1`), proving that $\frac{1}{1-x} \in \mathrm{RadiusJet} \setminus \mathrm{AnalyticJet}$ (`geom_not_analyticJet`) and showing how removing $n!$ forces differentiation to shrink the radius (`RadiusJet.deriv` shifts $(M, R) \mapsto (M+R+1, R+1)$).
4. **Proved Lookahead, Causality, and Kleene–Kreisel Continuity (`Continuity.lean`):**
   - Proves the exact prefix-agreement (`JetAgree`) lookahead laws for `tmJetAdd` ($0$), `Jet.mul` ($0$), `tmJetDeriv` ($+1$), and `tmJetInteg` ($-1$), proves the guarded Picard coefficient-locking theorem (`picard_jetAgree_lock`), and connects all 26 System T combinators to `Tracked` / `ContAt Q` in [`HAomega/Continuity.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Continuity.lean) and `hsOf_correct` in [`HAomega/HsSemantics.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/HsSemantics.lean).
5. **Proved Embedding Back into the Pointwise `E0`/`E1` Hierarchy (`EFTC.lean`):**
   - With `E1.diff` generalized to an approximating derivative family `∃ F : Nat → Q → Q`, proves `AnalyticJet.toE0 : E0` and `AnalyticJet.toE1 : E1` on $[-1, 1]$ and `RadiusJet.toE0 : E0` and `RadiusJet.toE1 : E1` on $[-2^{-(R+3)}, 2^{-(R+3)}]$.

---

## 2. The Fundamental Trade-Off: Exponential-Type Jets (`AnalyticJet`) vs. Cauchy–Hadamard Germs (`RadiusJet`)

A central structural finding of the formalization is the trade-off between **factorial-scaled bounds** and **radius-style bounds**:

| Property | Exponential-Type Entire Jets (`AnalyticJet`) | Cauchy–Hadamard Analytic Germs (`RadiusJet`) | Formal / Guarded Streams (`Jet`) |
| :--- | :--- | :--- | :--- |
| **Defining Bound** | $|c_n| \cdot n! \le 2^M \cdot (2^R)^n$ (Gevrey-$0$ / exponential type) | $|c_n| \le 2^M \cdot (2^R)^n$ (convergence radius $\rho = 2^{-R}$) | Unbounded formal stream $c : \mathbb{N} \to \mathbb{Q}$ |
| **Inhabitants** | $\mathbb{Q}[x]$, $\exp(kx)$, $\sin(kx)$, $\cos(kx)$, $\sinh(kx)$, $\cosh(kx)$ | All of `AnalyticJet` (`RadiusJet.ofAnalyticJet`) **plus** $\frac{1}{1-x}$ (`RadiusJet.geomOneMinusX`), $\tan x$, $\sec x$, $\arctan x$, $\ln(1+x)$, local nonlinear ODEs | All formal power series, Picard iterates, Newton–Schulz inverses |
| **Exclusions** | Excludes $\frac{1}{1-x}$ (`geom_not_analyticJet`), $\tan x$, $e^{e^x}$, and finite-blowup nonlinear ODEs ($y' = y^2$) | Excludes divergent formal series ($\sum n! x^n$) | No convergence guarantee without a majorant |
| **Differentiation $\mathcal{D}$** | **Radius-preserving:** $(M, R) \mapsto (M + R, R)$ (`AnalyticJet.deriv`), because $(n+1)$ is absorbed into $n! \mapsto (n+1)!$ | **Radius-shrinking:** $(M, R) \mapsto (M + R + 1, R + 1)$ (`RadiusJet.deriv`), because $(n+1) \le 2\cdot 2^n$ halves $\rho = 2^{-R}$ | 1-query combinator `tmJetDeriv` |
| **Integration $\mathcal{I}$** | **Bound-preserving:** $(M, R) \mapsto (M, R)$ (`AnalyticJet.integ`) | **Radius-preserving:** $(M, R) \mapsto (M, R)$ | 1-query causal combinator `tmJetInteg` |
| **Closure** | Strictly closed under $+, -, \times, \mathcal{D}, \int_0^x$, and constant-coefficient linear ODEs | Closed under $+, -, \times, \int_0^x$, unit inversion, composition, and Cauchy–Kowalevski ODEs (with radius shrink on $\mathcal{D}$) | Closed under $+, -, \times, \mathcal{D}, \int_0^x$, guarded Picard ODEs, Newton–Schulz unit inversion |

---

## 3. Honest Accounting of FTC1 Inside `Deriv` vs. Value-Level `Q`

When $\mathcal{D}$ (`tmJetDeriv`) and $\mathcal{I}$ (`tmJetInteg`) are formulated as closed System T terms on `JetTy := .arrow .nat .rat`:
1. **Pure $\beta\iota$-Reduction (`jetFTC1_beta_iota_D`):**
   Using only System T's $\beta$ and `recNat`-$\iota$ rules (`convBeta` + `convRecSucc`), `Deriv` proves:
   $$\mathrm{Deriv}\ \Delta\ \big((\mathrm{tmJetDeriv}\ (\mathrm{tmJetInteg}\ c))\ n = \mathrm{qmul}\ (\mathrm{qnat}\ (\mathrm{succ}\ n))\ (\mathrm{qdiv}\ (c\ n)\ (\mathrm{qnat}\ (\mathrm{succ}\ n)))\big).$$
2. **Why Bare `= c n` Cannot Hold Structurally on Raw `Q` (`Q.mul_div_not_id`):**
   As documented in [`HAomega/QArith.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/QArith.lean) (`Q.add_zero_not_id`), `Q` stores a positive denominator `denPred + 1` but does not carry a coprimality proof in its type (`⟨2, 3⟩` is an unnormalized inhabitant representing $2/4$). Because `Q.mul` normalizes via `Q.of`,
   $$\mathrm{Q.mul}\ (\mathrm{Q.ofNat}\ 1)\ (\mathrm{Q.div}\ \langle 2, 3\rangle\ (\mathrm{Q.ofNat}\ 1)) = \langle 1, 1\rangle \ne \langle 2, 3\rangle,$$
   which is proved by `decide` in `Q.mul_div_not_id`.
3. **Normalized and Difference Cancellation Inside `Deriv` (`jetFTC1_cancel_norm_D`, `jetFTC1_sub_zero_D`):**
   Both `Q.mul (Q.ofNat (n+1)) (Q.div a (Q.ofNat (n+1)))` and `Q.add a (Q.ofNat 0)` pass through `Q.of` and denote `a.val`, and their difference with `a` passes through `Q.of` and denotes `0`. Using `Q.mul_div_cancel_norm` and `Q.mul_div_sub_zero` (`convQMulDivCancel` and `convQMulDivSubZero`), `Deriv` proves:
   - `jetFTC1_cancel_norm_D`: $\mathrm{Deriv}\ \Delta\ \big((\mathcal{D}(\mathcal{I}\,c))(n) = c(n) + 0\big)$,
   - `jetFTC1_sub_zero_D`: $\mathrm{Deriv}\ \Delta\ \big((\mathcal{D}(\mathcal{I}\,c))(n) - c(n) = 0\big)$,
   while at the rational value level (`Q.val`), `Jet.deriv_integ_val` proves $((F.\mathrm{integ}.\mathrm{deriv}).\mathrm{coeff}\; n).\mathrm{val} = (F.\mathrm{coeff}\; n).\mathrm{val}$.

---

## 4. Proved Lookahead, Causality, and Kleene–Kreisel Continuity

In [`HAomega/ClosedCalculus.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ClosedCalculus.lean) and [`HAomega/MajorantDom.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/MajorantDom.lean), prefix agreement on streams is defined as:
$$\mathrm{JetAgree}\; n\; c_1\; c_2 \;:\Longleftrightarrow\; \forall i < n,\; c_1(i) = c_2(i).$$

| System T / Jet Operator | Proved Lookahead Theorem | Prefix Agreement Law |
| :--- | :--- | :--- |
| `tmJetAdd`, `tmJetSub` | `tmJetAdd_lookahead_zero`, `tmJetSub_lookahead_zero` | `JetAgree n a₁ a₂ → JetAgree n b₁ b₂ → JetAgree n (a₁ ± b₁) (a₂ ± b₂)` (shift $0$) |
| `Jet.mul` | `jetMul_lookahead_zero` | `JetAgree n a₁ a₂ → JetAgree n b₁ b₂ → JetAgree n (a₁ * b₁) (a₂ * b₂)` (shift $0$) |
| `tmJetDeriv` ($\mathcal{D}$) | `tmJetDeriv_lookahead_plus_one` | `JetAgree (n + 1) c₁ c₂ → JetAgree n (D c₁) (D c₂)` (lookahead $+1$) |
| `tmJetInteg` ($\mathcal{I}$) | `tmJetInteg_contractive_minus_one` | `JetAgree n c₁ c₂ → JetAgree (n + 1) (I c₁) (I c₂)` (lookahead $-1$, Baire $\frac{1}{2}$-contraction) |
| Picard Iteration $\mathcal{P}^{[k]}$ | `picard_jetAgree_lock` | `∀ k u v, JetAgree k (P^[k] u) (P^[k] v)` ($k$ steps lock $k$ coefficients) |
| Kleene–Kreisel `Tracked` | `tmJetDeriv_tracked`, `tmJetInteg_tracked`, `ftcAntideriv_tracked`, `jetMul_tracked`, `jetEvalPoly_tracked` | Connects directly to `eval_tracked` / `extract_tracked` in [`HAomega/Continuity.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Continuity.lean) |

---

## 5. Linking `AnalyticJet` Back to `E0` and `E1` (`HAomega/MajorantDom.lean`)

Using the elementary factorial dominance theorem `pow_le_pow_mul_fact` ($K^n \le K^K \cdot n!$), every `F : AnalyticJet` satisfies the global geometric decay bound (`AnalyticJet.coeff_geom_bound`):
$$|(F.\mathrm{coeff}\; n).\mathrm{val}| \cdot 2^n \le 2^{B(F)}, \qquad B(F) := F.M + (F.R + 1) \cdot 2^{F.R + 1}.$$
Because `F.deriv` and `F.deriv.mulIdxSucc` are also `AnalyticJet`s, a single geometric accumulation lemma (`AnalyticJet.geom_accum_bound`) establishes the complete bridge to [`HAomega/EFTC.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/EFTC.lean) on $[-1, 1]$:
1. **`AnalyticJet.toE0 (F : AnalyticJet) : E0`**:
   Constructs a certified `E0` approximating evaluator on $[-1, 1]$ with `ev := F.toJet.evalPoly` and Cauchy modulus `cm k := F.expBound + 1 + k`.
2. **`AnalyticJet.toE0_cont (F : AnalyticJet)`**:
   Proves `E1.cont` for `F.toE0` on $[-1, 1]$ with uniform continuity modulus `F.omegaE1 k := F.deriv.expBound + 1 + k`.
3. **`AnalyticJet.toE0_diff (F : AnalyticJet)`**:
   Proves the uniform difference-quotient inequality on $[-1, 1]$ between `F.toE0.ev (n + 1)` and the derivative's approximating evaluator `F.deriv.toE0.ev n` with step modulus `F.deltaE1 k := F.deriv.mulIdxSucc.expBound + 1 + k`.
4. **`AnalyticJet.toE1 (F : AnalyticJet) : E1` & `RadiusJet.toE1 (F : RadiusJet) : E1`**:
   With `E1.diff` quantifying over an approximating derivative family `∃ F : Nat → Q → Q`, constructs literal `E1` inhabitants directly on $[-1, 1]$ (`AnalyticJet.toE1`) and on $[-2^{-(F.R+3)}, 2^{-(F.R+3)}]$ (`RadiusJet.toE1`), whose moduli $\mathrm{cm}(k)$, $\omega(k)$, and $\delta(k)$ are synthesized by `extractedJetCauchyModulusGenuine`, `extractedJetContModulus`, and `extractedJetDiffModulus`.

---

## 6. System T Recursion Order in the Formalized Modules

In Gödel's System T ([`HAomega/Syntax.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Syntax.lean)), we distinguish the recursion order of the stream generators (noting that Order-0 `recNat` on $\mathbb{Q}^m$ is primitive recursion with base-type state, which is broader than D-finite/holonomic linear recurrences, and that exact rational arithmetic bit-sizes grow with degree $n$):
- **Loop-free / Bounded Fold (`PolyJet`, `PadeRat`):** Finite coefficient lists and rational Padé quotients.
- **Order-0 `recNat` (Base-Type State `.rat` or `.prod .rat .rat`, No Arrow Types in State):**
  `tmExpJet`, `tmSinJet`, `tmCosJet`, `tmSinFreqJet`, `tmCosFreqJet`, `tmSinhJet`, `tmCoshJet`, `tmJetInteg`, `tmJetMul`, `tmJetEvalPoly`.
- **Order-1 `recNat` (Function-Type State `JetTy := .arrow .nat .rat`):**
  Guarded Picard ODE solvers (`picardJetIterD`, `riccatiPicardD`, `quadBlowupPicardD`, `duffingPicardD`) and Quadratic Newton–Schulz unit jet inversion (`newtonJetInvD`).
