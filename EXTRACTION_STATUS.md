# Formal Extraction Status Report — HAomega

This report provides the audited status of program extraction in `HAomega` across all 424 `#guard`/`#eval` verification points, strictly categorizing each into **EXTRACTED**, **OBJECT-RUN**, and **PLAIN**, detailing the mathematical specification content, tautological status, certified 2-D objects, function-valued integral extraction, and the honest analysis assessment.

---

## A. Headline Table

Across `HAomega/*.lean`, verified proof extraction (**EXTRACTED**) accounts for **150** guards:

| Tier | Count | Description |
|---|---|---|
| **EXTRACTED** | **150** | Programs extracted via `extractClosed (d : Deriv)` from proof derivations |
| **OBJECT-RUN** | **30** | Hand-written System T terms (`Tm`) executed via `Tm.eval Env.nil` without a `Deriv` tree |
| **PLAIN** | **244** | Ordinary Lean mathematics, dyadic/rational arithmetic substrate, and reference algorithms |
| **Total** | **424** | All kernel verification points across the entire library |

### Raw `classify.py` Output

```
TOTALS: {'EXTRACT': 150, 'Tm.eval': 30, 'PLAIN': 244} sum: 424
AnalysisDeriv.lean               {'EXTRACT': 8, 'Tm.eval': 0, 'PLAIN': 0}
BanachInstance.lean              {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 14}
CauchyIntegral.lean              {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 5}
CauchyKowalevski.lean            {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 4}
CertifiedPlotter.lean            {'EXTRACT': 11, 'Tm.eval': 0, 'PLAIN': 2}
Chebyshev.lean                   {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 11}
ComplexAnalysis.lean             {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 4}
ConstructiveFFT.lean             {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 4}
DerivFTC.lean                    {'EXTRACT': 4, 'Tm.eval': 4, 'PLAIN': 0}
Dyadics.lean                     {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 14}
EFTC.lean                        {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 13}
EulerMaclaurin.lean              {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 6}
ExtractedOutput.lean             {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 12}
ExtractedPrograms.lean           {'EXTRACT': 2, 'Tm.eval': 0, 'PLAIN': 6}
FFT.lean                         {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 4}
Fib.lean                         {'EXTRACT': 4, 'Tm.eval': 2, 'PLAIN': 3}
Fourier.lean                     {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 10}
Gcd.lean                         {'EXTRACT': 1, 'Tm.eval': 4, 'PLAIN': 2}
Goodstein.lean                   {'EXTRACT': 2, 'Tm.eval': 0, 'PLAIN': 0}
GoodsteinTyped.lean              {'EXTRACT': 3, 'Tm.eval': 0, 'PLAIN': 0}
GreenDivergence.lean             {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 3}
Hanoi.lean                       {'EXTRACT': 1, 'Tm.eval': 6, 'PLAIN': 0}
HarmonicODE.lean                 {'EXTRACT': 4, 'Tm.eval': 0, 'PLAIN': 10}
HeatEquation.lean                {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 5}
Hercules.lean                    {'EXTRACT': 4, 'Tm.eval': 0, 'PLAIN': 0}
HerculesAny.lean                 {'EXTRACT': 4, 'Tm.eval': 0, 'PLAIN': 0}
HerculesTree.lean                {'EXTRACT': 2, 'Tm.eval': 0, 'PLAIN': 1}
HigherType.lean                  {'EXTRACT': 0, 'Tm.eval': 4, 'PLAIN': 2}
HsSemantics.lean                 {'EXTRACT': 1, 'Tm.eval': 0, 'PLAIN': 0}
Hydra.lean                       {'EXTRACT': 2, 'Tm.eval': 0, 'PLAIN': 0}
HydraSurgery.lean                {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 4}
HydraTree.lean                   {'EXTRACT': 5, 'Tm.eval': 0, 'PLAIN': 0}
HydraTyped.lean                  {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 5}
IntegralModulus.lean             {'EXTRACT': 14, 'Tm.eval': 0, 'PLAIN': 0}
IntegrationByParts.lean          {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 3}
InverseFunction.lean             {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 4}
Isoperimetric.lean               {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 6}
Modulus.lean                     {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 3}
NewtonRaphson.lean               {'EXTRACT': 15, 'Tm.eval': 0, 'PLAIN': 0}
NumericsDemo.lean                {'EXTRACT': 0, 'Tm.eval': 3, 'PLAIN': 1}
ODEDemo.lean                     {'EXTRACT': 18, 'Tm.eval': 0, 'PLAIN': 14}
ODEExtraction.lean               {'EXTRACT': 0, 'Tm.eval': 4, 'PLAIN': 6}
OrdCnf.lean                      {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 10}
PadeApproximants.lean            {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 3}
Pascal.lean                      {'EXTRACT': 0, 'Tm.eval': 3, 'PLAIN': 0}
PascalTheorem.lean               {'EXTRACT': 1, 'Tm.eval': 0, 'PLAIN': 0}
PolyRoots.lean                   {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 5}
QAnalysis.lean                   {'EXTRACT': 3, 'Tm.eval': 0, 'PLAIN': 0}
Rationals.lean                   {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 12}
ShowAll.lean                     {'EXTRACT': 1, 'Tm.eval': 0, 'PLAIN': 2}
Sperner.lean                     {'EXTRACT': 1, 'Tm.eval': 0, 'PLAIN': 1}
SquareRoot.lean                  {'EXTRACT': 36, 'Tm.eval': 0, 'PLAIN': 1}
SymplecticKepler.lean            {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 4}
Taylor.lean                      {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 5}
Transcendental.lean              {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 13}
UniformContinuity.lean           {'EXTRACT': 3, 'Tm.eval': 0, 'PLAIN': 1}
Weierstrass.lean                 {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 6}
```

---

## B. Certified Answers vs. Uncertified Iterations

| Quantity / Object | Fast Program (Specification) | Certifying Derivation (Specification) | Agreement Checked in Kernel |
|---|---|---|---|
| **Picard Fixed Point ($y=2$)** | `picardAffineExtracted` (Tautological $\forall n. \exists y. y = T^n(1)$) | `fnCrossingD` at $F(x) = x \cdot \frac{1}{2}, y = 1$ (**GENUINE**) | `#guard`s verify $T^n(1) \to 2$ while certified bracket $[k \cdot 2^{-n}, (k+1) \cdot 2^{-n})$ tightens around $2$ at $n=0, 1, 2, 4, 6$. |
| **Square Root ($\sqrt{2}$)** | `newtonSqrt2Extracted` (Tautological $\forall n. \exists y. y = x_n$) | `sqrtApproxD` / `fnCrossingD` at $F(x) = x^2, y = 2$ (**GENUINE**) | `#guard` verifies Newton iterate $x_4 = \frac{665857}{470832}$ lands strictly inside certified bracket $[\frac{362}{256}, \frac{363}{256})$. |
| **Square Root ($\sqrt{3}$)** | `newtonSqrt3Extracted` (Tautological $\forall n. \exists y. y = x_n$) | `fnCrossingD` at $F(x) = x^2, y = 3$ (**GENUINE**) | `#guard` verifies Newton iterate $x_4 = \frac{18817}{10864}$ lands strictly inside certified bracket $[\frac{443}{256}, \frac{444}{256})$. |
| **2-D Unit Circle ($x^2+y^2=1$)** | — | `circleY` / `fnCrossingD` at $F(y) = y^2, y_0 = 1 - x^2$ (**GENUINE**) | `#guard`s verify axis intercepts $(0,1), (1,0)$, the 3-4-5 point $(3/5, 4/5)$, strict sweep monotonicity, and pointwise bracket containment. |
| **2-D Ellipse ($x^2/4+y^2=1$)** | — | `ellipseY` / `fnCrossingD` at $F(y) = y^2, y_0 = 1 - x^2/4$ (**GENUINE**) | `#guard`s verify intercepts $(0,1), (2,0)$ and rational point $(6/5, 4/5)$. |
| **2-D Cubic Curve ($y^3+y=x$)** | — | `cubicCurveY` / `fnCrossingD` (**GENUINE**) | `#guard`s verify integer solution points $(0,0), (2,1), (10,2), (30,3)$. |
| **Extracted Continuous Integral** | — | `integralFunctionD` ($\exists F : \mathbb{Q} \to \mathbb{Q}$, **GENUINE**) | Extracts realizer $(F, M)$ where $F$ is the integral function and $M(n) = n + j$ is the certified modulus of continuity. |
| **Riemann Integrator ($S(f, h, N)$)** | `riemannExtracted` (Tautological $\forall N. \exists y. y = S_N$) | *No certified convergence companion in Deriv yet* | Plainly disclosed in `DerivFTC.lean`. |

---

## C. Honest Analysis Assessment

### 1. What is certified?
* **For Target A (Certified Curve Plotter):** Every plotted rational point $(x, y)$ computed by `circleY`, `ellipseY`, or `cubicCurveY` is certified by `fnCrossingD` to satisfy the rigorous two-sided bracket:
  $$y^2 \le \Phi(x) < (y + 2^{-n})^2$$
* **For Target B (Extracted Continuous Integral):** The arrow-type existential $\exists F : \mathbb{Q} \to \mathbb{Q}$ extracts a function-valued witness $F$ paired with its certified modulus of uniform continuity $M(n) = n + j$.

### 2. What is not certified?
* **For Target A:** The sweep grid (the list of $x$-coordinates) is chosen externally by the caller. The points are certified individually as level-set crossings, not the global geometric curve as an abstract limit object in a function space.
* **For Target B:** The $2^j$-Lipschitz premise of the integrand is discharged outside the formal deductive system (by arithmetic computation at call sites).

### 3. Is this real mathematics recovered, or a demonstration?
It is a **real, constructive demonstration of certified numerical analysis**. A certified 2-D implicit curve plotter and an extracted function-valued continuous integral with modulus are genuine constructive artifacts, proved without tautological shortcuts (`∃y. y = t`). They demonstrate that modified realizability in higher types can produce certified solvers and continuous real functions without extra adapters. However, they are not yet a complete foundation for real analysis, which would require internalizing full metric space completions and arithmetic conversion rules for rational operations.

### 4. What is the single next genuine step?
**The Riemann sum monotonicity theorem (Target A1):**
$$\forall f, g : \mathbb{Q} \to \mathbb{Q}, \; (\forall x. f(x) < g(x)) \land (h > 0) \implies \forall N > 0. \; S(f, h, N) < S(g, h, N)$$
proved by mathematical induction in `Deriv` using `convQMulLt` and `convQAddLt`.
