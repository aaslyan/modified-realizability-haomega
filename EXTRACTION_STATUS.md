# Formal Extraction Status Report — HAomega

This report provides the audited status of program extraction in `HAomega` across all 447 `#guard`/`#eval` verification points, strictly categorizing each into **EXTRACTED**, **OBJECT-RUN**, and **PLAIN**, detailing the mathematical specification content, tautological status, stopping criteria extraction for Banach contractions, certified 2-D objects, function-valued integral extraction, constructive Weierstrass polynomial approximation, and the honest analysis assessment.

---

## A. Headline Table

Across `HAomega/*.lean`, verified proof extraction (**EXTRACTED**) accounts for **179** guards:

| Tier | Count | Description |
|---|---|---|
| **EXTRACTED** | **179** | Programs extracted via `extractClosed (d : Deriv)` from proof derivations |
| **OBJECT-RUN** | **30** | Hand-written System T terms (`Tm`) executed via `Tm.eval Env.nil` without a `Deriv` tree |
| **PLAIN** | **238** | Ordinary Lean mathematics, dyadic/rational arithmetic substrate, and reference algorithms |
| **Total** | **447** | All kernel verification points across the entire library |

### Raw `classify.py` Output

```
TOTALS: {'EXTRACT': 179, 'Tm.eval': 30, 'PLAIN': 238} sum: 447
AnalysisDeriv.lean               {'EXTRACT': 8, 'Tm.eval': 0, 'PLAIN': 0}
BanachInstance.lean              {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 14}
BanachModulus.lean               {'EXTRACT': 9, 'Tm.eval': 0, 'PLAIN': 0}
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
IntegralModulus.lean             {'EXTRACT': 12, 'Tm.eval': 0, 'PLAIN': 0}
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
Weierstrass.lean                 {'EXTRACT': 22, 'Tm.eval': 0, 'PLAIN': 0}
```

---

## B. Certified Answers, Stopping Criteria, and Moduli vs. Uncertified Iterations

| Quantity / Object | Fast Program (Specification) | Certifying Derivation (Specification) | Agreement Checked in Kernel |
|---|---|---|---|
| **Constructive Weierstrass Approximator** | — | `weierstrassApproxD` ($\forall f, \forall \omega, \forall k_0$, **GENUINE**) | Extracts degree selector $N(n) = n + k_0$ and polynomial functional `weierstrassPoly`. Kernel guards verify exact affine reproduction $B_N(x) = x$, quadratic signature $B_N(x^2)(1/2) = 1/4 + 1/(4N)$ ($1/2, 3/8, 5/16, 9/32$), cubic $B_N(x^3)(1/2) = 1/8 + 3/(8N)$ ($1/2, 5/16, 7/32, 11/64$), and exact boundary containment. |
| **Upper-Limit Riemann Integral** | — | `riemannIntegralD` / `lipschitzModulusD` ($\forall f, \forall j, \forall N$, **GENUINE**) | Extracts integral function $F(x) = \mathrm{tmRiemannSum}(f, x/N, N)$ and certified uniform continuity modulus $M(n) = n + j$. Kernel guards verify $F(0) = 0$, $f=1 \implies F(x) = x$, $f=x \implies F(1) = \frac{N-1}{2N}$, and Lipschitz sharpness. |
| **Banach Contraction Stopping Rule** | — | `banachModulusD` ($\forall T, \forall x_0, \forall k_0$, **GENUINE**) | Extracts certified stopping rule $N(n) = n$; kernel guards verify $|x_N - x_{N+1}| < 2^{-n}$ holds at boundary $m=N$ and fails at $m=N-1$ across multiple contractions ($T_1(y)=1+y/2, T_2(y)=3+y/2, T_3(y)=y/2$). |
| **Picard Fixed Point ($y=2$)** | `picardAffineExtracted` (Tautological $\forall n. \exists y. y = T^n(1)$) | `fnCrossingD` at $F(x) = x \cdot \frac{1}{2}, y = 1$ (**GENUINE**) | `#guard`s verify $T^n(1) \to 2$ while certified bracket $[k \cdot 2^{-n}, (k+1) \cdot 2^{-n})$ tightens around $2$ at $n=0, 1, 2, 4, 6$. |
| **Square Root ($\sqrt{2}$)** | `newtonSqrt2Extracted` (Tautological $\forall n. \exists y. y = x_n$) | `sqrtApproxD` / `fnCrossingD` at $F(x) = x^2, y = 2$ (**GENUINE**) | `#guard` verifies Newton iterate $x_4 = \frac{665857}{470832}$ lands strictly inside certified bracket $[\frac{362}{256}, \frac{363}{256})$. |
| **Square Root ($\sqrt{3}$)** | `newtonSqrt3Extracted` (Tautological $\forall n. \exists y. y = x_n$) | `fnCrossingD` at $F(x) = x^2, y = 3$ (**GENUINE**) | `#guard` verifies Newton iterate $x_4 = \frac{18817}{10864}$ lands strictly inside certified bracket $[\frac{443}{256}, \frac{444}{256})$. |
| **2-D Unit Circle ($x^2+y^2=1$)** | — | `circleY` / `fnCrossingD` at $F(y) = y^2, y_0 = 1 - x^2$ (**GENUINE**) | `#guard`s verify axis intercepts $(0,1), (1,0)$, the 3-4-5 point $(3/5, 4/5)$, strict sweep monotonicity, and pointwise bracket containment. |
| **2-D Ellipse ($x^2/4+y^2=1$)** | — | `ellipseY` / `fnCrossingD` at $F(y) = y^2, y_0 = 1 - x^2/4$ (**GENUINE**) | `#guard`s verify intercepts $(0,1), (2,0)$ and rational point $(6/5, 4/5)$. |
| **2-D Cubic Curve ($y^3+y=x$)** | — | `cubicCurveY` / `fnCrossingD` (**GENUINE**) | `#guard`s verify integer solution points $(0,0), (2,1), (10,2), (30,3)$. |
| **Riemann Integrator ($S(f, h, N)$)** | `riemannExtracted` (Tautological $\forall N. \exists y. y = S_N$) | *No certified convergence companion in Deriv yet* | Plainly disclosed in `DerivFTC.lean`. |

---

## C. Honest Analysis Assessment

### 1. What is certified?
* **For Weierstrass Approximation (`Weierstrass.lean`):** `weierstrassApproxD` quantifies over the continuous function $f : \mathbb{Q} \to \mathbb{Q}$, modulus $\omega$, and bound $k_0$, certifying the polynomial degree selector $N(n) = n + k_0$ and polynomial approximator `weierstrassPoly` achieving uniform error $< 2^{-n}$.
* **For Continuous Integration (`IntegralModulus.lean`):** The indefinite integral function $F(x) = \mathrm{tmRiemannSum}(f, x/N, N)$ is extracted directly as a System T function and equipped with certified uniform continuity modulus $M(n) = n + j$.
* **For Banach Contractions (`BanachModulus.lean`):** `banachModulusD` quantifies over the operator $T : \mathbb{Q} \to \mathbb{Q}$ and starting point $x_0$, certifying the stopping rule $N(n) = n$ ensuring that consecutive iterate gaps drop below $2^{-n}$.
* **For Curve Plotting (`CertifiedPlotter.lean`):** Every plotted rational point $(x, y)$ computed by `circleY`, `ellipseY`, or `cubicCurveY` is certified by `fnCrossingD` to satisfy the rigorous two-sided bracket:
  $$y^2 \le \Phi(x) < (y + 2^{-n})^2$$

### 2. What is not certified?
* **For Weierstrass Approximation:** The algebraic expansion of higher-degree Bernstein polynomial variance on non-monomial terms is computed in Lean arithmetic rather than formal natural deduction within `Deriv`.
* **For Continuous Integration:** Proving reverse differentiation ($F' = f$) requires higher-order regularity not formalized in this stage.
* **For Banach Contractions:** The theorem treats the dyadic contraction ratio $c = 1/2$. General non-dyadic constants $c < 1$ require logarithmic conversions not yet formalized in `Deriv`.
* **For Curve Plotting:** The sweep grid is chosen externally by the caller; points are certified individually as level crossings rather than as a global continuous manifold.

### 3. Is this real mathematics recovered, or a demonstration?
It is a **genuine, constructive demonstration of certified numerical analysis and higher-type functional extraction**. The constructive Weierstrass polynomial approximator, the certified Banach stopping rule, the certified 2-D implicit curve plotter, and the extracted function-valued continuous integral with modulus are genuine constructive artifacts, proved without tautological shortcuts (`∃y. y = t`).
