# Formal Extraction Status Report — HAomega

This report provides an honest, audited status of mathematical theorems and program extraction in `HAomega` across all 471 `#guard`/`#eval` verification points, strictly distinguishing between **genuinely proved derivations in `Deriv`**, **modulus extraction templates**, and **evaluated computational operators**.

---

## A. Honest Classification of Theorems vs. Computational Operators

### 1. The Genuinely Proved Constructive Analysis Theorems in `Deriv`

There are **two** fundamentally new constructive analysis theorems formalized with genuine, non-tautological natural deduction trees in `Deriv`:

1. **The Discrete Crossing / Sperner Root Solver (`fnCrossingD` in `SquareRoot.lean`)**:
   - **Statement**: Proves that for ANY computable function $F : \mathbb{Q} \to \mathbb{Q}$ and target $y$, a sign change on $[0, K \cdot 2^{-n}]$ constructively yields an isolated discrete crossing index $k < K$.
   - **Constructive Content**: Higher-type derivation over function variable $F$, extracting the certified solver `fnCrossingX`.
   - **Derived Computational Objects**:
     - `invOp` (`InverseFunction.lean`): Inverts strictly monotone functions ($2x \mapsto y/2$, $x^3+x \mapsto 2$, non-closed-form $x^5+x \mapsto 193/256$).
     - `circleY`, `ellipseY`, `cubicCurveY` (`CertifiedPlotter.lean`): 2-D implicit curve plotting with certified brackets.
     - `sqrtApproxD`, `cubeApproxD`: Pointwise root solvers.

2. **Banach Contraction Stopping Criteria (`banachModulusD` in `BanachModulus.lean`)**:
   - **Statement**: Proves that for ANY operator $T : \mathbb{Q} \to \mathbb{Q}$ and starting point $x_0$, if $T$ contracts with ratio $\le 1/2$, the stopping rule $N(n) = n$ guarantees consecutive iterate gaps $|x_N - x_{N+1}| < 2^{-n}$.
   - **Constructive Content**: Quantifies over operator $T$, extracting the stopping criterion function.

---

### 2. Modulus Extraction Templates in `Deriv`

The following derivations provide formal extraction of continuity moduli:
- `uniContD` (`UniformContinuity.lean`): Extracts modulus $M(n) = \omega(n)$ from a supplied uniform continuity premise.
- `lipschitzModulusD` (`IntegralModulus.lean`): Extracts modulus $M(n) = n + j$ from a supplied $2^j$-Lipschitz premise.
- `inverseModulusD` (`InverseFunction.lean`), `mollifierModulusD` (`Mollification.lean`), `weierstrassApproxD` (`Weierstrass.lean`): Instances / aliases of the Lipschitz/continuity modulus extraction template.

---

### 3. Evaluated System T Terms & Arithmetic Substrates

The following computational operators are evaluated directly in System T / Lean without a corresponding internal deductive proof of their analytic properties inside `Deriv`:
- `integralF` (`IntegralModulus.lean`): Evaluates the intrinsically typed System T Riemann sum $S(f, x/N, N)$ defined in `riemannUpperSumTm`. (Proving $S(f)$ is $2^j$-Lipschitz inside `Deriv` requires strip induction).
- `bernsteinOp` (`Weierstrass.lean`): Evaluates Bernstein polynomial sums in Lean arithmetic. (Verified with exact affine reproduction and quadratic defect $1/(4N)$).
- `mollifyEval`, `mollifyIter` (`Mollification.lean`): Evaluates rational moving average filters and iterated smoothing.

---

## B. Headline Table (`classify.py`)

Across `HAomega/*.lean`, the 471 kernel verification points break down as follows:

| Tier | Count | Description |
|---|---|---|
| **EXTRACTED** | **197** | Programs extracted via `extractClosed (d : Deriv)` from proof derivations |
| **OBJECT-RUN** | **40** | System T terms (`Tm`) executed via `Tm.eval Env.nil` without a `Deriv` tree (including `integralF`) |
| **PLAIN** | **234** | Ordinary Lean mathematics, dyadic/rational arithmetic substrate, and reference algorithms |
| **Total** | **471** | All kernel verification points across the entire library |

### Raw `classify.py` Output

```
TOTALS: {'EXTRACT': 197, 'Tm.eval': 40, 'PLAIN': 234} sum: 471
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
IntegralModulus.lean             {'EXTRACT': 2, 'Tm.eval': 10, 'PLAIN': 0}
IntegrationByParts.lean          {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 3}
InverseFunction.lean             {'EXTRACT': 12, 'Tm.eval': 0, 'PLAIN': 0}
Isoperimetric.lean               {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 6}
Modulus.lean                     {'EXTRACT': 0, 'Tm.eval': 0, 'PLAIN': 3}
Mollification.lean               {'EXTRACT': 16, 'Tm.eval': 0, 'PLAIN': 0}
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

## C. Kernel-Verified Guarantees

| Quantity / Object | Computation Mechanism | Proof / Certification Grounding | Kernel Verification |
|---|---|---|---|
| **Certified Inverse Functions** | `invOp` evaluating `fnCrossingSol` | Certified by `fnCrossingD` (Sperner crossing theorem) | Exact round-trip $f(g(y)) = y$ on $2x \mapsto y/2$, $x^3+x \mapsto 2$, non-closed-form $x^5+x \mapsto 193/256$. |
| **Certified 2-D Curves** | `circleY`, `ellipseY`, `cubicCurveY` | Certified by `fnCrossingD` | Pointwise bracket containment on unit circle, ellipse, and cubic curve $y^3+y=x$. |
| **Banach Contraction Stopping Rule** | `banachModulusD` extractor | Proved in `Deriv` via `banachModulusD` | Sharp stopping at $m = N$ across multiple contractions ($1+y/2, 3+y/2, y/2$). |
| **Quadratic Error Signature in Weierstrass** | `weierstrassPoly` | Evaluated in Lean arithmetic | Exact affine reproduction $B_N(x) = x$; exact variance defect $B_N(x^2)(1/2) = 1/4 + 1/(4N)$ ($1/2, 3/8, 5/16, 9/32$). |
| **Mollifier Smoothing** | `mollifyEval`, `mollifyIter` | Evaluated in System T / Lean | Affine preservation, jump discontinuity smoothing, quadratic shift invariant $\mathcal{S}_h^m(x^2)(0) = m \cdot h^2/2$. |
| **Riemann Upper-Limit Sum** | `integralF` | Evaluated in System T (`riemannUpperSumTm`) | $F(0) = 0$, $f=1 \implies F(x) = x$, $f=x \implies F(1) = \frac{N-1}{2N}$. |
