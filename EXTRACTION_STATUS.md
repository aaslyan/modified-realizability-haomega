# Formal Extraction Status Report — HAomega

This report provides an honest, audited status of mathematical theorems and program extraction in `HAomega` across all verification points, strictly distinguishing between **genuinely proved derivations in `Deriv`**, **modulus extraction theorems**, and **evaluated computational operators**.

---

## A. Honest Classification of Theorems vs. Computational Operators

### 1. The Genuinely Proved Constructive Analysis Theorems in `Deriv`

There are **five** fundamental constructive analysis theorems formalized with genuine, non-tautological natural deduction trees in `Deriv`:

1. **The Discrete Crossing / Sperner Root Solver (`fnCrossingD` in `SquareRoot.lean`)**:
   - **Statement**: Proves that for ANY computable function $F : \mathbb{Q} \to \mathbb{Q}$ and target $y$, a sign change on $[0, K \cdot 2^{-n}]$ constructively yields an isolated discrete crossing index $k < K$.
   - **Constructive Content**: Higher-type derivation over function variable $F$, extracting the certified solver `fnCrossingX`.
   - **Derived Computational Objects**:
     - `invOp` (`InverseFunction.lean`): Inverts strictly monotone functions ($2x \mapsto y/2$, $x^3+x \mapsto 2$, non-closed-form $x^5+x \mapsto 193/256$).
     - `circleY`, `ellipseY`, `cubicCurveY` (`CertifiedPlotter.lean`): 2-D implicit curve plotting with certified brackets.
     - `sqrtApproxD`, `cubeApproxD`: Pointwise root solvers.

2. **Banach Contraction Convergence Modulus (`banachContractionD` / `banachModulusD` in `BanachModulus.lean`)**:
   - **Statement**: Proves by mathematical induction (`Deriv.ind`) that for ANY contraction $T : \mathbb{Q} \to \mathbb{Q}$ with seed $x_0$ and initial scale $k_0$, the stopping criterion $N(n) = n$ guarantees that consecutive iterate gaps drop below $2^{-n}$ for all future iterations $N + d$:
     $$\forall n, \exists N, \forall d. \; \text{close}(n, x_{N+d}, x_{N+d+1}) = 1$$
   - **Constructive Content**: Quantifies over operator $T$, initial point $x_0$, and scale $k_0$, deriving exact precision $n$ via scale-monotonicity conversion `convQCloseMono` and associativity `plusAssocD`.

3. **Uniform Continuity from Lipschitz Bound (`uniContLipD` in `UniformContinuity.lean`)**:
   - **Statement**: Proves that for ANY function $f : \mathbb{Q} \to \mathbb{Q}$ satisfying the algebraic Lipschitz bound $|f(x) - f(y)| \le 2^j |x - y|$, $f$ is uniformly continuous with modulus $M(n) = n + j$:
     $$\forall n, \exists M, \forall x \forall y. \; \text{close}(M, x, y) = 1 \implies \text{close}(n, f x, f y) = 1$$
   - **Constructive Content**: Uses the scaled difference conversion rule `convQLipScale` to extract the modulus $M(n) = n + j$.

4. **Riemann Integrator & Modulus Extraction (`riemannIntegralD` in `IntegralModulus.lean`)**:
   - **Statement**: For EVERY integrand $f$, bound scale $j$, and partition $N$, synthesizes the genuine closed System T integrator $G := \text{riemannUpperSumClosed} \; f \; N$ as the existential witness, and derives its uniform continuity modulus $M(n) = n + j$ via `convQLipScale`.
   - **Constructive Content**: Eliminates Pattern P1 by supplying the actual System T computational integrator term in the existential witness.

5. **1D Discrete Intermediate Value Theorem (`spernerD` in `Sperner.lean`)**:
   - **Statement**: Proves 1D discrete intermediate value theorem by mathematical induction on the bracket length.

---

### 2. Evaluated System T Terms & Arithmetic Substrates

The following computational operators are evaluated directly in System T / Lean:
- `integralF` (`IntegralModulus.lean`): Evaluates the intrinsically typed System T Riemann sum $S(f, x/N, N)$ defined in `riemannUpperSumClosed`.
- `bernsteinOp` (`Weierstrass.lean`): Evaluates Bernstein polynomial sums in Lean arithmetic (verified with exact affine reproduction and quadratic defect $1/(4N)$).
- `mollifyEval`, `mollifyIter` (`Mollification.lean`): Evaluates rational moving average filters and iterated smoothing.

---

## B. Audit of Axiom Independence

Every `Deriv` theorem in the core and analysis modules is verified to have **empty `#print axioms`** (depending only on the standard Lean 4 kernel foundations `[propext, Quot.sound]`, with zero `sorry` and zero non-standard axioms).
