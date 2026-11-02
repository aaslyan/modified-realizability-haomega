# Descriptive Differential Theory: Ordinal-Graded ODE Systems and "Waves Over Waves" Below $\varepsilon_0$

**Primary Lean 4 Module:** [`HAomega/OrdinalODEHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean)  
**Supporting Modules:** [`HAomega/SystemBound.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemBound.lean), [`HAomega/SystemEval.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean), [`HAomega/UniverseGPAC.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseGPAC.lean), [`HAomega/UniverseExpr.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseExpr.lean), [`HAomega/OrdCnf.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdCnf.lean)  
**Verification Status:** 100% mechanized in Lean 4 (`lake build HAomega.OrdinalODEHierarchy` — 0 errors, 0 warnings, 0 `sorry`s).

---

## 1. Core Thesis: Connecting Mathematical Logic to Numerical Analysis

In classical analysis, a real function is treated extensionally as a "black box" $x \mapsto f(x)$. By Myhill's theorem (1971), black-box functions are not closed under differentiation, and definite integration by Riemann sums requires $\mathcal{O}(2^k)$ evaluations for $k$ bits of accuracy.

Our architecture in $\mathrm{HA}^\omega$ replaces the black box with an **intensional, uniform analytic representation**:
1. Every function in the closed universe ([`InGPAC`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseGPAC.lean#L46-L48)) is the solution component [`solN sys v`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseCore.lean#L211-L212) of a polynomial initial-value ODE system
   $$Y_v(x) = A_v + \int_0^x F_v(Y(t))\,dt \quad (\text{`GPACSys sys`}),$$
   equipped with a syntax-computed Cauchy majorant pair $(M, R) = \mathrm{sysParams}(\mathrm{sys})$ ([`sysParams`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L82-L84)) certifying $|c_n| \le 2^M \cdot (2^R)^n$ ([`solN_geom_bound_computed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L107-L146)).
2. Because functions are defined by differential equations, **functions defined at ordinal stage $\beta \prec \alpha$ can serve as the coefficients, phase drivers, or vector-field inputs of differential equations at stage $\alpha$**.
3. This induces a transfinite cumulative hierarchy of smooth analytic functions — a **Descriptive Differential Hierarchy** $\mathcal{D}_0 \subsetneq \mathcal{D}_1 \subsetneq \cdots \subsetneq \mathcal{D}_\omega \subsetneq \mathcal{D}_{\omega^2} \subsetneq \mathcal{D}_{\omega^\omega} \subsetneq \cdots \subsetneq \mathcal{D}_{<\varepsilon_0}$ ([`InDescDiff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1907-L1909)) — where the **structural ordinal complexity of the differential equation imposes the analytic complexity of its solution**.

---

## 2. Prior Art Comparison: Why This Has Never Been Done Before

Four classical mathematical traditions have studied parts of this landscape, but **none has ever constructed an ordinal-graded hierarchy of smooth polynomial ODE systems and wave-modulation cascades ("waves over waves") below $\varepsilon_0$**:

| Classical Tradition | What It Achieves | Why It Stops Short of Descriptive Differential Theory |
| :--- | :--- | :--- |
| **1. Liouvillian Towers in Differential Algebra**<br>*(Liouville 1833, Ritt 1950, Kolchin 1973)* | Builds differential field extensions $K_0 \subset K_1 \subset \cdots \subset K_n$ by adjoining integrals $\int a$ and exponentials $\exp(\int a)$, where coefficients at stage $i$ come from stage $i-1$. | Restricted to **finite tower depth $n < \omega$**; excludes nonlinear GPAC feedback ($y' = y^2$ or implicit ODE inversion); purely algebraic (no Cantor ordinals $\alpha \prec \varepsilon_0$, no Cauchy majorants $(M, R)$, no constructive numerical evaluators). |
| **2. Hardy Fields & Transseries**<br>*(Hardy 1910, Bourbaki, Rosenlicht 1983, van den Dries–Macintyre–Marker)* | Grades asymptotic growth rates at $x \to +\infty$ using ordinals below $\varepsilon_0$ (e.g. $\exp^{[h]}(x) \sim \omega_h$). | **Strictly forbids oscillating waves!** Every element of a Hardy field must have eventually constant sign as $x \to \infty$ so that $f \neq 0 \implies 1/f$ is defined. Therefore **$\sin x$, $\cos x$, Fourier modes, and FM wave-over-wave modulations ($\sin(x + \sin x)$, $\exp(\sin x)$) cannot exist in any Hardy field.** |
| **3. Descriptive Set Theory Ranks on Functions**<br>*(Borel $\Sigma^0_\alpha$, Baire hierarchy, Kechris–Louveau ranks on Baire class 1)* | Uses countable ordinals $\alpha$ to classify functions by iterated pointwise limits or oscillation ranks. | Classifies **discontinuous / non-differentiable** functions via pointwise topological limits — not smooth analytic solutions of polynomial ODE systems where stage-$\beta$ waveforms act as the vector-field drivers of stage-$\alpha$ ODEs. |
| **4. GPAC & Analog Computability**<br>*(Shannon 1941, Pour-El 1974, Graça–Bournez–Pouly 2004–2017)* | Proves that polynomial ODE systems (`GPACSys`) coincide with computable analysis globally, and studies discontinuous "hypercomputation" ODEs. | Treats all smooth polynomial ODEs as a **single flat class** (polynomial-time computable real functions). Never stratified smooth polynomial ODE systems (`GPACSys`) into an internal Cantor ordinal hierarchy $\mathcal{D}_\alpha$ ($\alpha \prec \varepsilon_0$). |

### Why Our Synthesis Works
By working inside $\mathrm{HA}^\omega$ where functions are represented by polynomial ODE systems ([`GPACSys`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseGPAC.lean#L41-L42)) and certified local Taylor recurrences ([`solN`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseCore.lean#L211-L212)) around $x_0 = 0$:
- **Waves and growth live in the same algebra:** Unlike Hardy fields, $\sin x$ and $\cos x$ ($y'' = -y$) are first-class citizens at level $\omega$ right alongside $e^x$, so iterating differential equations produces true **"waves over waves"** (frequency/phase/amplitude modulation cascades) graded by Cantor ordinals $\alpha \prec \varepsilon_0$.
- **Direct ODE-recurrence majorants separate the levels:** Because every ODE $Y_v' = F_v(Y)$ unfolds via the Taylor recurrence
  $$(n+1) Y_v(n+1) = F_v(Y)(n) \quad (\text{`sbd_solN_succ_val`}),$$
  the algebraic structure of $F_v$ at ordinal $\alpha$ directly controls the analytic growth of the Taylor coefficients $|(Y_v)_n|$ and their certified Cauchy modulus.

---

## 3. Direct ODE-System Complexity Bounds (`LinearGPACSys` vs. Nonlinear Blowup)

A central question is whether the $\omega \prec \omega^2$ barrier holds **directly on polynomial ODE systems `sys : List (Tm [] JetTy × JExprN)` of arbitrary dimension $N$**, independent of expression trees. In Section 9A of [`OrdinalODEHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1498-L1890), we prove that it does.

### 3.1 Linear GPAC Systems ([`LinearGPACSys`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1541-L1542))
- **[`JExprN.NoVars`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1524-L1527):** A `JExprN` expression is a state-free constant scalar expression if it contains no state variables `.var i` and no `.integ`. By [`sbdEvalExpr_noVars_succ_zero`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1555-L1583), every such expression vanishes at all Taylor degrees $k + 1 \ge 1$.
- **[`JExprN.IsLinear`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1532-L1536) & [`LinearGPACSys`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1541-L1542):** A `GPACSys sys` is linear if every multiplication `.mul a b` in its right-hand-side vector field multiplies at least one state-free scalar (`NoVars`) by a linear state expression. This class encompasses all $N$-dimensional constant-coefficient linear ODE systems $\dot{Y} = A Y + b$, arbitrary finite superpositions of harmonic oscillators ($\sin(\omega_k x), \cos(\omega_k x)$), and damped exponential waves ($e^{\lambda_k x}$) of **any dimension $N \in \mathbb{N}$**.

### 3.2 Why Linear ODE Systems Always Decay Like $1/n!$
In a general nonlinear `GPACSys` (such as $y' = y^2$), the Cauchy product $(Y_u \cdot Y_w)_m = \sum_{j=0}^m (Y_u)_j (Y_w)_{m-j}$ sums over all splits $j + (m-j) = m$; because $\sum_{j=0}^m \binom{m}{j} = 2^m$, the $1/n!$ factorial decay is destroyed, leaving only the geometric bound $|(Y_v)_n| \le 2^M (2^R)^n$ ([`solN_geom_bound_computed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L107-L146)).

By contrast, in a `LinearGPACSys`:
1. **Cauchy Convolution Collapse ([`sbd_mul_noVars_left_val`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1628-L1637), [`sbd_mul_noVars_right_val`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1640-L1651)):** Whenever `a.NoVars`, all terms with $j \ge 1$ in $\sum_{j=0}^m a(j) b(m-j)$ vanish, collapsing the Cauchy product to the single term $a(0) \cdot b(m)$.
2. **Factorial Bound Preservation ([`sbdEvalExpr_linear_fact_bound`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1657-L1773)):** If $|W_u(m)| \cdot m! \le K \cdot B^m$ for all $u < \mathrm{sys.length}$ and $m \le n$, then $|F(W)(m)| \cdot m! \le \Phi_F(K) \cdot B^m$.
3. **Accumulation of $\frac{1}{k+1}$ into $\frac{1}{n!}$ ([`sbd_solN_linear_fact_bound`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1778-L1822)):** In the ODE recurrence $(k+1) Y_v(k+1) = F_v(Y)(k)$, multiplying by $(k+1)! = (k+1) \cdot k!$ cancels the $1/(k+1)$ integration factor at every step $k$.

### 3.3 The Computed Linear Factorial Bound & Separation Theorem
Using the **exact same syntax-computed parameters** $(M, R) = \mathrm{sysParams}(\mathrm{sys})$ from [`SystemEval.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L82-L84):

- **Theorem ([`solN_linear_factorial_bound_computed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1830-L1869)):**
  For every linear ODE system `sys` (`LinearGPACSys sys`), every component $v < \mathrm{sys.length}$, and every degree $n \in \mathbb{N}$:
  $$|(Y_v)_n| \cdot n! \le 2^M \cdot (2^R)^n \quad \text{where } (M, R) = \mathrm{sysParams}(\mathrm{sys}).$$
- **Corollary ([`linearGPACSys_semEntireExpType`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1875-L1878)):**
  Every solution component `solN sys v` of a `LinearGPACSys` belongs to the entire exponential-type semantic class [`SemEntireExpType`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L820-L821) (infinite radius of convergence $\rho = \infty$).
- **Theorem ([`no_linearGPACSys_semJetEq_uGeom`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1885-L1890)):**
  **No linear ODE system `LinearGPACSys sys` of any dimension $N \in \mathbb{N}$** (no matter how many coupled harmonic oscillators, Fourier modes, or linear states it superposes) can ever have a solution component semantically equal to [`uGeom`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1083) ($\frac{1}{1-x}$, the solution to the 1-variable quadratic ODE $y' = y^2$ at ordinal $\omega^2$).

---

## 4. The Cumulative Descriptive Differential Hierarchy $\mathcal{D}_\alpha$ (`InDescDiff α`)

In Section 9B of [`OrdinalODEHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1892-L2048), we formalize the cumulative hierarchy $\mathcal{D}_\alpha$ ($\alpha \prec \varepsilon_0$) directly in terms of compiled polynomial ODE solutions:

### 4.1 Definition and Fundamental Properties
- **Definition ([`InDescDiff α c`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1907-L1909)):**
  A Taylor jet `c : ℕ → Q` belongs to level $\alpha \in \mathrm{Eps0}$ of the Descriptive Differential Hierarchy ($c \in \mathcal{D}_\alpha$) if there exists a well-defined expression `e : UExpr` with syntactic ordinal $e.\mathrm{ord} \preceq \alpha$ whose compiled polynomial ODE system `e.compile` has solution `solN e.compile.sys e.compile.v` semantically equal to `c`:
  ```lean
  def InDescDiff (α : Eps0) (c : ℕ → Q) : Prop :=
    ∃ e : UExpr, e.Defined ∧ (Eps0.OLtE e.ord α ∨ e.ord = α) ∧
      SemJetEq (solN e.compile.sys e.compile.v) c
  ```
- **Equivalence with Intrinsic Presentation Ordinal ([`InDescDiff_iff_hasPresentationLe`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1914-L1924)):**
  By [`UExpr.compile_correct`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseExpr.lean#L540-L619), `InDescDiff α c ↔ HasPresentationLe α c`.
- **Containment in the GPAC Universe ([`InDescDiff_inGPAC`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1928-L1931)):**
  Every level $\mathcal{D}_\alpha$ ($\alpha \prec \varepsilon_0$) is contained in [`InGPAC`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseGPAC.lean#L46-L48):
  $$\bigcup_{\alpha \prec \varepsilon_0} \mathcal{D}_\alpha \subseteq \mathrm{InGPAC}.$$
- **Cumulative Monotonicity ([`InDescDiff_mono`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1936-L1943)):**
  Whenever $\beta \prec \alpha$ in the structural Cantor normal form order [`Eps0.OLtE`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdCnf.lean#L135),
  $$\mathcal{D}_\beta \subseteq \mathcal{D}_\alpha \quad (\text{`InDescDiff β c → InDescDiff α c`}).$$
- **Exact Ordinal Surjectivity onto $\varepsilon_0$ ([`odeOfOrd_ord`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L767-L805)):**
  Every Cantor Normal Form ordinal $\alpha \prec \varepsilon_0$ (`α.nf = true`) is realized by a canonical differential-equation witness `odeOfOrd α` with `(odeOfOrd α).ord = α` and `InDescDiff α (odeOfOrd α).eval`.

---

## 5. "Waves Over Waves": The Transfinite Wave-Modulation Cascade (`uWaveTower`)

To formalize the intuition of **"waves over waves"** — where a waveform generated by a differential equation at stage $h$ becomes the phase/rate modulator of a new differential equation at stage $h+1$ — we define [`uWaveTower : ℕ → UExpr`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1950-L1952):

```lean
def uWaveTower : ℕ → UExpr
  | 0 => .sin
  | h + 1 => .comp .exp (uWaveTower h)
```

- **Stage $0$ (`uWaveTower 0 = .sin`):** The fundamental harmonic oscillator $\sin x$, solving the 2-dimensional linear ODE system $y_0' = y_1, y_1' = -y_0$ at ordinal $\omega = \omega_2$.
- **Stage $h + 1$ (`uWaveTower (h + 1) = .comp .exp (uWaveTower h)`):** Feeds the stage-$h$ waveform $W_h(x)$ into the modulated differential equation
  $$W_{h+1}'(x) = W_h'(x) \cdot W_{h+1}(x), \qquad W_{h+1}(0) = 1.$$

### Mechanized Theorems for `uWaveTower`
1. **Cantor Ordinal Climb ([`uWaveTower_ord`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1976-L1986)):**
   $$\forall h \in \mathbb{N},\quad (\mathrm{uWaveTower}\; h).\mathrm{ord} = \omega_{h+2} \quad (\omega \prec \omega^\omega \prec \omega^{\omega^\omega} \prec \cdots \prec \varepsilon_0).$$
2. **Compiled ODE System Dimension ([`uWaveTower_compile_length`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1992-L1999)):**
   $$\forall h \in \mathbb{N},\quad (\mathrm{uWaveTower}\; h).\mathrm{compile}.\mathrm{sys}.\mathrm{length} = h + 2.$$
   (2 coupled harmonic-oscillator states for $\sin/\cos$, plus $h$ nonlinear wave-modulation states.)
3. **Exact Quadratic Modulation Law ([`uWaveTower_eval_two`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L2010-L2020)):**
   Starting from $[x^2]\sin x = 0$, each wave-over-wave modulation stage $h$ adds exactly $1/2$ to the quadratic Taylor coefficient:
   $$\forall h \in \mathbb{N},\quad [x^2](\mathrm{uWaveTower}\; h) = \frac{h}{2}.$$
4. **Strict Hierarchy Expansion ([`uWaveTower_hierarchy_strictness`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L2024-L2037)):**
   For every $h \in \mathbb{N}$, `uWaveTower (h + 1)` belongs to $\mathcal{D}_{\omega_{h+3}}$, satisfies [`SemBellTowerLe (h + 1)`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1322-L1323), and **provably escapes `SemBellTowerLe h`**! By [`soundness_unitSeedTower`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1373-L1429), no unit-seed wave/exponential expression of composition depth $\le h$ (even with arbitrary constant shifts) can ever equal `uWaveTower (h + 1)`.
5. **Pairwise Semantic Distinctness ([`uWaveTower_semJetEq_injective`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L2042-L2047)):**
   $$\forall h_1, h_2 \in \mathbb{N},\quad \mathrm{SemJetEq}\; (\mathrm{uWaveTower}\; h_1).\mathrm{eval}\; (\mathrm{uWaveTower}\; h_2).\mathrm{eval} \implies h_1 = h_2.$$

---

## 6. Summary Table of the 4-Regime Ordinal Hierarchy Below $\varepsilon_0$

| Ordinal Regime $\alpha \prec \varepsilon_0$ | Differential Equation Mechanism | Semantic Function Class $H_\alpha$ | Soundness Theorem | Strict Separation & Impossibility Theorem |
| :--- | :--- | :--- | :--- | :--- |
| **Regime I:**<br>Finite Ordinals $k < \omega$ | Nilpotent / triangular integration chains $y_i' = y_{i-1}$ (`IsPoly`, `polyDeg ≤ k`) | [`SemPolyDegLe k`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L813): Taylor series vanishing identically for $n > k$ ($c_n = 0$) | [`soundness_polyDegLe`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L844-L852), [`soundness_below_omega`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L932-L935) | [`strictness_polyDegLe`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L889-L905), [`intrinsic_lower_bound_poly`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L912-L926) ($x^{k+1} \notin H_k$) |
| **Regime II:**<br>Linear Feedback $\omega \preceq \alpha \prec \omega^2$ | Arbitrary $N$-D linear ODE systems $\dot{Y} = AY + b$ ([`LinearGPACSys`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1541-L1542)) & exp-trig polynomials (`IsExpPoly`) | [`SemEntireExpType`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L820-L821): Entire functions with factorial decay $|c_n| \cdot n! \le 2^M (2^R)^n$ ($\rho = \infty$) | [`solN_linear_factorial_bound_computed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1830-L1869), [`soundness_below_omegaSq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1072-L1077) | [`strictness_at_omega`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L948-L954), [`no_isPoly_semJetEq_exp`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L958-L961) ($e^x \notin H_{<\omega}$) |
| **Regime III:**<br>Quadratic Self-Feedback $\alpha = \omega^2$ | Autonomous quadratic feedback $y' = y^2$ (`uGeom` $= \frac{1}{1-x}$) | Local analytic jets ([`RadiusJet`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RadiusJet.lean)) with finite blowup radius $\rho = 2^{-R} < \infty$ ($|c_n| \le 2^M (2^R)^n$) | [`solN_geom_bound_computed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L107-L146) | [`strictness_at_omegaSq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1130-L1140), [`no_linearGPACSys_semJetEq_uGeom`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1885-L1890), [`no_isExpPoly_semJetEq_uGeom`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1145-L1148) ($\frac{1}{1-x} \notin H_{<\omega^2}$) |
| **Regime IV:**<br>Transfinite Cascades $\omega_2 \prec \omega_3 \prec \cdots \prec \varepsilon_0$ | Iterated ODE composition & wave modulation $Y_{h+1}' = Y_h' \cdot Y_{h+1}$ ([`uTower`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L588-L592), [`uWaveTower`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1950-L1952)) | [`SemBellTowerLe h`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1322-L1323): Bell-tower / FM wave-modulation hierarchy ($|c_1| \le 1, c_2 \le h/2$) | [`soundness_unitSeedTower`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1373-L1429) | [`strictness_unitSeedTower`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1433-L1442), [`uWaveTower_hierarchy_strictness`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L2024-L2037), [`intrinsic_lower_bound_tower`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1448-L1455) |
