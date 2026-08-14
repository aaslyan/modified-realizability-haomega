# Constructive Analysis via Galois Adequacy: Newton–Leibniz, Banach Fixed Points, and Picard–Lindelöf Synthesis

**Author**: Ara Aslyan  
**Formalization**: Lean 4 (`HAomega.EFTC`, `HAomega.QAnalysis`, `HAomega.Picard`, `HAomega.FixedPoint`, `HAomega.ODEDemo`)

---

## Abstract

We demonstrate the Galois adequacy framework developed in Paper A on two independent foundational theorem families of analysis:
1. **Newton–Leibniz Fundamental Theorems of Calculus ($\mathrm{EFTC1}/\mathrm{EFTC2}$)** on exact rational samplers ($A_0, A_1$) and approximating evaluators ($E_0, E_1$).
2. **Fixed Point Analysis**: The Banach Contraction Mapping Theorem and the Browder–Göhde–Kirk / Krasnoselskii–Mann theorem for non-expansive mappings.

We prove that these two pillars synthesize to solve non-linear ordinary differential equations $y'(x) = f(x, y(x))$ purely by composing the Riemann integration operator ($\mathrm{EFTC1}$), the $A_1$ composition closure ($\circ$), and the Banach contraction fixed-point iteration. Every construction and theorem is formalized in Lean 4 with 0 axioms beyond standard logic, extracting explicit polynomial convergence rates and executing concrete ODE solutions in the proof assistant.

---

## 1. The Calculus Universe: $A_0, A_1, E_0, E_1$

We define a constructive hierarchy of function representations on a rational interval $[a, b]$:

```
                          Differentiation (EFTC2)
                     A₁ ───────────────────────────> E₀
                     │                                ▲
             Forget  │                                │ Conservativity
                     ▼         Integration (EFTC1)    │
                     A₀ ───────────────────────────> E₁
```

1. **$A_0$ (Uniformly Continuous Samplers)**:
   A rational function $f : \mathbb{Q} \to \mathbb{Q}$ equipped with an explicit modulus of continuity $\omega : \mathbb{N} \to \mathbb{N}$:
   $$|x - y| \le 2^{-\omega(k)} \implies |f(x) - f(y)| < 2^{-k}$$
2. **$A_1$ (Uniformly Differentiable Samplers)**:
   Extends $A_0$ with a derivative sampler $F' : \mathbb{Q} \to \mathbb{Q}$ and a modulus of uniform differentiability $\delta : \mathbb{N} \to \mathbb{N}$:
   $$0 < |h| \le 2^{-\delta(k)} \implies \left| \frac{f(x+h) - f(x)}{h} - F'(x) \right| < 2^{-k}$$
3. **$E_0$ (Approximating Evaluators)**:
   A sequence of rational samplers $f_n : \mathbb{Q} \to \mathbb{Q}$ converging uniformly with rate $c : \mathbb{N} \to \mathbb{N}$:
   $$n, m \ge c(k) \implies \|f_n - f_m\|_\infty \le 2^{-k}$$
4. **$E_1$ (Approximating $C^1$ Evaluators)**:
   $E_0$ equipped with uniform continuity and difference quotient convergence data.

### Formalized Theorems (Lean 4)
- **$\mathrm{EFTC1}$ (`A0.intE1`)**: For every $f \in A_0$, its Riemann integral $\int_a^x f(t)\,dt$ is in $E_1$ with exact derivative $f$.
- **$\mathrm{EFTC2}$ (`eftc2_thm`)**: For every $F \in A_1$, $\int_a^b F'(t)\,dt = F(b) - F(a)$.
- **Composition Closure (`CompData1.comp`)**: If $F, G \in A_1$, then $F \circ G \in A_1$ with extracted modulus:
  $$\delta_{F \circ G}(k) = \max\Big(G.\delta(k + 3 + M_F),\ G.\omega\big(F.\delta(k + 3 + M_G)\big)\Big)$$

---

## 2. Fixed Point Analysis: Contractions and Non-Expansive Maps

### 2.1 The Banach Contraction Mapping Theorem (`HAomega.Picard`)

Let $\mathcal{T} : (C[a, b], \|\cdot\|_\infty) \to (C[a, b], \|\cdot\|_\infty)$ be a uniform $2^{-p}$-contraction ($p \ge 1$).

**Theorem (Cauchy Convergence with Extracted Rate)**:
Starting from initial point $y_0$ with $\|y_0 - \mathcal{T}(y_0)\|_\infty \le 2^M$, the Picard iterates $y_{n+1} = \mathcal{T}(y_n)$ satisfy:
1. **Consecutive step bound**: $\|y_n - y_{n+1}\|_\infty \le 2^M / 2^{p n}$.
2. **Geometric telescoping sum**:
   $$\|y_n - y_m\|_\infty \le \frac{2^{M+1}}{2^{p n}} \left(1 - \frac{1}{2^{m-n}}\right) \le \frac{2^{M+1}}{2^{p n}}$$
3. **Extracted Rate**: $\Phi(k) = \lceil (k + M + 1) / p \rceil$ guarantees $\|y_n - y_m\|_\infty \le 2^{-k}$ for all $n, m \ge \Phi(k)$ (`ContractionOp.cauchy`).

**Corollary (`PicardData.solution`)**: The sequence packages into a `LimSeq`, producing the unique fixed-point solution $y^* \in E_0$ with inherited modulus of uniform continuity.

### 2.2 Non-Expansive Maps: Browder–Göhde–Kirk & Krasnoselskii–Mann (`HAomega.FixedPoint`)

For non-expansive maps ($L = 1$, $|T(x) - T(y)| \le |x - y|$), Picard iteration fails. The averaged Krasnoselskii–Mann operator:
$$T_{1/2}(x) = \frac{1}{2} x + \frac{1}{2} T(x)$$
computes approximate fixed points $|x_n - T(x_n)| \le 2^{-k}$ with polynomial rate:
$$\Phi(k) = 4 \lceil (b - a)^2 + 1 \rceil \cdot 4^k$$

### 2.3 The Intermediate Value Theorem: Constructive Barrier & Galois Adequacy (`HAomega.IVT`)

The classical Intermediate Value Theorem $\forall f \in C[a, b], (f(a) < 0 \land f(b) > 0) \implies \exists x, f(x) = 0$ is well-known to be **constructively false** because locating the exact zero requires the Limited Principle of Omniscience ($\mathrm{LLPO}$).

Under Galois adequacy:
1. **The Galois Approximate IVT (`ivt_adjacent_bracket`)**:
   For any $f \in A_0$, on any grid of step size $\delta \le 2^{-\omega(k)}$, adjacent sign crossings $f(x_i) \le 0 \le f(x_{i+1})$ bracket a $2^{-k}$-approximate zero: $|f(x_i)| \le 2^{-k}$ and $|f(x_{i+1})| \le 2^{-k}$.
2. **Transversality and Root Isolation (`root_isolation`)**:
   When $f \in A_1$ has derivative bounded away from zero ($f' \ge 2^{-M} > 0$), any two $2^{-k}$-approximate zeros are geometrically isolated: $|x - y| \le 2^{M + 1 - k}$, establishing constructive convergence to an exact isolated root.

---

## 3. The Picard–Lindelöf Synthesis

We unify integration and fixed-point iteration to solve initial value problems:
$$y'(x) = f(x, y(x)), \quad y(a) = y_0$$

### The Algorithmic Pipeline
1. **Integral Formulation ($\mathrm{EFTC1}$)**: Transform ODE into integral operator:
   $$\mathcal{T}(y)(x) = y_0 + \int_a^x f(t, y(t))\,dt$$
2. **Evaluation Composition ($\circ$)**: $t \mapsto f(t, y(t))$ is preserved under $A_0$ composition.
3. **Contractivity**: For $f$ with Lipschitz constant $2^L$ on interval $b - a \le 2^{-(L + p)}$, $\mathcal{T}$ is a $2^{-p}$-contraction (`picard_integral_contracts`).
4. **Banach Fixed Point**: Iteration $y_{n+1} = \mathcal{T}(y_n)$ converges in $E_0$ with rate $\Phi(k)$.
5. **Regularity Promotion**: Since $y^* = \mathcal{T}(y^*)$, $y^*$ is the integral of a continuous function, hence promoted by $\mathrm{EFTC1}$ to $E_1 \cong A_1$, satisfying $(y^*)'(x) = f(x, y^*(x))$ with $y^*(a) = y_0$.

---

## 4. Executable Verification in Lean 4 (`HAomega.ODEDemo`)

We instantiate the pipeline on the canonical IVP $y' = y, y(0) = 1$ on $[0, 1/2]$:
- Picard operator: $\mathcal{T}(P)(x) = 1 + \int_0^x P(t)\,dt$.
- Iterates: $P_n(x) = \sum_{j=0}^n \frac{x^j}{j!}$ (Taylor polynomials of $e^x$).
- Lean `#guard` verified exact rational values at $x = 1/2$ ($\sqrt{e} \approx 1.64872127$):
  - $P_1(1/2) = 3/2 = 1.5$
  - $P_2(1/2) = 13/8 = 1.625$
  - $P_3(1/2) = 79/48 \approx 1.64583$
  - $P_4(1/2) = 211/128 \approx 1.6484375$
  - $P_5(1/2) = 6331/3840 \approx 1.6486979$
  - $P_6(1/2) = 75973/46080 \approx 1.6487196$ (error $< 2 \cdot 10^{-6}$)

---

## 5. Conclusion

By grounding analysis in Galois adequacy, we obtain an ultra-aphoristic, fully constructive universe of mathematical analysis:
- All theorems are computational algorithms with extracted rates of convergence.
- Differentiation, integration, and fixed point iteration compose seamlessly.
- The entire theory is machine-verified with 0 unproved axioms in Lean 4.
