# Computationally Adequate Analysis: Formal Specification & Architecture

**Module:** [`HAomega/ComputationalAdequacy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean)  
**Companion Hierarchy Module:** [`HAomega/OrdinalODEHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean)

---

## 1. Architectural Overview: Three Levels of Adequacy

A central insight of the $\mathsf{HA}^\omega$ development is that turning constructive mathematical analysis into an executable numerical discipline requires distinguishing—and formally bridging—three levels of adequacy:

| Level | Meaning | Formal Realization in `HAomega/` |
| :--- | :--- | :--- |
| **1. Logical Adequacy** | Constructive proofs in $\mathsf{HA}^\omega$ (`Deriv`) yield Gödel System T witnesses (`Tm`) via modified realizability. | [`extract`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Extraction.lean#L99-L100), [`soundness`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Soundness.lean#L172-L174), [`genSolveND`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/PolyODESystemN.lean#L365-L370), [`jetCauchyModulusComputedD`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/JetCauchyComputed.lean#L276-L286) |
| **2. Representation Adequacy** | Extracted witnesses for a specified family of polynomial ODE proofs (`PolyODEProof`) admit syntax-computed analytic majorants $(M, R)$ and define a convergent infinite power series $f_{S,v}(x) = \sum_{n=0}^\infty c_{S,v}(n) x^n \in \mathbb{R}$. | [`PolyODEProof`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L64-L68), [`CertifiedAnalyticRep`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L112-L126), [`sysParams`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L82-L84), [`solN_geom_bound_computed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L107-L109) |
| **3. Numerical Adequacy** | An optimized bottom-up dynamic-programming evaluator (`solFast`) computes the exact same rational coefficients as the proof-extracted System T witness (avoiding exponential Picard tree unfolding) and approximates $f_{S,v}(x)$ within $2^{-k}$ at the proof-extracted truncation degree $N(k) = k + M + 3$. | [`solFast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemFast.lean#L38-L39), [`solFast_val`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemFast.lean#L124-L126), [`extraction_to_fast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L146-L148), [`certified_evaluation`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L279-L309) |

Furthermore, we separate three methodological claims throughout:
1. **Expressive Sufficiency:** Well-formed rational polynomial IVPs (`GPACSys`) generate the analytic expression universe [`UExpr`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseExpr.lean#L28-L41).
2. **Computational Adequacy:** Theorem I (Extraction–Representation–Evaluation Adequacy) and Theorem II (Compositional Calculus Adequacy).
3. **Selected Non-Redundancy (Not Absolute Minimality):** Representation-independent separation theorems showing what breaks when ODE feedback, nonlinear state multiplication, or effective tail-bound certificates are omitted.

---

## 2. Theorem I — The Extraction–Representation–Evaluation Adequacy Theorem

Let $P \in \mathsf{PolyODEProof}$ be a well-formed rational polynomial initial-value problem
$$Y_v = A_v + \int_0^x F_v(Y), \qquad v < \mathrm{sys.length},$$
with canonical $\mathsf{HA}^\omega$ inductive existence derivation
$$\mathcal{D}_P := \operatorname{genSolveND}\;P.\mathrm{sys}\;(\operatorname{gpac\_wf}\;P.\mathrm{wf}) : \mathrm{Deriv}\;\mathrm{Ctx.nil}\;(\forall k : \mathrm{nat}.\; \operatorname{genSolveNInv}\;P.\mathrm{sys}).$$
Let $c_{P}(n) = (\operatorname{solN}\;P.\mathrm{sys}\;P.v\;n).\mathrm{val} \in \mathbb{Q}$ be the $n$-th Taylor coefficient of component $v$, and let $(M, R) = \operatorname{sysParams}(P.\mathrm{sys})$.

### The Commuting Diagram

```
  Constructive Proof in HA^ω                Polynomial IVP Syntax
    D_P := genSolveND sys hwf                     GPACSys sys
               │                                       │
 extractClosed │                                       │ sysParams + solFast
               ▼                                       ▼
    Extracted System T Witness             Certified Fast Tabular Evaluator
      extractedCoeff sys hwf v n  ═══════►     (solFast sys v n).val
                              extraction_to_fast
                                       │
                                       │  N(k) = extractedJetCauchyModulusComputed
                                       ▼
                        Certified Numerical Evaluation
                  |approxFast(sys, v, x, k) - f_{sys,v}(x)| ≤ 2^{-k}
```

### Formal Components in [`HAomega/ComputationalAdequacy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean)

1. **Part A — Extraction Correctness ([`extractedCoeff_eq_solN`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L84-L88), [`extractedCoeff_unique_of_fixedPoint`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L94-L100)):**
   For every $n \in \mathbb{N}$, the witness extracted by `extractClosed` at Picard step $n + 1$ computes the unique formal ODE Taylor coefficient:
   $$\operatorname{extractedCoeff}\;P.\mathrm{sys}\;(\operatorname{gpac\_wf}\;P.\mathrm{wf})\;P.v\;n = c_P(n).$$
2. **Part B — Fast Evaluation Equivalence ([`PolyODEProof.toCertifiedAnalyticRep`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L130-L141), [`extraction_to_fast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L146-L148)):**
   For every $S : \mathrm{CertifiedAnalyticRep}$ and $n \in \mathbb{N}$,
   $$\operatorname{extractedCoeff}\;S.\mathrm{sys}\;(\operatorname{gpac\_wf}\;S.\mathrm{wf})\;S.v\;n = (\operatorname{solFast}\;S.\mathrm{sys}\;S.v\;n).\mathrm{val} = S.\mathrm{coeff}\;n.$$
3. **Part C — Certified Analytic Representation & Infinite-Series Limit in $\mathbb{R}$ ([`CertifiedAnalyticRep.analyticValue`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L174-L175), [`summable_seriesTerm`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L218-L223), [`analyticValue_sub_evalPoly_le`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L231-L266)):**
   Define the real-valued power series
   $$S.\operatorname{analyticValue}(x) := \sum_{n=0}^{\infty} (S.\mathrm{coeff}\;n : \mathbb{R}) \cdot (x.\mathrm{val} : \mathbb{R})^n \in \mathbb{R}.$$
   For every rational point $x$ in the certified disk $|x.\mathrm{val}| \le 2^{-(S.R + 1)}$:
   - Each term satisfies $\|S.\operatorname{seriesTerm}\;x\;n\| \le 2^{S.M} \cdot (1/2)^n$ ([`seriesTerm_abs_le`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L200-L214)), so the series is absolutely summable in $\mathbb{R}$.
   - Since `Jet.evalPoly F N x` sums indices $0 \le n < N$ (`Finset.range N`), the infinite remainder from index $N$ to $\infty$ satisfies:
     $$\left|\big((\operatorname{Jet.mk}\;(\operatorname{solFast}\;S.\mathrm{sys}\;S.v)).\operatorname{evalPoly}\;N\;x\big).\mathrm{val} - S.\operatorname{analyticValue}(x)\right| \le \frac{2^{S.M + 1}}{2^N}.$$
4. **Part D — Certified Numerical Adequacy ([`certified_evaluation`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L279-L309), [`certified_evaluation_rational_tail`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L313-L318)):**
   Evaluating [`GPACSys.approxFast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemFast.lean#L144-L146) at the proof-extracted Cauchy modulus $N(k) = k + M + 3$ gives an error at most $2^{-(k+2)} \le 2^{-k}$ against the true real analytic sum:
   $$\left|(\operatorname{GPACSys.approxFast}\;P.\mathrm{sys}\;P.v\;x\;k).\mathrm{val} - P.\operatorname{toCertifiedAnalyticRep}.\operatorname{analyticValue}(x)\right| \le \frac{1}{2^k}.$$

---

## 3. Theorem II — Calculus Adequacy, Validated Root Location, and Strip Fourier Analysis

### A. Whole-Universe Compilation ([`UExpr.toPolyODEProof`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L324-L328), [`UExpr.eval_eq_extracted_and_fast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L339-L347))
Every defined expression $e : \mathrm{UExpr}$ (built from constants, $x, \exp, \sin, \cos$, $+, -, \times, \mathrm{inv}, \int_0^x, \frac{d}{dx}, \circ$) compiles via [`UExpr.compile`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseEval.lean#L86-L108) into a `PolyODEProof` such that for all $n \in \mathbb{N}$:
$$(e.\operatorname{eval}\;n).\mathrm{val} = \operatorname{extractedCoeff}\;e.\mathrm{compile.sys}\;\dots\;e.\mathrm{compile.v}\;n = (\operatorname{solFast}\;e.\mathrm{compile.sys}\;e.\mathrm{compile.v}\;n).\mathrm{val}.$$

### B. Validated Root Location via Corrected Derivative Remainder Margin ([`RadiusJet.deriv_margin_persists`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L517-L534), [`RadiusJet.location_error_of_deriv_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L545-L561))
A lower bound $|S_N(f')(y)| \ge m > 0$ on a single truncated derivative polynomial does **not** by itself certify a root-location bound for later partial sums or the true function $f$, because the derivative truncation remainder could destroy the lower bound.

Instead, let $N_k = k + (F.\mathrm{deriv}.M + 3)$ be the proof-extracted Cauchy modulus of `F.deriv` at precision $k$ on $[a,b] \subseteq [-2^{-(F.R+2)}, 2^{-(F.R+2)}]$. If the truncated derivative satisfies the **remainder-guarded margin**:
$$(F.\mathrm{deriv}.\mathrm{toJet}.\mathrm{evalPoly}\;N_k\;y).\mathrm{val} - \frac{1}{2^k} \ge m > 0 \qquad \forall y \in [a, b],$$
then:
1. By [`RadiusJet.deriv_margin_persists`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L517-L534), **every higher partial sum** $S_{N_k + d}(F')(y)$ ($d \in \mathbb{N}$) satisfies $S_{N_k + d}(F')(y) \ge m > 0$ on $[a, b]$.
2. By [`jet_evalPoly_secant_lower_bound`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L486-L505) and [`RadiusJet.location_error_of_deriv_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L545-L561), for every $d \in \mathbb{N}$ and all $x, z \in [a, b]$:
   $$|x.\mathrm{val} - z.\mathrm{val}| \le \frac{|(F.\mathrm{toJet}.\mathrm{evalPoly}\;(N_k + d + 1)\;x).\mathrm{val} - (F.\mathrm{toJet}.\mathrm{evalPoly}\;(N_k + d + 1)\;z).\mathrm{val}|}{m}.$$

### C. Analytic Fourier Adequacy on a Strip ([`StripFourierRep`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L585-L590))
Models $2\pi$-periodic functions analytic on a strip of width $R \ge 1$ via two-sided Gaussian-rational coefficient streams `c : Int → CQ` satisfying
$$|(c\;n).\mathrm{re}.\mathrm{val}| + |(c\;n).\mathrm{im}.\mathrm{val}| \le 2^M \cdot \left(\frac{1}{2^R}\right)^{|n|},$$
proving exponential mode decay ([`tail_mode_bound`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L613-L622)) and closure under addition ([`StripFourierRep.add`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L625-L654)).

---

## 4. Selected Non-Redundancy & Scope Notes

1. **Necessity of Effective Tail Information ([`no_uniform_modulus_without_tail_info`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L673-L705)):**
   For any candidate truncation degree $N_0 \in \mathbb{N}$, there exist two jets $F_1, F_2$ agreeing on all coefficients $n \le N_0$ whose degree-$(N_0 + 2)$ evaluations at $x = 1/2$ differ by $2$. This proves that some effective tail bound (whether $(M, R)$ or an equivalent majorant) is indispensable for certified evaluation.
2. **Non-Redundancy of ODE Feedback & Nonlinearity:**
   - Removing ODE feedback collapses to polynomials (`no_poly_eq_exp` in [`AlgebraicHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/AlgebraicHierarchy.lean#L211-L216)).
   - Removing nonlinear state multiplication restricts coefficients to $O(C^n / n!)$, excluding $1/(1-x)$ (`no_linearGPACSys_semJetEq_uGeom` in [`OrdinalODEHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L438-L450)).
3. **Scope Note on Bit Complexity & Conditioning:**
   The equivalence `solFast_val` eliminates the exponential $O(2^n)$ Picard tree recursion of `solN` in favor of $O(n^2 |\mathrm{sys}|)$ rational arithmetic operations, and `N(k) = k + M + 3` is linear in $k$. Full polynomial bit-complexity bounds additionally require tracking the bit-length growth of exact rational denominators or dyadic rounding, which is treated as a separate complexity layer.
