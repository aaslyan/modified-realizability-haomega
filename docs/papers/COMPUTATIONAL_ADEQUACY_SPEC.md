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

## 3. Theorem II — Calculus Adequacy, True Infinite-Series Root Location, and Representation-to-Representation Closure

### A. Decisive Theorem IIA — True Infinite-Series Secant & Root-Location Adequacy in $\mathbb{R}$
A lower bound $|S_N(f')(y)| \ge m > 0$ on a single truncated derivative polynomial does **not** by itself certify a root-location bound for later partial sums or the true function $f$, because the derivative truncation remainder could destroy the lower bound.

Instead, let $P : \mathsf{PolyODEProof}$, $S := P.\operatorname{toCertifiedAnalyticRep}$, and $F := \operatorname{GPACSys.radiusJet}\;P.\mathrm{sys}\;P.\mathrm{wf}\;P.v\;P.\mathrm{hv}$. Let $N_k = k + (F.\mathrm{deriv}.M + 3)$ be the proof-extracted Cauchy modulus of `F.deriv` at precision $k$ on $[a,b] \subseteq [-2^{-(F.R+2)}, 2^{-(F.R+2)}]$. If the truncated derivative satisfies the **remainder-guarded margin**:
$$(F.\mathrm{deriv}.\mathrm{toJet}.\mathrm{evalPoly}\;N_k\;y).\mathrm{val} - \frac{1}{2^k} \ge m > 0 \qquad \forall y \in [a, b],$$
then:
1. **Persistence across all higher partial sums ([`RadiusJet.deriv_margin_persists`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L527-L544)):** Every higher partial sum $S_{N_k + d}(F')(y)$ ($d \in \mathbb{N}$) satisfies $S_{N_k + d}(F')(y) \ge m > 0$ on $[a, b]$.
2. **Secant bound for all higher partial sums ([`RadiusJet.location_error_of_deriv_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L555-L571)):** For every $d \in \mathbb{N}$ and all $x, z \in [a, b]$,
   $$|x.\mathrm{val} - z.\mathrm{val}| \le \frac{|(F.\mathrm{toJet}.\mathrm{evalPoly}\;(N_k + d + 1)\;x).\mathrm{val} - (F.\mathrm{toJet}.\mathrm{evalPoly}\;(N_k + d + 1)\;z).\mathrm{val}|}{m}.$$
3. **Passage to the $d \to \infty$ Infinite-Series Limit in $\mathbb{R}$ ([`PolyODEProof.analyticValue_secant_of_deriv_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L661-L731)):** Combining [`CertifiedAnalyticRep.analyticValue_sub_evalPoly_le`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L239-L273) at $x$ and $z$ with Archimedean elimination of $C / 2^d$ across all $d \in \mathbb{N}$ ([`real_le_of_forall_sub_pow2_le`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L627-L639)), the **true infinite real power series** $S.\operatorname{analyticValue} : Q \to \mathbb{R}$ satisfies:
   $$(m : \mathbb{R}) \cdot \big|(x.\mathrm{val} : \mathbb{R}) - (z.\mathrm{val} : \mathbb{R})\big| \le \big|S.\operatorname{analyticValue}(x) - S.\operatorname{analyticValue}(z)\big|.$$
4. **True Infinite-Series Root Location & Fast Evaluation Error Bound ([`PolyODEProof.analyticValue_root_location_of_deriv_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L740-L775)):** For any zero $z \in [a, b]$ of the true analytic function ($S.\operatorname{analyticValue}(z) = 0$), every point $x \in [a, b]$, and every evaluation precision $j \in \mathbb{N}$:
   $$\big|(x.\mathrm{val} : \mathbb{R}) - (z.\mathrm{val} : \mathbb{R})\big| \le \frac{|S.\operatorname{analyticValue}(x)|}{(m : \mathbb{R})} \le \frac{\big|((\operatorname{GPACSys.approxFast}\;P.\mathrm{sys}\;P.v\;x\;j).\mathrm{val} : \mathbb{R})\big| + 1 / (2 : \mathbb{R})^j}{(m : \mathbb{R})}.$$
5. **Constructive Root Approximation & Cauchy Bounds Under Endpoint Sign Changes ([`PolyODEProof.analyticValue_lipschitz_disk`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L784-L844), [`PolyODEProof.rootFast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L856-L857), [`PolyODEProof.rootFast_analyticValue_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L866-L939), [`PolyODEProof.rootFast_cauchy_of_deriv_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L948-L977)):**
   - Using the proof-extracted binary search [`bisect`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Bisection.lean#L24-L28) applied to `GPACSys.approxFast`, whenever the endpoint sign colors differ (`P.rootColor a b j p 0 ≠ P.rootColor a b j p (2^j)`), `P.rootFast a b j p` constructs a rational point $r_{j,p} \in [a, b]$ whose true infinite power series satisfies:
     $$\big|S.\operatorname{analyticValue}(r_{j,p})\big| \le \frac{1}{2^p} + 2^{M + R + 2}\frac{b - a}{2^j}.$$
   - Combined with the secant lower bound, any two bisection approximations $r_{j_1, p_1}, r_{j_2, p_2}$ satisfy the explicit mutual Cauchy bound:
     $$\big|(r_{j_1, p_1}.\mathrm{val} : \mathbb{R}) - (r_{j_2, p_2}.\mathrm{val} : \mathbb{R})\big| \le \frac{|S.\operatorname{analyticValue}(r_{j_1, p_1})| + |S.\operatorname{analyticValue}(r_{j_2, p_2})|}{(m : \mathbb{R})}.$$
   - *Scope note:* `rootFast_cauchy_of_deriv_margin` bounds the residual and mutual Cauchy distance of bisection iterates given endpoint sign changes; proving unconditional real root existence additionally requires defining the explicit precision schedule $(j(n), p(n))$ and discharging the endpoint sign-color hypothesis uniformly from $f(a) < 0 < f(b)$.

### B. Decisive Theorem IIB — Representation-to-Representation Closure (`PolyODEProof → PolyODEProof` Transformers, Representation-Level Newton–Leibniz, and Local Autonomous Inverse)
Every calculus operation acts directly as a representation-to-representation compiler $\mathsf{PolyODEProof} \longrightarrow \mathsf{PolyODEProof}$ preserving well-formedness (`GPACSys`), extracted realizers (`genSolveND`), fast evaluation (`solFast_val`), and infinite-series convergence (`CertifiedAnalyticRep`):

| Operation | `PolyODEProof` Transformer | Coefficient Soundness Theorem |
| :--- | :--- | :--- |
| Addition ($f + g$) | [`PolyODEProof.add`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L986-L990) | [`PolyODEProof.add_coeff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L993-L1009) |
| Subtraction ($f - g$) | [`PolyODEProof.sub`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1012-L1016) | [`PolyODEProof.sub_coeff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1019-L1035) |
| Multiplication ($f \cdot g$) | [`PolyODEProof.mul`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1038-L1042) | [`PolyODEProof.mul_coeff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1045-L1060) |
| Reciprocal ($1 / f$, $f(0) \neq 0$) | [`PolyODEProof.inv`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1063-L1067) | [`PolyODEProof.inv_coeff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1070-L1074) |
| Indefinite Integral ($\int_0^x f$) | [`PolyODEProof.integ`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1077-L1081) | [`PolyODEProof.integ_coeff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1084-L1099) |
| Derivative ($f'$) | [`PolyODEProof.derivOp`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1102-L1106) | [`PolyODEProof.derivOp_coeff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1109-L1124) |
| Composition ($f \circ (g - g(0))$) | [`PolyODEProof.comp`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1128-L1136) | [`PolyODEProof.comp_coeff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1139-L1156) |
| Whole-Universe Compiler (`UExpr`) | [`UExpr.toPolyODEProof`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L334-L338) | [`UExpr.eval_eq_extracted_and_fast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L349-L357) |

In addition, we establish three foundational analytic closure results:
- **Representation-Level FTC Part 1 & Part 2 on Infinite Power Series ([`PolyODEProof.derivOp_integ_analyticValue`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1218-L1221), [`PolyODEProof.integ_derivOp_analyticValue`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1247-L1267)):**
  $$(P.\mathrm{integ}.\mathrm{derivOp}).\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(x) = P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(x),$$
  $$(P.\mathrm{derivOp}.\mathrm{integ}).\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(x) = P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(x) - (P.\mathrm{toCertifiedAnalyticRep}.\mathrm{coeff}\;0 : \mathbb{R}).$$
- **Representation-Level Infinite-Series Newton–Leibniz Adequacy ([`PolyODEProof.defIntegralFast_analyticValue_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1170-L1190), [`PolyODEProof.newtonLeibniz_analyticValue_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1275-L1290)):** For $a, b$ in the certified disks of `P` and `P.derivOp.integ`, the fast definite integral of the formal derivative `P.derivOp.defIntegralFast a b k` approximates the true infinite power-series difference of `P` within $2^{-k}$ in $\mathbb{R}$:
  $$\left|\big((P.\mathrm{derivOp}.\operatorname{defIntegralFast}\;a\;b\;k).\mathrm{val} : \mathbb{R}\big) - \big(P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(b) - P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(a)\big)\right| \le \frac{1}{2^k}.$$
  (*Scope note:* these identities equate the formal operators `derivOp` and `integ` at the level of the infinite power series `analyticValue`; connecting `derivOp.analyticValue` and `defIntegralFast` to Mathlib's `HasDerivAt` and `intervalIntegral` on $\mathbb{R}$ is a separate semantic bridge layer.)
- **Left Compositional Inverse of Autonomous 1D ODEs ([`UExpr.autoInverse`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1296-L1297), [`UExpr.autoInverse_toPolyODEProof`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1304-L1306), [`UExpr.autoInverse_comp_sol_eq_varX`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1315-L1380)):** For an autonomous 1D ODE $y'(x) = F(y(x))$ with $y(0) = 0$ and $F(0) \neq 0$, its inverse $g(t) = \int_0^t \frac{1}{F(s)}\,ds = \operatorname{UExpr.autoInverse}(F)$ compiles to a `PolyODEProof` and satisfies the exact left formal composition identity $(g \circ Y) = \mathrm{varX}$ (`((Jet.compZero ⟨(UExpr.autoInverse F).eval⟩ Y).coeff n).val = (Jet.varX.coeff n).val`) at every Taylor degree $n \in \mathbb{N}$ (scope restricted to autonomous 1D ODEs; general root/inverse evaluation is handled by `PolyODEProof.rootFast`).

### C. Certified Fourier Series Evaluation on a Strip ([`StripFourierRep`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1447-L1452))
Models $2\pi$-periodic Fourier series analytic on a strip of width $R \ge 1$ via two-sided Gaussian-rational coefficient streams `c : Int → CQ` satisfying
$$|(c\;n).\mathrm{re}.\mathrm{val}| + |(c\;n).\mathrm{im}.\mathrm{val}| \le 2^M \cdot \left(\frac{1}{2^R}\right)^{|n|},$$
and establishes:
1. **Exact Modal Coefficient Extraction ([`TrigPoly.inner_mode_eq_coeff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1403-L1429), [`StripFourierRep.inner_trunc_mode_eq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1464-L1470)):**
   $$\operatorname{toCRat}\bigl(\operatorname{TrigPoly.inner}\;(F.\mathrm{trunc}\;N)\;(\operatorname{TrigPoly.mode}\;n)\bigr) = \operatorname{toCRat}(F.c\;n) \qquad (|n| \le N).$$
2. **Certified Infinite Fourier Series Evaluation & Explicit Truncation Error ([`StripFourierRep.summable_shellTerm`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1559-L1566), [`StripFourierRep.fourierValue_sub_evalTrunc_le`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1584-L1618), [`StripFourierRep.certified_fourier_series_evaluation`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1631-L1642)):**
   For any bounded trigonometric phase pair $(\mathrm{cs}, \mathrm{sn} : \mathbb{Z} \to \mathbb{R})$ with $|\mathrm{cs}(n)| \le 1$, $|\mathrm{sn}(n)| \le 1$, the symmetric frequency-shell series converges absolutely to $F.\operatorname{fourierValue}(\mathrm{cs}, \mathrm{sn}) \in \mathbb{R}$, and at the linear truncation modulus $N(k) = k + F.M + 1$:
   $$\big|F.\operatorname{evalTrunc}(\mathrm{cs}, \mathrm{sn}, k + F.M + 1) - F.\operatorname{fourierValue}(\mathrm{cs}, \mathrm{sn})\big| \le \frac{1}{2^k}.$$
   (*Scope note:* `certified_fourier_series_evaluation` certifies evaluation of the Fourier series `F.fourierValue` from its stored coefficient stream `F.c`; proving genuine Fourier reconstruction $f(x) = \sum_{n \in \mathbb{Z}} \widehat{f}(n) e^{inx}$ where $\widehat{f}(n)$ is computed by the Fourier integral of an independently specified periodic analytic function $f$ is a separate theorem.)

### D. Unified Calculus Operations Adequacy Theorem ([`calculus_adequacy_master`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1699-L1724))
Packages (1) extraction-to-fast equivalence (`extraction_to_fast`), (2) $2^{-k}$ certified power-series evaluation (`certified_evaluation`), (3) representation-level FTC1 (`derivOp_integ_analyticValue`) and FTC2 (`newtonLeibniz_analyticValue_spec`), and (4) modal coefficient extraction and $2^{-k}$ infinite Fourier series evaluation (`certified_fourier_series_evaluation`) into a single summary theorem.

---

## 4. Selected Non-Redundancy & Scope Notes

1. **Necessity of Effective Tail Information ([`no_uniform_modulus_without_tail_info`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1744-L1776)):**
   For any candidate truncation degree $N_0 \in \mathbb{N}$, there exist two jets $F_1, F_2$ agreeing on all coefficients $n \le N_0$ whose degree-$(N_0 + 2)$ evaluations at $x = 1/2$ differ by $2$. This proves that some effective tail bound (whether $(M, R)$ or an equivalent majorant) is indispensable for certified evaluation.
2. **Non-Redundancy of ODE Feedback & Nonlinearity:**
   - Removing ODE feedback collapses to polynomials (`no_poly_eq_exp` in [`AlgebraicHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/AlgebraicHierarchy.lean#L211-L216)).
   - Removing nonlinear state multiplication restricts coefficients to $O(C^n / n!)$, excluding $1/(1-x)$ (`no_linearGPACSys_semJetEq_uGeom` in [`OrdinalODEHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L438-L450)).
3. **Scope Note on Bit Complexity & Conditioning:**
   The equivalence `solFast_val` eliminates the exponential $O(2^n)$ Picard tree recursion of `solN` in favor of $O(n^2 |\mathrm{sys}|)$ rational arithmetic operations, and `N(k) = k + M + 3` is linear in $k$. Full polynomial bit-complexity bounds additionally require tracking the bit-length growth of exact rational denominators or dyadic rounding, which is treated as a separate complexity layer.

---

## 5. Certified Normalization, Representation Compression, and Cost-Guided ODE Optimization ([`HAomega/CertifiedOptimization.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean))

We separate four distinct mechanisms for simplifying stacked analytic operations without losing correctness or convergence certificates:

1. **Terminating Bottom-Up Normalization ([`UExpr.normalize`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L284-L296), [`UExpr.normalize_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L619-L689), [`UExpr.normalize_idempotent`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L363-L459)):**
   - Cancels calculus and algebraic inverse pairs (`deriv (integ a) ⟶ a`, `inv (inv a) ⟶ a`, `comp a x ⟶ a`, `comp (const q) b ⟶ const q`, `deriv (const q) ⟶ 0`, `deriv x ⟶ 1`, `deriv exp ⟶ exp`, `deriv sin ⟶ cos`, and neutral elements) while respecting the zero-normalized composition semantics $\operatorname{comp}(f,g)(x) = f(g(x)-g(0))$ ([`compZero_varX_right_val`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L126-L135), [`compZero_varX_left_val`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L140-L185)).
   - Proved to preserve `UExpr.Defined` ([`UExpr.Defined.normalize`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L692-L693)), preserve exact rational Taylor coefficients ([`UExpr.normalize_eval_eq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L696-L698)) and infinite power-series sums ([`UExpr.normalize_analyticValue_eq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L705-L714)), never increase AST size ([`UExpr.normalize_astSize_le`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L322-L356)), reach an idempotent normal form in one pass (`e.normalize.normalize = e.normalize`), and collapse arbitrary-depth towers ([`UExpr.iterDerivInteg_normalize`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L736-L741), [`UExpr.iterCompX_normalize`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L746-L751), [`UExpr.iterInvPair_normalize`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L756-L764)).
2. **Representation Compression ([`PolyODEProof.SemEq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L772-L773), [`PolyODEProof.compress_of_coeff_eq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L815-L840)):**
   - Given a semantic equivalence certificate `h : P₁.SemEq P₂` ($\forall n,\;c_{P_1}(n) = c_{P_2}(n)$), evaluating `P₂` via `GPACSys.approxFast` on `P₂`'s certified disk approximates `P₁.toCertifiedAnalyticRep.analyticValue x` within $2^{-k}$; when $R_2 \le R_1$, `P₂` simultaneously serves as a drop-in evaluator on `P₁`'s disk and a certified analytic continuation to $|x| \le 2^{-(R_2+1)}$.
3. **Cost-Guided Candidate Selection ([`PolyODEProof.BetterRep`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L862-L863), [`PolyODEProof.selectBetter_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L890-L899), [`UExpr.optimizeToPolyODEProof_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L917-L933)):**
   - `UExpr.optimizeToPolyODEProof` accepts the normalized ODE system when it dominates the original in state dimension `dim`, majorant exponent `majM`, and radius exponent `radR`, guaranteeing `P.SemEq P_opt`, `P_opt.BetterRep P`, and `P_opt.RepCost ≤ P.RepCost` (without claiming global minimality across all possible ODE systems).
4. **Autonomous-Inverse Tower Compression ([`UExpr.autoInverse_comp_compress_to_varX`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L964-L999)):**
   - Proves that the compiled composition $(\operatorname{autoInverse}(F) \circ Y)$ is semantically equivalent (`SemEq`) to the 1-state identity ODE [`PolyODEProof.varX`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L938-L939) ($y' = 1, y(0) = 0$) and compresses to it under `selectBetter`.
