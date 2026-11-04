# The Complete Plain-English & Mathematical Guide to the $\mathsf{HA}^\omega$ Theorem Universe

**LaTeX Source:** [`docs/papers/complete_theorem_explainer.tex`](file:///Users/araaslyan/modified-realizability-haomega/docs/papers/complete_theorem_explainer.tex)  
**Compiled PDF (25 pages):** [`docs/papers/complete_theorem_explainer.pdf`](file:///Users/araaslyan/modified-realizability-haomega/docs/papers/complete_theorem_explainer.pdf)  
**Verification Status:** 100% verified by the Lean 4 kernel (0 errors, 0 warnings, 0 `sorry`s).

---

## Big Picture: How the Whole Universe Fits Together in 60 Seconds

1. **The Black-Box Problem:** In ordinary programming, a function $f$ is a "black box"—you plug in $x$ and get out $f(x)$. A computer cannot reliably take the derivative of a black box (because tiny hidden wiggles smaller than your step size $h$ can fool $\frac{f(x+h)-f(x)}{h}$), and integrating it to 10 decimal places by slicing into rectangles takes billions of steps.
2. **Our Solution (Taylor Recipe + 2 Safety Numbers):** Every function in our universe is stored not as a black box, but as:
   - A **Taylor coefficient recipe** $n \mapsto c_n \in \mathbb{Q}$ so that $f(x) = c_0 + c_1 x + c_2 x^2 + \cdots$, and
   - **Two safety numbers $(M, R) \in \mathbb{N}^2$** extracted directly from the formula's syntax that guarantee $|c_n| \le 2^M \cdot (2^R)^n$ for every $n$.
   Because of $(M, R)$, taking a derivative or integral takes **1 step**, and computing $f(x)$ to $k$ bits of accuracy ($2^{-k}$) only requires adding the first $N(k) = k + M + 3$ terms!

---

## Part I: The Proof-to-Program Engine ($\mathsf{HA}^\omega$ & System T)

### Theorem Group 1: Soundness of Modified Realizability (Proofs $\to$ Programs)
- **Explain It Like I'm 5:** Imagine a cookbook where every time someone proves *"a delicious cake exists,"* a magical machine automatically reads their proof and prints out the exact step-by-step baking recipe—along with a guarantee that the recipe never gets stuck and always bakes the exact cake promised. That machine is [`extract`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Extraction.lean#L99-L100).
- **Why It Matters:** Turns constructive proofs in $\mathsf{HA}^\omega$ (`Deriv`) into running functional programs in Gödel's System T (`Tm`) that are mathematically guaranteed to satisfy the formula's realizability specification.
- **Key Mathematical Facts:**
  - Every formula $\varphi$ has a realizer type [`Formula.realTy`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Realizability.lean) and specification $w \;\mathbf{mr}\; \varphi$ ([`Formula.mr`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Realizability.lean)).
  - **Soundness ([`soundness`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Soundness.lean#L172-L174), [`extractClosed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Extraction.lean)):** For any closed derivation $d : \mathrm{Deriv}\;[]\;\varphi$, $(\operatorname{extractClosed}\;d).\mathrm{eval}\;() \;\mathbf{mr}\; \varphi$.

### Theorem Group 2: The Kirby–Paris Hydra & Transfinite Induction Below $\varepsilon_0$
- **Explain It Like I'm 5:** Imagine fighting a monster tree (a Hydra). Every time you chop off one head, the Hydra grows *ten* new copies of the branch below it! It looks like the Hydra is getting bigger and bigger forever. This theorem proves that no matter which heads you chop, **the Hydra always dies in a finite number of chops** because every Hydra has a "super-number" (an ordinal below $\varepsilon_0$) that strictly goes down on every chop.
- **Why It Matters:** Proves that Cantor Normal Form ordinals below $\varepsilon_0$ ([`Eps0.oLtE_wf`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdCnf.lean#L249)) cannot decrease forever—giving us the transfinite ruler used to grade our differential-equation hierarchy.
- **Key Lean 4 Theorems:** [`hercules_wins`](file:///Users/araaslyan/modified-realizability-haomega/Realizability/Theorems/Hydra/HydraGeneral.lean#L299), [`no_infinite_play`](file:///Users/araaslyan/modified-realizability-haomega/Realizability/Theorems/Hydra/HydraGeneral.lean#L300), [`Eps0.oLtE_wf`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdCnf.lean#L249), [`ordEOfHydra`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/HydraTyped.lean#L159).

### Theorem Group 3: The Constructive Analysis Hierarchy & Galois Calibration (`A0` $\to$ `RadiusJet`)
- **Explain It Like I'm 5:** Think of functions like cars:
  - `A0` (Continuous): You only know where the car is.
  - `A1` (Differentiable): You also have a speedometer ($f'$).
  - `RadiusJet` (Power Series): You have the car's complete blueprint—every derivative at $0$ ($c_0, c_1, c_2, \dots$) plus two safety numbers $(M, R)$ that bound all of them at once.
  Once you have the `RadiusJet` blueprint, you can automatically build the speedometer (`A1`) and position tracker (`A0`) with zero guesswork!
- **Key Lean 4 Modules:** [`HAomega/SmoothnessHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SmoothnessHierarchy.lean), [`HAomega/Jet.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/Jet.lean), [`HAomega/AnalyticJet.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/AnalyticJet.lean), [`HAomega/RadiusJet.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RadiusJet.lean), [`HAomega/PascalTheorem.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/PascalTheorem.lean), [`HAomega/InverseFunction.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/InverseFunction.lean).

---

## Part II: Polynomial Differential Equations & The Closed Analytic Universe

### Theorem Group 4: Solving Any System of Polynomial ODEs One Coefficient at a Time (`genSolveND`)
- **Explain It Like I'm 5:** Suppose you have a machine where the speed of each gear depends on the positions of the other gears ($Y' = P(Y)$). Instead of guessing the whole curve at once, you find the starting position $c_0$, use the speed rule to find the initial slope $c_1$, use that to find the curvature $c_2$, and so on—locking in **one exact fraction $c_n$ at a time** like snapping Lego bricks together!
- **Key Mathematical Facts:**
  - Exact Taylor recurrence ([`sbd_solN_succ_val`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemBound.lean)): $(\operatorname{solN}\;\mathrm{sys}\;v\;(n+1)).\mathrm{val} = \frac{F_v(\operatorname{solN}\;\mathrm{sys})(n)}{n+1}$.
  - Formal $\mathsf{HA}^\omega$ existence proof: [`genSolveND`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/PolyODESystemN.lean#L365-L370).

### Theorem Group 5: The Two Magic Safety Numbers $(M, R)$ From Syntax (`sysParams` & `solN_geom_bound_computed`)
- **Explain It Like I'm 5:** Our function [`sysParams`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L82-L84) looks at a differential equation **just once** (without solving it!) and hands you two whole numbers $M$ and $R$. Those two numbers guarantee $|c_n| \le 2^M \cdot (2^R)^n$ for every $n$, which tells you **before you even start** that adding $k + M + 3$ terms gives $k$ bits of accuracy!
- **Key Lean 4 Theorems:** [`sysParams`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L82-L84), [`solN_geom_bound_computed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L107-L146), [`jetCauchyModulusComputedD`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/JetCauchyComputed.lean#L276-L286), [`extractedJetCauchyModulusComputed_eq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/JetCauchyComputed.lean).

### Theorem Group 6: The Closed Algebraic Universe of Calculus (`UExpr.compile_correct`)
- **Explain It Like I'm 5:** Start with just 5 Lego pieces: $\mathbb{Q}, x, e^x, \sin x, \cos x$. Combine them using $+, -, \times, \div, \frac{d}{dx}, \int_0^x$, and composition $f(g(x))$ as many times as you want. Every single creation you build automatically compiles into one unified Polynomial ODE machine (`GPACSys`) with its own $(M, R)$ safety numbers!
- **Key Lean 4 Theorems:** [`UExpr.compile`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseExpr.lean), [`UExpr.compile_correct`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseExpr.lean#L540-L619), [`InGPAC`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseGPAC.lean#L46-L48).

### Theorem Group 7: Automatic Inverse & 2-Variable Implicit Functions (`InGPAC_invFun` & `InGPAC_impFun`)
- **Explain It Like I'm 5:** What if $x$ and $y$ are tangled together in $g(y(x)) = x$ or $\sin(y) + x \cdot y - x = 0$ where you can't isolate $y$ by algebra? Differentiate both sides to find how fast $y$ moves ($y' = -E_x / E_y$), and let the ODE machine build $y(x)$ one Taylor coefficient at a time!
- **Key Lean 4 Theorems:** [`InGPAC_invFun`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseInvFun.lean), [`InGPAC_impFun`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseImpFun.lean#L938-L1044), [`UExpr.autoInverse_comp_sol_eq_varX`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1315-L1380).

### Theorem Group 8: Multi-Step Analytic Continuation & Boundary-Value Cannon Shooting (`stepData` & `shootBVP`)
- **Explain It Like I'm 5:** A power series centered at $0$ is like a flashlight that only lights up a small circle around $0$. To walk down a long hallway, walk partway to the edge of your circle, turn on a *new* flashlight centered where you are standing ([`stepData`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemStep.lean)), and keep marching! And to hit a target $y(b) = \beta$ at the end of the hallway, [`shootBVP`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ShootingBVP.lean) adjusts the starting angle of the cannon by binary search until the trajectory hits the bullseye!
- **Key Lean 4 Modules:** [`HAomega/SystemStep.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemStep.lean), [`HAomega/ShootingBVP.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ShootingBVP.lean).

---

## Part III: Computational Adequacy (`HAomega/ComputationalAdequacy.lean`)

### Theorem Group 9: From Exponential Proof Trees to Fast Dynamic Programming (`extraction_to_fast`)
- **Explain It Like I'm 5:** Direct proof extraction asks two helpers for the 29th number, each of whom asks two helpers for the 28th number—creating $2^{30} \approx 1\text{ billion}$ calls! A smart dynamic-programming table ([`solFast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemFast.lean#L38-L39)) writes the numbers down on a notepad from $0$ up to $n$ so nobody ever recalculates the same number twice. Theorem [`extraction_to_fast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L146-L148) proves that the fast notepad table gives the **exact same fraction** as the proof-extracted program!

### Theorem Group 10: Certified Infinite Power-Series Evaluation in $\mathbb{R}$ (`certified_evaluation`)
- **Explain It Like I'm 5:** Inside the safe circle $|x| \le 2^{-(R+1)}$, each term of the infinite series is at most half the size of the previous bound, so stopping at term $N(k) = k + M + 3$ is **guaranteed to be within $2^{-k}$ of the true infinite sum $\sum_{n=0}^\infty c_n x^n \in \mathbb{R}$**!
- **Key Lean 4 Theorems:** [`CertifiedAnalyticRep.analyticValue`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L174-L175), [`CertifiedAnalyticRep.analyticValue_sub_evalPoly_le`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L239-L273), [`certified_evaluation`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L279-L309).

### Theorem Group 11: Why You Can Never Skip the Tail Bound (`no_uniform_modulus_without_tail_info`)
- **Explain It Like I'm 5:** Even if two functions have the **exact same first $N_0$ coefficients** (say $0, 0, \dots, 0$), one can stay at $0$ forever while the other suddenly has a huge spike at term $N_0 + 1$ that changes $f(1/2)$ by $2$. Without a promise about the unseen infinite tail, no algorithm can ever certify accuracy!
- **Key Lean 4 Theorem:** [`no_uniform_modulus_without_tail_info`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1744-L1776).

### Theorem Group 12: Representation-to-Representation Closure (`PolyODEProof` Transformers)
- **Explain It Like I'm 5:** Every calculus operation ($+,-,\times,\div,\frac{d}{dx},\int_0^x,\circ$) transforms one certified ODE package (`PolyODEProof`) directly into another certified ODE package, and taking the derivative of the integral (or integrating the derivative) recovers the exact infinite series!
- **Key Lean 4 Theorems:** [`PolyODEProof.add`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L986-L990), [`PolyODEProof.mul`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1038-L1042), [`PolyODEProof.integ`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1077-L1081), [`PolyODEProof.derivOp`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1102-L1106), [`PolyODEProof.derivOp_integ_analyticValue`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1218-L1221), [`PolyODEProof.newtonLeibniz_analyticValue_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1275-L1290).

### Theorem Group 13: Infinite-Series Secant & Root-Location Adequacy (`analyticValue_root_location_of_deriv_margin`)
- **Explain It Like I'm 5:** If you are $0.01$ meters above sea level ($|f(x)| \le 0.01$) and the hill's slope is at least $m > 0$ everywhere, then the shoreline ($f(z)=0$) cannot be farther than $\frac{0.01}{m}$ away! We prove how to check that slope $m > 0$ using **one finite derivative polynomial** (`evalPoly` minus $2^{-k}$) so the guarantee holds for the **true infinite series**!
- **Key Lean 4 Theorems:** [`PolyODEProof.analyticValue_secant_of_deriv_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L661-L731), [`PolyODEProof.analyticValue_root_location_of_deriv_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L740-L775), [`PolyODEProof.rootFast_analyticValue_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L866-L939), [`PolyODEProof.rootFast_cauchy_of_deriv_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L948-L977).

### Theorem Group 14: Certified Fourier Series Evaluation & Parseval's Identity (`StripFourierRep`)
- **Explain It Like I'm 5:** Pure notes of different frequencies are orthogonal, so an inner product plucks out each exact Fourier coefficient ([`TrigPoly.inner_mode_eq_coeff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1403-L1429)) and total wave energy equals the sum of squared mode amplitudes ([`TrigPoly.parseval`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/TrigPolyInner.lean#L172)). When high-frequency notes decay exponentially ($|c_n| \le 2^M \cdot 2^{-R|n|}$), keeping frequencies $|n| \le k + M + 1$ approximates the infinite wave within $2^{-k}$ ([`StripFourierRep.certified_fourier_series_evaluation`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ComputationalAdequacy.lean#L1631-L1642))!

---

## Part IV: Classical Real-Analysis Semantic Bridge & Fixed-Point Operators (`HAomega/RealCalculusBridge.lean`)

### Theorem Group 15: Real Power-Series Extension & Quadratic Tangent-Line Remainder (`realAnalyticValue_quad_rem_disk`)
- **Explain It Like I'm 5:** Extends our power series from fractions $x \in \mathbb{Q}$ to **all real numbers $x \in \mathbb{R}$** ([`CertifiedAnalyticRep.realAnalyticValue`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L86-L87)), and proves that the gap between the curve $f(y)$ and its tangent line $f(x) + f'(x)(y-x)$ shrinks with the **square** of the distance: $|f(y) - f(x) - f'(x)(y-x)| \le 2^{M+2R+5}(y-x)^2$ ([`PolyODEProof.realAnalyticValue_quad_rem_disk`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L689-L745)).

### Theorem Group 16: Classical Mathlib `HasDerivAt` & `intervalIntegral` Fundamental Theorem of Calculus
- **Explain It Like I'm 5:** Proves that our formal derivative is 100% equal to Mathlib's classical real derivative [`HasDerivAt`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L802-L809) on $\mathbb{R}$, and that our fast definite-integral algorithm [`defIntegralFast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L883-L909) approximates Mathlib's classical Bochner/Riemann integral $\int_a^b f(t)\,dt$ within $2^{-k}$!

### Theorem Group 17: Unconditional Constructive Root Sequence & Genuine Real Zero Existence (`rootSeq_converges_to_real_zero`)
- **Explain It Like I'm 5:** If $f(a) \le -2^{-k_0}$ (underwater) and $f(b) \ge +2^{-k_0}$ (on dry land) with upward slope $m > 0$, our 1-parameter sequence $r_n = P.\operatorname{rootSeq}\;a\;b\;k_0\;n$ automatically picks the right grid depth and precision at every step so that $|f(r_n)| \le 2^{-n}$, and converges in $\mathbb{R}$ to a **genuine real zero $z_* \in [a, b]$ where $f(z_*) = 0$** without assuming a zero existed beforehand!
- **Key Lean 4 Theorems:** [`PolyODEProof.rootColor_endpoints_ne_of_sign_margin`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L975-L1016), [`PolyODEProof.rootSeq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L1027-L1028), [`PolyODEProof.rootSeq_residual_le`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L1035-L1089), [`PolyODEProof.rootSeq_converges_to_real_zero`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L1201-L1282).

### Theorem Group 18: Certified Fixed-Point Operators (`fixFast` & `fixRootSeq`)
- **Explain It Like I'm 5:** A fixed point is a number that doesn't move when you apply $f$: $f(z_*) = z_*$.
  1. **Shrinking Map Machine ([`PolyODEProof.fixFast`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L1290-L1292), [`PolyODEProof.fixFast_converges_to_fixedPoint`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L1433-L1521)):** If $f$ shrinks distances by at least half, iterating $x_{n+1} = \operatorname{approxFast}(x_n, 2n+2)$ cuts the distance to $z_*$ in half every step and converges to $f(z_*) = z_*$!
  2. **General Fixed-Point Machine ([`PolyODEProof.fixPointEq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L1525-L1526), [`PolyODEProof.fixPoint_iff_fixPointEq_zero`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RealCalculusBridge.lean#L1602-L1606)):** Even if $f$ doesn't shrink distances, $f(x) = x$ is the exact same thing as a root of $g(x) = f(x) - x = 0$!

---

## Part V: The Optimizing Compiler for Mathematical Analysis (`HAomega/CertifiedOptimization.lean`)

### Theorem Group 19: Terminating Bottom-Up Symbolic Normalizer (`UExpr.normalize`)
- **Explain It Like I'm 5:** If you integrate a function and immediately differentiate it ($\frac{d}{dx}\int_0^x f$), or take $1/(1/f)$, or compose $f$ with $x$, [`UExpr.normalize`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L284-L296) **cancels them out before building the differential equation**—and [`UExpr.normalize_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L619-L689) proves that the simplified expression preserves `Defined`, every Taylor coefficient, and the infinite series sum!

### Theorem Group 20: Arbitrary-Depth Tower Collapse (`iterDerivInteg_normalize` & `autoInverse_comp_compress_to_varX`)
- **Explain It Like I'm 5:** Stacking $d$ layers of $\frac{d}{dx}\int_0^x$ or $1/(1/\cdot)$ or composing an autonomous ODE $Y' = F(Y)$ with its inverse $\operatorname{autoInverse}(F) \circ Y$ collapses all the way down to $f$ (or to the 1-state identity ODE [`PolyODEProof.varX`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L938-L939), $y'=1, y(0)=0$)!
- **Key Lean 4 Theorems:** [`UExpr.iterDerivInteg_normalize`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L736-L741), [`UExpr.iterCompX_normalize`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L746-L751), [`UExpr.iterInvPair_normalize`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L756-L764), [`UExpr.autoInverse_comp_compress_to_varX`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L964-L999).

### Theorem Group 21: Certified Representation Compression & Cost-Guided Selection (`compress_of_coeff_eq` & `optimizeToPolyODEProof_spec`)
- **Explain It Like I'm 5:** If two ODE systems $P_1, P_2$ have the same Taylor coefficients (`SemEq`), [`PolyODEProof.compress_of_coeff_eq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L815-L840) and [`UExpr.optimizeToPolyODEProof_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CertifiedOptimization.lean#L917-L933) let you safely replace the big slow ODE with the smaller, faster one (and even analytically continue to a wider disk when $R_2 \le R_1$).

---

## Part VI: The $\varepsilon_0$ Descriptive Differential Hierarchy & "Waves Over Waves" (`HAomega/OrdinalODEHierarchy.lean`)

### Theorem Group 22: Regime I ($k < \omega$) — Finite Ordinals & The Polynomial Degree Wall
- **Explain It Like I'm 5:** Chains of integrators without feedback loops only make polynomials of degree $\le k$ whose coefficients are $0$ forever after $k$ ([`soundness_polyDegLe`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L844-L852)), and no formula of ordinal $\le k$ can ever equal $x^{k+1}$ ([`intrinsic_lower_bound_poly`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L912-L926)).

### Theorem Group 23: Regime II ($\omega \preceq \alpha \prec \omega^2$) — Linear ODE Systems & The $1/n!$ Factorial Barrier
- **Explain It Like I'm 5:** Linear feedback ($y'' = -y$ for $\sin x$, $y' = y$ for $e^x$, or any $N$-dimensional [`LinearGPACSys`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1541-L1542)) has Taylor coefficients that shrink like $1/n!$ ([`solN_linear_factorial_bound_computed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1830-L1869): $|c_n| \cdot n! \le 2^M(2^R)^n$), so linear waves never blow up at any finite time ($\rho = \infty$).

### Theorem Group 24: Regime III ($\alpha = \omega^2$) — Nonlinear Blowup & The Unbreakable $\omega^2$ Wall
- **Explain It Like I'm 5:** When a state multiplies by itself ($y' = y^2 \implies y = \frac{1}{1-x}$), it blows up at $x = 1$ ($c_n = 1$ forever). Theorem [`no_linearGPACSys_semJetEq_uGeom`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1885-L1890) proves that **even if you couple $N$ linear harmonic oscillators together for any dimension $N$, they can never equal $\frac{1}{1-x}$**!

### Theorem Group 25: Regime IV ($\omega_2 \prec \omega_3 \prec \cdots \prec \varepsilon_0$) — "Waves Over Waves" & The Descriptive Differential Hierarchy
- **Explain It Like I'm 5:** Feeding a wave $\sin x$ into the speed of the next differential equation $W_{h+1}' = W_h' \cdot W_{h+1}$ ([`uWaveTower`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1950-L1952)) climbs the Cantor ordinals $\omega \prec \omega^\omega \prec \omega^{\omega^\omega} \prec \cdots \prec \varepsilon_0$ inside the cumulative hierarchy [`InDescDiff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1907-L1909). Every single layer adds $\frac{1}{2}$ to the $x^2$ coefficient ($[x^2]W_h = \frac{h}{2}$, [`uWaveTower_eval_two`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L2010-L2020)), proving that **every level of the infinite $\varepsilon_0$ tower creates a genuinely new waveform that no lower level can ever reach** ([`uWaveTower_hierarchy_strictness`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L2024-L2037), [`uWaveTower_semJetEq_injective`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L2042-L2047))!

---

## Part VII: Validated Numerics, Krawczyk Boxes, and True Fourier Integral Reconstruction ([`HAomega/ValidatedNumerics.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean))

### Theorem Group 26: Fixed-Denominator Dyadic Ball Arithmetic (`approxDyadic_spec`)
- **Explain It Like I'm 5:** If you add fractions like $\frac{1}{3} + \frac{1}{5} + \frac{1}{7} + \frac{1}{11}$, the bottom number (the denominator) multiplies out to $3 \times 5 \times 7 \times 11 = 1155$ and quickly explodes to millions of digits! Instead, [`roundDyadic`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L59-L60) rounds every single term $c_n x^n$ onto a binary ruler with a fixed power-of-two denominator $2^p$ (`⌊q · 2^p⌋ / 2^p`). Because every term now has the *exact same denominator* $2^p$, we just add ordinary integers (`evalDyadicNum`), and [`CertifiedAnalyticRep.approxDyadic_spec`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L194-L237) proves that at degree $N = k + M + 2$ and binary precision $p = 2k + M + 3$, the combined rounding error plus infinite-series tail error is still at most $2^{-k}$!

### Theorem Group 27: The Certified 1D & $N$-Dimensional Krawczyk Operator (`krawczykFast_exists_unique_real_zero`, `krawczykND_exists_unique_zero`)
- **Explain It Like I'm 5:** Bisection (`rootSeq`) needs the curve to cross from below zero to above zero ($f(a) < 0 < f(b)$)—which doesn't even make sense when you have 3 equations and 3 unknowns in 3D space! The **Krawczyk / Simplified-Newton Operator** $K(x) = x - C \cdot F(x)$ takes a ball (or $d$-dimensional box) around your initial guess $x_0$ and checks if $K$ shrinks distances by at least $\frac{1}{2}$ inside the box ([`PolyODEProof.krawczykMap_contractive_of_deriv_approx`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L294-L358)) and moves the center $x_0$ by at most half the radius. When it does, the box is **trapped inside itself** ([`PolyODEProof.krawczykMap_maps_ball_to_ball`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L264-L286), [`krawczykIterND_mem_closedBall`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L633-L652)), guaranteeing that a **unique** true zero $z_*$ exists inside the box and that iterating $K$ converges to $z_*$ at speed $2^{-n}$ in both 1D ([`PolyODEProof.krawczykFast_exists_unique_real_zero`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L498-L598)) and $d$ dimensions ([`krawczykND_exists_unique_zero`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L714-L817))!

### Theorem Group 28: Classical Mathlib Fourier Integral Orthogonality & True Fourier Reconstruction (`certified_fourier_reconstruction`)
- **Explain It Like I'm 5:** Earlier, `certified_fourier_series_evaluation` proved that if we already know a wave's list of musical notes, adding the first $N(k) = k + M + 1$ notes gets within $2^{-k}$ of the infinite sum. Now we prove the full **musical tuning-fork theorem** using Mathlib's real integral $\int_0^{2\pi}$: multiplying a periodic analytic wave [`StripFourierRep.realWave`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L1041-L1042) by $\cos(mx)$ or $\sin(mx)$ and integrating from $0$ to $2\pi$ cancels out every other frequency ([`integral_cos_mul_cos_two_pi`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L921-L952), [`integral_sin_mul_sin_two_pi`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L957-L988), [`integral_sin_mul_cos_two_pi`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L993-L1011)), extracts the exact amplitudes ([`StripFourierRep.realFourierA0_realWave`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L1324-L1345), [`StripFourierRep.realFourierA_realWave`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L1350-L1377), [`StripFourierRep.realFourierB_realWave`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L1382-L1409)), and reconstructs the original wave $F.\operatorname{realWave}(x)$ from its classical Mathlib Fourier integrals within $2^{-k}$ ([`StripFourierRep.certified_fourier_reconstruction`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ValidatedNumerics.lean#L1443-L1459))!

