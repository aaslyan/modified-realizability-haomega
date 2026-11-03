/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SystemFast
import HAomega.NewtonUniverse
import HAomega.TrigPolyInner
import HAomega.OrdinalODEHierarchy

/-!
# Computationally Adequate Analysis: The Extraction–Representation–Evaluation Bridge

This module formalizes the two central adequacy theorems connecting constructive
proof theory in $\mathsf{HA}^\omega$ (modified realizability and Gödel System T witness
extraction) to certified analytic representations (`GPACSys`, `RadiusJet`) and
optimized numerical evaluation (`solFast`, `GPACSys.approxFast`):

## Theorem I — Extraction–Representation–Evaluation Adequacy (`CertifiedAnalyticRep`)
For every well-formed rational polynomial initial-value problem $S \in \mathsf{PolyODEProof}$
($Y_v = A_v + \int F_v(Y)$ with constant initial jets and constant leaves):
1. **A. Extraction Correctness (`extractedCoeff_eq_solN`, `extractedCoeff_unique_of_fixedPoint`)**:
   The canonical $\mathsf{HA}^\omega$ inductive existence derivation `genSolveND` extracts, via
   `extractClosed`, a closed Gödel System T functional whose value at $(n+1, v, n)$ computes
   the unique Taylor coefficient $c_{S,v}(n)$ of the ODE system.
2. **B. Fast Evaluation Equivalence (`extraction_to_fast`)**:
   The bottom-up dynamic-programming evaluator `solFast` computes the exact same rational
   coefficients as the proof-extracted System T witness:
   $$\operatorname{extractedCoeff}(S, v, n) = (\operatorname{solFast}\;S\;v\;n).\mathrm{val} = c_{S,v}(n).$$
3. **C. Certified Analytic Representation & Real Power-Series Limit (`analyticValue_sub_evalPoly_le`)**:
   The syntax-computed parameters $(M, R) = \operatorname{sysParams}(S)$ certify the geometric
   majorant $|c_{S,v}(n)| \le 2^M \cdot (2^R)^n$. Consequently, on the certified disk
   $|x| \le 2^{-(R+1)}$, the infinite power series
   $$f_{S,v}(x) = \sum_{n=0}^{\infty} c_{S,v}(n)\,x^n \in \mathbb{R}$$
   converges absolutely (`summable_seriesTerm`) and satisfies the explicit remainder bound
   $$\left|\big((\operatorname{Jet.mk}\;(\operatorname{solFast}\;S\;v)).\operatorname{evalPoly}\;N\;x\big).\mathrm{val}
     - f_{S,v}(x)\right| \le \frac{2^{M+1}}{2^N}.$$
4. **D. Certified Numerical Adequacy (`certified_evaluation`)**:
   Evaluating `GPACSys.approxFast S v x k` at the proof-extracted Cauchy modulus
   $N(k) = \operatorname{extractedJetCauchyModulusComputed}(\dots) = k + M + 3$ guarantees:
   $$\left|(\operatorname{GPACSys.approxFast}\;S\;v\;x\;k).\mathrm{val} - f_{S,v}(x)\right|
     \le 2^{-(k+2)} \le 2^{-k}.$$

## Theorem II — Compositional Calculus Adequacy, Validated Root Location, and Non-Redundancy
1. **Whole-Universe Compilation (`UExpr.toCertifiedAnalyticRep`)**:
   Every defined expression $e : \mathrm{UExpr}$ compiles via `UExpr.compile` into a
   `PolyODEProof` whose direct coefficient semantics `(e.eval n).val`, proof-extracted
   System T witness `extractedCoeff`, and fast evaluator `solFast` commute.
2. **Validated Root Location with Derivative Remainder Margin (`location_error_of_deriv_margin`)**:
   Replaces the uncertified assumption $|S_N(f')| \ge m$ with the remainder-guarded margin
   $(S_N(f')(y)).\mathrm{val} - 2^{M'+3-N} \ge m > 0$ across $[a,b] \subseteq [-2^{-(R+2)}, 2^{-(R+2)}]$,
   proving that *every* higher partial sum $S_{N+d}(f')$ remains $\ge m > 0$ and hence
   $$|x.\mathrm{val} - z.\mathrm{val}|
     \le \frac{|(S_{N+d+1}(f)(x)).\mathrm{val} - (S_{N+d+1}(f)(z)).\mathrm{val}|}{m}.$$
3. **Analytic Fourier Adequacy on a Strip (`StripFourierRep`)**:
   Periodic analytic functions with two-sided geometric decay $|c_k|_1 \le 2^M \cdot (2^{-R})^{|k|}$
   ($R \ge 1$) enjoy exponential truncation bounds and closure under addition and mean-zero integration.
4. **Necessity of Effective Tail Information (`no_uniform_modulus_without_tail_info`)**:
   No finite prefix of Taylor coefficients alone can determine a valid $2^{-k}$ truncation degree
   on $|x| \le 1/2$ without an upper bound certificate on the unseen tail.
-/

namespace HAomega

open Rat

/-! ## Section 1: Theorem I — Extraction–Representation–Evaluation Adequacy -/

/-- The canonical family of $\mathsf{HA}^\omega$ derivations for well-formed rational
    polynomial initial-value problems: packages a system `sys`, its `GPACSys` certificate,
    and a valid component index `v < sys.length`. -/
structure PolyODEProof where
  sys : List (Tm [] JetTy × JExprN)
  wf  : GPACSys sys
  v   : Nat
  hv  : v < sys.length

/-- The canonical $\mathsf{HA}^\omega$ natural-deduction proof
    $\mathcal{D}_S : \mathrm{Deriv}\;\mathrm{Ctx.nil}\;(\forall k : \mathrm{nat}.\; \mathrm{genSolveNInv}\;S.\mathrm{sys})$
    associated with `S : PolyODEProof`. -/
def PolyODEProof.deriv (S : PolyODEProof) :
    Deriv Ctx.nil (.all .nat (genSolveNInv S.sys)) :=
  genSolveND S.sys (gpac_wf S.wf)

/-- The rational Taylor coefficient extracted by modified realizability (`extractClosed`)
    from `genSolveND sys hwf` at Picard step `n + 1` (where degree `n` stabilizes). -/
def extractedCoeff (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v n : Nat) : Rat :=
  ((((extractClosed (genSolveND sys hwf)).eval Env.nil) (n + 1)).1 v n).val

/-- **Part A.1 (Extraction Correctness)**:
    The witness extracted by `extractClosed` from `genSolveND sys hwf` computes the
    exact rational value of `solN sys v n` for every $v, n \in \mathbb{N}$. -/
theorem extractedCoeff_eq_solN (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v n : Nat) :
    extractedCoeff sys hwf v n = (solN sys v n).val := by
  unfold extractedCoeff solN
  rw [extractClosed_genSolveND_fst sys hwf (n + 1)]

/-- **Part A.2 (Uniqueness of Extracted Witness)**:
    For any value-level fixed point $Z : \mathbb{N} \to \mathbb{N} \to Q$ of the ODE system's
    Picard operator `genStepN sys`, the proof-extracted witness `extractedCoeff` equals
    $(Z\;v\;n).\mathrm{val}$ for every $v < \mathrm{sys.length}$ and $n \in \mathbb{N}$. -/
theorem extractedCoeff_unique_of_fixedPoint (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (Z : Nat → Nat → Q)
    (hZ : ∀ v < sys.length, ∀ n,
      ((((genStepN sys (Γ := [])).eval Env.nil) Z) v n).val = (Z v n).val)
    (v : Nat) (hv : v < sys.length) (n : Nat) :
    extractedCoeff sys hwf v n = (Z v n).val :=
  genSolveN_unique_val sys hwf Z hZ (n + 1) v n hv (Nat.lt_succ_self n)

/-- **Certified Analytic Representation (`CertifiedAnalyticRep`)**:
    Assembles a well-formed polynomial IVP component `(sys, v)`, its mathematical
    Taylor coefficient sequence `coeff : ℕ → ℚ`, its majorant parameters `(M, R)`,
    and the three adequacy bridges:
    - `extraction_correct`: agreement with the proof-extracted System T realizer,
    - `fast_correct`: agreement with the bottom-up dynamic-programming evaluator `solFast`,
    - `majorant`: the geometric Cauchy majorant $|c_n| \le 2^M \cdot (2^R)^n$. -/
structure CertifiedAnalyticRep where
  sys   : List (Tm [] JetTy × JExprN)
  v     : Nat
  hv    : v < sys.length
  wf    : GPACSys sys
  M     : Nat
  R     : Nat
  coeff : Nat → Rat
  extraction_correct :
    ∀ n : Nat, extractedCoeff sys (gpac_wf wf) v n = coeff n
  fast_correct :
    ∀ n : Nat, (solFast sys v n).val = coeff n
  majorant :
    ∀ n : Nat, |coeff n| ≤ (2 : Rat) ^ M * ((2 : Rat) ^ R) ^ n

/-- **Part B.1 (Canonical Bridge from `PolyODEProof` to `CertifiedAnalyticRep`)**:
    Every `P : PolyODEProof` induces a `CertifiedAnalyticRep` with syntax-computed
    parameters `(M, R) = sysParams P.sys`. -/
def PolyODEProof.toCertifiedAnalyticRep (P : PolyODEProof) : CertifiedAnalyticRep where
  sys := P.sys
  v := P.v
  hv := P.hv
  wf := P.wf
  M := (sysParams P.sys).1
  R := (sysParams P.sys).2
  coeff := fun n ↦ (solN P.sys P.v n).val
  extraction_correct := fun n ↦ extractedCoeff_eq_solN P.sys (gpac_wf P.wf) P.v n
  fast_correct := fun n ↦ solFast_val P.sys P.wf P.v P.hv n
  majorant := fun n ↦ solN_geom_bound_computed P.sys P.wf P.v P.hv n

/-- **Part B.2 (Fast Evaluation Equivalence — The Commuting Diagram)**:
    For every `S : CertifiedAnalyticRep` and degree $n \in \mathbb{N}$, the coefficient
    extracted from the $\mathsf{HA}^\omega$ proof `genSolveND` equals the rational value
    computed by the bottom-up tabular evaluator `solFast`. -/
theorem extraction_to_fast (S : CertifiedAnalyticRep) (n : Nat) :
    extractedCoeff S.sys (gpac_wf S.wf) S.v n = (solFast S.sys S.v n).val := by
  rw [S.extraction_correct n, S.fast_correct n]

/-- Polynomial evaluation of `Jet.mk c` up to degree $N$ equals the finite sum
    $\sum_{n \in \mathrm{Finset.range}\;N} (c\;n).\mathrm{val} \cdot x.\mathrm{val}^n$. -/
theorem jet_evalPoly_val_eq_sum (c : Nat → Q) (x : Q) : ∀ N : Nat,
    ((Jet.mk c).evalPoly N x).val =
      ∑ n ∈ Finset.range N, (c n).val * x.val ^ n
  | 0 => by simp [Jet.evalPoly, Q.val_zero]
  | N + 1 => by
    rw [Jet.evalPoly_succ, jet_evalPoly_val_eq_sum c x N, Finset.sum_range_succ]

/-- Evaluating `solFast S.sys S.v` up to degree $N$ computes the exact polynomial
    partial sum $\sum_{n < N} S.\mathrm{coeff}(n)\, x^n$. -/
theorem CertifiedAnalyticRep.evalPoly_solFast_eq_sum (S : CertifiedAnalyticRep) (x : Q) (N : Nat) :
    ((Jet.mk (solFast S.sys S.v)).evalPoly N x).val =
      ∑ n ∈ Finset.range N, S.coeff n * x.val ^ n := by
  rw [jet_evalPoly_val_eq_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [S.fast_correct n]

/-! ### Part C: Infinite Power-Series Semantics in `ℝ` and Tail Remainder Bound -/

/-- The $n$-th real power-series term $c_n x^n \in \mathbb{R}$ of `S : CertifiedAnalyticRep`. -/
noncomputable def CertifiedAnalyticRep.seriesTerm (S : CertifiedAnalyticRep) (x : Q) (n : Nat) : ℝ :=
  (S.coeff n : ℝ) * (x.val : ℝ) ^ n

/-- **The Semantic Analytic Function $f_{S,v}(x) = \sum_{n=0}^{\infty} c_{S,v}(n)\,x^n \in \mathbb{R}$**
    defined by the convergent power series on the certified disk. -/
noncomputable def CertifiedAnalyticRep.analyticValue (S : CertifiedAnalyticRep) (x : Q) : ℝ :=
  ∑' n : Nat, S.seriesTerm x n

/-- Real-cast version of the majorant bound: $|S.\mathrm{coeff}\;n| \le 2^M \cdot (2^R)^n$ in $\mathbb{R}$. -/
theorem CertifiedAnalyticRep.majorant_real (S : CertifiedAnalyticRep) (n : Nat) :
    |(S.coeff n : ℝ)| ≤ (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ n := by
  have h := S.majorant n
  have hcast : ((|(S.coeff n)| : Rat) : ℝ) ≤ (((2 : Rat) ^ S.M * ((2 : Rat) ^ S.R) ^ n : Rat) : ℝ) := by
    exact_mod_cast h
  simpa only [Rat.cast_abs, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using hcast

/-- On the certified disk $|x.\mathrm{val}| \le 2^{-(R+1)}$, we have $2^R \cdot |x.\mathrm{val}| \le 1/2$ in $\mathbb{R}$. -/
theorem CertifiedAnalyticRep.scaled_abs_le_half (S : CertifiedAnalyticRep) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (S.R + 1)) :
    (2 : ℝ) ^ S.R * |(x.val : ℝ)| ≤ (1 / 2 : ℝ) := by
  have hx_real : |(x.val : ℝ)| ≤ 1 / (2 : ℝ) ^ (S.R + 1) := by
    have hcast : ((|x.val| : Rat) : ℝ) ≤ ((1 / (2 : Rat) ^ (S.R + 1) : Rat) : ℝ) := by
      exact_mod_cast hx
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hcast
  have hmul := mul_le_mul_of_nonneg_left hx_real (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ S.R)
  have hpow : (2 : ℝ) ^ S.R * (1 / (2 : ℝ) ^ (S.R + 1)) = (1 / 2 : ℝ) := by
    rw [pow_succ (2 : ℝ) S.R]
    field_simp
  linarith

/-- **Part C.1 (Termwise Geometric Decay on the Certified Disk)**:
    For $|x.\mathrm{val}| \le 2^{-(R+1)}$ and all $n \in \mathbb{N}$,
    $$|\operatorname{S.seriesTerm}\;x\;n| \le 2^M \cdot (1 / 2)^n.$$ -/
theorem CertifiedAnalyticRep.seriesTerm_abs_le (S : CertifiedAnalyticRep) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (S.R + 1)) (n : Nat) :
    ‖S.seriesTerm x n‖ ≤ (2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ n := by
  rw [Real.norm_eq_abs]
  unfold seriesTerm
  rw [abs_mul, abs_pow]
  have hmaj := S.majorant_real n
  have h1 := mul_le_mul_of_nonneg_right hmaj (by positivity : (0 : ℝ) ≤ |(x.val : ℝ)| ^ n)
  have hcomb : (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R) ^ n * |(x.val : ℝ)| ^ n =
      (2 : ℝ) ^ S.M * ((2 : ℝ) ^ S.R * |(x.val : ℝ)|) ^ n := by
    rw [mul_assoc, ← mul_pow]
  rw [hcomb] at h1
  have hhalf := S.scaled_abs_le_half x hx
  have hpow : ((2 : ℝ) ^ S.R * |(x.val : ℝ)|) ^ n ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_left₀ (by positivity) hhalf n
  have h2 := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ S.M)
  linarith

/-- **Part C.2 (Absolute Convergence of the Power Series)**:
    For $|x.\mathrm{val}| \le 2^{-(R+1)}$, the power series `S.seriesTerm x` is summable in $\mathbb{R}$. -/
theorem CertifiedAnalyticRep.summable_seriesTerm (S : CertifiedAnalyticRep) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (S.R + 1)) :
    Summable (S.seriesTerm x) := by
  have hgeom : Summable (fun n : Nat ↦ (2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left ((2 : ℝ) ^ S.M)
  exact Summable.of_norm_bounded hgeom (S.seriesTerm_abs_le x hx)

/-- **Part C.3 (Infinite-Series Tail Remainder Bound)**:
    On the certified disk $|x.\mathrm{val}| \le 2^{-(R+1)}$, for every truncation degree $N \in \mathbb{N}$,
    the difference between the degree-$N$ polynomial evaluation of `solFast` ($\sum_{n < N} c_n x^n$)
    and the infinite power-series sum `S.analyticValue x` is bounded by $2^{M+1-N}$:
    $$\left|\big((\operatorname{Jet.mk}\;(\operatorname{solFast}\;S.\mathrm{sys}\;S.v)).\operatorname{evalPoly}\;N\;x\big).\mathrm{val}
      - S.\operatorname{analyticValue}\;x\right| \le \frac{(2 : \mathbb{R})^{S.M + 1}}{(2 : \mathbb{R})^N}.$$ -/
theorem CertifiedAnalyticRep.analyticValue_sub_evalPoly_le (S : CertifiedAnalyticRep) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (S.R + 1)) (N : Nat) :
    |(((Jet.mk (solFast S.sys S.v)).evalPoly N x).val : ℝ) - S.analyticValue x|
      ≤ (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N := by
  have hsum_cast : (((Jet.mk (solFast S.sys S.v)).evalPoly N x).val : ℝ) =
      ∑ n ∈ Finset.range N, S.seriesTerm x n := by
    rw [S.evalPoly_solFast_eq_sum x N, Rat.cast_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    unfold seriesTerm
    simp [Rat.cast_mul, Rat.cast_pow]
  rw [hsum_cast]
  have hsummable := S.summable_seriesTerm x hx
  have hsplit := hsummable.sum_add_tsum_nat_add N
  have hdiff : (∑ n ∈ Finset.range N, S.seriesTerm x n) - S.analyticValue x =
      - (∑' k : Nat, S.seriesTerm x (k + N)) := by
    unfold analyticValue
    linarith
  rw [hdiff, abs_neg, ← Real.norm_eq_abs]
  have hshift_summable : Summable (fun k : Nat ↦ S.seriesTerm x (k + N)) :=
    hsummable.comp_injective (add_left_injective N)
  have hgeom_shift : Summable (fun k : Nat ↦ ((2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hterm_le : ∀ k : Nat,
      ‖S.seriesTerm x (k + N)‖ ≤ ((2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k := by
    intro k
    have hb := S.seriesTerm_abs_le x hx (k + N)
    have hpow : (2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ (k + N) =
        ((2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k := by
      rw [pow_add]
      ring
    linarith
  have htsum_le := norm_tsum_le_tsum_norm hshift_summable.norm
  have hbound := Summable.tsum_le_tsum hterm_le hshift_summable.norm hgeom_shift
  have hgeom_val : (∑' k : Nat, ((2 : ℝ) ^ S.M * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k) =
      (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    rw [pow_succ (2 : ℝ) S.M, one_div_pow]
    ring
  linarith

/-- **Part D.1 (Theorem I — Master Certified Numerical Adequacy Theorem)**:
    For every well-formed polynomial IVP $P \in \mathsf{PolyODEProof}$, every rational point
    $x$ in the certified disk $|x.\mathrm{val}| \le 2^{-(R+1)}$, and every target precision $k \in \mathbb{N}$,
    evaluating `GPACSys.approxFast` (which truncates `solFast` at the proof-extracted Cauchy
    modulus $N(k) = k + M + 3$) approximates the true infinite power-series sum
    `P.toCertifiedAnalyticRep.analyticValue x` within $2^{-(k+2)} \le 2^{-k}$:
    $$\left|(\operatorname{GPACSys.approxFast}\;P.\mathrm{sys}\;P.v\;x\;k).\mathrm{val}
      - P.\operatorname{toCertifiedAnalyticRep}.\operatorname{analyticValue}\;x\right|
      \le \frac{1}{(2 : \mathbb{R})^k}.$$ -/
theorem certified_evaluation (P : PolyODEProof) (x : Q) (k : Nat)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1)) :
    |((GPACSys.approxFast P.sys P.v x k).val : ℝ) -
        P.toCertifiedAnalyticRep.analyticValue x| ≤ 1 / (2 : ℝ) ^ k := by
  let S := P.toCertifiedAnalyticRep
  have hM : S.M = (sysParams P.sys).1 := rfl
  have hR : S.R = (sysParams P.sys).2 := rfl
  set N := extractedJetCauchyModulusComputed (solFast P.sys P.v) (sysParams P.sys).1 x k
  have hN_eq : N = k + ((sysParams P.sys).1 + 3) :=
    extractedJetCauchyModulusComputed_eq (solFast P.sys P.v) (sysParams P.sys).1 x k
  have hrem := S.analyticValue_sub_evalPoly_le x hx N
  change |((GPACSys.approxFast P.sys P.v x k).val : ℝ) - S.analyticValue x| ≤
    (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N at hrem
  have hle : (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N ≤ 1 / (2 : ℝ) ^ k := by
    rw [hM, hN_eq]
    have hpow : (2 : ℝ) ^ (k + ((sysParams P.sys).1 + 3)) =
        (2 : ℝ) ^ k * (2 : ℝ) ^ ((sysParams P.sys).1 + 1) * 4 := by
      rw [show k + ((sysParams P.sys).1 + 3) = k + ((sysParams P.sys).1 + 1) + 2 by omega,
          pow_add, pow_add]
      norm_num
    rw [hpow]
    have hpos_M : (0 : ℝ) < (2 : ℝ) ^ ((sysParams P.sys).1 + 1) := by positivity
    have hpos_k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hsimp : (2 : ℝ) ^ ((sysParams P.sys).1 + 1) /
        ((2 : ℝ) ^ k * (2 : ℝ) ^ ((sysParams P.sys).1 + 1) * 4) =
        (1 / 4) * (1 / (2 : ℝ) ^ k) := by
      field_simp
    rw [hsimp]
    linarith [one_div_nonneg.mpr (le_of_lt hpos_k)]
  exact le_trans hrem hle

/-- **Part D.2 (Rational Finite-Tail Adequacy Corollary)**:
    Every later partial sum of degree $N(k) + d$ stays within $2^{-k}$ of
    `GPACSys.approxFast P.sys P.v x k` purely in $\mathbb{Q}$. -/
theorem certified_evaluation_rational_tail (P : PolyODEProof) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1)) (k d : Nat) :
    |(Jet.evalPoly ⟨solFast P.sys P.v⟩
        (extractedJetCauchyModulusComputed (solFast P.sys P.v) (sysParams P.sys).1 x k + d) x).val
      - (GPACSys.approxFast P.sys P.v x k).val| < 1 / (2 : Rat) ^ k :=
  GPACSys.approxFast_spec P.sys P.wf P.v P.hv x hx k d

/-! ## Section 2: Theorem II (Part 1) — Compositional Calculus Adequacy (`UExpr` Bridge) -/

/-- Every defined analytic expression `e : UExpr` compiles into a canonical `PolyODEProof`
    via `UExpr.compile`. -/
def UExpr.toPolyODEProof (e : UExpr) (he : e.Defined) : PolyODEProof where
  sys := e.compile.sys
  wf := (e.compile_correct he).1
  v := e.compile.v
  hv := e.compile.hv

/-- Every defined analytic expression `e : UExpr` induces a `CertifiedAnalyticRep`. -/
def UExpr.toCertifiedAnalyticRep (e : UExpr) (he : e.Defined) : CertifiedAnalyticRep :=
  (e.toPolyODEProof he).toCertifiedAnalyticRep

/-- **Three-Way Coefficient Adequacy for `UExpr`**:
    For every defined expression `e : UExpr` and index $n \in \mathbb{N}$, its direct
    recursively evaluated Taylor coefficient `(e.eval n).val` agrees identically with:
    1. the coefficient extracted by `extractClosed` from `genSolveND` on `e.compile.sys`, and
    2. the coefficient computed by the bottom-up DP table `solFast e.compile.sys e.compile.v`. -/
theorem UExpr.eval_eq_extracted_and_fast (e : UExpr) (he : e.Defined) (n : Nat) :
    (e.eval n).val =
      extractedCoeff e.compile.sys (gpac_wf (e.compile_correct he).1) e.compile.v n ∧
    (e.eval n).val = (solFast e.compile.sys e.compile.v n).val := by
  have hcomp := (e.compile_correct he).2 n
  have hext := extractedCoeff_eq_solN e.compile.sys (gpac_wf (e.compile_correct he).1) e.compile.v n
  have hfast := solFast_val e.compile.sys (e.compile_correct he).1 e.compile.v e.compile.hv n
  exact ⟨hcomp.trans hext.symm, hcomp.trans hfast.symm⟩

/-- **Compositional Representation Compiler (`compile_T`) on `RadiusJet`**:
    Every calculus operation preserves `RadiusJet` (Taylor stream + majorant `(M, R)`)
    and satisfies exact Newton–Leibniz (FTC1 and FTC2) at every truncation degree. -/
theorem radiusJet_ftc_adequacy (F : RadiusJet) (N : Nat) (x : Q) :
    ((F.deriv.integ.toJet).evalPoly (N + 1) x).val =
      (F.toJet.evalPoly (N + 1) x).val - (F.toJet.coeff 0).val ∧
    ((F.integ.deriv.toJet).evalPoly N x).val = (F.toJet.evalPoly N x).val :=
  ⟨Jet.evalPoly_integ_deriv_val F.toJet N x, Jet.evalPoly_deriv_integ_val F.toJet N x⟩

/-! ## Section 3: Theorem II (Part 2) — Validated Root Location via Derivative Remainder Margin

We prove the corrected root-location and secant-inversion theorems for jets:
1. First, for any jet `F : Jet` and degree `M`, if the degree-`M` derivative polynomial
   $S_M(F')(y) \ge m$ across $[a, b]$, then the degree-$(M+1)$ polynomial $S_{M+1}(F)$ satisfies
   $$m \cdot |x.\mathrm{val} - z.\mathrm{val}|
     \le |(F.\mathrm{evalPoly}\;(M+1)\;x).\mathrm{val} - (F.\mathrm{evalPoly}\;(M+1)\;z).\mathrm{val}|.$$
2. Second, for `F : RadiusJet`, if at truncation degree $N \ge F.\mathrm{deriv}.M + 3$, the
   truncated derivative polynomial exceeds the certified derivative remainder bound:
   $$(F.\mathrm{deriv}.\mathrm{toJet}.\mathrm{evalPoly}\;N\;y).\mathrm{val} -
     \frac{1}{2^{N - (F.\mathrm{deriv}.M + 3)}} \ge m > 0 \quad \forall y \in [a, b],$$
   then **every later partial sum** $S_{N+d}(F')(y)$ satisfies $S_{N+d}(F')(y) \ge m > 0$ on $[a, b]$,
   and hence for all $d \in \mathbb{N}$ and all $x, z \in [a, b]$:
   $$|x.\mathrm{val} - z.\mathrm{val}|
     \le \frac{|(F.\mathrm{toJet}.\mathrm{evalPoly}\;(N + d + 1)\;x).\mathrm{val} -
               (F.\mathrm{toJet}.\mathrm{evalPoly}\;(N + d + 1)\;z).\mathrm{val}|}{m}.$$
-/

/-- Quadratic remainder bound constant for `S_{M+1}(F)` on `|z| ≤ R`, generalized to any `F : Jet`. -/
def jetQuadBound (F : Jet) : Nat → Rat → Rat
  | 0, _ => 0
  | M + 1, R => jetQuadBound F M R + |(F.coeff (M + 1)).val| * ((M + 1 : Nat) : Rat) ^ 2 * R ^ M

theorem jetQuadBound_nonneg (F : Jet) : ∀ (M : Nat) (R : Rat), 0 ≤ R → 0 ≤ jetQuadBound F M R
  | 0, _, _ => le_refl 0
  | M + 1, R, hR => by
    dsimp [jetQuadBound]
    have ih := jetQuadBound_nonneg F M R hR
    have hterm : 0 ≤ |(F.coeff (M + 1)).val| * ((M + 1 : Nat) : Rat) ^ 2 * R ^ M := by positivity
    linarith

/-- First-order Taylor remainder between `F.evalPoly (M + 1)` and `F.deriv.evalPoly M` on `|z|, |w| ≤ R` (`1 ≤ R`). -/
theorem jet_evalPoly_quad_rem (F : Jet) : ∀ (M : Nat) (R : Rat), 1 ≤ R →
    ∀ (z w : Q), |z.val| ≤ R → |w.val| ≤ R →
      |(F.evalPoly (M + 1) w).val - (F.evalPoly (M + 1) z).val
        - (F.deriv.evalPoly M z).val * (w.val - z.val)|
        ≤ jetQuadBound F M R * (w.val - z.val) ^ 2
  | 0, R, _, z, w, _, _ => by
    rw [Jet.evalPoly_one, Jet.evalPoly_one, Jet.evalPoly_zero]
    dsimp [jetQuadBound]
    simp
  | M + 1, R, hR, z, w, hz, hw => by
    have ih := jet_evalPoly_quad_rem F M R hR z w hz hw
    have hderiv_coeff : (F.deriv.coeff M).val = ((M + 1 : Nat) : Rat) * (F.coeff (M + 1)).val := by
      dsimp [Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat]
    have hsplit : (F.evalPoly (M + 2) w).val - (F.evalPoly (M + 2) z).val
        - (F.deriv.evalPoly (M + 1) z).val * (w.val - z.val)
        = ((F.evalPoly (M + 1) w).val - (F.evalPoly (M + 1) z).val
            - (F.deriv.evalPoly M z).val * (w.val - z.val))
          + (F.coeff (M + 1)).val *
            (w.val ^ (M + 1) - z.val ^ (M + 1) - ((M + 1 : Nat) : Rat) * (w.val - z.val) * z.val ^ M) := by
      rw [Jet.evalPoly_succ F (M + 1) w, Jet.evalPoly_succ F (M + 1) z,
          Jet.evalPoly_succ F.deriv M z, hderiv_coeff]
      ring
    rw [hsplit]
    have htri := abs_add_le'
      ((F.evalPoly (M + 1) w).val - (F.evalPoly (M + 1) z).val
        - (F.deriv.evalPoly M z).val * (w.val - z.val))
      ((F.coeff (M + 1)).val *
        (w.val ^ (M + 1) - z.val ^ (M + 1) - ((M + 1 : Nat) : Rat) * (w.val - z.val) * z.val ^ M))
    rw [abs_mul] at htri
    have hpow := nwt_pow_lin_rem_bound R hR z.val w.val hz hw M
    have hmul : |(F.coeff (M + 1)).val| *
        |w.val ^ (M + 1) - z.val ^ (M + 1) - ((M + 1 : Nat) : Rat) * (w.val - z.val) * z.val ^ M|
        ≤ |(F.coeff (M + 1)).val| * (((M + 1 : Nat) : Rat) ^ 2 * R ^ M * (w.val - z.val) ^ 2) :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    dsimp [jetQuadBound]
    linarith

/-- Grid points `nwtGridPt x z n k` lie in `[a, b]` and satisfy `|pt| ≤ |a| + |b| + 1` when `x, z ∈ [a, b]` with `x ≤ z`. -/
theorem nwtGridPt_mem_interval (a b x z : Q)
    (hxa : a.val ≤ x.val) (_hxb : x.val ≤ b.val)
    (_hza : a.val ≤ z.val) (hzb : z.val ≤ b.val)
    (hxz : x.val ≤ z.val) (n k : Nat) (hn : 0 < n) (hk : k ≤ n) :
    a.val ≤ (nwtGridPt x z n k).val ∧
    (nwtGridPt x z n k).val ≤ b.val ∧
    |(nwtGridPt x z n k).val| ≤ |a.val| + |b.val| + 1 := by
  have hnR : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  have hkR : (k : Rat) ≤ (n : Rat) := by exact_mod_cast hk
  set t : Rat := (k : Rat) / (n : Rat)
  have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg k) (le_of_lt hnR)
  have ht1 : t ≤ 1 := (div_le_one hnR).mpr hkR
  have hval : (nwtGridPt x z n k).val = x.val + t * (z.val - x.val) := by
    rw [nwtGridPt_val]; dsimp [t]; ring
  have hge_x : x.val ≤ (nwtGridPt x z n k).val := by
    rw [hval]
    have : 0 ≤ t * (z.val - x.val) := mul_nonneg ht0 (by linarith)
    linarith
  have hle_z : (nwtGridPt x z n k).val ≤ z.val := by
    rw [hval]
    have : t * (z.val - x.val) ≤ 1 * (z.val - x.val) :=
      mul_le_mul_of_nonneg_right ht1 (by linarith)
    linarith
  have ha_le : a.val ≤ (nwtGridPt x z n k).val := le_trans hxa hge_x
  have hb_ge : (nwtGridPt x z n k).val ≤ b.val := le_trans hle_z hzb
  have hrad : |(nwtGridPt x z n k).val| ≤ |a.val| + |b.val| + 1 := by
    rw [abs_le]
    have ha_abs : -|a.val| ≤ a.val := neg_abs_le a.val
    have hb_abs : b.val ≤ |b.val| := le_abs_self b.val
    have h0a : (0 : Rat) ≤ |a.val| := abs_nonneg _
    have h0b : (0 : Rat) ≤ |b.val| := abs_nonneg _
    constructor <;> linarith
  exact ⟨ha_le, hb_ge, hrad⟩

/-- **Ordered Polynomial Secant Lower Bound**:
    If `(F.deriv.evalPoly M y).val ≥ m` for all `y ∈ [a, b]`, then for all `x, z ∈ [a, b]`
    with `x.val ≤ z.val`,
    $$m \cdot (z.\mathrm{val} - x.\mathrm{val})
      \le (F.\mathrm{evalPoly}\;(M + 1)\;z).\mathrm{val} - (F.\mathrm{evalPoly}\;(M + 1)\;x).\mathrm{val}.$$ -/
theorem jet_evalPoly_secant_ordered (F : Jet) (M : Nat) (a b : Q) (m : Rat)
    (hd : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val → m ≤ (F.deriv.evalPoly M y).val)
    (x z : Q) (hxa : a.val ≤ x.val) (hxb : x.val ≤ b.val)
    (hza : a.val ≤ z.val) (hzb : z.val ≤ b.val) (hxz : x.val ≤ z.val) :
    m * (z.val - x.val) ≤ (F.evalPoly (M + 1) z).val - (F.evalPoly (M + 1) x).val := by
  let R : Rat := |a.val| + |b.val| + 1
  have hR1 : 1 ≤ R := by
    dsimp [R]
    have : (0 : Rat) ≤ |a.val| + |b.val| := by positivity
    linarith
  have hR0 : 0 ≤ R := by linarith
  let C : Rat := jetQuadBound F M R
  have hC : 0 ≤ C := jetQuadBound_nonneg F M R hR0
  refine nwt_le_of_forall_pos_div _ _ (C * (z.val - x.val) ^ 2) (by positivity) (fun n hn ↦ ?_)
  have hnR : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  set h : Rat := (z.val - x.val) / (n : Rat)
  have hh_nonneg : 0 ≤ h := div_nonneg (by linarith) (le_of_lt hnR)
  let pt : Nat → Q := nwtGridPt x z n
  let P : Q → Rat := fun p ↦ (F.evalPoly (M + 1) p).val
  let P' : Q → Rat := fun p ↦ (F.deriv.evalPoly M p).val
  have hstep : ∀ k ∈ Finset.range n,
      m * h - C * h ^ 2 ≤ P (pt (k + 1)) - P (pt k) := by
    intro k hk
    have hkl : k < n := Finset.mem_range.mp hk
    have hpk := nwtGridPt_mem_interval a b x z hxa hxb hza hzb hxz n k hn (le_of_lt hkl)
    have hpk1 := nwtGridPt_mem_interval a b x z hxa hxb hza hzb hxz n (k + 1) hn hkl
    have hrem := jet_evalPoly_quad_rem F M R hR1 (pt k) (pt (k + 1)) hpk.2.2 hpk1.2.2
    have hstep_val : (pt (k + 1)).val - (pt k).val = h := nwtGridPt_step x z n k
    rw [hstep_val] at hrem
    have hlow := (abs_le.mp hrem).1
    have hd_k : m ≤ P' (pt k) := hd (pt k) hpk.1 hpk.2.1
    have hmh : m * h ≤ P' (pt k) * h := mul_le_mul_of_nonneg_right hd_k hh_nonneg
    linarith
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_range_sub (fun k ↦ P (pt k)) n] at hsum
  have hpt0 : P (pt 0) = P x :=
    nwt_evalPoly_val_congr F (M + 1) (by rw [nwtGridPt_val]; push_cast; ring)
  have hptn : P (pt n) = P z :=
    nwt_evalPoly_val_congr F (M + 1) (by
      rw [nwtGridPt_val, mul_div_cancel₀ _ (ne_of_gt hnR)]; ring)
  rw [hpt0, hptn] at hsum
  have hlhs : (n : Rat) * (m * h - C * h ^ 2) =
      m * (z.val - x.val) - C * (z.val - x.val) ^ 2 / (n : Rat) := by
    dsimp [h]
    field_simp
  linarith

/-- **Symmetric Polynomial Secant Lower Bound**:
    If `(F.deriv.evalPoly M y).val ≥ m` for all `y ∈ [a, b]` with `0 ≤ m`, then for all
    `x, z ∈ [a, b]`,
    $$m \cdot |x.\mathrm{val} - z.\mathrm{val}|
      \le |(F.\mathrm{evalPoly}\;(M + 1)\;x).\mathrm{val} - (F.\mathrm{evalPoly}\;(M + 1)\;z).\mathrm{val}|.$$ -/
theorem jet_evalPoly_secant_lower_bound (F : Jet) (M : Nat) (a b : Q) (m : Rat)
    (hd : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val → m ≤ (F.deriv.evalPoly M y).val)
    (x z : Q) (hxa : a.val ≤ x.val) (hxb : x.val ≤ b.val)
    (hza : a.val ≤ z.val) (hzb : z.val ≤ b.val) :
    m * |x.val - z.val| ≤ |(F.evalPoly (M + 1) x).val - (F.evalPoly (M + 1) z).val| := by
  rcases le_total x.val z.val with hxz | hzx
  · have h := jet_evalPoly_secant_ordered F M a b m hd x z hxa hxb hza hzb hxz
    have habs1 : |x.val - z.val| = z.val - x.val := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have habs2 : (F.evalPoly (M + 1) z).val - (F.evalPoly (M + 1) x).val ≤
        |(F.evalPoly (M + 1) x).val - (F.evalPoly (M + 1) z).val| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    rw [habs1]
    linarith
  · have h := jet_evalPoly_secant_ordered F M a b m hd z x hza hzb hxa hxb hzx
    have habs1 : |x.val - z.val| = x.val - z.val := abs_of_nonneg (by linarith)
    have habs2 : (F.evalPoly (M + 1) x).val - (F.evalPoly (M + 1) z).val ≤
        |(F.evalPoly (M + 1) x).val - (F.evalPoly (M + 1) z).val| := le_abs_self _
    rw [habs1]
    linarith

/-- **Corrected Derivative Remainder Margin Persistence (`deriv_margin_persists`)**:
    For `F : RadiusJet`, let $N_k = k + (F.\mathrm{deriv}.M + 3)$ be the Cauchy modulus of `F.deriv`
    at precision $k$. By `F.deriv.cauchyComputed_correct`, the truncation tail of `F.deriv` on
    $|y| \le 2^{-(F.R + 2)} = 2^{-(F.\mathrm{deriv}.R + 1)}$ is strictly bounded by $2^{-k}$.
    Therefore, if on $[a, b] \subseteq [-2^{-(F.R+2)}, 2^{-(F.R+2)}]$ the truncated derivative
    at $N_k$ satisfies the **remainder-guarded lower bound**:
    $$(F.\mathrm{deriv}.\mathrm{toJet}.\mathrm{evalPoly}\;N_k\;y).\mathrm{val} - \frac{1}{2^k} \ge m,$$
    then **every later partial sum** $S_{N_k + d}(F')(y)$ ($d \in \mathbb{N}$) satisfies:
    $$(F.\mathrm{deriv}.\mathrm{toJet}.\mathrm{evalPoly}\;(N_k + d)\;y).\mathrm{val} \ge m.$$ -/
theorem RadiusJet.deriv_margin_persists (F : RadiusJet) (a b : Q) (k : Nat) (m : Rat)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ (F.R + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ (F.R + 2))
    (hmargin : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val →
      m ≤ (F.deriv.toJet.evalPoly (k + (F.deriv.M + 3)) y).val - 1 / (2 : Rat) ^ k)
    (d : Nat) (y : Q) (hya : a.val ≤ y.val) (hyb : y.val ≤ b.val) :
    m ≤ (F.deriv.toJet.evalPoly (k + (F.deriv.M + 3) + d) y).val := by
  have hy_disk : |y.val| ≤ 1 / (2 : Rat) ^ (F.deriv.R + 1) := by
    change |y.val| ≤ 1 / (2 : Rat) ^ (F.R + 1 + 1)
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith [ha.1, hb.2]
  have hcauchy := F.deriv.cauchyComputed_correct y hy_disk k 0 d
  dsimp only at hcauchy
  rw [extractedJetCauchyModulusComputed_eq, Nat.add_zero] at hcauchy
  have hlow := (abs_lt.mp hcauchy).2
  have hm := hmargin y hya hyb
  linarith

/-- **Validated Root-Location Theorem under Derivative Remainder Margin (`location_error_of_deriv_margin`)**:
    Under the remainder-guarded derivative margin
    $$(F.\mathrm{deriv}.\mathrm{toJet}.\mathrm{evalPoly}\;N_k\;y).\mathrm{val} - 2^{-k} \ge m > 0$$
    on $[a, b] \subseteq [-2^{-(F.R+2)}, 2^{-(F.R+2)}]$, where $N_k = k + (F.\mathrm{deriv}.M + 3)$,
    every later partial sum $S_{N_k + d + 1}(F)$ ($d \in \mathbb{N}$) satisfies the true location bound:
    $$|x.\mathrm{val} - z.\mathrm{val}|
      \le \frac{|(F.\mathrm{toJet}.\mathrm{evalPoly}\;(N_k + d + 1)\;x).\mathrm{val} -
                (F.\mathrm{toJet}.\mathrm{evalPoly}\;(N_k + d + 1)\;z).\mathrm{val}|}{m}$$
    for all $x, z \in [a, b]$. -/
theorem RadiusJet.location_error_of_deriv_margin (F : RadiusJet) (a b : Q) (k : Nat) (m : Rat)
    (hm : 0 < m)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ (F.R + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ (F.R + 2))
    (hmargin : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val →
      m ≤ (F.deriv.toJet.evalPoly (k + (F.deriv.M + 3)) y).val - 1 / (2 : Rat) ^ k)
    (d : Nat) (x z : Q) (hxa : a.val ≤ x.val) (hxb : x.val ≤ b.val)
    (hza : a.val ≤ z.val) (hzb : z.val ≤ b.val) :
    |x.val - z.val| ≤
      |(F.toJet.evalPoly (k + (F.deriv.M + 3) + d + 1) x).val -
       (F.toJet.evalPoly (k + (F.deriv.M + 3) + d + 1) z).val| / m := by
  have hd_persists : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val →
      m ≤ (F.toJet.deriv.evalPoly (k + (F.deriv.M + 3) + d) y).val :=
    fun y hya hyb ↦ F.deriv_margin_persists a b k m ha hb hmargin d y hya hyb
  have hsec := jet_evalPoly_secant_lower_bound F.toJet (k + (F.deriv.M + 3) + d) a b m
    hd_persists x z hxa hxb hza hzb
  exact (le_div_iff₀ hm).mpr (by linarith)

/-! ### Decisive Theorem IIA: Infinite-Series Limit Secant & True Root-Location Adequacy in `ℝ`

Passing `location_error_of_deriv_margin` to the $d \to \infty$ limit via
`analyticValue_sub_evalPoly_le` connects the **finite rational derivative check**
on $S_{N_k}(F')$ directly to the **infinite real power series** $S.\operatorname{analyticValue}(x) \in \mathbb{R}$. -/

/-- Elementary dominance `(d : ℝ) ≤ (2 : ℝ) ^ d`. -/
theorem real_nat_le_two_pow : ∀ d : Nat, (d : ℝ) ≤ (2 : ℝ) ^ d
  | 0 => by norm_num
  | d + 1 => by
    have ih := real_nat_le_two_pow d
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    push_cast
    linarith

/-- Archimedean elimination of `C / 2^d` across all `d : Nat` in `ℝ`. -/
theorem real_le_of_forall_sub_pow2_le (A B C : ℝ) (_hC : 0 ≤ C)
    (h : ∀ d : Nat, A ≤ B + C / (2 : ℝ) ^ d) : A ≤ B := by
  by_contra hlt
  push_neg at hlt
  have hAB : 0 < A - B := sub_pos.mpr hlt
  obtain ⟨d, hd⟩ := exists_nat_gt (C / (A - B))
  have hd_pow : (d : ℝ) ≤ (2 : ℝ) ^ d := real_nat_le_two_pow d
  have h2d_gt : C / (A - B) < (2 : ℝ) ^ d := lt_of_lt_of_le hd hd_pow
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have h1 := h d
  have h2 : C < (2 : ℝ) ^ d * (A - B) := (div_lt_iff₀ hAB).mp h2d_gt
  have h3 : C / (2 : ℝ) ^ d < A - B := (div_lt_iff₀ h2d_pos).mpr (by linarith)
  linarith

/-- For `P : PolyODEProof`, evaluating `solN P.sys P.v` up to degree `N` has the same
    rational value as evaluating `solFast P.sys P.v` up to degree `N`. -/
theorem PolyODEProof.evalPoly_solN_eq_solFast (P : PolyODEProof) (N : Nat) (x : Q) :
    ((Jet.mk (solN P.sys P.v)).evalPoly N x).val =
      ((Jet.mk (solFast P.sys P.v)).evalPoly N x).val := by
  rw [jet_evalPoly_val_eq_sum, jet_evalPoly_val_eq_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [solFast_val P.sys P.wf P.v P.hv n]

/-- **Theorem IIA.1 (Infinite-Series Secant Lower Bound from Finite Rational Derivative Margin)**:
    Let `P : PolyODEProof`, `S := P.toCertifiedAnalyticRep`, and
    `F := GPACSys.radiusJet P.sys P.wf P.v P.hv`.
    If on $[a, b] \subseteq [-2^{-(S.R+2)}, 2^{-(S.R+2)}]$, the finite rational derivative
    polynomial at degree $N_k = k + (F.\mathrm{deriv}.M + 3)$ satisfies
    $$(F.\mathrm{deriv}.\mathrm{toJet}.\mathrm{evalPoly}\;N_k\;y).\mathrm{val} - \frac{1}{2^k} \ge m$$
    for all $y \in [a, b]$, then the **true infinite real power series**
    $S.\operatorname{analyticValue} : Q \to \mathbb{R}$ satisfies the global secant bound:
    $$(m : \mathbb{R}) \cdot |(x.\mathrm{val} : \mathbb{R}) - (z.\mathrm{val} : \mathbb{R})|
      \le \big|S.\operatorname{analyticValue}(x) - S.\operatorname{analyticValue}(z)\big|$$
    for all $x, z \in [a, b]$. -/
theorem PolyODEProof.analyticValue_secant_of_deriv_margin (P : PolyODEProof)
    (a b : Q) (k : Nat) (m : Rat)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hmargin : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val →
      m ≤ ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.toJet.evalPoly
            (k + ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.M + 3)) y).val
          - 1 / (2 : Rat) ^ k)
    (x z : Q) (hxa : a.val ≤ x.val) (hxb : x.val ≤ b.val)
    (hza : a.val ≤ z.val) (hzb : z.val ≤ b.val) :
    (m : ℝ) * |(x.val : ℝ) - (z.val : ℝ)| ≤
      |P.toCertifiedAnalyticRep.analyticValue x - P.toCertifiedAnalyticRep.analyticValue z| := by
  let S := P.toCertifiedAnalyticRep
  let F := GPACSys.radiusJet P.sys P.wf P.v P.hv
  have hSR : S.R = (sysParams P.sys).2 := rfl
  have hx_disk : |x.val| ≤ 1 / (2 : Rat) ^ (S.R + 1) := by
    have hx2 : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2) := by
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [ha.1, hb.2]
    exact le_trans hx2 (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hz_disk : |z.val| ≤ 1 / (2 : Rat) ^ (S.R + 1) := by
    have hz2 : |z.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2) := by
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [ha.1, hb.2]
    exact le_trans hz2 (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  set N₀ := k + (F.deriv.M + 3) + 1
  let C : ℝ := 2 * (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ N₀
  have hC : 0 ≤ C := by positivity
  refine real_le_of_forall_sub_pow2_le _ _ C hC (fun d ↦ ?_)
  have hd_persists : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val →
      m ≤ (F.toJet.deriv.evalPoly (k + (F.deriv.M + 3) + d) y).val :=
    fun y hya hyb ↦ F.deriv_margin_persists a b k m ha hb hmargin d y hya hyb
  have hsec_rat := jet_evalPoly_secant_lower_bound F.toJet (k + (F.deriv.M + 3) + d) a b m
    hd_persists x z hxa hxb hza hzb
  have hN_eq : k + (F.deriv.M + 3) + d + 1 = N₀ + d := by omega
  rw [hN_eq] at hsec_rat
  have hsec_real : (m : ℝ) * |(x.val : ℝ) - (z.val : ℝ)| ≤
      |(((F.toJet.evalPoly (N₀ + d) x).val : ℝ) - ((F.toJet.evalPoly (N₀ + d) z).val : ℝ))| := by
    have hcast : ((m * |x.val - z.val| : Rat) : ℝ) ≤
        ((|(F.toJet.evalPoly (N₀ + d) x).val - (F.toJet.evalPoly (N₀ + d) z).val| : Rat) : ℝ) := by
      exact_mod_cast hsec_rat
    simpa only [Rat.cast_mul, Rat.cast_abs, Rat.cast_sub] using hcast
  have hx_eq : (F.toJet.evalPoly (N₀ + d) x).val =
      ((Jet.mk (solFast P.sys P.v)).evalPoly (N₀ + d) x).val :=
    P.evalPoly_solN_eq_solFast (N₀ + d) x
  have hz_eq : (F.toJet.evalPoly (N₀ + d) z).val =
      ((Jet.mk (solFast P.sys P.v)).evalPoly (N₀ + d) z).val :=
    P.evalPoly_solN_eq_solFast (N₀ + d) z
  rw [hx_eq, hz_eq] at hsec_real
  set Px : ℝ := (((Jet.mk (solFast P.sys P.v)).evalPoly (N₀ + d) x).val : ℝ)
  set Pz : ℝ := (((Jet.mk (solFast P.sys P.v)).evalPoly (N₀ + d) z).val : ℝ)
  set fx : ℝ := S.analyticValue x
  set fz : ℝ := S.analyticValue z
  have hsec_real' : (m : ℝ) * |(x.val : ℝ) - (z.val : ℝ)| ≤ |Px - Pz| := hsec_real
  have hrem_x : |Px - fx| ≤ (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ (N₀ + d) :=
    S.analyticValue_sub_evalPoly_le x hx_disk (N₀ + d)
  have hrem_z : |Pz - fz| ≤ (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ (N₀ + d) :=
    S.analyticValue_sub_evalPoly_le z hz_disk (N₀ + d)
  have htri1 : |Px - Pz| = |(Px - fx) + ((fx - fz) + (fz - Pz))| := by
    congr 1; ring
  have htri2 := abs_add_le (Px - fx) ((fx - fz) + (fz - Pz))
  have htri3 := abs_add_le (fx - fz) (fz - Pz)
  have hrem_z' : |fz - Pz| ≤ (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ (N₀ + d) := by
    rw [abs_sub_comm]; exact hrem_z
  have hpow_split : 2 * ((2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ (N₀ + d)) = C / (2 : ℝ) ^ d := by
    dsimp [C]
    rw [pow_add (2 : ℝ) N₀ d]
    ring
  linarith

/-- **Theorem IIA.2 (True Infinite-Series Root-Location & Uniqueness Theorem)**:
    Under the finite rational derivative margin of `analyticValue_secant_of_deriv_margin`,
    if $z \in [a, b]$ is a zero of the true analytic function ($S.\operatorname{analyticValue}(z) = 0$),
    then for every point $x \in [a, b]$ and every evaluation precision $j \in \mathbb{N}$:
    $$\big|(x.\mathrm{val} : \mathbb{R}) - (z.\mathrm{val} : \mathbb{R})\big|
      \le \frac{|S.\operatorname{analyticValue}(x)|}{(m : \mathbb{R})}
      \le \frac{|((\operatorname{GPACSys.approxFast}\;P.\mathrm{sys}\;P.v\;x\;j).\mathrm{val} : \mathbb{R})| + 1 / (2 : \mathbb{R})^j}{(m : \mathbb{R})}.$$ -/
theorem PolyODEProof.analyticValue_root_location_of_deriv_margin (P : PolyODEProof)
    (a b : Q) (k : Nat) (m : Rat) (hm : 0 < m)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hmargin : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val →
      m ≤ ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.toJet.evalPoly
            (k + ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.M + 3)) y).val
          - 1 / (2 : Rat) ^ k)
    (x z : Q) (hxa : a.val ≤ x.val) (hxb : x.val ≤ b.val)
    (hza : a.val ≤ z.val) (hzb : z.val ≤ b.val)
    (hroot : P.toCertifiedAnalyticRep.analyticValue z = 0) (j : Nat) :
    |(x.val : ℝ) - (z.val : ℝ)| ≤
      |P.toCertifiedAnalyticRep.analyticValue x| / (m : ℝ) ∧
    |(x.val : ℝ) - (z.val : ℝ)| ≤
      (|((GPACSys.approxFast P.sys P.v x j).val : ℝ)| + 1 / (2 : ℝ) ^ j) / (m : ℝ) := by
  have hm_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsec := P.analyticValue_secant_of_deriv_margin a b k m ha hb hmargin x z hxa hxb hza hzb
  rw [hroot, sub_zero] at hsec
  have h1 : |(x.val : ℝ) - (z.val : ℝ)| ≤
      |P.toCertifiedAnalyticRep.analyticValue x| / (m : ℝ) :=
    (le_div_iff₀ hm_real).mpr (by linarith)
  refine ⟨h1, le_trans h1 ?_⟩
  have hx_disk : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1) := by
    have hx2 : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2) := by
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [ha.1, hb.2]
    exact le_trans hx2 (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  set A : ℝ := ((GPACSys.approxFast P.sys P.v x j).val : ℝ)
  set F : ℝ := P.toCertifiedAnalyticRep.analyticValue x
  have hcert : |A - F| ≤ 1 / (2 : ℝ) ^ j := certified_evaluation P x j hx_disk
  have htri : |F| ≤ |A| + |A - F| := by
    have hsub := abs_add_le A (F - A)
    rw [add_sub_cancel, abs_sub_comm F A] at hsub
    exact hsub
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hm_real)

/-- **Infinite-Series Lipschitz Theorem on the Quarter-Radius Disk (`analyticValue_lipschitz_disk`)**:
    For `P : PolyODEProof` and any $x, y$ in the quarter-radius disk
    $|x.\mathrm{val}|, |y.\mathrm{val}| \le 2^{-(R+2)}$ where $(M, R) = \operatorname{sysParams}(P.\mathrm{sys})$,
    the true infinite power series satisfies:
    $$\big|P.\operatorname{toCertifiedAnalyticRep}.\operatorname{analyticValue}(x) -
          P.\operatorname{toCertifiedAnalyticRep}.\operatorname{analyticValue}(y)\big|
      \le 2^{M + R + 2} \cdot \big|(x.\mathrm{val} : \mathbb{R}) - (y.\mathrm{val} : \mathbb{R})\big|.$$ -/
theorem PolyODEProof.analyticValue_lipschitz_disk (P : PolyODEProof) (x y : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hy : |y.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2)) :
    |P.toCertifiedAnalyticRep.analyticValue x - P.toCertifiedAnalyticRep.analyticValue y| ≤
      (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) *
        |(x.val : ℝ) - (y.val : ℝ)| := by
  let S := P.toCertifiedAnalyticRep
  let F := GPACSys.radiusJet P.sys P.wf P.v P.hv
  have hSR : S.R = (sysParams P.sys).2 := rfl
  have hFR : F.R = (sysParams P.sys).2 := rfl
  have hFM : F.M = (sysParams P.sys).1 := rfl
  have hx_disk : |x.val| ≤ 1 / (2 : Rat) ^ (S.R + 1) :=
    le_trans hx (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hy_disk : |y.val| ≤ 1 / (2 : Rat) ^ (S.R + 1) :=
    le_trans hy (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  let C : ℝ := 2 * (2 : ℝ) ^ (S.M + 1)
  refine real_le_of_forall_sub_pow2_le _ _ C (by positivity) (fun d ↦ ?_)
  let r : Q := D.toQ (D.pow2neg (F.R + 2))
  have hr : |r.val| = 1 / (2 : Rat) ^ (F.R + 2) := by
    dsimp [r]; rw [toQ_pow2neg_val, abs_of_pos (by positivity)]
  have hlip_rat := F.evalPoly_lip_disk r x y (by rw [hr])
    (by rw [hr, hFR]; exact hx) (by rw [hr, hFR]; exact hy) d
  have hDM : F.deriv.M + 1 = (sysParams P.sys).1 + (sysParams P.sys).2 + 2 := by
    show F.M + F.R + 1 + 1 = _
    rw [hFM, hFR]
  rw [hDM] at hlip_rat
  have hlip_real :
      |(((F.toJet.evalPoly d x).val : ℝ) - ((F.toJet.evalPoly d y).val : ℝ))| ≤
        (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) *
          |(x.val : ℝ) - (y.val : ℝ)| := by
    have hcast :
        ((|(F.toJet.evalPoly d x).val - (F.toJet.evalPoly d y).val| : Rat) : ℝ) ≤
          (((2 : Rat) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) * |x.val - y.val| : Rat) : ℝ) := by
      exact_mod_cast hlip_rat
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using hcast
  have hx_eq : (F.toJet.evalPoly d x).val =
      ((Jet.mk (solFast P.sys P.v)).evalPoly d x).val :=
    P.evalPoly_solN_eq_solFast d x
  have hy_eq : (F.toJet.evalPoly d y).val =
      ((Jet.mk (solFast P.sys P.v)).evalPoly d y).val :=
    P.evalPoly_solN_eq_solFast d y
  rw [hx_eq, hy_eq] at hlip_real
  set Px : ℝ := (((Jet.mk (solFast P.sys P.v)).evalPoly d x).val : ℝ)
  set Py : ℝ := (((Jet.mk (solFast P.sys P.v)).evalPoly d y).val : ℝ)
  set fx : ℝ := S.analyticValue x
  set fy : ℝ := S.analyticValue y
  have hlip_real' : |Px - Py| ≤
      (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) * |(x.val : ℝ) - (y.val : ℝ)| :=
    hlip_real
  have hrem_x : |Px - fx| ≤ (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ d :=
    S.analyticValue_sub_evalPoly_le x hx_disk d
  have hrem_y : |Py - fy| ≤ (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ d :=
    S.analyticValue_sub_evalPoly_le y hy_disk d
  have hrem_x' : |fx - Px| ≤ (2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ d := by
    rw [abs_sub_comm]; exact hrem_x
  have htri1 : |fx - fy| = |(fx - Px) + ((Px - Py) + (Py - fy))| := by congr 1; ring
  have htri2 := abs_add_le (fx - Px) ((Px - Py) + (Py - fy))
  have htri3 := abs_add_le (Px - Py) (Py - fy)
  have hC_div : 2 * ((2 : ℝ) ^ (S.M + 1) / (2 : ℝ) ^ d) = C / (2 : ℝ) ^ d := by
    dsimp [C]; ring
  change |fx - fy| ≤
    (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) * |(x.val : ℝ) - (y.val : ℝ)| +
      C / (2 : ℝ) ^ d
  linarith

/-- Sign coloring of `GPACSys.approxFast` on the binary grid `rootGrid a b j k` at precision `2^{-p}`. -/
def PolyODEProof.rootColor (P : PolyODEProof) (a b : Q) (j p : Nat) (k : Nat) : Nat :=
  Q.ltN (GPACSys.approxFast P.sys P.v (rootGrid a b j k) p) (Q.ofNat 0)

/-- Proof-extracted bisection grid index for `P : PolyODEProof`. -/
def PolyODEProof.rootIndex (P : PolyODEProof) (a b : Q) (j p : Nat) : Nat :=
  bisect j (P.rootColor a b j p) 0

/-- **Constructive Fast Bisection Root Operator (`PolyODEProof.rootFast`)**:
    Composes the proof-extracted binary search `bisect` (`Bisection.lean`) with
    the fast DP evaluator `GPACSys.approxFast` on the grid `rootGrid a b j`. -/
def PolyODEProof.rootFast (P : PolyODEProof) (a b : Q) (j p : Nat) : Q :=
  rootGrid a b j (P.rootIndex a b j p)

/-- **Theorem IIA.3 (Constructive Infinite-Series Approximate IVT via Fast Bisection)**:
    If on $[a, b] \subseteq [-2^{-(R+2)}, 2^{-(R+2)}]$ ($a \le b$), the fast evaluator
    changes sign between the endpoints (`P.rootColor a b j p 0 ≠ P.rootColor a b j p (2 ^ j)`),
    then the constructed rational point $r = P.\operatorname{rootFast}\;a\;b\;j\;p$ lies in $[a, b]$
    and the **true infinite real power series** satisfies the residual bound:
    $$\big|P.\operatorname{toCertifiedAnalyticRep}.\operatorname{analyticValue}(r)\big|
      \le \frac{1}{2^p} + 2^{M + R + 2} \frac{b - a}{2^j}.$$ -/
theorem PolyODEProof.rootFast_analyticValue_spec (P : PolyODEProof) (a b : Q) (j p : Nat)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hab : a.val ≤ b.val)
    (hends : P.rootColor a b j p 0 ≠ P.rootColor a b j p (2 ^ j)) :
    a.val ≤ (P.rootFast a b j p).val ∧
    (P.rootFast a b j p).val ≤ b.val ∧
    |P.toCertifiedAnalyticRep.analyticValue (P.rootFast a b j p)| ≤
      1 / (2 : ℝ) ^ p +
        (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) *
          (((b.val : ℝ) - (a.val : ℝ)) / (2 : ℝ) ^ j) := by
  set c := P.rootColor a b j p with hcdef
  have hb0 : c 0 ≠ c (0 + 2 ^ j) := by rwa [Nat.zero_add]
  obtain ⟨hi, hci⟩ := bisect_spec j c 0 hb0
  set i := bisect j c 0 with hidef
  rw [Nat.zero_add] at hci
  have hroot : P.rootFast a b j p = rootGrid a b j i := rfl
  rw [hroot]
  set x := rootGrid a b j i with hxdef
  set y := rootGrid a b j (i + 1) with hydef
  have hxm := rootGrid_mem a b j i hab (le_of_lt hi)
  have hym := rootGrid_mem a b j (i + 1) hab hi
  refine ⟨hxm.1, hxm.2, ?_⟩
  have hdisk2 : ∀ z : Q, a.val ≤ z.val → z.val ≤ b.val →
      |z.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2) := by
    intro z h1 h2
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith [ha.1, hb.2]
  have hdisk1 : ∀ z : Q, |z.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2) →
      |z.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1) := by
    intro z hz
    exact le_trans hz (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hxd2 := hdisk2 x hxm.1 hxm.2
  have hyd2 := hdisk2 y hym.1 hym.2
  set Ax : ℝ := ((GPACSys.approxFast P.sys P.v x p).val : ℝ)
  set Ay : ℝ := ((GPACSys.approxFast P.sys P.v y p).val : ℝ)
  set fx : ℝ := P.toCertifiedAnalyticRep.analyticValue x
  set fy : ℝ := P.toCertifiedAnalyticRep.analyticValue y
  have hax : |Ax - fx| ≤ 1 / (2 : ℝ) ^ p := certified_evaluation P x p (hdisk1 x hxd2)
  have hay : |Ay - fy| ≤ 1 / (2 : ℝ) ^ p := certified_evaluation P y p (hdisk1 y hyd2)
  have hlip : |fx - fy| ≤
      (2 : ℝ) ^ ((sysParams P.sys).1 + (sysParams P.sys).2 + 2) *
        (((b.val : ℝ) - (a.val : ℝ)) / (2 : ℝ) ^ j) := by
    have hl := P.analyticValue_lipschitz_disk x y hxd2 hyd2
    have hstep_rat : |x.val - y.val| = (b.val - a.val) / (2 : Rat) ^ j := by
      have hs := rootGrid_step a b j i
      rw [abs_sub_comm, abs_of_nonneg (by
        rw [← hydef, ← hxdef] at hs; rw [hs]
        have : 0 ≤ b.val - a.val := by linarith
        positivity)]
      exact hs
    have hstep_real : |(x.val : ℝ) - (y.val : ℝ)| = ((b.val : ℝ) - (a.val : ℝ)) / (2 : ℝ) ^ j := by
      have hcast : ((|x.val - y.val| : Rat) : ℝ) = (((b.val - a.val) / (2 : Rat) ^ j : Rat) : ℝ) :=
        congrArg Rat.cast hstep_rat
      simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hcast
    rwa [hstep_real] at hl
  rw [abs_le] at hax hay hlip ⊢
  rcases Q.ltN_eq_zero_or_one (GPACSys.approxFast P.sys P.v x p) (Q.ofNat 0) with hx0 | hx1 <;>
  rcases Q.ltN_eq_zero_or_one (GPACSys.approxFast P.sys P.v y p) (Q.ofNat 0) with hy0 | hy1
  · exact absurd (hx0.trans hy0.symm) hci
  · rw [Q.ltN_eq_zero_iff, Q.val_ofNat_zero] at hx0
    rw [Q.ltN_eq_one_iff, Q.val_ofNat_zero] at hy1
    have hx0_r : (0 : ℝ) ≤ ((GPACSys.approxFast P.sys P.v x p).val : ℝ) := by exact_mod_cast hx0
    have hy1_r : ((GPACSys.approxFast P.sys P.v y p).val : ℝ) < (0 : ℝ) := by exact_mod_cast hy1
    have hx0_Ax : (0 : ℝ) ≤ Ax := hx0_r
    have hy1_Ay : Ay < (0 : ℝ) := hy1_r
    constructor <;> linarith
  · rw [Q.ltN_eq_one_iff, Q.val_ofNat_zero] at hx1
    rw [Q.ltN_eq_zero_iff, Q.val_ofNat_zero] at hy0
    have hx1_r : ((GPACSys.approxFast P.sys P.v x p).val : ℝ) < (0 : ℝ) := by exact_mod_cast hx1
    have hy0_r : (0 : ℝ) ≤ ((GPACSys.approxFast P.sys P.v y p).val : ℝ) := by exact_mod_cast hy0
    have hx1_Ax : Ax < (0 : ℝ) := hx1_r
    have hy0_Ay : (0 : ℝ) ≤ Ay := hy0_r
    constructor <;> linarith
  · exact absurd (hx1.trans hy1.symm) hci

/-- **Theorem IIA.4 (Constructive Cauchy Convergence of Bisection Root Approximations)**:
    Under the finite rational derivative margin of `analyticValue_secant_of_deriv_margin`,
    any two bisection root approximations $r_1 = P.\operatorname{rootFast}\;a\;b\;j_1\;p_1$ and
    $r_2 = P.\operatorname{rootFast}\;a\;b\;j_2\;p_2$ with verified endpoint sign changes satisfy
    the explicit mutual Cauchy distance bound:
    $$\big|(r_1.\mathrm{val} : \mathbb{R}) - (r_2.\mathrm{val} : \mathbb{R})\big|
      \le \frac{|S.\operatorname{analyticValue}(r_1)| + |S.\operatorname{analyticValue}(r_2)|}{(m : \mathbb{R})},$$
    without assuming an external real zero a priori. -/
theorem PolyODEProof.rootFast_cauchy_of_deriv_margin (P : PolyODEProof)
    (a b : Q) (k : Nat) (m : Rat) (hm : 0 < m)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 2))
    (hab : a.val ≤ b.val)
    (hmargin : ∀ y : Q, a.val ≤ y.val → y.val ≤ b.val →
      m ≤ ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.toJet.evalPoly
            (k + ((GPACSys.radiusJet P.sys P.wf P.v P.hv).deriv.M + 3)) y).val
          - 1 / (2 : Rat) ^ k)
    (j₁ p₁ j₂ p₂ : Nat)
    (hends₁ : P.rootColor a b j₁ p₁ 0 ≠ P.rootColor a b j₁ p₁ (2 ^ j₁))
    (hends₂ : P.rootColor a b j₂ p₂ 0 ≠ P.rootColor a b j₂ p₂ (2 ^ j₂)) :
    |((P.rootFast a b j₁ p₁).val : ℝ) - ((P.rootFast a b j₂ p₂).val : ℝ)| ≤
      (|P.toCertifiedAnalyticRep.analyticValue (P.rootFast a b j₁ p₁)| +
       |P.toCertifiedAnalyticRep.analyticValue (P.rootFast a b j₂ p₂)|) / (m : ℝ) := by
  have hm_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hr₁ := P.rootFast_analyticValue_spec a b j₁ p₁ ha hb hab hends₁
  have hr₂ := P.rootFast_analyticValue_spec a b j₂ p₂ ha hb hab hends₂
  set r₁ := P.rootFast a b j₁ p₁
  set r₂ := P.rootFast a b j₂ p₂
  have hsec := P.analyticValue_secant_of_deriv_margin a b k m ha hb hmargin
    r₁ r₂ hr₁.1 hr₁.2.1 hr₂.1 hr₂.2.1
  set f₁ : ℝ := P.toCertifiedAnalyticRep.analyticValue r₁
  set f₂ : ℝ := P.toCertifiedAnalyticRep.analyticValue r₂
  have htri : |f₁ - f₂| ≤ |f₁| + |f₂| := by
    simpa [sub_eq_add_neg] using abs_add_le f₁ (-f₂)
  exact (le_div_iff₀ hm_real).mpr (by linarith)

/-! ## Section 4: Decisive Theorem IIB — Representation-to-Representation Closure (`PolyODEProof` Transformers, True Definite Integral, and Local Inverse)

Every calculus operation—including local compositional inversion of autonomous 1D polynomial
ODEs—acts as an explicit representation-to-representation compiler:
$$\mathsf{PolyODEProof} \longrightarrow \mathsf{PolyODEProof}.$$ -/

/-- **Addition of `PolyODEProof` representations (`PolyODEProof.add`)**. -/
def PolyODEProof.add (P₁ P₂ : PolyODEProof) : PolyODEProof where
  sys := sumSys P₁.sys P₂.sys P₁.v P₂.v P₁.hv P₂.hv
  wf  := gpac_sumSys P₁.sys P₂.sys P₁.wf P₂.wf P₁.v P₂.v P₁.hv P₂.hv
  v   := P₁.sys.length + P₂.sys.length
  hv  := by rw [sumSys_length]; exact Nat.lt_succ_self _

/-- Coefficient soundness of `PolyODEProof.add`. -/
theorem PolyODEProof.add_coeff (P₁ P₂ : PolyODEProof) (n : Nat) :
    (P₁.add P₂).toCertifiedAnalyticRep.coeff n =
      P₁.toCertifiedAnalyticRep.coeff n + P₂.toCertifiedAnalyticRep.coeff n := by
  change (solN (sumSys P₁.sys P₂.sys P₁.v P₂.v P₁.hv P₂.hv) (P₁.sys.length + P₂.sys.length) n).val =
    (solN P₁.sys P₁.v n).val + (solN P₂.sys P₂.v n).val
  let S := sumSys P₁.sys P₂.sys P₁.v P₂.v P₁.hv P₂.hv
  have hgpacS := gpac_sumSys P₁.sys P₂.sys P₁.wf P₂.wf P₁.v P₂.v P₁.hv P₂.hv
  have hvS : P₁.sys.length + P₂.sys.length < S.length := by
    rw [sumSys_length]; exact Nat.lt_succ_self _
  have huniq := genSolveN_unique_val S (gpac_wf hgpacS) (sumTargetState P₁.sys P₂.sys P₁.v P₂.v)
    (sumTargetState_fixed P₁.sys P₂.sys (gpac_wf P₁.wf) (gpac_wf P₂.wf) P₁.v P₂.v P₁.hv P₂.hv)
    (n + 1) (P₁.sys.length + P₂.sys.length) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (solN S (P₁.sys.length + P₂.sys.length) n).val = _ at huniq
  rw [huniq]
  unfold sumTargetState
  rw [if_neg (by omega), if_neg (by omega), Q.val_add]

/-- **Subtraction of `PolyODEProof` representations (`PolyODEProof.sub`)**. -/
def PolyODEProof.sub (P₁ P₂ : PolyODEProof) : PolyODEProof where
  sys := subSys P₁.sys P₂.sys P₁.v P₂.v P₁.hv P₂.hv
  wf  := gpac_subSys P₁.sys P₂.sys P₁.wf P₂.wf P₁.v P₂.v P₁.hv P₂.hv
  v   := P₁.sys.length + P₂.sys.length
  hv  := by rw [uSub_subSys_length]; exact Nat.lt_succ_self _

/-- Coefficient soundness of `PolyODEProof.sub`. -/
theorem PolyODEProof.sub_coeff (P₁ P₂ : PolyODEProof) (n : Nat) :
    (P₁.sub P₂).toCertifiedAnalyticRep.coeff n =
      P₁.toCertifiedAnalyticRep.coeff n - P₂.toCertifiedAnalyticRep.coeff n := by
  change (solN (subSys P₁.sys P₂.sys P₁.v P₂.v P₁.hv P₂.hv) (P₁.sys.length + P₂.sys.length) n).val =
    (solN P₁.sys P₁.v n).val - (solN P₂.sys P₂.v n).val
  let S := subSys P₁.sys P₂.sys P₁.v P₂.v P₁.hv P₂.hv
  have hgpacS := gpac_subSys P₁.sys P₂.sys P₁.wf P₂.wf P₁.v P₂.v P₁.hv P₂.hv
  have hvS : P₁.sys.length + P₂.sys.length < S.length := by
    rw [uSub_subSys_length]; exact Nat.lt_succ_self _
  have huniq := genSolveN_unique_val S (gpac_wf hgpacS) (uSubTargetState P₁.sys P₂.sys P₁.v P₂.v)
    (uSubTargetState_fixed P₁.sys P₂.sys (gpac_wf P₁.wf) (gpac_wf P₂.wf) P₁.v P₂.v P₁.hv P₂.hv)
    (n + 1) (P₁.sys.length + P₂.sys.length) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (solN S (P₁.sys.length + P₂.sys.length) n).val = _ at huniq
  rw [huniq]
  unfold uSubTargetState
  rw [if_neg (by omega), if_neg (by omega), Q.val_sub]

/-- **Cauchy Multiplication of `PolyODEProof` representations (`PolyODEProof.mul`)**. -/
def PolyODEProof.mul (P₁ P₂ : PolyODEProof) : PolyODEProof where
  sys := mulSys P₁.sys P₂.sys P₁.v P₂.v P₁.hv P₂.hv
  wf  := gpac_mulSys P₁.sys P₂.sys P₁.wf P₂.wf P₁.v P₂.v P₁.hv P₂.hv
  v   := P₁.sys.length + P₂.sys.length
  hv  := by rw [mulSys_length]; exact Nat.lt_succ_self _

/-- Coefficient soundness of `PolyODEProof.mul`. -/
theorem PolyODEProof.mul_coeff (P₁ P₂ : PolyODEProof) (n : Nat) :
    (P₁.mul P₂).toCertifiedAnalyticRep.coeff n =
      ((((tmJetMul (Γ := [])).eval Env.nil) (solN P₁.sys P₁.v) (solN P₂.sys P₂.v)) n).val := by
  change (solN (mulSys P₁.sys P₂.sys P₁.v P₂.v P₁.hv P₂.hv) (P₁.sys.length + P₂.sys.length) n).val = _
  let S := mulSys P₁.sys P₂.sys P₁.v P₂.v P₁.hv P₂.hv
  have hgpacS := gpac_mulSys P₁.sys P₂.sys P₁.wf P₂.wf P₁.v P₂.v P₁.hv P₂.hv
  have hvS : P₁.sys.length + P₂.sys.length < S.length := by
    rw [mulSys_length]; exact Nat.lt_succ_self _
  have huniq := genSolveN_unique_val S (gpac_wf hgpacS) (uMulTargetState P₁.sys P₂.sys P₁.v P₂.v)
    (uMulTargetState_fixed P₁.sys P₂.sys (gpac_wf P₁.wf) (gpac_wf P₂.wf) P₁.v P₂.v P₁.hv P₂.hv)
    (n + 1) (P₁.sys.length + P₂.sys.length) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (solN S (P₁.sys.length + P₂.sys.length) n).val = _ at huniq
  rw [huniq]
  unfold uMulTargetState
  rw [if_neg (by omega), if_neg (by omega)]

/-- **Reciprocal of a `PolyODEProof` representation (`PolyODEProof.inv`)**. -/
def PolyODEProof.inv (P : PolyODEProof) : PolyODEProof where
  sys := invSys P.sys P.v P.hv
  wf  := inv_gpac_invSys P.sys P.wf P.v P.hv
  v   := P.sys.length
  hv  := by simp [invSys]

/-- Coefficient soundness of `PolyODEProof.inv` when `(solN P.sys P.v 0).val ≠ 0`. -/
theorem PolyODEProof.inv_coeff (P : PolyODEProof)
    (h0 : (solN P.sys P.v 0).val ≠ 0) (n : Nat) :
    P.inv.toCertifiedAnalyticRep.coeff n = (Jet.recip (solN P.sys P.v) n).val :=
  (ux_inv_unique_val (solN P.sys P.v) (solN (invSys P.sys P.v P.hv) P.sys.length) h0
    (ux_invSys_mul_val (solN P.sys P.v) P.sys P.wf P.v P.hv (fun _ ↦ rfl) h0) n).symm

/-- **Indefinite Integration of a `PolyODEProof` representation (`PolyODEProof.integ`)**. -/
def PolyODEProof.integ (P : PolyODEProof) : PolyODEProof where
  sys := integSys P.sys P.v
  wf  := gpac_integSys P.sys P.wf P.v P.hv
  v   := P.sys.length
  hv  := by simp [integSys]

/-- Coefficient soundness of `PolyODEProof.integ`. -/
theorem PolyODEProof.integ_coeff (P : PolyODEProof) (n : Nat) :
    P.integ.toCertifiedAnalyticRep.coeff n =
      ((((tmJetInteg (Γ := [])).eval Env.nil) (solN P.sys P.v)) n).val := by
  change (solN (integSys P.sys P.v) P.sys.length n).val = _
  let S := integSys P.sys P.v
  have hgpacS := gpac_integSys P.sys P.wf P.v P.hv
  have hvS : P.sys.length < S.length := by
    rw [uInteg_integSys_length]; exact Nat.lt_succ_self _
  have huniq := genSolveN_unique_val S (gpac_wf hgpacS) (uIntegTargetState P.sys P.v)
    (uIntegTargetState_fixed P.sys (gpac_wf P.wf) P.v P.hv)
    (n + 1) P.sys.length n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (solN S P.sys.length n).val = _ at huniq
  rw [huniq]
  unfold uIntegTargetState
  rw [if_neg (Nat.lt_irrefl _)]

/-- **Differentiation of a `PolyODEProof` representation (`PolyODEProof.derivOp`)**. -/
def PolyODEProof.derivOp (P : PolyODEProof) : PolyODEProof where
  sys := derivSysC P.sys P.v P.hv
  wf  := gpac_derivSysC P.sys P.wf P.v P.hv
  v   := P.sys.length
  hv  := by rw [gpac_derivSysC_length]; exact Nat.lt_succ_self _

/-- Coefficient soundness of `PolyODEProof.derivOp`. -/
theorem PolyODEProof.derivOp_coeff (P : PolyODEProof) (n : Nat) :
    P.derivOp.toCertifiedAnalyticRep.coeff n =
      ((((tmJetDeriv (Γ := [])).eval Env.nil) (solN P.sys P.v)) n).val := by
  change (solN (derivSysC P.sys P.v P.hv) P.sys.length n).val = _
  let S := derivSysC P.sys P.v P.hv
  have hgpacS := gpac_derivSysC P.sys P.wf P.v P.hv
  have hvS : P.sys.length < S.length := by
    rw [gpac_derivSysC_length]; exact Nat.lt_succ_self _
  have huniq := genSolveN_unique_val S (gpac_wf hgpacS) (uDerivTargetState P.sys P.v)
    (gpac_derivSysC_fixed P.sys (gpac_wf P.wf) P.v P.hv)
    (n + 1) P.sys.length n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (solN S P.sys.length n).val = _ at huniq
  rw [huniq]
  unfold uDerivTargetState
  rw [if_neg (Nat.lt_irrefl _)]

/-- **Composition of `PolyODEProof` representations (`PolyODEProof.comp`)**:
    `P₁.comp P₂` represents $f_{P_1}(f_{P_2}(x) - f_{P_2}(0))$. -/
def PolyODEProof.comp (P₁ P₂ : PolyODEProof) : PolyODEProof where
  sys := compSys (flatAll P₁.sys) P₂.sys P₂.v P₂.hv
  wf  := comp_gpac_compSys (flatAll P₁.sys) P₂.sys (ux_flatAll_props P₁.sys P₁.wf).1 P₂.wf P₂.v P₂.hv
  v   := P₂.sys.length + P₁.v
  hv  := by
    have := flatAll_length_ge P₁.sys
    have := P₁.hv
    rw [comp_compSys_length]
    omega

/-- Coefficient soundness of `PolyODEProof.comp`. -/
theorem PolyODEProof.comp_coeff (P₁ P₂ : PolyODEProof) (n : Nat) :
    (P₁.comp P₂).toCertifiedAnalyticRep.coeff n =
      ((Jet.compZero ⟨solN P₁.sys P₁.v⟩ ⟨solN P₂.sys P₂.v⟩).coeff n).val := by
  obtain ⟨hgpacF, hnoF, hvalF⟩ := ux_flatAll_props P₁.sys P₁.wf
  let S := compSys (flatAll P₁.sys) P₂.sys P₂.v P₂.hv
  have hgpacS := comp_gpac_compSys (flatAll P₁.sys) P₂.sys hgpacF P₂.wf P₂.v P₂.hv
  have hvS : P₂.sys.length + P₁.v < S.length := (P₁.comp P₂).hv
  have huniq := genSolveN_unique_val S (gpac_wf hgpacS) (compTargetState (flatAll P₁.sys) P₂.sys P₂.v)
    (compTargetState_fixed (flatAll P₁.sys) P₂.sys hgpacF hnoF (gpac_wf P₂.wf) P₂.v P₂.hv)
    (n + 1) (P₂.sys.length + P₁.v) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (solN S (P₂.sys.length + P₁.v) n).val = _ at huniq
  change (solN S (P₂.sys.length + P₁.v) n).val = _
  rw [huniq]
  unfold compTargetState
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  exact (compZero_congr_val ⟨solN P₁.sys P₁.v⟩ ⟨solN (flatAll P₁.sys) P₁.v⟩
    ⟨solN P₂.sys P₂.v⟩ (hvalF P₁.v P₁.hv) n).symm

/-- **Fast Certified Definite Integral (`PolyODEProof.defIntegralFast`)**:
    Evaluates $\int_a^b f_P(t)\,dt$ to precision $2^{-k}$ via `P.integ` and `approxFast`. -/
def PolyODEProof.defIntegralFast (P : PolyODEProof) (a b : Q) (k : Nat) : Q :=
  Q.sub (GPACSys.approxFast P.integ.sys P.integ.v b (k + 1))
        (GPACSys.approxFast P.integ.sys P.integ.v a (k + 1))

/-- **True Infinite-Series Definite Integral Adequacy (`defIntegralFast_analyticValue_spec`)**:
    For $a, b$ in the certified disk of `P.integ`, `P.defIntegralFast a b k` approximates the
    true real antiderivative difference
    $$P.\mathrm{integ}.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(b) -
      P.\mathrm{integ}.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(a)$$
    within $2^{-k}$. -/
theorem PolyODEProof.defIntegralFast_analyticValue_spec (P : PolyODEProof) (a b : Q) (k : Nat)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.integ.sys).2 + 1))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.integ.sys).2 + 1)) :
    |((P.defIntegralFast a b k).val : ℝ) -
      (P.integ.toCertifiedAnalyticRep.analyticValue b -
       P.integ.toCertifiedAnalyticRep.analyticValue a)| ≤ 1 / (2 : ℝ) ^ k := by
  unfold defIntegralFast
  rw [Q.val_sub, Rat.cast_sub]
  set Ia : ℝ := ((GPACSys.approxFast P.integ.sys P.integ.v a (k + 1)).val : ℝ)
  set Ib : ℝ := ((GPACSys.approxFast P.integ.sys P.integ.v b (k + 1)).val : ℝ)
  set Fa : ℝ := P.integ.toCertifiedAnalyticRep.analyticValue a
  set Fb : ℝ := P.integ.toCertifiedAnalyticRep.analyticValue b
  have ha_cert : |Ia - Fa| ≤ 1 / (2 : ℝ) ^ (k + 1) := certified_evaluation P.integ a (k + 1) ha
  have hb_cert : |Ib - Fb| ≤ 1 / (2 : ℝ) ^ (k + 1) := certified_evaluation P.integ b (k + 1) hb
  have hsplit : (Ib - Ia) - (Fb - Fa) = (Ib - Fb) + (Fa - Ia) := by ring
  rw [hsplit]
  have htri := abs_add_le (Ib - Fb) (Fa - Ia)
  have ha_cert' : |Fa - Ia| ≤ 1 / (2 : ℝ) ^ (k + 1) := by rw [abs_sub_comm]; exact ha_cert
  have hhalf : (1 : ℝ) / (2 : ℝ) ^ (k + 1) + 1 / (2 : ℝ) ^ (k + 1) = 1 / (2 : ℝ) ^ k := by
    rw [pow_succ (2 : ℝ) k]
    field_simp
    ring
  linarith

/-- Two `CertifiedAnalyticRep`s with identical rational coefficients have the exact
    same infinite real power series `analyticValue` at every rational point `x : Q`. -/
theorem CertifiedAnalyticRep.analyticValue_congr (S₁ S₂ : CertifiedAnalyticRep)
    (h : ∀ n : Nat, S₁.coeff n = S₂.coeff n) (x : Q) :
    S₁.analyticValue x = S₂.analyticValue x := by
  unfold analyticValue seriesTerm
  congr 1; ext n; rw [h n]

/-- **FTC Part 1 on `PolyODEProof` Coefficients (`derivOp_integ_coeff`)**:
    Differentiating the antiderivative `P.integ` via `derivOp` recovers the exact
    rational Taylor coefficients of `P` at every degree $n \in \mathbb{N}$. -/
theorem PolyODEProof.derivOp_integ_coeff (P : PolyODEProof) (n : Nat) :
    (P.integ.derivOp).toCertifiedAnalyticRep.coeff n = P.toCertifiedAnalyticRep.coeff n := by
  rw [P.integ.derivOp_coeff n]
  change (Q.mul (Q.ofNat (n + 1)) (solN P.integ.sys P.integ.v (n + 1))).val =
    P.toCertifiedAnalyticRep.coeff n
  rw [Q.val_mul, Q.val_ofNat]
  have hint := P.integ_coeff (n + 1)
  change (solN P.integ.sys P.integ.v (n + 1)).val =
    (Q.div (solN P.sys P.v n) (Q.ofNat (n + 1))).val at hint
  rw [hint, Q.val_div_all, Q.val_ofNat]
  have hn : ((n + 1 : Nat) : Rat) ≠ 0 := by positivity
  exact mul_div_cancel₀ _ hn

/-- **FTC Part 1 in the Real Analytic Interpretation (`derivOp_integ_analyticValue`)**:
    The derivative representation `P.integ.derivOp` of the antiderivative `P.integ`
    has the exact same infinite real power series `analyticValue` as `P`. -/
theorem PolyODEProof.derivOp_integ_analyticValue (P : PolyODEProof) (x : Q) :
    (P.integ.derivOp).toCertifiedAnalyticRep.analyticValue x =
      P.toCertifiedAnalyticRep.analyticValue x :=
  CertifiedAnalyticRep.analyticValue_congr _ _ P.derivOp_integ_coeff x

/-- **FTC Part 2 on `PolyODEProof` Coefficients at `0` (`integ_derivOp_coeff_zero`)**. -/
theorem PolyODEProof.integ_derivOp_coeff_zero (P : PolyODEProof) :
    (P.derivOp.integ).toCertifiedAnalyticRep.coeff 0 = 0 := by
  rw [P.derivOp.integ_coeff 0]
  exact Q.val_zero

/-- **FTC Part 2 on `PolyODEProof` Coefficients at `n + 1` (`integ_derivOp_coeff_succ`)**. -/
theorem PolyODEProof.integ_derivOp_coeff_succ (P : PolyODEProof) (n : Nat) :
    (P.derivOp.integ).toCertifiedAnalyticRep.coeff (n + 1) =
      P.toCertifiedAnalyticRep.coeff (n + 1) := by
  rw [P.derivOp.integ_coeff (n + 1)]
  change (Q.div (solN P.derivOp.sys P.derivOp.v n) (Q.ofNat (n + 1))).val =
    P.toCertifiedAnalyticRep.coeff (n + 1)
  rw [Q.val_div_all, Q.val_ofNat]
  have hd := P.derivOp_coeff n
  change (solN P.derivOp.sys P.derivOp.v n).val =
    (Q.mul (Q.ofNat (n + 1)) (solN P.sys P.v (n + 1))).val at hd
  rw [hd, Q.val_mul, Q.val_ofNat]
  have hn : ((n + 1 : Nat) : Rat) ≠ 0 := by positivity
  exact mul_div_cancel_left₀ _ hn

/-- **FTC Part 2 in the Real Analytic Interpretation (`integ_derivOp_analyticValue`)**:
    For $x$ in the certified disks of `P` and `P.derivOp.integ`, the infinite real power
    series of `P.derivOp.integ` equals $P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(x) - f_P(0)$. -/
theorem PolyODEProof.integ_derivOp_analyticValue (P : PolyODEProof) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (hx_di : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.derivOp.integ.sys).2 + 1)) :
    (P.derivOp.integ).toCertifiedAnalyticRep.analyticValue x =
      P.toCertifiedAnalyticRep.analyticValue x - (P.toCertifiedAnalyticRep.coeff 0 : ℝ) := by
  let S := P.toCertifiedAnalyticRep
  let S_di := (P.derivOp.integ).toCertifiedAnalyticRep
  have h1 := (S.summable_seriesTerm x hx).sum_add_tsum_nat_add 1
  have h2 := (S_di.summable_seriesTerm x hx_di).sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at h1 h2
  have h0_S : S.seriesTerm x 0 = (S.coeff 0 : ℝ) := by
    unfold CertifiedAnalyticRep.seriesTerm; simp
  have h0_di : S_di.seriesTerm x 0 = 0 := by
    unfold CertifiedAnalyticRep.seriesTerm
    rw [P.integ_derivOp_coeff_zero]; simp
  have htail : (∑' k : Nat, S_di.seriesTerm x (k + 1)) = ∑' k : Nat, S.seriesTerm x (k + 1) := by
    congr 1; ext k
    unfold CertifiedAnalyticRep.seriesTerm
    rw [P.integ_derivOp_coeff_succ k]
  change S_di.analyticValue x = S.analyticValue x - (S.coeff 0 : ℝ)
  unfold CertifiedAnalyticRep.analyticValue
  linarith

/-- **Full Infinite-Series Newton–Leibniz Adequacy Theorem (`newtonLeibniz_analyticValue_spec`)**:
    For $a, b$ in the certified disks of `P` and `P.derivOp.integ`, the fast definite integral
    of the derivative representation `P.derivOp.defIntegralFast a b k` approximates the true
    infinite power-series difference of the original function `P` within $2^{-k}$ in $\mathbb{R}$:
    $$\left|\big((P.\mathrm{derivOp}.\operatorname{defIntegralFast}\;a\;b\;k).\mathrm{val} : \mathbb{R}\big) -
      \big(P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(b) -
           P.\mathrm{toCertifiedAnalyticRep}.\operatorname{analyticValue}(a)\big)\right| \le \frac{1}{2^k}.$$ -/
theorem PolyODEProof.newtonLeibniz_analyticValue_spec (P : PolyODEProof) (a b : Q) (k : Nat)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (ha_di : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.derivOp.integ.sys).2 + 1))
    (hb_di : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.derivOp.integ.sys).2 + 1)) :
    |((P.derivOp.defIntegralFast a b k).val : ℝ) -
      (P.toCertifiedAnalyticRep.analyticValue b -
       P.toCertifiedAnalyticRep.analyticValue a)| ≤ 1 / (2 : ℝ) ^ k := by
  have hspec := P.derivOp.defIntegralFast_analyticValue_spec a b k ha_di hb_di
  have h_a := P.integ_derivOp_analyticValue a ha ha_di
  have h_b := P.integ_derivOp_analyticValue b hb hb_di
  have hdiff : (P.derivOp.integ).toCertifiedAnalyticRep.analyticValue b -
      (P.derivOp.integ).toCertifiedAnalyticRep.analyticValue a =
      P.toCertifiedAnalyticRep.analyticValue b - P.toCertifiedAnalyticRep.analyticValue a := by
    rw [h_a, h_b]; ring
  rwa [hdiff] at hspec

/-- **Local Analytic Inverse of an Autonomous 1D ODE (`UExpr.autoInverse`)**:
    For an autonomous 1D ODE $y'(x) = F(y(x))$ with $y(0) = 0$ and $F(0) \neq 0$,
    its inverse $g = y^{-1}$ satisfies $g(0) = 0$ and $g'(t) = 1 / F(t)$, so
    $$g(t) = \int_0^t \frac{1}{F(s)}\,ds = \operatorname{UExpr.integ}(\operatorname{UExpr.inv}\;F).$$ -/
def UExpr.autoInverse (F : UExpr) : UExpr :=
  .integ (.inv F)

theorem UExpr.autoInverse_defined (F : UExpr) (hF : F.Defined) (h0 : (F.eval 0).val ≠ 0) :
    (UExpr.autoInverse F).Defined :=
  ⟨hF, h0⟩

/-- Compiling `UExpr.autoInverse F` produces a `PolyODEProof` for the local inverse $y^{-1}$. -/
def UExpr.autoInverse_toPolyODEProof (F : UExpr) (hF : F.Defined) (h0 : (F.eval 0).val ≠ 0) :
    PolyODEProof :=
  (UExpr.autoInverse F).toPolyODEProof (UExpr.autoInverse_defined F hF h0)

/-- **Left Compositional Inverse Adequacy for Autonomous 1D ODEs (`autoInverse_comp_sol_eq_varX`)**:
    Let $F : \mathrm{UExpr}$ have `(F.eval 0).val ≠ 0`, and let $Y : \mathrm{Jet}$ solve the
    autonomous 1D ODE $Y(0) = 0$, $Y' = F \circ Y$ (in rational value).
    Then composing the inverse jet `⟨(UExpr.autoInverse F).eval⟩` on the left with $Y$ yields
    the exact identity coordinate jet `Jet.varX` ($g(Y(x)) = x$) at every Taylor degree $n \in \mathbb{N}$.
    (Scope note: this theorem establishes the left formal power-series composition identity for
    autonomous 1D ODEs; general non-autonomous root/inverse evaluation is provided by `PolyODEProof.rootFast`.) -/
theorem UExpr.autoInverse_comp_sol_eq_varX (F : UExpr) (h0 : (F.eval 0).val ≠ 0)
    (Y : Jet) (_hY0 : (Y.coeff 0).val = 0)
    (hY_ode : ∀ k, (Y.deriv.coeff k).val = ((Jet.compZero ⟨F.eval⟩ Y).coeff k).val) :
    ∀ n : Nat,
      ((Jet.compZero ⟨(UExpr.autoInverse F).eval⟩ Y).coeff n).val = (Jet.varX.coeff n).val
  | 0 => by
    rw [compZero_coeff_val_eq_sum _ Y 0 0 (le_refl 0), Finset.sum_range_one]
    change (Q.zero : Q).val * ((hPow Y 0).coeff 0).val = Q.zero.val
    rw [Q.val_zero, zero_mul]
  | k + 1 => by
    let G : Jet := ⟨(UExpr.autoInverse F).eval⟩
    have hG_deriv : ∀ m, (G.deriv.coeff m).val = (Jet.recip F.eval m).val := by
      intro m
      have hd := Jet.deriv_integ_val ⟨Jet.recip F.eval⟩ m
      exact hd
    have hchain := compZero_deriv_val G Y k
    have hmul_comp : ((Y.deriv.mul (Jet.compZero G.deriv Y)).coeff k).val =
        (((Jet.compZero ⟨F.eval⟩ Y).mul (Jet.compZero ⟨Jet.recip F.eval⟩ Y)).coeff k).val := by
      dsimp [Jet.mul]
      rw [TrigPoly.cauchyConvAux_val, TrigPoly.cauchyConvAux_val]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hY_ode j, compZero_congr_val G.deriv ⟨Jet.recip F.eval⟩ Y hG_deriv (k - j)]
    have hcomp_mul := (compZero_mul_val ⟨F.eval⟩ ⟨Jet.recip F.eval⟩ Y k).symm
    have hrecip_one : ∀ m, ((Jet.mk F.eval).mul ⟨Jet.recip F.eval⟩).coeff m =
        ((tmJetMul (Γ := [])).eval Env.nil) F.eval (Jet.recip F.eval) m := by
      intro m; rw [tmJetMul_eval]
    have hcomp_one : ((Jet.compZero ((Jet.mk F.eval).mul ⟨Jet.recip F.eval⟩) Y).coeff k).val =
        ((Jet.compZero (Jet.const (Q.ofNat 1)) Y).coeff k).val :=
      compZero_congr_val ((Jet.mk F.eval).mul ⟨Jet.recip F.eval⟩) (Jet.const (Q.ofNat 1)) Y
        (fun m ↦ by rw [hrecip_one m]; exact Jet.recip_spec F.eval h0 m) k
    have hconst_one : ((Jet.compZero (Jet.const (Q.ofNat 1)) Y).coeff k).val =
        ((Jet.const (Q.ofNat 1)).coeff k).val :=
      compZero_const_val (Jet.const (Q.ofNat 1)) Y (fun m ↦ Q.val_zero) k
    have hderiv_eq : (((Jet.compZero G Y).deriv).coeff k).val =
        ((Jet.const (Q.ofNat 1)).coeff k).val :=
      hchain.trans (hmul_comp.trans (hcomp_mul.trans (hcomp_one.trans hconst_one)))
    have hderiv_def : (((Jet.compZero G Y).deriv).coeff k).val =
        ((k + 1 : Nat) : Rat) * ((Jet.compZero G Y).coeff (k + 1)).val := by
      dsimp [Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat]
    rw [hderiv_def] at hderiv_eq
    cases k with
    | zero =>
      change ((0 + 1 : Nat) : Rat) * ((Jet.compZero G Y).coeff 1).val = (Q.ofNat 1).val at hderiv_eq
      rw [Q.val_ofNat] at hderiv_eq
      change ((Jet.compZero G Y).coeff 1).val = (Q.ofNat 1).val
      rw [Q.val_ofNat]
      push_cast at hderiv_eq ⊢
      linarith
    | succ m =>
      change ((m + 1 + 1 : Nat) : Rat) * ((Jet.compZero G Y).coeff (m + 2)).val = Q.zero.val at hderiv_eq
      rw [Q.val_zero] at hderiv_eq
      have hpos : ((m + 1 + 1 : Nat) : Rat) ≠ 0 := by positivity
      have hzero : ((Jet.compZero G Y).coeff (m + 2)).val = 0 :=
        (mul_eq_zero.mp hderiv_eq).resolve_left hpos
      change ((Jet.compZero G Y).coeff (m + 2)).val = Q.zero.val
      rw [Q.val_zero]
      exact hzero

/-! ## Section 5: Certified Fourier Series Evaluation on a Strip (`StripFourierRep`)

A $2\pi$-periodic function analytic on the strip $|\mathrm{Im}(z)| \le R \ln 2$ ($R \ge 1$) is
represented by its two-sided Gaussian-rational Fourier coefficient stream `c : Int → CQ`
together with an exponential decay certificate:
$$|(c\;n).\mathrm{re}.\mathrm{val}| + |(c\;n).\mathrm{im}.\mathrm{val}|
  \le 2^M \cdot \left(\frac{1}{2^R}\right)^{|n|}, \qquad R \ge 1.$$
We establish:
1. **Exact Modal Coefficient Extraction (`TrigPoly.inner_mode_eq_coeff`, `StripFourierRep.inner_trunc_mode_eq`)**:
   The Hermitian inner product `TrigPoly.inner _ (TrigPoly.mode k)` extracts the exact $k$-th
   Fourier coefficient in `CRat`.
2. **Infinite Fourier Series Evaluation & Explicit Truncation Error (`StripFourierRep.fourierValue_sub_evalTrunc_le`, `StripFourierRep.certified_fourier_series_evaluation`)**:
   For any bounded trigonometric phase pair `(cs, sn : Int → ℝ)` with `|cs n| ≤ 1`, `|sn n| ≤ 1`,
   the symmetric frequency-shell series converges absolutely in $\mathbb{R}$, and the degree-$N$
   truncation approximates the stored infinite Fourier series within $2^{M + 1} / 2^N$ (and within $2^{-k}$
   at the linear truncation modulus $N(k) = k + M + 1$). -/

/-- **Exact Modal Coefficient Extraction (`TrigPoly.inner_mode_eq_coeff`)**:
    For every trigonometric polynomial `p : TrigPoly` and frequency `k : Int`,
    the Hermitian inner product `TrigPoly.inner p (TrigPoly.mode k)` recovers
    the exact `k`-th Fourier coefficient `p.coeff k` in `CRat`. -/
theorem TrigPoly.inner_mode_eq_coeff (p : TrigPoly) (k : Int) :
    TrigPoly.toCRat (TrigPoly.inner p (TrigPoly.mode k)) = TrigPoly.toCRat (p.coeff k) := by
  rw [TrigPoly.tpi_inner_eq_sum]
  by_cases hk : k.natAbs ≤ p.deg
  · rw [Finset.sum_eq_single k]
    · rw [TrigPoly.tpi_toCRat_mode_coeff, if_pos rfl]
      have hconj1 : TrigPoly.CRat.conj 1 = 1 := by ext <;> simp [TrigPoly.CRat.conj]
      rw [hconj1, mul_one]
    · intro j _ hjk
      rw [TrigPoly.tpi_toCRat_mode_coeff, if_neg hjk]
      have hconj0 : TrigPoly.CRat.conj 0 = 0 := by ext <;> simp [TrigPoly.CRat.conj]
      rw [hconj0, mul_zero]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_Icc]
      omega
  · have hsum0 : (∑ j ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int),
        TrigPoly.toCRat (p.coeff j) *
          TrigPoly.CRat.conj (TrigPoly.toCRat ((TrigPoly.mode k).coeff j))) = 0 := by
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      rw [Finset.mem_Icc] at hj
      have hjk : j ≠ k := by omega
      rw [TrigPoly.tpi_toCRat_mode_coeff, if_neg hjk]
      have hconj0 : TrigPoly.CRat.conj 0 = 0 := by ext <;> simp [TrigPoly.CRat.conj]
      rw [hconj0, mul_zero]
    rw [hsum0, TrigPoly.coeff, if_neg hk, TrigPoly.toCRat_zero]

/-- The $\ell^1$-norm $|z.\mathrm{re}| + |z.\mathrm{im}| \in \mathbb{Q}$ of a Gaussian rational `z : CQ`. -/
def CQ.l1Norm (z : CQ) : Rat :=
  |z.re.val| + |z.im.val|

theorem CQ.l1Norm_nonneg (z : CQ) : 0 ≤ z.l1Norm := by
  unfold CQ.l1Norm
  positivity

theorem CQ.l1Norm_add_le (z w : CQ) : (CQ.add z w).l1Norm ≤ z.l1Norm + w.l1Norm := by
  unfold CQ.l1Norm CQ.add
  rw [Q.val_add, Q.val_add]
  have h1 := abs_add_le' z.re.val w.re.val
  have h2 := abs_add_le' z.im.val w.im.val
  linarith

/-- Certified representation of a $2\pi$-periodic analytic function on a strip of width $R \ge 1$. -/
structure StripFourierRep where
  c     : Int → CQ
  M     : Nat
  R     : Nat
  hR    : 1 ≤ R
  decay : ∀ n : Int, (c n).l1Norm ≤ (2 : Rat) ^ M * (1 / (2 : Rat) ^ R) ^ n.natAbs

namespace StripFourierRep

/-- Degree-$N$ trigonometric polynomial truncation of `F : StripFourierRep`. -/
def trunc (F : StripFourierRep) (N : Nat) : TrigPoly where
  deg := N
  c := F.c

/-- **Modal Coefficient Extraction on `StripFourierRep` (`inner_trunc_mode_eq`)**:
    For every `F : StripFourierRep` and frequency `|k| ≤ N`, the inner product of
    `F.trunc N` against `TrigPoly.mode k` recovers the exact coefficient `F.c k`. -/
theorem inner_trunc_mode_eq (F : StripFourierRep) (N : Nat) (k : Int) (hk : k.natAbs ≤ N) :
    TrigPoly.toCRat (TrigPoly.inner (F.trunc N) (TrigPoly.mode k)) = TrigPoly.toCRat (F.c k) := by
  rw [TrigPoly.inner_mode_eq_coeff]
  unfold trunc TrigPoly.coeff
  dsimp
  rw [if_pos hk]

/-- Every mode $n$ satisfies `(F.c n).l1Norm ≤ 2^M · (1/2)^|n|` since $R \ge 1$. -/
theorem mode_decay_half (F : StripFourierRep) (n : Int) :
    (F.c n).l1Norm ≤ (2 : Rat) ^ F.M * (1 / 2 : Rat) ^ n.natAbs := by
  have hdec := F.decay n
  have h2R : (2 : Rat) ^ 1 ≤ (2 : Rat) ^ F.R :=
    pow_le_pow_right₀ (by norm_num) F.hR
  have hinv : 1 / (2 : Rat) ^ F.R ≤ 1 / 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : Rat) < 2) h2R
    simpa using this
  have hpow : (1 / (2 : Rat) ^ F.R) ^ n.natAbs ≤ (1 / 2 : Rat) ^ n.natAbs :=
    pow_le_pow_left₀ (by positivity) hinv n.natAbs
  exact le_trans hdec (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- At the truncation modulus $N(k) = k + M + 1$, every positive/negative mode beyond $N(k)$
    has $\ell^1$-norm at most $2^{-(k+1)}$. -/
theorem tail_mode_bound (F : StripFourierRep) (k m : Nat) (n : Int)
    (hn : n.natAbs = k + F.M + 1 + m) :
    (F.c n).l1Norm ≤ 1 / (2 : Rat) ^ (k + 1 + m) := by
  have h := F.mode_decay_half n
  rw [hn] at h
  have hpow : (2 : Rat) ^ F.M * (1 / 2 : Rat) ^ (k + F.M + 1 + m) =
      1 / (2 : Rat) ^ (k + 1 + m) := by
    rw [show k + F.M + 1 + m = F.M + (k + 1 + m) by omega, pow_add, one_div_pow, one_div_pow]
    field_simp
  linarith

/-- Real part of the $n$-th Fourier mode `F.c n` evaluated against a phase pair `(cs n, sn n)`
    (e.g., $\mathrm{cs}(n) = \cos(n\theta)$, $\mathrm{sn}(n) = \sin(n\theta)$). -/
def modeEvalRe (F : StripFourierRep) (cs sn : Int → ℝ) (n : Int) : ℝ :=
  ((F.c n).re.val : ℝ) * cs n - ((F.c n).im.val : ℝ) * sn n

/-- Bound on a single Fourier mode evaluation when `|cs n| ≤ 1` and `|sn n| ≤ 1`. -/
theorem modeEvalRe_abs_le (F : StripFourierRep) (cs sn : Int → ℝ)
    (hcs : ∀ n : Int, |cs n| ≤ 1) (hsn : ∀ n : Int, |sn n| ≤ 1) (n : Int) :
    |F.modeEvalRe cs sn n| ≤ (2 : ℝ) ^ F.M * (1 / 2 : ℝ) ^ n.natAbs := by
  unfold modeEvalRe
  have htri : |((F.c n).re.val : ℝ) * cs n - ((F.c n).im.val : ℝ) * sn n| ≤
      |((F.c n).re.val : ℝ) * cs n| + |((F.c n).im.val : ℝ) * sn n| := by
    simpa [sub_eq_add_neg] using
      abs_add_le (((F.c n).re.val : ℝ) * cs n) (-(((F.c n).im.val : ℝ) * sn n))
  rw [abs_mul, abs_mul] at htri
  have hre : |((F.c n).re.val : ℝ)| * |cs n| ≤ |((F.c n).re.val : ℝ)| * 1 :=
    mul_le_mul_of_nonneg_left (hcs n) (abs_nonneg _)
  have him : |((F.c n).im.val : ℝ)| * |sn n| ≤ |((F.c n).im.val : ℝ)| * 1 :=
    mul_le_mul_of_nonneg_left (hsn n) (abs_nonneg _)
  have hdec := F.mode_decay_half n
  have hdec_real : (((F.c n).l1Norm : Rat) : ℝ) ≤
      (((2 : Rat) ^ F.M * (1 / 2 : Rat) ^ n.natAbs : Rat) : ℝ) := by
    exact_mod_cast hdec
  unfold CQ.l1Norm at hdec_real
  push_cast at hdec_real
  linarith

/-- Symmetric frequency shell `m : Nat` combining modes `+m` and `-m` (and mode `0` at `m = 0`). -/
def shellTerm (F : StripFourierRep) (cs sn : Int → ℝ) : Nat → ℝ
  | 0 => F.modeEvalRe cs sn 0
  | m + 1 => F.modeEvalRe cs sn ((m + 1 : Nat) : Int) + F.modeEvalRe cs sn (-((m + 1 : Nat) : Int))

/-- Every frequency shell `m : Nat` is bounded by `2^{M + 1} · (1/2)^m`. -/
theorem shellTerm_abs_le (F : StripFourierRep) (cs sn : Int → ℝ)
    (hcs : ∀ n : Int, |cs n| ≤ 1) (hsn : ∀ n : Int, |sn n| ≤ 1) (m : Nat) :
    ‖F.shellTerm cs sn m‖ ≤ (2 : ℝ) ^ (F.M + 1) * (1 / 2 : ℝ) ^ m := by
  rw [Real.norm_eq_abs]
  cases m with
  | zero =>
    dsimp [shellTerm]
    have h0 := F.modeEvalRe_abs_le cs sn hcs hsn 0
    simp only [Int.natAbs_zero, pow_zero, mul_one] at h0 ⊢
    have hpow : (2 : ℝ) ^ F.M ≤ (2 : ℝ) ^ (F.M + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    linarith
  | succ k =>
    change |F.modeEvalRe cs sn ((k + 1 : Nat) : Int) +
      F.modeEvalRe cs sn (-((k + 1 : Nat) : Int))| ≤
        (2 : ℝ) ^ (F.M + 1) * (1 / 2 : ℝ) ^ (k + 1)
    have hp := F.modeEvalRe_abs_le cs sn hcs hsn ((k + 1 : Nat) : Int)
    have hn := F.modeEvalRe_abs_le cs sn hcs hsn (-((k + 1 : Nat) : Int))
    rw [Int.natAbs_natCast] at hp
    rw [Int.natAbs_neg, Int.natAbs_natCast] at hn
    have htri := abs_add_le (F.modeEvalRe cs sn ((k + 1 : Nat) : Int))
      (F.modeEvalRe cs sn (-((k + 1 : Nat) : Int)))
    have hsum : (2 : ℝ) ^ (F.M + 1) * (1 / 2 : ℝ) ^ (k + 1) =
        (2 : ℝ) ^ F.M * (1 / 2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ F.M * (1 / 2 : ℝ) ^ (k + 1) := by
      rw [pow_succ (2 : ℝ) F.M]
      ring
    linarith

/-- Absolute summability of the symmetric Fourier frequency shells in `ℝ`. -/
theorem summable_shellTerm (F : StripFourierRep) (cs sn : Int → ℝ)
    (hcs : ∀ n : Int, |cs n| ≤ 1) (hsn : ∀ n : Int, |sn n| ≤ 1) :
    Summable (F.shellTerm cs sn) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left ((2 : ℝ) ^ (F.M + 1))) ?_
  intro m
  exact F.shellTerm_abs_le cs sn hcs hsn m

/-- **Infinite Real Fourier Series Value (`StripFourierRep.fourierValue`)**:
    Sum of all symmetric frequency shells $m = 0, 1, 2, \dots$ in $\mathbb{R}$. -/
noncomputable def fourierValue (F : StripFourierRep) (cs sn : Int → ℝ) : ℝ :=
  ∑' m : Nat, F.shellTerm cs sn m

/-- **Degree-$N$ Truncated Fourier Evaluation (`StripFourierRep.evalTrunc`)**:
    Finite sum of frequency shells $0 \le m \le N$ (all modes $|n| \le N$). -/
def evalTrunc (F : StripFourierRep) (cs sn : Int → ℝ) (N : Nat) : ℝ :=
  ∑ m ∈ Finset.range (N + 1), F.shellTerm cs sn m

/-- **Explicit Infinite-Series Fourier Truncation Error (`fourierValue_sub_evalTrunc_le`)**:
    For any bounded trigonometric phase pair `(cs, sn)` (`|cs n| ≤ 1`, `|sn n| ≤ 1`) and
    any truncation degree $N \in \mathbb{N}$:
    $$\big|F.\operatorname{evalTrunc}(\mathrm{cs}, \mathrm{sn}, N) -
          F.\operatorname{fourierValue}(\mathrm{cs}, \mathrm{sn})\big|
      \le \frac{(2 : \mathbb{R})^{F.M + 1}}{(2 : \mathbb{R})^N}.$$ -/
theorem fourierValue_sub_evalTrunc_le (F : StripFourierRep) (cs sn : Int → ℝ)
    (hcs : ∀ n : Int, |cs n| ≤ 1) (hsn : ∀ n : Int, |sn n| ≤ 1) (N : Nat) :
    |F.evalTrunc cs sn N - F.fourierValue cs sn| ≤
      (2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N := by
  have hsum := F.summable_shellTerm cs sn hcs hsn
  have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
  have hsub : F.evalTrunc cs sn N - F.fourierValue cs sn =
      -(∑' k : Nat, F.shellTerm cs sn (k + (N + 1))) := by
    unfold evalTrunc fourierValue
    linarith
  rw [hsub, abs_neg, ← Real.norm_eq_abs]
  have htail_summable : Summable (fun k : Nat ↦ F.shellTerm cs sn (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr hsum
  have hgeom_summable : Summable (fun k : Nat ↦
      ((2 : ℝ) ^ (F.M + 1) * (1 / 2 : ℝ) ^ (N + 1)) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hbound : ∀ k : Nat,
      ‖F.shellTerm cs sn (k + (N + 1))‖ ≤
        ((2 : ℝ) ^ (F.M + 1) * (1 / 2 : ℝ) ^ (N + 1)) * (1 / 2 : ℝ) ^ k := by
    intro k
    have hterm := F.shellTerm_abs_le cs sn hcs hsn (k + (N + 1))
    have hpow : (2 : ℝ) ^ (F.M + 1) * (1 / 2 : ℝ) ^ (k + (N + 1)) =
        ((2 : ℝ) ^ (F.M + 1) * (1 / 2 : ℝ) ^ (N + 1)) * (1 / 2 : ℝ) ^ k := by
      rw [pow_add]
      ring
    rwa [hpow] at hterm
  have htsum_le := norm_tsum_le_tsum_norm htail_summable.norm
  have hle2 := htail_summable.norm.tsum_le_tsum hbound hgeom_summable
  have hgeom_eval : (∑' k : Nat, ((2 : ℝ) ^ (F.M + 1) * (1 / 2 : ℝ) ^ (N + 1)) * (1 / 2 : ℝ) ^ k) =
      (2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ N := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h12, one_div_pow, pow_succ (2 : ℝ) N]
    field_simp
  linarith

/-- **Certified $2^{-k}$ Fourier Series Evaluation Theorem (`certified_fourier_series_evaluation`)**:
    At the linear truncation modulus $N(k) = k + F.M + 1$:
    1. Every Fourier coefficient $F.c\;n$ for $|n| \le N(k)$ is extracted by the orthogonal
       inner product `TrigPoly.inner (F.trunc N(k)) (TrigPoly.mode n)`.
    2. The truncated Fourier sum `F.evalTrunc cs sn (k + F.M + 1)` approximates the infinite
       Fourier series `F.fourierValue cs sn` stored in `F : StripFourierRep` with certified
       error at most $2^{-k}$ in $\mathbb{R}$.
    (Scope note: this certifies evaluation of the Fourier series `F.fourierValue` from its
    stored coefficients `F.c`; proving that `F.fourierValue` equals an independently specified
    periodic analytic function $f$ whose coefficients are defined by the Fourier integral of $f$
    is a separate Fourier reconstruction theorem.) -/
theorem certified_fourier_series_evaluation (F : StripFourierRep) (cs sn : Int → ℝ)
    (hcs : ∀ n : Int, |cs n| ≤ 1) (hsn : ∀ n : Int, |sn n| ≤ 1) (k : Nat) :
    (∀ n : Int, n.natAbs ≤ k + F.M + 1 →
      TrigPoly.toCRat (TrigPoly.inner (F.trunc (k + F.M + 1)) (TrigPoly.mode n)) =
        TrigPoly.toCRat (F.c n)) ∧
    |F.evalTrunc cs sn (k + F.M + 1) - F.fourierValue cs sn| ≤ 1 / (2 : ℝ) ^ k := by
  refine ⟨fun n hn ↦ F.inner_trunc_mode_eq (k + F.M + 1) n hn, ?_⟩
  have hrem := F.fourierValue_sub_evalTrunc_le cs sn hcs hsn (k + F.M + 1)
  have hpow : (2 : ℝ) ^ (F.M + 1) / (2 : ℝ) ^ (k + F.M + 1) = 1 / (2 : ℝ) ^ k := by
    rw [show k + F.M + 1 = k + (F.M + 1) by omega, pow_add (2 : ℝ) k (F.M + 1)]
    field_simp
  rwa [hpow] at hrem

/-- Pointwise addition of two `StripFourierRep` representations preserves the strip analyticity class. -/
def add (F G : StripFourierRep) : StripFourierRep where
  c := fun n ↦ CQ.add (F.c n) (G.c n)
  M := max F.M G.M + 1
  R := min F.R G.R
  hR := le_min F.hR G.hR
  decay n := by
    have htri := CQ.l1Norm_add_le (F.c n) (G.c n)
    have hF := F.decay n
    have hG := G.decay n
    have hRF : (1 / (2 : Rat) ^ F.R) ^ n.natAbs ≤ (1 / (2 : Rat) ^ (min F.R G.R)) ^ n.natAbs := by
      refine pow_le_pow_left₀ (by positivity) ?_ n.natAbs
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (min_le_left _ _))
    have hRG : (1 / (2 : Rat) ^ G.R) ^ n.natAbs ≤ (1 / (2 : Rat) ^ (min F.R G.R)) ^ n.natAbs := by
      refine pow_le_pow_left₀ (by positivity) ?_ n.natAbs
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (min_le_right _ _))
    have hMF : (2 : Rat) ^ F.M ≤ (2 : Rat) ^ (max F.M G.M) :=
      pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    have hMG : (2 : Rat) ^ G.M ≤ (2 : Rat) ^ (max F.M G.M) :=
      pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    have hF' : (F.c n).l1Norm ≤ (2 : Rat) ^ (max F.M G.M) * (1 / (2 : Rat) ^ (min F.R G.R)) ^ n.natAbs :=
      le_trans hF (mul_le_mul hMF hRF (by positivity) (by positivity))
    have hG' : (G.c n).l1Norm ≤ (2 : Rat) ^ (max F.M G.M) * (1 / (2 : Rat) ^ (min F.R G.R)) ^ n.natAbs :=
      le_trans hG (mul_le_mul hMG hRG (by positivity) (by positivity))
    have hsum : (2 : Rat) ^ (max F.M G.M + 1) * (1 / (2 : Rat) ^ (min F.R G.R)) ^ n.natAbs =
        (2 : Rat) ^ (max F.M G.M) * (1 / (2 : Rat) ^ (min F.R G.R)) ^ n.natAbs +
        (2 : Rat) ^ (max F.M G.M) * (1 / (2 : Rat) ^ (min F.R G.R)) ^ n.natAbs := by
      rw [pow_succ]
      ring
    linarith

end StripFourierRep

/-! ## Section 6: Unified Calculus Operations Adequacy Theorem (`calculus_adequacy_master`)

We now package the verified adequacy theorems of this module into a single summary theorem:
1. **Extraction–Representation–Evaluation Equivalence**: Proof-extracted System T witnesses
   equal the fast DP table `solFast` and converge to `analyticValue` within $2^{-k}$.
2. **Representation-Level FTC1 & FTC2 on Infinite Series**: `integ` and `derivOp`
   satisfy `(P.integ.derivOp).analyticValue = P.analyticValue` and
   `|(P.derivOp.defIntegralFast a b k) - (P.analyticValue b - P.analyticValue a)| ≤ 2^{-k}`
   (connecting `derivOp` and `integ` to `analyticValue` on $\mathbb{R}$; the semantic bridge to
   Mathlib's `HasDerivAt` and `intervalIntegral` is treated separately).
3. **Constructive Root Approximation & Secant Location**: `PolyODEProof.rootFast` constructs
   rational approximate zeros with certified infinite-series residual and mutual Cauchy bounds
   under verified endpoint sign changes (`rootFast_analyticValue_spec`, `rootFast_cauchy_of_deriv_margin`).
4. **Certified Fourier Series Evaluation**: `StripFourierRep` extracts exact modes via `TrigPoly.inner`
   and evaluates the infinite Fourier series `F.fourierValue` within $2^{-k}$ at the linear modulus $k + M + 1$. -/

/-- **Unified Calculus Operations Adequacy Theorem (`calculus_adequacy_master`)**:
    Simultaneously certifies:
    1. Extraction-to-fast evaluation equivalence and $2^{-k}$ evaluation adequacy for `P : PolyODEProof`;
    2. Representation-level FTC1 (`derivOp_integ_analyticValue`) and FTC2 (`newtonLeibniz_analyticValue_spec`)
       on the infinite power series `analyticValue`;
    3. Exact modal extraction and $2^{-k}$ infinite Fourier series evaluation (`certified_fourier_series_evaluation`). -/
theorem calculus_adequacy_master (P : PolyODEProof) (x a b : Q) (k : Nat)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1))
    (ha_di : |a.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.derivOp.integ.sys).2 + 1))
    (hb_di : |b.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.derivOp.integ.sys).2 + 1))
    (F : StripFourierRep) (cs sn : Int → ℝ)
    (hcs : ∀ n : Int, |cs n| ≤ 1) (hsn : ∀ n : Int, |sn n| ≤ 1) :
    (∀ n : Nat,
      extractedCoeff P.sys (gpac_wf P.wf) P.v n = (solFast P.sys P.v n).val) ∧
    (|((GPACSys.approxFast P.sys P.v x k).val : ℝ) -
        P.toCertifiedAnalyticRep.analyticValue x| ≤ 1 / (2 : ℝ) ^ k) ∧
    ((P.integ.derivOp).toCertifiedAnalyticRep.analyticValue x =
        P.toCertifiedAnalyticRep.analyticValue x) ∧
    (|((P.derivOp.defIntegralFast a b k).val : ℝ) -
        (P.toCertifiedAnalyticRep.analyticValue b -
         P.toCertifiedAnalyticRep.analyticValue a)| ≤ 1 / (2 : ℝ) ^ k) ∧
    ((∀ n : Int, n.natAbs ≤ k + F.M + 1 →
        TrigPoly.toCRat (TrigPoly.inner (F.trunc (k + F.M + 1)) (TrigPoly.mode n)) =
          TrigPoly.toCRat (F.c n)) ∧
      |F.evalTrunc cs sn (k + F.M + 1) - F.fourierValue cs sn| ≤ 1 / (2 : ℝ) ^ k) :=
  ⟨fun n ↦ extraction_to_fast P.toCertifiedAnalyticRep n,
   certified_evaluation P x k hx,
   P.derivOp_integ_analyticValue x,
   P.newtonLeibniz_analyticValue_spec a b k ha hb ha_di hb_di,
   F.certified_fourier_series_evaluation cs sn hcs hsn k⟩

/-! ## Section 7: Selected Non-Redundancy — Necessity of Effective Tail Information

Why must a certified analytic representation carry tail-bound information (such as
$(M, R)$ or an equivalent tail envelope) rather than a bare coefficient stream
`c : Nat → Q`?

Because any evaluation algorithm that inspects only a finite prefix $c_0, \dots, c_{N_0}$
cannot distinguish the zero jet $F_1(x) = 0$ from the monomial jet
$F_2(x) = 2^{N_0 + 2} x^{N_0 + 1}$, which agrees with $F_1$ at all indices $n \le N_0$
yet has partial-sum value $2 > 1$ at $x = 1/2 \in [-1/2, 1/2]$ at degree $N_0 + 2$.
-/

/-- **Necessity of Effective Tail Information (`no_uniform_modulus_without_tail_info`)**:
    For every candidate truncation degree $N_0 \in \mathbb{N}$, there exist two jets
    $F_1, F_2 : \mathrm{Jet}$ whose coefficients are identical at all degrees $n \le N_0$,
    yet at $x = 1/2$ their degree-$(N_0 + 2)$ evaluations differ by $2 > 1$.
    Thus, no modulus depending only on finite coefficient prefixes can certify evaluation
    accuracy without tail-bound information. -/
theorem no_uniform_modulus_without_tail_info (N₀ : Nat) :
    ∃ (F₁ F₂ : Jet),
      (∀ n ≤ N₀, F₁.coeff n = F₂.coeff n) ∧
      |(F₂.evalPoly (N₀ + 2) ⟨1, 1⟩).val - (F₁.evalPoly (N₀ + 2) ⟨1, 1⟩).val| ≥ 2 := by
  let F₁ : Jet := ⟨fun _ ↦ Q.zero⟩
  let F₂ : Jet := ⟨fun n ↦ if n = N₀ + 1 then Q.ofNat (2 ^ (N₀ + 2)) else Q.zero⟩
  refine ⟨F₁, F₂, ?_, ?_⟩
  · intro n hn
    dsimp [F₁, F₂]
    rw [if_neg (by omega)]
  · have hx : (⟨1, 1⟩ : Q).val = 1 / 2 := by
      unfold Q.val Q.den
      norm_num
    have hF1 : (F₁.evalPoly (N₀ + 2) ⟨1, 1⟩).val = 0 := by
      rw [jet_evalPoly_val_eq_sum]
      refine Finset.sum_eq_zero fun n _ ↦ ?_
      dsimp [F₁]
      rw [Q.val_zero, zero_mul]
    have hF2 : (F₂.evalPoly (N₀ + 2) ⟨1, 1⟩).val = 2 := by
      rw [jet_evalPoly_val_eq_sum, Finset.sum_range_succ]
      have hpre : ∑ n ∈ Finset.range (N₀ + 1), (F₂.coeff n).val * (⟨1, 1⟩ : Q).val ^ n = 0 := by
        refine Finset.sum_eq_zero fun n hn ↦ ?_
        rw [Finset.mem_range] at hn
        change (if n = N₀ + 1 then Q.ofNat (2 ^ (N₀ + 2)) else Q.zero).val * (⟨1, 1⟩ : Q).val ^ n = 0
        rw [if_neg (by omega), Q.val_zero, zero_mul]
      rw [hpre, zero_add]
      change (if N₀ + 1 = N₀ + 1 then Q.ofNat (2 ^ (N₀ + 2)) else Q.zero).val *
        (⟨1, 1⟩ : Q).val ^ (N₀ + 1) = 2
      rw [if_pos rfl, Q.val_ofNat, hx]
      push_cast
      rw [pow_succ (2 : Rat) (N₀ + 1), one_div_pow]
      field_simp
    rw [hF1, hF2, sub_zero, abs_of_pos (by norm_num)]

#print axioms PolyODEProof.toCertifiedAnalyticRep
#print axioms extraction_to_fast
#print axioms CertifiedAnalyticRep.analyticValue_sub_evalPoly_le
#print axioms certified_evaluation
#print axioms UExpr.eval_eq_extracted_and_fast
#print axioms RadiusJet.location_error_of_deriv_margin
#print axioms PolyODEProof.analyticValue_secant_of_deriv_margin
#print axioms PolyODEProof.analyticValue_root_location_of_deriv_margin
#print axioms PolyODEProof.rootFast_analyticValue_spec
#print axioms PolyODEProof.rootFast_cauchy_of_deriv_margin
#print axioms PolyODEProof.defIntegralFast_analyticValue_spec
#print axioms PolyODEProof.derivOp_integ_analyticValue
#print axioms PolyODEProof.newtonLeibniz_analyticValue_spec
#print axioms UExpr.autoInverse_comp_sol_eq_varX
#print axioms TrigPoly.inner_mode_eq_coeff
#print axioms StripFourierRep.certified_fourier_series_evaluation
#print axioms calculus_adequacy_master
#print axioms no_uniform_modulus_without_tail_info

end HAomega
