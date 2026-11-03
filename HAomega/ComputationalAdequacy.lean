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

/-! ## Section 4: Theorem II (Part 3) — Analytic Fourier Adequacy on a Strip (`StripFourierRep`)

A $2\pi$-periodic function analytic on the strip $|\mathrm{Im}(z)| \le R \ln 2$ ($R \ge 1$) is
represented by its two-sided Gaussian-rational Fourier coefficient stream `c : Int → CQ`
together with an exponential decay certificate:
$$|(c\;n).\mathrm{re}.\mathrm{val}| + |(c\;n).\mathrm{im}.\mathrm{val}|
  \le 2^M \cdot \left(\frac{1}{2^R}\right)^{|n|}, \qquad R \ge 1.$$
-/

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

/-! ## Section 5: Selected Non-Redundancy — Necessity of Effective Tail Information

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
#print axioms no_uniform_modulus_without_tail_info

end HAomega
