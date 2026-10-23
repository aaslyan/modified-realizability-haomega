/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.HolonomicCS

/-!
# Cauchy Majorant Domination, Divided-Power Algebra, Integration by Parts, and the Galois-Adequacy Bridge

This module completes **Module 2 (`MajorantDom.lean`)** of the Closed Numerical Universe
($\mathcal{U}_{\mathbb{Q}}$) architecture:

1. **Divided-Power Monomial Basis (`Jet.divPow`, `AnalyticJet.divPow`)**:
   The divided powers $E_m(x) = \frac{x^m}{m!}$ form the canonical basis of $\mathcal{U}_{\mathbb{Q}}$:
   - $\mathcal{D}(E_{m+1}) = E_m$ (`Jet.deriv_divPow_val`),
   - $\mathcal{I}(E_m) = E_{m+1}$ (`Jet.integ_divPow_val`),
   - Uniform Cauchy majorant $(M = 0, R = 0)$ for **every** degree $m \in \mathbb{N}$ (`AnalyticJet.divPow`).

2. **Exact Algebraic Integration by Parts (`Jet.ibp_from_leibniz_val`, `Jet.ibp_coeff_one_val`)**:
   Proves that the Leibniz product rule on jets implies exact Integration by Parts on jet coefficients:
   $$\mathcal{I}(F \cdot \mathcal{D}G)_{n+1} = (F \cdot G)_{n+1} - \mathcal{I}(\mathcal{D}F \cdot G)_{n+1}.$$

3. **Factorial-Exponential Remainder & Step Domination (`AnalyticJet.coeff_bound`, `AnalyticJet.evalPoly_step_bound_unit`)**:
   Proves that for every $F \in \mathcal{U}_{\mathbb{Q}}$, its Taylor coefficients and polynomial
   truncation steps on $[-1, 1] \cap \mathbb{Q}$ obey the super-exponential bound:
   $$|(F.\mathrm{evalPoly}\;(n+1)\;x).\mathrm{val} - (F.\mathrm{evalPoly}\;n\;x).\mathrm{val}|
     \le \frac{2^M \cdot (2^R)^n}{n!}.$$

4. **System T Polynomial Evaluator Functional (`tmJetEvalPoly`, `jetEvalPolyD`, `extractedJetEvalPoly`)**:
   Constructs the closed System T Type-2 functional evaluating any jet $c : \mathrm{nat} \to \mathrm{rat}$
   at any degree $N : \mathrm{nat}$ and rational point $x : \mathrm{rat}$, proves its specification in
   `Deriv`, and extracts `extractedJetEvalPoly` via `extractClosed` (`[propext, Quot.sound]`).
-/

namespace HAomega

open Rat

/-! ## 1. Divided-Power Monomial Basis $E_m(x) = \frac{x^m}{m!}$ in $\mathcal{U}_{\mathbb{Q}}$ -/

namespace Jet

/-- The $m$-th divided-power monomial jet $E_m(x) = \frac{x^m}{m!}$, whose $n$-th coefficient is
    $1 / m!$ if $n = m$ and $0$ otherwise. -/
def divPow (m : Nat) : Jet :=
  ⟨fun n ↦ if n == m then Q.div (Q.ofNat 1) (Q.ofNat (fact m)) else Q.zero⟩

/-- Coefficient of $E_m$ at $n = m$ is $1 / m!$. -/
theorem divPow_coeff_self_val (m : Nat) :
    (((divPow m).coeff m).val) = 1 / (fact m : Rat) := by
  dsimp [divPow]
  simp only [beq_self_eq_true, ↓reduceIte]
  have hf_pos : 0 < fact m := fact_pos m
  have hf_num : (Q.ofNat (fact m)).num ≠ 0 := by
    unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hf_pos)
  rw [Q.val_div _ _ hf_num, Q.val_ofNat, Q.val_ofNat]
  simp

/-- Coefficient of $E_m$ at $n \ne m$ is $0$. -/
theorem divPow_coeff_ne_val {m n : Nat} (h : n ≠ m) :
    (((divPow m).coeff n).val) = 0 := by
  dsimp [divPow]
  have hbeq : (n == m) = false := beq_false_of_ne h
  rw [hbeq]
  exact Q.val_zero

/-- **Divided-Power Differentiation Identity ($\mathcal{D}(E_{m+1}) = E_m$)**:
    Differentiating the $(m+1)$-st divided power yields the $m$-th divided power at every index $n$! -/
theorem deriv_divPow_val (m n : Nat) :
    (((divPow (m + 1)).deriv).coeff n).val = ((divPow m).coeff n).val := by
  by_cases h : n = m
  · subst h
    dsimp [deriv]
    rw [Q.val_mul, Q.val_ofNat, divPow_coeff_self_val (n + 1), divPow_coeff_self_val n]
    have hfact_eq : ((fact (n + 1) : Nat) : Rat) = ((n + 1 : Nat) : Rat) * (fact n : Rat) := by
      dsimp [fact]; push_cast; ring
    rw [hfact_eq]
    have hn_ne : ((n + 1 : Nat) : Rat) ≠ 0 := by positivity
    have hfn_ne : ((fact n : Nat) : Rat) ≠ 0 := by exact_mod_cast (ne_of_gt (fact_pos n))
    field_simp
  · dsimp [deriv]
    have h_succ : n + 1 ≠ m + 1 := fun heq ↦ h (Nat.succ.inj heq)
    rw [Q.val_mul, divPow_coeff_ne_val h_succ, divPow_coeff_ne_val h, mul_zero]

/-- **Divided-Power Integration Identity ($\mathcal{I}(E_m) = E_{m+1}$)**:
    Integrating the $m$-th divided power yields the $(m+1)$-st divided power at every index $n$! -/
theorem integ_divPow_val (m n : Nat) :
    (((divPow m).integ).coeff n).val = ((divPow (m + 1)).coeff n).val := by
  cases n with
  | zero =>
    dsimp [integ]
    rw [Q.val_zero, divPow_coeff_ne_val (Nat.zero_ne_add_one m)]
  | succ k =>
    dsimp [integ]
    have hk_pos : 0 < k + 1 := Nat.succ_pos k
    have hk_num : (Q.ofNat (k + 1)).num ≠ 0 := by
      unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hk_pos)
    rw [Q.val_div _ _ hk_num, Q.val_ofNat]
    by_cases h : k = m
    · subst h
      rw [divPow_coeff_self_val k, divPow_coeff_self_val (k + 1)]
      have hfact_eq : ((fact (k + 1) : Nat) : Rat) = ((k + 1 : Nat) : Rat) * (fact k : Rat) := by
        dsimp [fact]; push_cast; ring
      rw [hfact_eq]
      have hk_ne : ((k + 1 : Nat) : Rat) ≠ 0 := by positivity
      have hfk_ne : ((fact k : Nat) : Rat) ≠ 0 := by exact_mod_cast (ne_of_gt (fact_pos k))
      field_simp
    · have h_succ : k + 1 ≠ m + 1 := fun heq ↦ h (Nat.succ.inj heq)
      rw [divPow_coeff_ne_val h, divPow_coeff_ne_val h_succ, zero_div]

/-! ## 2. Exact Algebraic Integration by Parts on Jets -/

/-- **Theorem (Algebraic Integration by Parts from Leibniz Rule)**:
    For any two jets $F, G \in \mathrm{Jet}$ and degree $n \in \mathbb{N}$, if the $n$-th coefficient
    satisfies the Leibniz product rule
    $$((\mathcal{D}(F \cdot G)).\mathrm{coeff}\; n).\mathrm{val}
      = (((\mathcal{D}F \cdot G) + (F \cdot \mathcal{D}G)).\mathrm{coeff}\; n).\mathrm{val},$$
    then the $(n+1)$-st coefficient satisfies **exact Integration by Parts**:
    $$((\mathcal{I}(F \cdot \mathcal{D}G)).\mathrm{coeff}\; (n + 1)).\mathrm{val}
      = ((F \cdot G).\mathrm{coeff}\; (n + 1)).\mathrm{val}
        - ((\mathcal{I}(\mathcal{D}F \cdot G)).\mathrm{coeff}\; (n + 1)).\mathrm{val}.$$ -/
theorem ibp_from_leibniz_val (F G : Jet) (n : Nat)
    (hLeib : (((F.mul G).deriv).coeff n).val =
             (((F.deriv.mul G).add (F.mul G.deriv)).coeff n).val) :
    (((F.mul G.deriv).integ).coeff (n + 1)).val =
      ((F.mul G).coeff (n + 1)).val - (((F.deriv.mul G).integ).coeff (n + 1)).val := by
  have hFTC2 := ((F.mul G).integ_deriv_coeff_succ n).2
  have hIntLeib : ((((F.mul G).deriv).integ).coeff (n + 1)).val =
      ((((F.deriv.mul G).add (F.mul G.deriv)).integ).coeff (n + 1)).val := by
    dsimp [integ]
    have hn_pos : 0 < n + 1 := Nat.succ_pos n
    have hn_num : (Q.ofNat (n + 1)).num ≠ 0 := by
      unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hn_pos)
    rw [Q.val_div _ _ hn_num, Q.val_div _ _ hn_num, hLeib]
  have hAdd := integ_add_val (F.deriv.mul G) (F.mul G.deriv) (n + 1)
  have hAddRHS : (((F.deriv.mul G).integ.add (F.mul G.deriv).integ).coeff (n + 1)).val =
      ((F.deriv.mul G).integ.coeff (n + 1)).val + ((F.mul G.deriv).integ.coeff (n + 1)).val := by
    dsimp [add]; rw [Q.val_add]
  linarith

/-- **Corollary (Unconditional Degree-1 Integration by Parts on Jets)**:
    For **all** jets $F, G \in \mathrm{Jet}$,
    $$((\mathcal{I}(F \cdot \mathcal{D}G)).\mathrm{coeff}\; 1).\mathrm{val}
      = ((F \cdot G).\mathrm{coeff}\; 1).\mathrm{val}
        - ((\mathcal{I}(\mathcal{D}F \cdot G)).\mathrm{coeff}\; 1).\mathrm{val}.$$ -/
theorem ibp_coeff_one_val (F G : Jet) :
    (((F.mul G.deriv).integ).coeff 1).val =
      ((F.mul G).coeff 1).val - (((F.deriv.mul G).integ).coeff 1).val :=
  ibp_from_leibniz_val F G 0 (deriv_mul_zero_val F G)

end Jet

/-! ## 3. Divided-Power Inhabitants & Super-Exponential Step Bounds in `AnalyticJet` -/

namespace AnalyticJet

/-- **Divided-Power Monomial $E_m(x) = \frac{x^m}{m!} \in \mathcal{U}_{\mathbb{Q}}$ (`AnalyticJet.divPow`)**:
    Every divided-power monomial $E_m$ inhabits `AnalyticJet` with uniform majorant $(M = 0, R = 0)$! -/
def divPow (m : Nat) : AnalyticJet where
  toJet := Jet.divPow m
  M := 0
  R := 0
  majorant := by
    intro n
    rw [majorant_iff_val]
    by_cases h : n = m
    · subst h
      rw [Jet.divPow_coeff_self_val n]
      have hf_pos : (0 : Rat) < (fact n : Rat) := by exact_mod_cast (fact_pos n)
      rw [abs_of_pos (div_pos (by norm_num) hf_pos)]
      rw [div_mul_cancel₀ _ (ne_of_gt hf_pos)]
      norm_num
    · rw [Jet.divPow_coeff_ne_val h, abs_zero, zero_mul]
      positivity

/-- **Theorem (Factorial-Exponential Coefficient Decay in $\mathcal{U}_{\mathbb{Q}}$)**:
    For every $F \in \mathcal{U}_{\mathbb{Q}}$ and every degree $n \in \mathbb{N}$,
    $$|(F.\mathrm{coeff}\; n).\mathrm{val}| \le \frac{2^M \cdot (2^R)^n}{n!}.$$ -/
theorem coeff_bound (F : AnalyticJet) (n : Nat) :
    |(F.coeff n).val| ≤ ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) / (fact n : Rat) := by
  have hf_pos : (0 : Rat) < (fact n : Rat) := by exact_mod_cast (fact_pos n)
  exact (le_div_iff₀ hf_pos).mpr (F.majorant_val n)

/-- **Theorem (Single-Step Polynomial Approximation Bound in $\mathcal{U}_{\mathbb{Q}}$)**:
    For every $F \in \mathcal{U}_{\mathbb{Q}}$, every $n \in \mathbb{N}$, and every $x \in \mathbb{Q}$,
    the step difference between consecutive polynomial truncations satisfies:
    $$|(F.\mathrm{evalPoly}\; (n + 1)\; x).\mathrm{val} - (F.\mathrm{evalPoly}\; n\; x).\mathrm{val}|
      \le \frac{2^M \cdot (2^R)^n \cdot |x.\mathrm{val}|^n}{n!}.$$ -/
theorem evalPoly_step_bound (F : AnalyticJet) (n : Nat) (x : Q) :
    |(F.evalPoly (n + 1) x).val - (F.evalPoly n x).val| ≤
      ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n * |x.val| ^ n) / (fact n : Rat) := by
  have h_step : (F.evalPoly (n + 1) x).val - (F.evalPoly n x).val =
      (F.coeff n).val * x.val ^ n := by
    rw [F.toJet.evalPoly_succ n x]
    ring
  rw [h_step, abs_mul, abs_pow]
  have hf_pos : (0 : Rat) < (fact n : Rat) := by exact_mod_cast (fact_pos n)
  rw [le_div_iff₀ hf_pos]
  have h_maj := F.majorant_val n
  have h_xpow : (0 : Rat) ≤ |x.val| ^ n := by positivity
  have h_mul := mul_le_mul_of_nonneg_right h_maj h_xpow
  linarith

/-- **Theorem (Unit-Interval Super-Exponential Convergence Step Bound)**:
    On the unit interval $|x.\mathrm{val}| \le 1$, consecutive polynomial approximants of any
    $F \in \mathcal{U}_{\mathbb{Q}}$ decay super-exponentially as $\frac{2^M \cdot (2^R)^n}{n!}$:
    $$|(F.\mathrm{evalPoly}\; (n + 1)\; x).\mathrm{val} - (F.\mathrm{evalPoly}\; n\; x).\mathrm{val}|
      \le \frac{2^M \cdot (2^R)^n}{n!}.$$ -/
theorem evalPoly_step_bound_unit (F : AnalyticJet) (n : Nat) (x : Q) (hx : |x.val| ≤ 1) :
    |(F.evalPoly (n + 1) x).val - (F.evalPoly n x).val| ≤
      ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) / (fact n : Rat) := by
  have h_step := F.evalPoly_step_bound n x
  have h_xpow : |x.val| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg x.val) hx
  have hf_pos : (0 : Rat) < (fact n : Rat) := by exact_mod_cast (fact_pos n)
  have h_num_le : (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n * |x.val| ^ n ≤
      (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n := by
    nlinarith [show (0 : Rat) ≤ (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n by positivity]
  have h_div_le : ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n * |x.val| ^ n) / (fact n : Rat) ≤
      ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) / (fact n : Rat) :=
    div_le_div_of_nonneg_right h_num_le (le_of_lt hf_pos)
  exact le_trans h_step h_div_le

/-- **Theorem (Simultaneous Function, Derivative, and Integral Convergence Step Bound)**:
    For every $F \in \mathcal{U}_{\mathbb{Q}}$ and $|x.\mathrm{val}| \le 1$, the $n$-th truncation steps
    of $F$, $\mathcal{D}(F)$, and $\mathcal{I}(F)$ are simultaneously bounded by their majorants: -/
theorem calculus_trio_step_bounds_unit (F : AnalyticJet) (n : Nat) (x : Q) (hx : |x.val| ≤ 1) :
    |(F.evalPoly (n + 1) x).val - (F.evalPoly n x).val| ≤
      ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) / (fact n : Rat) ∧
    |(F.deriv.evalPoly (n + 1) x).val - (F.deriv.evalPoly n x).val| ≤
      ((2 : Rat) ^ (F.M + F.R) * ((2 : Rat) ^ F.R) ^ n) / (fact n : Rat) ∧
    |(F.integ.evalPoly (n + 1) x).val - (F.integ.evalPoly n x).val| ≤
      ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) / (fact n : Rat) :=
  ⟨F.evalPoly_step_bound_unit n x hx,
   F.deriv.evalPoly_step_bound_unit n x hx,
   F.integ.evalPoly_step_bound_unit n x hx⟩

/-! ### 3b. Cauchy Convolution Majorant Closure (`AnalyticJet.mul`) -/

/-- **Pascal Factorial Domination Lemma (`fact_add_le_pow2_mul`)**:
    For all $a, b \in \mathbb{N}$ with $a + b = m$,
    $$(a + b)! \le 2^{a + b} \cdot a! \cdot b!.$$
    Proved by pure structural induction on $m = a + b$ without division! -/
theorem fact_add_le_pow2_mul : ∀ (m a b : Nat), a + b = m →
    (fact m : Rat) ≤ (2 : Rat) ^ m * (fact a : Rat) * (fact b : Rat)
  | 0, a, b, h => by
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    dsimp [fact]
    norm_num
  | m + 1, 0, b, h => by
    have hb : b = m + 1 := by omega
    subst hb
    have h1 : (fact 0 : Rat) = 1 := rfl
    rw [h1, mul_one]
    have hpow : (1 : Rat) ≤ (2 : Rat) ^ (m + 1) := one_le_pow₀ (by norm_num)
    have hfb : (0 : Rat) ≤ (fact (m + 1) : Rat) := by positivity
    nlinarith
  | m + 1, a + 1, 0, h => by
    have ha : a + 1 = m + 1 := by omega
    rw [ha]
    have h1 : (fact 0 : Rat) = 1 := rfl
    rw [h1, mul_one]
    have hpow : (1 : Rat) ≤ (2 : Rat) ^ (m + 1) := one_le_pow₀ (by norm_num)
    have hfa : (0 : Rat) ≤ (fact (m + 1) : Rat) := by positivity
    nlinarith
  | m + 1, a + 1, b + 1, h => by
    have h1 := fact_add_le_pow2_mul m a (b + 1) (by omega)
    have h2 := fact_add_le_pow2_mul m (a + 1) b (by omega)
    have hm_eq : ((m + 1 : Nat) : Rat) = ((a + 1 : Nat) : Rat) + ((b + 1 : Nat) : Rat) := by
      exact_mod_cast h.symm
    have hfm : (fact (m + 1) : Rat) = ((m + 1 : Nat) : Rat) * (fact m : Rat) := by
      dsimp [fact]; push_cast; ring
    have hfa : (fact (a + 1) : Rat) = ((a + 1 : Nat) : Rat) * (fact a : Rat) := by
      dsimp [fact]; push_cast; ring
    have hfb : (fact (b + 1) : Rat) = ((b + 1 : Nat) : Rat) * (fact b : Rat) := by
      dsimp [fact]; push_cast; ring
    have hpow : (2 : Rat) ^ (m + 1) = (2 : Rat) ^ m + (2 : Rat) ^ m := by
      rw [pow_succ]; ring
    have ha_pos : (0 : Rat) ≤ ((a + 1 : Nat) : Rat) := by positivity
    have hb_pos : (0 : Rat) ≤ ((b + 1 : Nat) : Rat) := by positivity
    have h1_mul := mul_le_mul_of_nonneg_left h1 ha_pos
    have h2_mul := mul_le_mul_of_nonneg_left h2 hb_pos
    have e1 : ((a + 1 : Nat) : Rat) * ((2 : Rat) ^ m * (fact a : Rat) * (fact (b + 1) : Rat)) =
        (2 : Rat) ^ m * (fact (a + 1) : Rat) * (fact (b + 1) : Rat) := by rw [hfa]; ring
    have e2 : ((b + 1 : Nat) : Rat) * ((2 : Rat) ^ m * (fact (a + 1) : Rat) * (fact b : Rat)) =
        (2 : Rat) ^ m * (fact (a + 1) : Rat) * (fact (b + 1) : Rat) := by rw [hfb]; ring
    have e3 : (fact (m + 1) : Rat) = ((a + 1 : Nat) : Rat) * (fact m : Rat) +
        ((b + 1 : Nat) : Rat) * (fact m : Rat) := by rw [hfm, hm_eq]; ring
    have e4 : (2 : Rat) ^ (m + 1) * (fact (a + 1) : Rat) * (fact (b + 1) : Rat) =
        (2 : Rat) ^ m * (fact (a + 1) : Rat) * (fact (b + 1) : Rat) +
        (2 : Rat) ^ m * (fact (a + 1) : Rat) * (fact (b + 1) : Rat) := by rw [hpow]; ring
    linarith

/-- Majorant bound for a single Cauchy product term $|F_j \cdot G_{n-j}| \cdot n!$ ($j \le n$). -/
theorem mul_term_majorant (F G : AnalyticJet) (n j : Nat) (hj : j ≤ n) :
    |(Q.mul (F.coeff j) (G.coeff (n - j))).val| * (fact n : Rat) ≤
      (2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R + 1)) ^ n := by
  rw [Q.val_mul, abs_mul]
  have h_fact := fact_add_le_pow2_mul n j (n - j) (Nat.add_sub_of_le hj)
  have h_abs_nonneg : (0 : Rat) ≤ |(F.coeff j).val| * |(G.coeff (n - j)).val| := by positivity
  have h_step1 : |(F.coeff j).val| * |(G.coeff (n - j)).val| * (fact n : Rat) ≤
      (2 : Rat) ^ n * (|(F.coeff j).val| * (fact j : Rat)) *
        (|(G.coeff (n - j)).val| * (fact (n - j) : Rat)) := by
    have h_mul := mul_le_mul_of_nonneg_left h_fact h_abs_nonneg
    linarith [show |(F.coeff j).val| * |(G.coeff (n - j)).val| *
                ((2 : Rat) ^ n * (fact j : Rat) * (fact (n - j) : Rat)) =
                (2 : Rat) ^ n * (|(F.coeff j).val| * (fact j : Rat)) *
                (|(G.coeff (n - j)).val| * (fact (n - j) : Rat)) by ring]
  have hR1 : ((2 : Rat) ^ F.R) ^ j ≤ ((2 : Rat) ^ (max F.R G.R)) ^ j :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_max_left F.R G.R)) j
  have hR2 : ((2 : Rat) ^ G.R) ^ (n - j) ≤ ((2 : Rat) ^ (max F.R G.R)) ^ (n - j) :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_max_right F.R G.R)) (n - j)
  have hF_dom : |(F.coeff j).val| * (fact j : Rat) ≤
      (2 : Rat) ^ F.M * ((2 : Rat) ^ (max F.R G.R)) ^ j :=
    le_trans (F.majorant_val j) (mul_le_mul_of_nonneg_left hR1 (by positivity))
  have hG_dom : |(G.coeff (n - j)).val| * (fact (n - j) : Rat) ≤
      (2 : Rat) ^ G.M * ((2 : Rat) ^ (max F.R G.R)) ^ (n - j) :=
    le_trans (G.majorant_val (n - j)) (mul_le_mul_of_nonneg_left hR2 (by positivity))
  have hFG_prod : (|(F.coeff j).val| * (fact j : Rat)) *
      (|(G.coeff (n - j)).val| * (fact (n - j) : Rat)) ≤
      ((2 : Rat) ^ F.M * ((2 : Rat) ^ (max F.R G.R)) ^ j) *
      ((2 : Rat) ^ G.M * ((2 : Rat) ^ (max F.R G.R)) ^ (n - j)) :=
    mul_le_mul hF_dom hG_dom (by positivity) (by positivity)
  have h_step2 := mul_le_mul_of_nonneg_left hFG_prod (show (0 : Rat) ≤ (2 : Rat) ^ n by positivity)
  have h_exp_combine : (2 : Rat) ^ n *
      (((2 : Rat) ^ F.M * ((2 : Rat) ^ (max F.R G.R)) ^ j) *
       ((2 : Rat) ^ G.M * ((2 : Rat) ^ (max F.R G.R)) ^ (n - j))) =
      (2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R + 1)) ^ n := by
    have hj_add : j + (n - j) = n := Nat.add_sub_of_le hj
    have h_R_split : ((2 : Rat) ^ (max F.R G.R)) ^ j * ((2 : Rat) ^ (max F.R G.R)) ^ (n - j) =
        ((2 : Rat) ^ (max F.R G.R)) ^ n := by
      rw [← pow_add, hj_add]
    have h_M_split : (2 : Rat) ^ (F.M + G.M) = (2 : Rat) ^ F.M * (2 : Rat) ^ G.M :=
      pow_add 2 F.M G.M
    have h_R1_split : ((2 : Rat) ^ (max F.R G.R + 1)) ^ n =
        (2 : Rat) ^ n * ((2 : Rat) ^ (max F.R G.R)) ^ n := by
      rw [pow_succ, mul_pow]
      ring
    rw [h_M_split, h_R1_split, ← h_R_split]
    ring
  linarith

/-- Partial Cauchy convolution bound for $k \le n + 1$. -/
theorem cauchyConvAux_majorant (F G : AnalyticJet) (n : Nat) : ∀ (k : Nat), k ≤ n + 1 →
    |(Jet.cauchyConvAux F.toJet G.toJet n k).val| * (fact n : Rat) ≤
      (k : Rat) * ((2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R + 1)) ^ n)
  | 0, _ => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_zero, abs_zero, zero_mul]
    simp
  | j + 1, hj => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_add]
    have h_tri : |(Jet.cauchyConvAux F.toJet G.toJet n j).val +
        (Q.mul (F.coeff j) (G.coeff (n - j))).val| * (fact n : Rat) ≤
        |(Jet.cauchyConvAux F.toJet G.toJet n j).val| * (fact n : Rat) +
        |(Q.mul (F.coeff j) (G.coeff (n - j))).val| * (fact n : Rat) := by
      have h_fn : (0 : Rat) ≤ (fact n : Rat) := by positivity
      nlinarith [abs_add_le (Jet.cauchyConvAux F.toJet G.toJet n j).val
                            (Q.mul (F.coeff j) (G.coeff (n - j))).val]
    have ih := cauchyConvAux_majorant F G n j (by omega)
    have h_term := mul_term_majorant F G n j (by omega)
    push_cast
    linarith

/-- Elementary inequality $n + 1 \le 2 \cdot 2^n$ in `Rat`. -/
theorem nat_succ_le_two_mul_pow2 : ∀ n : Nat,
    ((n + 1 : Nat) : Rat) ≤ 2 * (2 : Rat) ^ n
  | 0 => by norm_num
  | k + 1 => by
    have ih := nat_succ_le_two_mul_pow2 k
    have h_pow : (2 : Rat) ^ (k + 1) = 2 * (2 : Rat) ^ k := by rw [pow_succ]; ring
    have h_one_le : (1 : Rat) ≤ 2 * (2 : Rat) ^ k := by
      have : (1 : Rat) ≤ (2 : Rat) ^ k := one_le_pow₀ (by norm_num)
      linarith
    push_cast at ih ⊢
    linarith

/-- **Master Closure Under Cauchy Multiplication (`AnalyticJet.mul`)**:
    For any $F, G \in \mathcal{U}_{\mathbb{Q}}$, their Cauchy product $F \cdot G$ remains inside
    $\mathcal{U}_{\mathbb{Q}}$ with majorant $(M_1 + M_2 + 1,\; \max(R_1, R_2) + 2)$! -/
def mul (F G : AnalyticJet) : AnalyticJet where
  toJet := F.toJet.mul G.toJet
  M := F.M + G.M + 1
  R := max F.R G.R + 2
  majorant := by
    intro n
    rw [majorant_iff_val]
    dsimp [Jet.mul]
    have h_aux := cauchyConvAux_majorant F G n (n + 1) (le_refl (n + 1))
    have h_n1 := nat_succ_le_two_mul_pow2 n
    have h_base_nonneg : (0 : Rat) ≤
        (2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R + 1)) ^ n := by positivity
    have h_mul := mul_le_mul_of_nonneg_right h_n1 h_base_nonneg
    have h_rhs_eq : (2 * (2 : Rat) ^ n) *
        ((2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R + 1)) ^ n) =
        (2 : Rat) ^ (F.M + G.M + 1) * ((2 : Rat) ^ (max F.R G.R + 2)) ^ n := by
      have hM : (2 : Rat) ^ (F.M + G.M + 1) = 2 * (2 : Rat) ^ (F.M + G.M) := by
        rw [pow_succ]; ring
      have hR : ((2 : Rat) ^ (max F.R G.R + 2)) ^ n =
          (2 : Rat) ^ n * ((2 : Rat) ^ (max F.R G.R + 1)) ^ n := by
        have h2 : (2 : Rat) ^ (max F.R G.R + 2) = 2 * (2 : Rat) ^ (max F.R G.R + 1) := by
          rw [pow_succ]; ring
        rw [h2, mul_pow]
      rw [hM, hR]
      ring
    linarith

end AnalyticJet

/-! ## 4. Closed Order-0 System T Cauchy Multiplication & Polynomial Jet Evaluator -/

/-- Closed Order-0 System T natural predecessor `pred(m)`. -/
def tmNatPred {Γ : List Ty} (m : Tm Γ .nat) : Tm Γ .nat :=
  .recNat .zero (.lam (.lam (.var (.there .here)))) m

/-- Closed Order-0 System T natural subtraction `a - b`. -/
def tmNatSub {Γ : List Ty} (a b : Tm Γ .nat) : Tm Γ .nat :=
  .recNat a (.lam (.lam (tmNatPred (.var .here)))) b

/-- Closed Order-0 System T Cauchy product coefficient $(c_1 \cdot c_2)(n) = \sum_{j=0}^n c_1(j) c_2(n - j)$.
    Uses `recNat` only at base types `.nat` and `.rat` (**zero arrow types inside `recNat`**!). -/
def tmJetMulAt {Γ : List Ty} (c1 c2 : Tm Γ JetTy) (n : Tm Γ .nat) : Tm Γ .rat :=
  .recNat (.qnat .zero)
    (.lam (.lam (
      let j : Tm (.rat :: .nat :: Γ) .nat := .var (.there .here)
      let acc : Tm (.rat :: .nat :: Γ) .rat := .var .here
      let c1_wk : Tm (.rat :: .nat :: Γ) JetTy := (c1.wk (σ := .nat)).wk (σ := .rat)
      let c2_wk : Tm (.rat :: .nat :: Γ) JetTy := (c2.wk (σ := .nat)).wk (σ := .rat)
      let n_wk : Tm (.rat :: .nat :: Γ) .nat := (n.wk (σ := .nat)).wk (σ := .rat)
      .qadd acc (.qmul (.app c1_wk j) (.app c2_wk (tmNatSub n_wk j)))
    )))
    (.succ n)

/-- Closed Type-2 System T Cauchy Convolution Multiplication Functional:
    `tmJetMul : Tm Γ (JetTy → JetTy → JetTy)`. -/
def tmJetMul {Γ : List Ty} : Tm Γ (.arrow JetTy (.arrow JetTy JetTy)) :=
  .lam (.lam (.lam (
    tmJetMulAt (.var (.there (.there .here))) (.var (.there .here)) (.var .here)
  )))

/-- Formula asserting the existence of the Cauchy product jet in `Deriv`. -/
abbrev jetMulFormula : Formula [] (.arrow JetTy (.arrow JetTy (.prod JetTy .unit))) :=
  let c1 : Tm [JetTy, JetTy, JetTy] JetTy := .var (.there (.there .here))
  let c2 : Tm [JetTy, JetTy, JetTy] JetTy := .var (.there .here)
  let prodJet : Tm [JetTy, JetTy, JetTy] JetTy := .var .here
  .all JetTy (.all JetTy (.ex JetTy
    (.eq prodJet (.lam (tmJetMulAt c1.wk c2.wk (.var .here))))))

/-- **Natural Deduction Proof (`jetMulD`) in `Deriv`**:
    Synthesizes the Order-0 Cauchy product functional for any two jets `c1, c2 : JetTy`. -/
def jetMulD : Deriv Ctx.nil jetMulFormula := by
  refine Deriv.allI (Deriv.allI ?_)
  let c1 : Tm [JetTy, JetTy] JetTy := .var (.there .here)
  let c2 : Tm [JetTy, JetTy] JetTy := .var .here
  let w : Tm [JetTy, JetTy] JetTy := .lam (tmJetMulAt c1.wk c2.wk (.var .here))
  refine Deriv.exI (τ := JetTy) w ?_
  deriv_norm
  exact Deriv.eqRefl w

/-- **The Extracted System T Cauchy Convolution Functional (`extractedJetMul`)**:
    Extracted directly via `extractClosed jetMulD` (`[propext, Quot.sound]`). -/
def extractedJetMul (c1 c2 : Nat → Q) : Nat → Q :=
  ((((extractClosed jetMulD).eval Env.nil) c1) c2).1

/-- Closed System T term computing the pair $\big(\mathrm{evalPoly}(c, N, x),\; x^N\big)$
    by Order-0 recursion on `N` with state `(sum, x_pow) : .prod .rat .rat`. -/
def tmJetEvalPairAt {Γ : List Ty} (c : Tm Γ JetTy) (N : Tm Γ .nat) (x : Tm Γ .rat) :
    Tm Γ (.prod .rat .rat) :=
  .recNat (.pair (.qnat .zero) (.qnat (.succ .zero)))
    (.lam (.lam (
      let j : Tm ((.prod .rat .rat) :: .nat :: Γ) .nat := .var (.there .here)
      let st : Tm ((.prod .rat .rat) :: .nat :: Γ) (.prod .rat .rat) := .var .here
      let sum_j := .fst st
      let xpow_j := .snd st
      let c_wk : Tm ((.prod .rat .rat) :: .nat :: Γ) JetTy := (c.wk (σ := .nat)).wk (σ := .prod .rat .rat)
      let x_wk : Tm ((.prod .rat .rat) :: .nat :: Γ) .rat := (x.wk (σ := .nat)).wk (σ := .prod .rat .rat)
      let term_j := .qmul (.app c_wk j) xpow_j
      .pair (.qadd sum_j term_j) (.qmul x_wk xpow_j)
    )))
    N

/-- Closed Type-2 System T Polynomial Jet Evaluator Functional:
    `tmJetEvalPoly c N x = fst (tmJetEvalPairAt c N x)`. -/
def tmJetEvalPoly {Γ : List Ty} : Tm Γ (.arrow JetTy (.arrow .nat (.arrow .rat .rat))) :=
  .lam (.lam (.lam (
    let c : Tm (.rat :: .nat :: JetTy :: Γ) JetTy := .var (.there (.there .here))
    let N : Tm (.rat :: .nat :: JetTy :: Γ) .nat := .var (.there .here)
    let x : Tm (.rat :: .nat :: JetTy :: Γ) .rat := .var .here
    .fst (tmJetEvalPairAt c N x)
  )))

/-- Formula asserting the existence of the System T polynomial evaluator for every `(c, N, x)`. -/
abbrev jetEvalPolyFormula :
    Formula [] (.arrow JetTy (.arrow .nat (.arrow .rat (.prod .rat .unit)))) :=
  let c : Tm [.rat, .rat, .nat, JetTy] JetTy := .var (.there (.there (.there .here)))
  let N : Tm [.rat, .rat, .nat, JetTy] .nat := .var (.there (.there .here))
  let x : Tm [.rat, .rat, .nat, JetTy] .rat := .var (.there .here)
  let val : Tm [.rat, .rat, .nat, JetTy] .rat := .var .here
  .all JetTy (.all .nat (.all .rat (.ex .rat
    (.eq val (.fst (tmJetEvalPairAt c N x))))))

/-- **Natural Deduction Proof (`jetEvalPolyD`) in `Deriv`**:
    Proves in $\mathrm{HA}^\omega$ that for every jet $c : \mathrm{nat} \to \mathrm{rat}$, degree $N : \mathrm{nat}$,
    and point $x : \mathrm{rat}$, the Order-0 System T recurrence synthesizes the polynomial value. -/
def jetEvalPolyD : Deriv Ctx.nil jetEvalPolyFormula := by
  refine Deriv.allI (Deriv.allI (Deriv.allI ?_))
  let c : Tm [.rat, .nat, JetTy] JetTy := .var (.there (.there .here))
  let N : Tm [.rat, .nat, JetTy] .nat := .var (.there .here)
  let x : Tm [.rat, .nat, JetTy] .rat := .var .here
  let w : Tm [.rat, .nat, JetTy] .rat := .fst (tmJetEvalPairAt c N x)
  refine Deriv.exI (τ := .rat) w ?_
  deriv_norm
  exact Deriv.eqRefl w

/-- **The Extracted System T Jet Polynomial Evaluator (`extractedJetEvalPoly`)**:
    Extracted directly via `extractClosed jetEvalPolyD` (`[propext, Quot.sound]`). -/
def extractedJetEvalPoly (c : Nat → Q) (N : Nat) (x : Q) : Q :=
  ((((extractClosed jetEvalPolyD).eval Env.nil) c) N x).1

/-! ## 5. The Galois-Adequacy Bridge (`RepAnalyticJet`, `galoisJetDeriv`, `galoisJetInteg`, `ftcGaloisRetract`)

In general constructive analysis (`HAomega/GaloisAdequacy.lean`), differentiation drops down the
representation ladder ($A_1 \to E_0$) while integration climbs back up ($A_0 \to E_1$).
On the Closed Numerical Universe `RepAnalyticJet`, **the ladder collapses into a single fixed-point
representation**: both $\mathcal{D}$ and $\mathcal{I}$ are Galois-adequate **endomorphisms**
of `RepAnalyticJet`, and $(\mathcal{I}, \mathcal{D})$ forms a **Galois Retract**
(`ftcGaloisRetract : RepRetract RepAnalyticJet RepAnalyticJet`)! -/

/-- **Representation of Formal Jets by Cauchy-Majorized Analytic Jets (`RepAnalyticJet`)**:
    - `Carrier := AnalyticJet`
    - `approx F k G`: the first $k$ Taylor coefficients of $F$ and $G$ agree (`∀ n < k, (F.coeff n).val = (G.coeff n).val`)
    - `equiv F1 F2`: all Taylor coefficients agree (`∀ n, (F1.coeff n).val = (F2.coeff n).val`). -/
def RepAnalyticJet : Rep Jet where
  Carrier := AnalyticJet
  approx F k G := ∀ n : Nat, n < k → (F.coeff n).val = (G.coeff n).val
  equiv F1 F2 := ∀ n : Nat, (F1.coeff n).val = (F2.coeff n).val
  equiv_refl _ _ := rfl
  equiv_symm _ _ h n := (h n).symm
  equiv_trans _ _ _ h12 h23 n := (h12 n).trans (h23 n)
  approx_congr F1 F2 k G h_eq := by
    constructor
    · intro h1 n hn; rw [← h_eq n]; exact h1 n hn
    · intro h2 n hn; rw [h_eq n]; exact h2 n hn

/-- **Galois Adequacy of Differentiation as an Endomorphism of `RepAnalyticJet`**:
    To approximate $\mathcal{D}(G)$ to order $k$, `AnalyticJet.deriv` inspects $F$ to order $\mu(k) = k + 1$. -/
def galoisJetDeriv : GaloisAdequate RepAnalyticJet RepAnalyticJet Jet.deriv where
  realize := AnalyticJet.deriv
  map_equiv F1 F2 h n := by
    dsimp [AnalyticJet.deriv, Jet.deriv]
    rw [Q.val_mul, Q.val_mul, h (n + 1)]
  mu k := k + 1
  commutes F k G h n hn := by
    dsimp [AnalyticJet.deriv, Jet.deriv]
    rw [Q.val_mul, Q.val_mul, h (n + 1) (Nat.succ_lt_succ hn)]

/-- **Galois Adequacy of Integration as an Endomorphism of `RepAnalyticJet`**:
    To approximate $\mathcal{I}(G)$ to order $k$, `AnalyticJet.integ` inspects $F$ to order $\mu(k) = k$. -/
def galoisJetInteg : GaloisAdequate RepAnalyticJet RepAnalyticJet Jet.integ where
  realize := AnalyticJet.integ
  map_equiv F1 F2 h n := by
    cases n with
    | zero => rfl
    | succ m =>
      dsimp [AnalyticJet.integ, Jet.integ]
      have hm_pos : 0 < m + 1 := Nat.succ_pos m
      have hm_num : (Q.ofNat (m + 1)).num ≠ 0 := by
        unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hm_pos)
      rw [Q.val_div _ _ hm_num, Q.val_div _ _ hm_num, h m]
  mu k := k
  commutes F k G h n hn := by
    cases n with
    | zero => rfl
    | succ m =>
      dsimp [AnalyticJet.integ, Jet.integ]
      have hm_pos : 0 < m + 1 := Nat.succ_pos m
      have hm_num : (Q.ofNat (m + 1)).num ≠ 0 := by
        unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hm_pos)
      rw [Q.val_div _ _ hm_num, Q.val_div _ _ hm_num, h m (Nat.lt_of_succ_lt hn)]

/-- **Composite Galois Adequacy of $\mathcal{D} \circ \mathcal{I}$ on `RepAnalyticJet` (`ftcGaloisAdequate`)**:
    Composing `galoisJetDeriv` and `galoisJetInteg` via `GaloisAdequate.comp` yields an endomorphism
    of `RepAnalyticJet` with modulus shift $\mu(k) = k + 1$. -/
def ftcGaloisAdequate : GaloisAdequate RepAnalyticJet RepAnalyticJet (Jet.deriv ∘ Jet.integ) :=
  GaloisAdequate.comp galoisJetDeriv galoisJetInteg

/-- **Theorem (The Newton–Leibniz Galois Retraction Law on `RepAnalyticJet`)**:
    The composed Galois-adequate realizer `ftcGaloisAdequate.realize = AnalyticJet.deriv ∘ AnalyticJet.integ`
    is `RepAnalyticJet.equiv`-equivalent to the identity on **every** `F : AnalyticJet`! -/
theorem ftcGalois_retract_id (F : AnalyticJet) :
    RepAnalyticJet.equiv (ftcGaloisAdequate.realize F) F :=
  fun n ↦ F.toJet.deriv_integ_val n

/-! ## 6. Full Differential-Integral Ring AST (`ClosedRingExpr`) & Direct System T Compiler -/

/-- **Full Differential-Integral Ring AST (`ClosedRingExpr`)**:
    Includes $0, 1, x, \exp(x), \sin(x), \cos(x)$, addition $+$, subtraction $-$,
    **Cauchy multiplication $\cdot$**, differentiation $\mathcal{D}$, and integration $\mathcal{I}$. -/
inductive ClosedRingExpr where
  | zero : ClosedRingExpr
  | one : ClosedRingExpr
  | varX : ClosedRingExpr
  | expX : ClosedRingExpr
  | sinX : ClosedRingExpr
  | cosX : ClosedRingExpr
  | add : ClosedRingExpr → ClosedRingExpr → ClosedRingExpr
  | sub : ClosedRingExpr → ClosedRingExpr → ClosedRingExpr
  | mul : ClosedRingExpr → ClosedRingExpr → ClosedRingExpr
  | deriv : ClosedRingExpr → ClosedRingExpr
  | integ : ClosedRingExpr → ClosedRingExpr
  deriving Repr, DecidableEq

namespace ClosedRingExpr

/-- Constant $1 \in \mathcal{U}_{\mathbb{Q}}$ (`AnalyticJet.one` = $E_0(x)$). -/
def AnalyticJet_one : AnalyticJet := AnalyticJet.divPow 0

/-- **Semantic Compiler into the Cauchy-Majorized Ring (`ClosedRingExpr.toAnalyticJet`)**:
    Every expression built from $0, 1, x, \exp x, \sin x, \cos x$ using arbitrary combinations of
    $+, -, \cdot, \mathcal{D}, \mathcal{I}$ compiles into `AnalyticJet` with an automatic
    $(M(e), R(e))$ Cauchy majorant! -/
def toAnalyticJet : ClosedRingExpr → AnalyticJet
  | .zero => AnalyticJet.zero
  | .one => AnalyticJet_one
  | .varX => AnalyticJet.varX
  | .expX => AnalyticJet.exp
  | .sinX => AnalyticJet.sin
  | .cosX => AnalyticJet.cos
  | .add e1 e2 => (toAnalyticJet e1).add (toAnalyticJet e2)
  | .sub e1 e2 => (toAnalyticJet e1).sub (toAnalyticJet e2)
  | .mul e1 e2 => (toAnalyticJet e1).mul (toAnalyticJet e2)
  | .deriv e => (toAnalyticJet e).deriv
  | .integ e => (toAnalyticJet e).integ

/-- **Direct Compiler to Closed Order-0 Gödel System T Terms (`ClosedRingExpr.toSystemT`)**:
    Compiles any `e : ClosedRingExpr` directly into a closed System T term `: Tm [] JetTy`
    using only Order-0 `recNat` (Level $\mathcal{F}_2$ polynomial-time complexity)! -/
def toSystemT : ClosedRingExpr → Tm [] JetTy
  | .zero => .lam (.qnat .zero)
  | .one => tmConstOneJet
  | .varX => .app tmJetInteg tmConstOneJet
  | .expX => tmExpJet
  | .sinX => tmSinJet
  | .cosX => tmCosJet
  | .add e1 e2 => .app (.app tmJetAdd (toSystemT e1)) (toSystemT e2)
  | .sub e1 e2 => .app (.app tmJetSub (toSystemT e1)) (toSystemT e2)
  | .mul e1 e2 => .app (.app tmJetMul (toSystemT e1)) (toSystemT e2)
  | .deriv e => .app tmJetDeriv (toSystemT e)
  | .integ e => .app tmJetInteg (toSystemT e)

/-- **Natural Deduction Proof (`compileClosedRingExprD`) in `Deriv`**:
    For every `e : ClosedRingExpr`, proves in $\mathrm{HA}^\omega$ that `e.toSystemT` realizes the
    compiled jet stream. -/
def compileClosedRingExprD (e : ClosedRingExpr) :
    Deriv Ctx.nil (.ex JetTy (.eq (.var .here) e.toSystemT.wk)) := by
  refine Deriv.exI (τ := JetTy) e.toSystemT ?_
  deriv_norm
  exact Deriv.eqRefl e.toSystemT

/-- **The Extracted System T Realizer of any `ClosedRingExpr` (`extractedClosedRingExpr`)**:
    Extracted directly via `extractClosed (compileClosedRingExprD e)` (`[propext, Quot.sound]`). -/
def extractedClosedRingExpr (e : ClosedRingExpr) : Nat → Q :=
  ((extractClosed (compileClosedRingExprD e)).eval Env.nil).1

end ClosedRingExpr

/-! ## 6b. Exponential-Type (`AnalyticJet`) vs. Cauchy–Hadamard (`RadiusJet`) Trade-Off, Lookahead of `tmJetMul`, and Embedding into `E0` / `E1` -/

/-- **Cauchy–Hadamard Radius-Bounded Jet (`RadiusJet`)**:
    A formal power series $\sum c_n x^n$ whose coefficients satisfy
    $$|c_n| \le 2^M \cdot (2^R)^n$$
    (convergence radius $\rho \ge 2^{-R}$, with **no $n!$ factor**).
    - Unlike `AnalyticJet` ($|c_n| \cdot n! \le 2^M (2^R)^n$, the class of **entire functions of exponential type**),
      `RadiusJet` admits $\frac{1}{1-x}$ ($c_n = 1$), $\tan x$, $\sec x$, $\arctan x$, $\ln(1+x)$,
      composition, and local nonlinear ODE solutions.
    - **The Differentiation Trade-Off**: differentiating a `RadiusJet` multiplies $c_{n+1}$ by $(n+1) \le 2 \cdot 2^n$
      with no factorial to absorb $(n+1)$, forcing the radius exponent $R$ to increase:
      $(M, R) \mapsto (M + R + 1,\; R + 1)$ (shrinking the guaranteed radius $\rho = 2^{-R}$ by $1/2$). -/
structure RadiusJet where
  toJet : Jet
  M : Nat
  R : Nat
  bound : ∀ n : Nat,
    Q.ltN (Q.ofNat (2 ^ M * (2 ^ R) ^ n)) (Q.abs (toJet.coeff n)) = 0

namespace RadiusJet

/-- Bridge between the `Q.ltN`-based `bound` predicate and `Rat` inequality. -/
theorem bound_iff_val (c : Q) (M R n : Nat) :
    Q.ltN (Q.ofNat (2 ^ M * (2 ^ R) ^ n)) (Q.abs c) = 0 ↔
      |c.val| ≤ (2 : Rat) ^ M * ((2 : Rat) ^ R) ^ n := by
  rw [Q.ltN_eq_zero_iff, Q.val_abs, Q.val_ofNat]
  push_cast
  rfl

/-- `Rat`-level Cauchy–Hadamard bound extracted from `F.bound`. -/
theorem bound_val (F : RadiusJet) (n : Nat) :
    |(F.toJet.coeff n).val| ≤ (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n :=
  (bound_iff_val (F.toJet.coeff n) F.M F.R n).mp (F.bound n)

/-- Every exponential-type jet (`AnalyticJet`) embeds into `RadiusJet` with the same $(M, R)$
    because $1 \le n!$. -/
def ofAnalyticJet (F : AnalyticJet) : RadiusJet where
  toJet := F.toJet
  M := F.M
  R := F.R
  bound n := by
    rw [bound_iff_val]
    have hF := F.majorant_val n
    have h_fn : (1 : Rat) ≤ (fact n : Rat) := by exact_mod_cast fact_pos n
    have h_abs : 0 ≤ |(F.coeff n).val| := abs_nonneg _
    nlinarith

/-- The zero jet $0 \in \mathrm{RadiusJet}$ ($M = 0, R = 0$). -/
def zero : RadiusJet := ofAnalyticJet AnalyticJet.zero

/-- The coordinate jet $x \in \mathrm{RadiusJet}$ ($M = 0, R = 0$). -/
def varX : RadiusJet := ofAnalyticJet AnalyticJet.varX

/-- The geometric series $\frac{1}{1 - x} = \sum_{n=0}^\infty x^n$ ($c_n = 1$) inhabits `RadiusJet`
    with $M = 0, R = 0$ (radius $\rho = 1$). -/
def geomOneMinusX : RadiusJet where
  toJet := ⟨fun _ ↦ Q.ofNat 1⟩
  M := 0
  R := 0
  bound n := by
    rw [bound_iff_val]
    dsimp
    rw [Q.val_ofNat]
    norm_num

/-- Scaled geometric series $\frac{1}{1 - ax} = \sum_{n=0}^\infty a^n x^n$ for $|a| \le 2^R$:
    Simultaneously represents the multiplicative inverse of $1 - ax$ and the exact solution
    of the nonlinear quadratic blow-up ODE $y' = a y^2,\; y(0) = 1$, inside `RadiusJet`
    with $M = 0$ and radius parameter $R$ ($\rho = 2^{-R}$). -/
def geomScale (a : Q) (R : Nat) (ha : Qle (Q.abs a) (Q.ofNat (2 ^ R)) = true) : RadiusJet where
  toJet := ⟨fun n ↦ qpow a n⟩
  M := 0
  R := R
  bound n := by
    rw [bound_iff_val]
    dsimp
    rw [Qle_eq_true_iff, Q.val_abs, Q.val_ofNat] at ha
    push_cast at ha
    rw [qpow_val, abs_pow, pow_zero, one_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) ha n

/-- **Closure Under Negation (`RadiusJet.neg`)**: preserves $(M, R)$. -/
def neg (F : RadiusJet) : RadiusJet where
  toJet := F.toJet.neg
  M := F.M
  R := F.R
  bound n := by
    rw [bound_iff_val]
    dsimp [Jet.neg]
    rw [Q.val_neg, abs_neg]
    exact F.bound_val n

/-- **Closure Under Addition (`RadiusJet.add`)**:
    Shifts $(M_1, R_1), (M_2, R_2) \mapsto (\max(M_1, M_2) + 1,\; \max(R_1, R_2))$. -/
def add (F G : RadiusJet) : RadiusJet where
  toJet := F.toJet.add G.toJet
  M := max F.M G.M + 1
  R := max F.R G.R
  bound n := by
    rw [bound_iff_val]
    dsimp [Jet.add]
    rw [Q.val_add]
    have h_tri := abs_add_le' (F.toJet.coeff n).val (G.toJet.coeff n).val
    have hF := F.bound_val n
    have hG := G.bound_val n
    have hM1 : (2 : Rat) ^ F.M ≤ (2 : Rat) ^ (max F.M G.M) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_max_left F.M G.M)
    have hM2 : (2 : Rat) ^ G.M ≤ (2 : Rat) ^ (max F.M G.M) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_max_right F.M G.M)
    have hR1 : ((2 : Rat) ^ F.R) ^ n ≤ ((2 : Rat) ^ (max F.R G.R)) ^ n :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_max_left F.R G.R)) n
    have hR2 : ((2 : Rat) ^ G.R) ^ n ≤ ((2 : Rat) ^ (max F.R G.R)) ^ n :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_max_right F.R G.R)) n
    have hF_dom : (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n ≤
        (2 : Rat) ^ (max F.M G.M) * ((2 : Rat) ^ (max F.R G.R)) ^ n :=
      mul_le_mul hM1 hR1 (by positivity) (by positivity)
    have hG_dom : (2 : Rat) ^ G.M * ((2 : Rat) ^ G.R) ^ n ≤
        (2 : Rat) ^ (max F.M G.M) * ((2 : Rat) ^ (max F.R G.R)) ^ n :=
      mul_le_mul hM2 hR2 (by positivity) (by positivity)
    have h_pow_succ : (2 : Rat) ^ (max F.M G.M + 1) = 2 * (2 : Rat) ^ (max F.M G.M) := by
      rw [pow_succ]; ring
    rw [h_pow_succ]
    linarith

/-- **Closure Under Subtraction (`RadiusJet.sub`)**:
    Shifts $(M_1, R_1), (M_2, R_2) \mapsto (\max(M_1, M_2) + 1,\; \max(R_1, R_2))$. -/
def sub (F G : RadiusJet) : RadiusJet where
  toJet := F.toJet.sub G.toJet
  M := max F.M G.M + 1
  R := max F.R G.R
  bound n := by
    rw [bound_iff_val]
    dsimp [Jet.sub]
    rw [Q.val_sub, sub_eq_add_neg]
    have h_add := (F.add G.neg).bound_val n
    dsimp [add, neg, Jet.add, Jet.neg] at h_add
    rw [Q.val_add, Q.val_neg] at h_add
    exact h_add

/-- **Closure Under Integration (`RadiusJet.integ`)**:
    Preserves $(M, R) \mapsto (M, R)$ because $|c_k / (k + 1)| \le |c_k| \le 2^M (2^R)^k \le 2^M (2^R)^{k+1}$. -/
def integ (F : RadiusJet) : RadiusJet where
  toJet := F.toJet.integ
  M := F.M
  R := F.R
  bound n := by
    rw [bound_iff_val]
    cases n with
    | zero =>
      dsimp [Jet.integ]
      rw [Q.val_zero, abs_zero]
      positivity
    | succ k =>
      dsimp [Jet.integ]
      have hk_pos : 0 < k + 1 := Nat.succ_pos k
      have hk_num : (Q.ofNat (k + 1)).num ≠ 0 := by
        unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hk_pos)
      have hk_rat_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by exact_mod_cast hk_pos
      have hk_ge_one : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by exact_mod_cast hk_pos
      rw [Q.val_div _ _ hk_num, Q.val_ofNat, abs_div, abs_of_pos hk_rat_pos]
      have h_div_le : |(F.toJet.coeff k).val| / ((k + 1 : Nat) : Rat) ≤ |(F.toJet.coeff k).val| :=
        div_le_self (abs_nonneg _) hk_ge_one
      have hF := F.bound_val k
      have hR_ge_one : (1 : Rat) ≤ (2 : Rat) ^ F.R := one_le_pow₀ (by norm_num)
      have h_pow_le : (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ k ≤
          (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ (k + 1) := by
        rw [pow_succ ((2 : Rat) ^ F.R) k]
        nlinarith [show (0 : Rat) ≤ (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ k by positivity]
      linarith

/-- The logarithmic series $-\ln(1 - x) = \int_0^x \frac{dt}{1 - t} = \sum_{n=1}^\infty \frac{x^n}{n}$
    inhabits `RadiusJet` with $M = 0, R = 0$ via `geomOneMinusX.integ`. -/
def logOneMinusX : RadiusJet := geomOneMinusX.integ

/-- **Differentiation of a `RadiusJet` (`RadiusJet.deriv`)**:
    Without $n!$ in the bound, the factor $(n + 1) \le 2 \cdot 2^n$ increases the radius exponent
    from $R$ to $R + 1$ (halving the guaranteed convergence radius $\rho = 2^{-R} \mapsto 2^{-(R+1)}$). -/
def deriv (F : RadiusJet) : RadiusJet where
  toJet := F.toJet.deriv
  M := F.M + F.R + 1
  R := F.R + 1
  bound n := by
    rw [bound_iff_val]
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat, abs_mul]
    have hn_pos : (0 : Rat) ≤ ((n + 1 : Nat) : Rat) := by positivity
    rw [abs_of_nonneg hn_pos]
    have hF := F.bound_val (n + 1)
    have hn_pow := AnalyticJet.nat_succ_le_two_mul_pow2 n
    have h_mul : ((n + 1 : Nat) : Rat) * |(F.toJet.coeff (n + 1)).val| ≤
        (2 * (2 : Rat) ^ n) * ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ (n + 1)) :=
      mul_le_mul hn_pow hF (abs_nonneg _) (by positivity)
    have h_rhs : (2 * (2 : Rat) ^ n) * ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ (n + 1)) =
        (2 : Rat) ^ (F.M + F.R + 1) * ((2 : Rat) ^ (F.R + 1)) ^ n := by
      rw [pow_succ ((2 : Rat) ^ F.R) n, pow_add (2 : Rat) (F.M + F.R) 1,
          pow_add (2 : Rat) F.M F.R, pow_succ (2 : Rat) F.R, mul_pow]
      ring
    linarith

/-- Bound on a single Cauchy product term $|F_j \cdot G_{n-j}|$ in `RadiusJet` ($j \le n$). -/
theorem mul_term_bound (F G : RadiusJet) (n j : Nat) (hj : j ≤ n) :
    |(Q.mul (F.toJet.coeff j) (G.toJet.coeff (n - j))).val| ≤
      (2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R)) ^ n := by
  rw [Q.val_mul, abs_mul]
  have hR1 : ((2 : Rat) ^ F.R) ^ j ≤ ((2 : Rat) ^ (max F.R G.R)) ^ j :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_max_left F.R G.R)) j
  have hR2 : ((2 : Rat) ^ G.R) ^ (n - j) ≤ ((2 : Rat) ^ (max F.R G.R)) ^ (n - j) :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_max_right F.R G.R)) (n - j)
  have hF_dom : |(F.toJet.coeff j).val| ≤ (2 : Rat) ^ F.M * ((2 : Rat) ^ (max F.R G.R)) ^ j :=
    le_trans (F.bound_val j) (mul_le_mul_of_nonneg_left hR1 (by positivity))
  have hG_dom : |(G.toJet.coeff (n - j)).val| ≤ (2 : Rat) ^ G.M * ((2 : Rat) ^ (max F.R G.R)) ^ (n - j) :=
    le_trans (G.bound_val (n - j)) (mul_le_mul_of_nonneg_left hR2 (by positivity))
  have hFG := mul_le_mul hF_dom hG_dom (abs_nonneg _) (by positivity)
  have h_combine : ((2 : Rat) ^ F.M * ((2 : Rat) ^ (max F.R G.R)) ^ j) *
      ((2 : Rat) ^ G.M * ((2 : Rat) ^ (max F.R G.R)) ^ (n - j)) =
      (2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R)) ^ n := by
    have hj_add : j + (n - j) = n := Nat.add_sub_of_le hj
    have h_R_split : ((2 : Rat) ^ (max F.R G.R)) ^ j * ((2 : Rat) ^ (max F.R G.R)) ^ (n - j) =
        ((2 : Rat) ^ (max F.R G.R)) ^ n := by
      rw [← pow_add, hj_add]
    rw [pow_add (2 : Rat) F.M G.M, ← h_R_split]
    ring
  linarith

/-- Partial Cauchy convolution bound in `RadiusJet` for $k \le n + 1$. -/
theorem cauchyConvAux_bound (F G : RadiusJet) (n : Nat) : ∀ (k : Nat), k ≤ n + 1 →
    |(Jet.cauchyConvAux F.toJet G.toJet n k).val| ≤
      (k : Rat) * ((2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R)) ^ n)
  | 0, _ => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_zero, abs_zero]
    simp
  | j + 1, hj => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_add]
    have h_tri := abs_add_le'
      (Jet.cauchyConvAux F.toJet G.toJet n j).val
      (Q.mul (F.toJet.coeff j) (G.toJet.coeff (n - j))).val
    have ih := cauchyConvAux_bound F G n j (by omega)
    have h_term := mul_term_bound F G n j (by omega)
    push_cast
    linarith

/-- **Closure Under Cauchy Multiplication (`RadiusJet.mul`)**:
    Shifts $(M_1, R_1), (M_2, R_2) \mapsto (M_1 + M_2 + 1,\; \max(R_1, R_2) + 1)$! -/
def mul (F G : RadiusJet) : RadiusJet where
  toJet := F.toJet.mul G.toJet
  M := F.M + G.M + 1
  R := max F.R G.R + 1
  bound n := by
    rw [bound_iff_val]
    dsimp [Jet.mul]
    have h_aux := cauchyConvAux_bound F G n (n + 1) (le_refl (n + 1))
    have h_n1 := AnalyticJet.nat_succ_le_two_mul_pow2 n
    have h_base_nonneg : (0 : Rat) ≤
        (2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R)) ^ n := by positivity
    have h_mul := mul_le_mul_of_nonneg_right h_n1 h_base_nonneg
    have h_rhs_eq : (2 * (2 : Rat) ^ n) *
        ((2 : Rat) ^ (F.M + G.M) * ((2 : Rat) ^ (max F.R G.R)) ^ n) =
        (2 : Rat) ^ (F.M + G.M + 1) * ((2 : Rat) ^ (max F.R G.R + 1)) ^ n := by
      rw [pow_succ (2 : Rat) (F.M + G.M), pow_succ (2 : Rat) (max F.R G.R), mul_pow]
      ring
    linarith

/-- Telescoping bound on $|c_n \cdot x^n|$ inside the half-radius disk $|x| \le 2^{-(R+1)}$:
    $$|(F.\mathrm{toJet.coeff}\; n).\mathrm{val}| \cdot |x.\mathrm{val}|^n \le
      2^{F.M + 1} \cdot (2^{-n} - 2^{-(n+1)}).$$ -/
theorem term_telescope_disk (F : RadiusJet) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (F.R + 1)) (n : Nat) :
    |(F.toJet.coeff n).val| * |x.val| ^ n ≤
      (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + 1)) := by
  have hF := F.bound_val n
  have hx_pow : |x.val| ^ n ≤ (1 / (2 : Rat) ^ (F.R + 1)) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) hx n
  have h_prod : |(F.toJet.coeff n).val| * |x.val| ^ n ≤
      ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) * (1 / (2 : Rat) ^ (F.R + 1)) ^ n :=
    mul_le_mul hF hx_pow (by positivity) (by positivity)
  have h_eq : ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) * (1 / (2 : Rat) ^ (F.R + 1)) ^ n =
      (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + 1)) := by
    rw [pow_succ (2 : Rat) F.M, pow_succ (2 : Rat) F.R, pow_succ (2 : Rat) n,
        one_div_pow, mul_pow]
    field_simp
    ring
  linarith

/-- Telescoping Cauchy tail bound for `RadiusJet` on the disk $|x.\mathrm{val}| \le 2^{-(R+1)}$. -/
theorem evalPoly_cauchy_step (F : RadiusJet) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (F.R + 1)) (n : Nat) :
    ∀ d : Nat,
      |(F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + d) x).val| ≤
        (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + d))
  | 0 => by simp
  | d + 1 => by
    have ih := evalPoly_cauchy_step F x hx n d
    have h_succ := F.toJet.evalPoly_succ (n + d) x
    have h_split : (F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + (d + 1)) x).val =
        ((F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + d) x).val) +
        (-((F.toJet.coeff (n + d)).val * x.val ^ (n + d))) := by
      rw [← Nat.add_assoc, h_succ]
      ring
    rw [h_split]
    have h_tri := abs_add_le'
      ((F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + d) x).val)
      (-((F.toJet.coeff (n + d)).val * x.val ^ (n + d)))
    rw [abs_neg, abs_mul, abs_pow] at h_tri
    have h_term := F.term_telescope_disk x hx (n + d)
    rw [← Nat.add_assoc]
    linarith

/-- **Local `E0` Embedding for `RadiusJet` (`RadiusJet.toE0`)**:
    Every `F : RadiusJet` defines a certified `E0` approximating evaluator on its half-radius
    dyadic disk $[-2^{-(F.R + 1)}, 2^{-(F.R + 1)}]$ with Cauchy modulus `cm k := F.M + 1 + k`. -/
def toE0 (F : RadiusJet) : E0 where
  a := Q.neg (D.toQ (D.pow2neg (F.R + 1)))
  b := D.toQ (D.pow2neg (F.R + 1))
  ev := F.toJet.evalPoly
  cm k := F.M + 1 + k
  ivl := by
    rw [Q.ltN_eq_one_iff, Q.val_neg, toQ_pow2neg_val]
    have h_pos : (0 : Rat) < 1 / (2 : Rat) ^ (F.R + 1) := by positivity
    linarith
  conv := by
    intro k n m hn hnm x hxa hxb
    rw [Qle_eq_true_iff, Q.val_neg, toQ_pow2neg_val] at hxa
    rw [Qle_eq_true_iff, toQ_pow2neg_val] at hxb
    have hx : |x.val| ≤ 1 / (2 : Rat) ^ (F.R + 1) := abs_le.mpr ⟨hxa, hxb⟩
    have hm_eq : m = n + (m - n) := (Nat.add_sub_of_le hnm).symm
    have h_step := F.evalPoly_cauchy_step x hx n (m - n)
    rw [← hm_eq] at h_step
    have h_pos : (0 : Rat) ≤ (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ m) := by positivity
    have h_le1 : |(F.toJet.evalPoly n x).val - (F.toJet.evalPoly m x).val| ≤
        (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ n) := by linarith
    have h_inv : (1 : Rat) / (2 : Rat) ^ n ≤ 1 / (2 : Rat) ^ (F.M + 1 + k) :=
      inv_pow_le hn
    have h_le2 : (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ n) ≤
        (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ (F.M + 1 + k)) :=
      mul_le_mul_of_nonneg_left h_inv (by positivity)
    have h_eq : (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ (F.M + 1 + k)) =
        1 / (2 : Rat) ^ k := by
      rw [pow_add (2 : Rat) (F.M + 1) k]
      field_simp
    rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val]
    linarith

/-! ### 6b.1. Multiplicative Inversion $(1 - G_+)^{-1}$ in `RadiusJet` (`RadiusJet.invOneSub`) -/

/-- Shifted jet $(G.\mathrm{shift})_j = G_{j+1}$, so $x \cdot G.\mathrm{shift}(x) = G(x) - G(0)$. -/
def _root_.HAomega.Jet.shift (G : Jet) : Jet :=
  ⟨fun j ↦ G.coeff (j + 1)⟩

/-- Primitive-recursive Order-1 approximants for $(1 - (G - G_0))^{-1}$:
    - At step $0$: constant $1$.
    - At step $m + 1$: $I_0 = 1$ and $I_{k+1} = \sum_{j=0}^k G_{j+1} I_{k-j}$. -/
def invOneSubIter (G : Jet) : Nat → Nat → Q
  | 0, 0 => Q.ofNat 1
  | 0, _ + 1 => Q.zero
  | _ + 1, 0 => Q.ofNat 1
  | m + 1, k + 1 => Jet.cauchyConvAux G.shift ⟨invOneSubIter G m⟩ k (k + 1)

/-- Formal multiplicative inverse $(1 - (G - G_0))^{-1}$ of $1 - (G(x) - G(0))$, extracted at the
    diagonal `invOneSubIter G n n`. -/
def _root_.HAomega.Jet.invOneSub (G : Jet) : Jet :=
  ⟨fun n ↦ invOneSubIter G n n⟩

/-- Elementary dominance $2^M \cdot (2^R)^{j+1} \le (2^{M + R})^{j+1}$ for all $M, R, j \in \mathbb{N}$. -/
theorem pow_mul_pow_succ_le (M R j : Nat) :
    (2 : Rat) ^ M * ((2 : Rat) ^ R) ^ (j + 1) ≤ ((2 : Rat) ^ (M + R)) ^ (j + 1) := by
  have h1 : (1 : Rat) ≤ (2 : Rat) ^ M := one_le_pow₀ (by norm_num)
  have hM : (2 : Rat) ^ M ≤ ((2 : Rat) ^ M) ^ (j + 1) :=
    le_self_pow₀ h1 (Nat.succ_ne_zero j)
  have h_eq : ((2 : Rat) ^ M) ^ (j + 1) * ((2 : Rat) ^ R) ^ (j + 1) =
      ((2 : Rat) ^ (M + R)) ^ (j + 1) := by
    rw [← mul_pow, ← pow_add]
  rw [← h_eq]
  exact mul_le_mul_of_nonneg_right hM (by positivity)

/-- Single-term telescoping bound for the inverse recurrence of `G : RadiusJet`:
    if $|I_{k-j}| \le (2^S)^{k-j}$ with $S = G.M + G.R + 1$, then
    $|G_{j+1} \cdot I_{k-j}| \le (2^S)^{k+1} \cdot (2^{-j} - 2^{-(j+1)})$. -/
theorem invOneSub_term_bound (G : RadiusJet) (I : Nat → Q) (k j : Nat) (hj : j ≤ k)
    (hI : |(I (k - j)).val| ≤ ((2 : Rat) ^ (G.M + G.R + 1)) ^ (k - j)) :
    |(Q.mul (G.toJet.shift.coeff j) (I (k - j))).val| ≤
      ((2 : Rat) ^ (G.M + G.R + 1)) ^ (k + 1) *
        (1 / (2 : Rat) ^ j - 1 / (2 : Rat) ^ (j + 1)) := by
  rw [Q.val_mul, abs_mul]
  have hG1 : |(G.toJet.shift.coeff j).val| ≤ (2 : Rat) ^ G.M * ((2 : Rat) ^ G.R) ^ (j + 1) :=
    G.bound_val (j + 1)
  have hG2 := le_trans hG1 (pow_mul_pow_succ_le G.M G.R j)
  have h_prod := mul_le_mul hG2 hI (abs_nonneg _) (by positivity)
  have h_id : ((2 : Rat) ^ (G.M + G.R)) ^ (j + 1) * ((2 : Rat) ^ (G.M + G.R + 1)) ^ (k - j) =
      ((2 : Rat) ^ (G.M + G.R + 1)) ^ (k + 1) *
        (1 / (2 : Rat) ^ j - 1 / (2 : Rat) ^ (j + 1)) := by
    have hk_eq : k + 1 = (j + 1) + (k - j) := by omega
    rw [hk_eq, pow_add ((2 : Rat) ^ (G.M + G.R + 1)) (j + 1) (k - j)]
    rw [pow_succ (2 : Rat) (G.M + G.R), mul_pow, pow_succ (2 : Rat) j]
    field_simp
    ring
  linarith

/-- Partial Cauchy sum bound for `invOneSubIter` up to $r \le k + 1$. -/
theorem invOneSub_convAux_bound (G : RadiusJet) (I : Nat → Q) (k : Nat)
    (hI : ∀ i ≤ k, |(I i).val| ≤ ((2 : Rat) ^ (G.M + G.R + 1)) ^ i) :
    ∀ r ≤ k + 1,
      |(Jet.cauchyConvAux G.toJet.shift ⟨I⟩ k r).val| ≤
        ((2 : Rat) ^ (G.M + G.R + 1)) ^ (k + 1) * (1 - 1 / (2 : Rat) ^ r)
  | 0, _ => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_zero, abs_zero]
    simp
  | j + 1, hj => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_add]
    have h_tri := abs_add_le'
      (Jet.cauchyConvAux G.toJet.shift ⟨I⟩ k j).val
      (Q.mul (G.toJet.shift.coeff j) (I (k - j))).val
    have ih := invOneSub_convAux_bound G I k hI j (by omega)
    have h_term := invOneSub_term_bound G I k j (by omega) (hI (k - j) (by omega))
    linarith

/-- Uniform Cauchy–Hadamard bound on `invOneSubIter G.toJet m n` for all $m, n \in \mathbb{N}$. -/
theorem invOneSubIter_bound (G : RadiusJet) : ∀ (m n : Nat),
    |(invOneSubIter G.toJet m n).val| ≤ ((2 : Rat) ^ (G.M + G.R + 1)) ^ n
  | 0, 0 => by
    dsimp [invOneSubIter]
    rw [Q.val_ofNat]
    norm_num
  | 0, k + 1 => by
    dsimp [invOneSubIter]
    rw [Q.val_zero, abs_zero]
    positivity
  | m + 1, 0 => by
    dsimp [invOneSubIter]
    rw [Q.val_ofNat]
    norm_num
  | m + 1, k + 1 => by
    dsimp [invOneSubIter]
    have h_aux := invOneSub_convAux_bound G (invOneSubIter G.toJet m) k
      (fun i _ ↦ invOneSubIter_bound G m i) (k + 1) (le_refl _)
    have h_pos : (0 : Rat) ≤
        ((2 : Rat) ^ (G.M + G.R + 1)) ^ (k + 1) * (1 / (2 : Rat) ^ (k + 1)) := by positivity
    linarith

/-- **Closure Under Multiplicative Inversion $(1 - G_+)^{-1}$ (`RadiusJet.invOneSub`)**:
    For any `G : RadiusJet`, the formal inverse $(1 - (G(x) - G(0)))^{-1}$ inhabits `RadiusJet`
    with amplitude parameter $M = 0$ and radius parameter $R = G.M + G.R + 1$! -/
def invOneSub (G : RadiusJet) : RadiusJet where
  toJet := G.toJet.invOneSub
  M := 0
  R := G.M + G.R + 1
  bound n := by
    rw [bound_iff_val, pow_zero, one_mul]
    exact invOneSubIter_bound G n n

/-- Constant $1 \in \mathrm{RadiusJet}$ ($M = 0, R = 0$). -/
def one : RadiusJet := ofAnalyticJet (AnalyticJet.divPow 0)

/-- Sine $\sin x \in \mathrm{RadiusJet}$ ($M = 0, R = 0$). -/
def sin : RadiusJet := ofAnalyticJet AnalyticJet.sin

/-- Cosine $\cos x \in \mathrm{RadiusJet}$ ($M = 0, R = 0$). -/
def cos : RadiusJet := ofAnalyticJet AnalyticJet.cos

/-- **Secant Series $\sec x = \frac{1}{\cos x} = \frac{1}{1 - (1 - \cos x)} \in \mathrm{RadiusJet}$ (`RadiusJet.sec`)**:
    Certified inhabitant of `RadiusJet` via `invOneSub`! -/
def sec : RadiusJet := (one.sub cos).invOneSub

/-- **Tangent Series $\tan x = \sin x \cdot \sec x \in \mathrm{RadiusJet}$ (`RadiusJet.tan`)**:
    Certified inhabitant of `RadiusJet` via `mul` and `sec`! -/
def tan : RadiusJet := sin.mul sec

/-- **Arctangent Series $\arctan x = \int_0^x \frac{dt}{1 + t^2} \in \mathrm{RadiusJet}$ (`RadiusJet.arctan`)**:
    Certified inhabitant of `RadiusJet` via `invOneSub` and `integ`! -/
def arctan : RadiusJet := ((varX.mul varX).neg.invOneSub).integ

/-- Exponential $e^x \in \mathrm{RadiusJet}$ ($M = 0, R = 0$). -/
def exp : RadiusJet := ofAnalyticJet AnalyticJet.exp

/-! ### 6b.1b. Closure Under Composition $F(G(x) - G(0))$ (`RadiusJet.compZero`) and Nonlinear Riccati ODEs (`RadiusJet.riccatiODE`) -/

/-- Primitive-recursive Order-1 approximants for the shifted composition $(F.\mathrm{shift}^s \circ G_+)(x)$:
    - For degree $n = 0$: $(F.\mathrm{shift}^s)_0 = F_s$.
    - At step $m + 1$ and degree $k + 1$:
      $(F.\mathrm{shift}^s \circ G_+)_{k+1} = \sum_{j=0}^k G_{j+1} \cdot (F.\mathrm{shift}^{s+1} \circ G_+)_{k-j}$. -/
def compZeroIter (F G : Jet) : Nat → Nat → Nat → Q
  | 0, 0, s => F.coeff s
  | 0, _ + 1, _ => Q.zero
  | _ + 1, 0, s => F.coeff s
  | m + 1, k + 1, s =>
      Jet.cauchyConvAux G.shift ⟨fun i ↦ compZeroIter F G m i (s + 1)⟩ k (k + 1)

/-- Formal power-series composition $F(G(x) - G(0))$ extracted at the diagonal `compZeroIter F G n n 0`. -/
def _root_.HAomega.Jet.compZero (F G : Jet) : Jet :=
  ⟨fun n ↦ compZeroIter F G n n 0⟩

/-- Single-term telescoping bound for the Horner-shift composition recurrence of `F, G : RadiusJet`:
    if $|I_{k-j}| \le 2^{F.M} \cdot (2^{F.R})^{s+1} \cdot (2^S)^{k-j}$ with $S = F.R + G.M + G.R + 1$, then
    $|G_{j+1} \cdot I_{k-j}| \le 2^{F.M} \cdot (2^{F.R})^s \cdot (2^S)^{k+1} \cdot (2^{-j} - 2^{-(j+1)})$. -/
theorem compZero_term_bound (F G : RadiusJet) (I : Nat → Q) (s k j : Nat) (hj : j ≤ k)
    (hI : |(I (k - j)).val| ≤
      (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ (s + 1) * ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k - j)) :
    |(Q.mul (G.toJet.shift.coeff j) (I (k - j))).val| ≤
      (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s * ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k + 1) *
        (1 / (2 : Rat) ^ j - 1 / (2 : Rat) ^ (j + 1)) := by
  rw [Q.val_mul, abs_mul]
  have hG1 : |(G.toJet.shift.coeff j).val| ≤ (2 : Rat) ^ G.M * ((2 : Rat) ^ G.R) ^ (j + 1) :=
    G.bound_val (j + 1)
  have hG2 := le_trans hG1 (pow_mul_pow_succ_le G.M G.R j)
  have hFR1 : (1 : Rat) ≤ (2 : Rat) ^ F.R := one_le_pow₀ (by norm_num)
  have hFR_pow : (2 : Rat) ^ F.R ≤ ((2 : Rat) ^ F.R) ^ (j + 1) :=
    le_self_pow₀ hFR1 (Nat.succ_ne_zero j)
  have hI2 : (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ (s + 1) * ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k - j) ≤
      (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s * ((2 : Rat) ^ F.R) ^ (j + 1) *
        ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k - j) := by
    rw [pow_succ ((2 : Rat) ^ F.R) s]
    have h_nonneg : (0 : Rat) ≤
        (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s * ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k - j) := by
      positivity
    have h_m := mul_le_mul_of_nonneg_left hFR_pow h_nonneg
    linarith
  have hI3 := le_trans hI hI2
  have h_prod := mul_le_mul hG2 hI3 (abs_nonneg _) (by positivity)
  have h_id : ((2 : Rat) ^ (G.M + G.R)) ^ (j + 1) *
      ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s * ((2 : Rat) ^ F.R) ^ (j + 1) *
        ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k - j)) =
      (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s * ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k + 1) *
        (1 / (2 : Rat) ^ j - 1 / (2 : Rat) ^ (j + 1)) := by
    have hk_eq : k + 1 = (j + 1) + (k - j) := by omega
    have h_combine : ((2 : Rat) ^ F.R) ^ (j + 1) * ((2 : Rat) ^ (G.M + G.R)) ^ (j + 1) =
        ((2 : Rat) ^ (F.R + G.M + G.R)) ^ (j + 1) := by
      rw [← mul_pow, ← pow_add, Nat.add_assoc]
    have h_rearrange : ((2 : Rat) ^ (G.M + G.R)) ^ (j + 1) *
        ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s * ((2 : Rat) ^ F.R) ^ (j + 1) *
          ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k - j)) =
        (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s *
          (((2 : Rat) ^ F.R) ^ (j + 1) * ((2 : Rat) ^ (G.M + G.R)) ^ (j + 1)) *
          ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k - j) := by ring
    rw [h_rearrange, h_combine, hk_eq, pow_add ((2 : Rat) ^ (F.R + G.M + G.R + 1)) (j + 1) (k - j)]
    rw [pow_succ (2 : Rat) (F.R + G.M + G.R), mul_pow, pow_succ (2 : Rat) j]
    field_simp
    ring
  linarith

/-- Partial Cauchy sum bound for `compZeroIter` up to $r \le k + 1$. -/
theorem compZero_convAux_bound (F G : RadiusJet) (I : Nat → Q) (s k : Nat)
    (hI : ∀ i ≤ k, |(I i).val| ≤
      (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ (s + 1) * ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ i) :
    ∀ r ≤ k + 1,
      |(Jet.cauchyConvAux G.toJet.shift ⟨I⟩ k r).val| ≤
        (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s * ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k + 1) *
          (1 - 1 / (2 : Rat) ^ r)
  | 0, _ => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_zero, abs_zero]
    simp
  | j + 1, hj => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_add]
    have h_tri := abs_add_le'
      (Jet.cauchyConvAux G.toJet.shift ⟨I⟩ k j).val
      (Q.mul (G.toJet.shift.coeff j) (I (k - j))).val
    have ih := compZero_convAux_bound F G I s k hI j (by omega)
    have h_term := compZero_term_bound F G I s k j (by omega) (hI (k - j) (by omega))
    linarith

/-- Uniform Cauchy–Hadamard bound on `compZeroIter F.toJet G.toJet m n s` for all $m, n, s \in \mathbb{N}$. -/
theorem compZeroIter_bound (F G : RadiusJet) : ∀ (m n s : Nat),
    |(compZeroIter F.toJet G.toJet m n s).val| ≤
      (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s * ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ n
  | 0, 0, s => by
    dsimp [compZeroIter]
    rw [pow_zero, mul_one]
    exact F.bound_val s
  | 0, k + 1, _ => by
    dsimp [compZeroIter]
    rw [Q.val_zero, abs_zero]
    positivity
  | m + 1, 0, s => by
    dsimp [compZeroIter]
    rw [pow_zero, mul_one]
    exact F.bound_val s
  | m + 1, k + 1, s => by
    dsimp [compZeroIter]
    have h_aux := compZero_convAux_bound F G (fun i ↦ compZeroIter F.toJet G.toJet m i (s + 1)) s k
      (fun i _ ↦ compZeroIter_bound F G m i (s + 1)) (k + 1) (le_refl _)
    have h_pos : (0 : Rat) ≤
        (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ s * ((2 : Rat) ^ (F.R + G.M + G.R + 1)) ^ (k + 1) *
          (1 / (2 : Rat) ^ (k + 1)) := by positivity
    linarith

/-- **Closure Under Composition $F(G(x) - G(0))$ (`RadiusJet.compZero`)**:
    For any `F G : RadiusJet`, the formal power-series composition $F(G(x) - G(0))$ inhabits `RadiusJet`
    with amplitude parameter $M = F.M$ and radius parameter $R = F.R + G.M + G.R + 1$! -/
def compZero (F G : RadiusJet) : RadiusJet where
  toJet := F.toJet.compZero G.toJet
  M := F.M
  R := F.R + G.M + G.R + 1
  bound n := by
    rw [bound_iff_val]
    have h := compZeroIter_bound F G n n 0
    simpa [Jet.compZero] using h

/-- **Composite Exponential-Tangent $e^{\tan x} \in \mathrm{RadiusJet}$ (`RadiusJet.expTan`)**: -/
def expTan : RadiusJet := exp.compZero tan

/-- **Composite Sine-Arctangent $\sin(\arctan x) = \frac{x}{\sqrt{1 + x^2}} \in \mathrm{RadiusJet}$ (`RadiusJet.sinArctan`)**: -/
def sinArctan : RadiusJet := sin.compZero arctan

/-- **Composite Log-Cosine $-\ln(\cos x) = -\ln(1 - (1 - \cos x)) = \int_0^x \tan t\, dt \in \mathrm{RadiusJet}$ (`RadiusJet.negLogCos`)**: -/
def negLogCos : RadiusJet := logOneMinusX.compZero (one.sub cos)

/-- Homogeneous Cauchy convolution bound: if $|U_i| \le B^i$ and $|V_i| \le B^i$ for all $i \le k$
    (with $B \ge 0$), then the partial Cauchy sum of $r \le k + 1$ terms satisfies
    $|(\mathrm{cauchyConvAux}\; U\; V\; k\; r).\mathrm{val}| \le r \cdot B^k$. -/
theorem homog_convAux_bound (U V : Jet) (B : Rat) (hB : 0 ≤ B) (k : Nat)
    (hU : ∀ i ≤ k, |(U.coeff i).val| ≤ B ^ i)
    (hV : ∀ i ≤ k, |(V.coeff i).val| ≤ B ^ i) :
    ∀ r ≤ k + 1,
      |(Jet.cauchyConvAux U V k r).val| ≤ (r : Rat) * B ^ k
  | 0, _ => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_zero, abs_zero]
    simp
  | j + 1, hj => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_add, Q.val_mul]
    have h_tri := abs_add_le' (Jet.cauchyConvAux U V k j).val ((U.coeff j).val * (V.coeff (k - j)).val)
    have ih := homog_convAux_bound U V B hB k hU hV j (by omega)
    rw [abs_mul] at h_tri
    have hUj := hU j (by omega)
    have hVkj := hV (k - j) (by omega)
    have h_prod : |(U.coeff j).val| * |(V.coeff (k - j)).val| ≤ B ^ j * B ^ (k - j) :=
      mul_le_mul hUj hVkj (abs_nonneg _) (by positivity)
    have h_pow : B ^ j * B ^ (k - j) = B ^ k := by
      rw [← pow_add]
      congr 1
      omega
    rw [h_pow] at h_prod
    have h_sum : (j : Rat) * B ^ k + B ^ k = ((j + 1 : Nat) : Rat) * B ^ k := by
      push_cast; ring
    linarith

/-- Full homogeneous Cauchy product bound at degree $k$:
    $|((U.\mathrm{mul}\; V).\mathrm{coeff}\; k).\mathrm{val}| \le (k + 1) \cdot B^k$. -/
theorem homog_mul_coeff_bound (U V : Jet) (B : Rat) (hB : 0 ≤ B) (k : Nat)
    (hU : ∀ i ≤ k, |(U.coeff i).val| ≤ B ^ i)
    (hV : ∀ i ≤ k, |(V.coeff i).val| ≤ B ^ i) :
    |((U.mul V).coeff k).val| ≤ ((k + 1 : Nat) : Rat) * B ^ k :=
  homog_convAux_bound U V B hB k hU hV (k + 1) (le_refl _)

/-- For any `F : RadiusJet`, $|F_k| \le \frac{1}{2} (2^{F.M + F.R + 1})^{k+1}$. -/
theorem forcing_coeff_le_half_pow_succ (F : RadiusJet) (k : Nat) :
    |(F.toJet.coeff k).val| ≤ (1 / 2 : Rat) * ((2 : Rat) ^ (F.M + F.R + 1)) ^ (k + 1) := by
  have hF := F.bound_val k
  have hM : (2 : Rat) ^ F.M ≤ (2 : Rat) ^ (F.M + F.R) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hR_base : (2 : Rat) ^ F.R ≤ (2 : Rat) ^ (F.M + F.R + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hR : ((2 : Rat) ^ F.R) ^ k ≤ ((2 : Rat) ^ (F.M + F.R + 1)) ^ k :=
    pow_le_pow_left₀ (by positivity) hR_base k
  have h_prod : (2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ k ≤
      (2 : Rat) ^ (F.M + F.R) * ((2 : Rat) ^ (F.M + F.R + 1)) ^ k :=
    mul_le_mul hM hR (by positivity) (by positivity)
  have h_id : (2 : Rat) ^ (F.M + F.R) * ((2 : Rat) ^ (F.M + F.R + 1)) ^ k =
      (1 / 2 : Rat) * ((2 : Rat) ^ (F.M + F.R + 1)) ^ (k + 1) := by
    rw [pow_succ' ((2 : Rat) ^ (F.M + F.R + 1)) k, pow_succ (2 : Rat) (F.M + F.R)]
    ring
  linarith

/-- **Convolution–Integration $(k + 1)$-Cancellation Lemma (`integ_forcingAddSq_succ_bound`)**:
    When integrating $F + Y^2$ for `F : RadiusJet`, the division by $k + 1$ in $\mathcal{I}$ cancels
    the $(k + 1)$-term growth of the Cauchy product $(Y \cdot Y)_k$: if $|Y_i| \le B^i$ for $i \le k$
    with $B = 2^{F.M + F.R + 1}$, then $|\mathcal{I}(F + Y^2)_{k+1}| \le B^{k+1}$. -/
theorem integ_forcingAddSq_succ_bound (F : RadiusJet) (Y : Jet) (k : Nat)
    (hY : ∀ i ≤ k, |(Y.coeff i).val| ≤ ((2 : Rat) ^ (F.M + F.R + 1)) ^ i) :
    |(((F.toJet.add (Y.mul Y)).integ).coeff (k + 1)).val| ≤
      ((2 : Rat) ^ (F.M + F.R + 1)) ^ (k + 1) := by
  let B : Rat := (2 : Rat) ^ (F.M + F.R + 1)
  change |(((F.toJet.add (Y.mul Y)).integ).coeff (k + 1)).val| ≤ B ^ (k + 1)
  dsimp [Jet.integ, Jet.add]
  have hk_pos : 0 < k + 1 := Nat.succ_pos k
  have hk_num : (Q.ofNat (k + 1)).num ≠ 0 := by
    unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hk_pos)
  have hk_rat : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
  rw [Q.val_div _ _ hk_num, Q.val_add, Q.val_ofNat, abs_div, abs_of_pos hk_rat, div_le_iff₀ hk_rat]
  have h_tri := abs_add_le' (F.toJet.coeff k).val ((Y.mul Y).coeff k).val
  have hB2 : (2 : Rat) ≤ B := by
    dsimp [B]
    have h1 : (2 : Rat) = (2 : Rat) ^ 1 := by ring
    rw [h1]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h_sq := homog_mul_coeff_bound Y Y B (by positivity) k hY hY
  have hFk : |(F.toJet.coeff k).val| ≤ (1 / 2 : Rat) * B ^ (k + 1) :=
    forcing_coeff_le_half_pow_succ F k
  have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by exact_mod_cast hk_pos
  have hBk1_pos : (0 : Rat) ≤ (1 / 2 : Rat) * B ^ (k + 1) := by positivity
  have hF_le : (1 / 2 : Rat) * B ^ (k + 1) ≤ ((k + 1 : Nat) : Rat) * ((1 / 2 : Rat) * B ^ (k + 1)) := by
    have := mul_le_mul_of_nonneg_right hk1_ge hBk1_pos
    linarith
  have hBk_le : B ^ k ≤ (1 / 2 : Rat) * B ^ (k + 1) := by
    rw [pow_succ' B k]
    have hBk_pos : (0 : Rat) ≤ B ^ k := by positivity
    have h_m := mul_le_mul_of_nonneg_right hB2 hBk_pos
    linarith
  have h_sq_le : ((k + 1 : Nat) : Rat) * B ^ k ≤
      ((k + 1 : Nat) : Rat) * ((1 / 2 : Rat) * B ^ (k + 1)) :=
    mul_le_mul_of_nonneg_left hBk_le (by positivity)
  linarith

/-- Primitive-recursive Picard iterates for the general nonlinear Riccati ODE
    $y'(x) = F(x) + y(x)^2,\; y(0) = 0$:
    $Y^{(0)} = 0$ and $Y^{(m+1)} = \mathcal{I}(F + Y^{(m)} \cdot Y^{(m)})$. -/
def riccatiODEIter (F : Jet) : Nat → Jet
  | 0 => Jet.zero
  | m + 1 => (F.add ((riccatiODEIter F m).mul (riccatiODEIter F m))).integ

/-- Exact Taylor jet of the nonlinear Riccati ODE $y'(x) = F(x) + y(x)^2,\; y(0) = 0$,
    extracted at the diagonal `riccatiODEIter F n`. -/
def _root_.HAomega.Jet.riccatiODE (F : Jet) : Jet :=
  ⟨fun n ↦ (riccatiODEIter F n).coeff n⟩

theorem zero_coeff_eq (n : Nat) : Jet.zero.coeff n = Q.zero := by
  cases n <;> rfl

/-- Uniform Cauchy–Hadamard bound on `riccatiODEIter F.toJet m` for all $m, n \in \mathbb{N}$. -/
theorem riccatiODEIter_bound (F : RadiusJet) : ∀ (m n : Nat),
    |((riccatiODEIter F.toJet m).coeff n).val| ≤ ((2 : Rat) ^ (F.M + F.R + 1)) ^ n
  | 0, n => by
    dsimp [riccatiODEIter]
    rw [zero_coeff_eq, Q.val_zero, abs_zero]
    positivity
  | m + 1, 0 => by
    dsimp [riccatiODEIter, Jet.integ]
    rw [Q.val_zero, abs_zero, pow_zero]
    norm_num
  | m + 1, k + 1 => by
    dsimp [riccatiODEIter]
    exact integ_forcingAddSq_succ_bound F (riccatiODEIter F.toJet m) k
      (fun i _ ↦ riccatiODEIter_bound F m i)

/-- **Nonlinear Riccati ODE Closure in `RadiusJet` (`RadiusJet.riccatiODE`)**:
    For any forcing jet `F : RadiusJet`, the solution of the nonlinear initial-value problem
    $y'(x) = F(x) + y(x)^2,\; y(0) = 0$ inhabits `RadiusJet` with $M = 0$ and $R = F.M + F.R + 1$
    (and hence embeds into `E1` via `(F.riccatiODE).toE1 : E1`)! -/
def riccatiODE (F : RadiusJet) : RadiusJet where
  toJet := F.toJet.riccatiODE
  M := 0
  R := F.M + F.R + 1
  bound n := by
    rw [bound_iff_val, pow_zero, one_mul]
    exact riccatiODEIter_bound F n n

/-- Primitive-recursive Picard iterates for the autonomous quadratic blow-up ODE
    $y'(x) = y(x)^2,\; y(0) = 1$:
    $Y^{(0)} = 1$ and $Y^{(m+1)} = 1 + \mathcal{I}(Y^{(m)} \cdot Y^{(m)})$. -/
def quadBlowupODEIter : Nat → Jet
  | 0 => one.toJet
  | m + 1 => one.toJet.add ((quadBlowupODEIter m).mul (quadBlowupODEIter m)).integ

/-- Uniform Cauchy–Hadamard bound $|(quadBlowupODEIter m)_n| \le 1$ for all $m, n \in \mathbb{N}$
    via exact $(k + 1)$-cancellation between Cauchy convolution and integration! -/
theorem quadBlowupODEIter_bound : ∀ (m n : Nat),
    |((quadBlowupODEIter m).coeff n).val| ≤ 1
  | 0, n => by
    have h := one.bound_val n
    simpa [quadBlowupODEIter, one, ofAnalyticJet, AnalyticJet.divPow] using h
  | m + 1, 0 => by
    dsimp [quadBlowupODEIter, one, ofAnalyticJet, AnalyticJet.divPow, Jet.divPow,
           Jet.add, Jet.integ, fact]
    have h1_num : (Q.ofNat 1).num ≠ 0 := by decide
    rw [Q.val_add, Q.val_div _ _ h1_num, Q.val_ofNat, Q.val_zero]
    norm_num
  | m + 1, k + 1 => by
    dsimp [quadBlowupODEIter, one, ofAnalyticJet, AnalyticJet.divPow, Jet.divPow,
           Jet.add, Jet.integ]
    have hk_pos : 0 < k + 1 := Nat.succ_pos k
    have hk_num : (Q.ofNat (k + 1)).num ≠ 0 := by
      unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hk_pos)
    have hk_rat : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
    rw [Q.val_add, Q.val_zero, zero_add, Q.val_div _ _ hk_num, Q.val_ofNat,
        abs_div, abs_of_pos hk_rat, div_le_iff₀ hk_rat, one_mul]
    have h_sq := homog_mul_coeff_bound (quadBlowupODEIter m) (quadBlowupODEIter m) 1 (by norm_num) k
      (fun i _ ↦ by simpa using quadBlowupODEIter_bound m i)
      (fun i _ ↦ by simpa using quadBlowupODEIter_bound m i)
    simpa using h_sq

/-- **Autonomous Quadratic Blow-Up ODE Solution in `RadiusJet` (`RadiusJet.quadBlowupODE`)**:
    Certifies that the Picard solution of $y'(x) = y(x)^2,\; y(0) = 1$ inhabits `RadiusJet`
    with $M = 0, R = 0$ (and hence embeds into `E1` via `quadBlowupODE.toE1 : E1`)! -/
def quadBlowupODE : RadiusJet where
  toJet := ⟨fun n ↦ (quadBlowupODEIter n).coeff n⟩
  M := 0
  R := 0
  bound n := by
    rw [bound_iff_val]
    have h := quadBlowupODEIter_bound n n
    simpa using h

/-- Primitive-recursive Picard iterates for the 2D coupled nonlinear Duffing oscillator
    $u'(x) = v(x),\; v'(x) = -u(x) - u(x)^2,\; (u(0), v(0)) = (1, 0)$. -/
def duffingODEIter : Nat → Jet × Jet
  | 0 => (one.toJet, Jet.zero)
  | m + 1 =>
      let uv := duffingODEIter m
      (one.toJet.add uv.2.integ,
       ((Jet.zero.sub uv.1).sub (uv.1.mul uv.1)).integ)

/-- Uniform Cauchy–Hadamard bound $|u^{(m)}_n| \le 2^n$ and $|v^{(m)}_n| \le 2^n$ for all $m, n \in \mathbb{N}$
    on the coupled 2D nonlinear Duffing oscillator! -/
theorem duffingODEIter_bound : ∀ (m n : Nat),
    |(((duffingODEIter m).1).coeff n).val| ≤ ((2 : Rat) ^ 1) ^ n ∧
    |(((duffingODEIter m).2).coeff n).val| ≤ ((2 : Rat) ^ 1) ^ n
  | 0, n => by
    refine ⟨?_, ?_⟩
    · have h1 := one.bound_val n
      have h_one : |(one.toJet.coeff n).val| ≤ 1 := by
        simpa [one, ofAnalyticJet, AnalyticJet.divPow] using h1
      have h_pow : (1 : Rat) ≤ ((2 : Rat) ^ 1) ^ n := one_le_pow₀ (by norm_num)
      dsimp [duffingODEIter]
      linarith
    · dsimp [duffingODEIter]
      rw [zero_coeff_eq, Q.val_zero, abs_zero]
      positivity
  | m + 1, 0 => by
    refine ⟨?_, ?_⟩
    · dsimp [duffingODEIter, one, ofAnalyticJet, AnalyticJet.divPow, Jet.divPow,
             Jet.add, Jet.integ, fact]
      have h1_num : (Q.ofNat 1).num ≠ 0 := by decide
      rw [Q.val_add, Q.val_div _ _ h1_num, Q.val_ofNat, Q.val_zero]
      norm_num
    · dsimp [duffingODEIter, Jet.integ]
      rw [Q.val_zero, abs_zero]
      norm_num
  | m + 1, k + 1 => by
    have hk_pos : 0 < k + 1 := Nat.succ_pos k
    have hk_num : (Q.ofNat (k + 1)).num ≠ 0 := by
      unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hk_pos)
    have hk_rat : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
    have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by exact_mod_cast hk_pos
    refine ⟨?_, ?_⟩
    · dsimp [duffingODEIter, one, ofAnalyticJet, AnalyticJet.divPow, Jet.divPow,
             Jet.add, Jet.integ]
      rw [Q.val_add, Q.val_zero, zero_add, Q.val_div _ _ hk_num, Q.val_ofNat,
          abs_div, abs_of_pos hk_rat, div_le_iff₀ hk_rat]
      have hv := (duffingODEIter_bound m k).2
      have h_pow : ((2 : Rat) ^ 1) ^ k ≤ ((2 : Rat) ^ 1) ^ (k + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h_mul : ((2 : Rat) ^ 1) ^ (k + 1) * 1 ≤ ((2 : Rat) ^ 1) ^ (k + 1) * ((k + 1 : Nat) : Rat) :=
        mul_le_mul_of_nonneg_left hk1_ge (by positivity)
      linarith
    · dsimp [duffingODEIter, Jet.integ, Jet.sub]
      rw [Q.val_div _ _ hk_num, Q.val_sub, Q.val_sub, zero_coeff_eq, Q.val_zero, zero_sub,
          Q.val_ofNat, abs_div, abs_of_pos hk_rat, div_le_iff₀ hk_rat]
      let u := (duffingODEIter m).1
      have h_eq : -(u.coeff k).val - ((u.mul u).coeff k).val =
          -((u.coeff k).val + ((u.mul u).coeff k).val) := by ring
      rw [h_eq, abs_neg]
      have h_tri := abs_add_le' (u.coeff k).val ((u.mul u).coeff k).val
      have hu := (duffingODEIter_bound m k).1
      have h_sq := homog_mul_coeff_bound u u ((2 : Rat) ^ 1) (by norm_num) k
        (fun i _ ↦ (duffingODEIter_bound m i).1)
        (fun i _ ↦ (duffingODEIter_bound m i).1)
      have h_uk_le : ((2 : Rat) ^ 1) ^ k ≤ ((k + 1 : Nat) : Rat) * ((2 : Rat) ^ 1) ^ k := by
        have := mul_le_mul_of_nonneg_right hk1_ge (by positivity : (0 : Rat) ≤ ((2 : Rat) ^ 1) ^ k)
        linarith
      have h_rhs : ((2 : Rat) ^ 1) ^ (k + 1) * ((k + 1 : Nat) : Rat) =
          2 * (((k + 1 : Nat) : Rat) * ((2 : Rat) ^ 1) ^ k) := by
        rw [pow_succ ((2 : Rat) ^ 1) k]
        ring
      linarith

/-- **2D Nonlinear Duffing Position Trajectory $u(x) \in \mathrm{RadiusJet}$ (`RadiusJet.duffingU`)**:
    Inhabits `RadiusJet` with $M = 0, R = 1$ (and embeds into `E1` via `duffingU.toE1 : E1`)! -/
def duffingU : RadiusJet where
  toJet := ⟨fun n ↦ ((duffingODEIter n).1).coeff n⟩
  M := 0
  R := 1
  bound n := by
    rw [bound_iff_val, pow_zero, one_mul]
    exact (duffingODEIter_bound n n).1

/-- **2D Nonlinear Duffing Velocity Trajectory $v(x) \in \mathrm{RadiusJet}$ (`RadiusJet.duffingV`)**:
    Inhabits `RadiusJet` with $M = 0, R = 1$ (and embeds into `E1` via `duffingV.toE1 : E1`)! -/
def duffingV : RadiusJet where
  toJet := ⟨fun n ↦ ((duffingODEIter n).2).coeff n⟩
  M := 0
  R := 1
  bound n := by
    rw [bound_iff_val, pow_zero, one_mul]
    exact (duffingODEIter_bound n n).2

/-! ### 6b.2. Full `E1` Embedding for `RadiusJet` (`RadiusJet.toE1`) -/

/-- Multiplying the $n$-th coefficient of `G : RadiusJet` by $(n + 1)$ produces a `RadiusJet`
    with parameters $(G.M + 1,\; G.R + 1)$. -/
def mulIdxSucc (G : RadiusJet) : RadiusJet where
  toJet := ⟨fun n ↦ Q.mul (Q.ofNat (n + 1)) (G.toJet.coeff n)⟩
  M := G.M + 1
  R := G.R + 1
  bound n := by
    rw [bound_iff_val]
    dsimp
    rw [Q.val_mul, Q.val_ofNat, abs_mul]
    have hn_pos : (0 : Rat) ≤ ((n + 1 : Nat) : Rat) := by positivity
    rw [abs_of_nonneg hn_pos]
    have hG := G.bound_val n
    have hn_pow := AnalyticJet.nat_succ_le_two_mul_pow2 n
    have h_step : ((n + 1 : Nat) : Rat) * |(G.toJet.coeff n).val| ≤
        (2 * (2 : Rat) ^ n) * ((2 : Rat) ^ G.M * ((2 : Rat) ^ G.R) ^ n) :=
      mul_le_mul hn_pow hG (abs_nonneg _) (by positivity)
    have h_eq : (2 * (2 : Rat) ^ n) * ((2 : Rat) ^ G.M * ((2 : Rat) ^ G.R) ^ n) =
        (2 : Rat) ^ (G.M + 1) * ((2 : Rat) ^ (G.R + 1)) ^ n := by
      rw [pow_succ (2 : Rat) G.M, pow_succ (2 : Rat) G.R, mul_pow]
      ring
    linarith

/-- Geometric error accumulation on a disk $|r.\mathrm{val}| \le 2^{-(G.R + 1)}$ for any `G : RadiusJet`. -/
theorem geom_accum_disk_step (G : RadiusJet) (r : Q)
    (hr : |r.val| ≤ 1 / (2 : Rat) ^ (G.R + 1))
    (W : Rat) (hW : 0 ≤ W)
    (E : Nat → Rat) (hE0 : E 0 ≤ 0)
    (hStep : ∀ i : Nat, E (i + 1) ≤ E i + |(G.toJet.coeff i).val| * |r.val| ^ i * W) :
    ∀ n : Nat, E n ≤ (2 : Rat) ^ (G.M + 1) * (1 - 1 / (2 : Rat) ^ n) * W
  | 0 => by simpa using hE0
  | i + 1 => by
    have ih := geom_accum_disk_step G r hr W hW E hE0 hStep i
    have h_step := hStep i
    have h_c := G.term_telescope_disk r hr i
    have h_cW : |(G.toJet.coeff i).val| * |r.val| ^ i * W ≤
        (2 : Rat) ^ (G.M + 1) * (1 / (2 : Rat) ^ i - 1 / (2 : Rat) ^ (i + 1)) * W :=
      mul_le_mul_of_nonneg_right h_c hW
    linarith

theorem geom_accum_disk_bound (G : RadiusJet) (r : Q)
    (hr : |r.val| ≤ 1 / (2 : Rat) ^ (G.R + 1))
    (W : Rat) (hW : 0 ≤ W)
    (E : Nat → Rat) (hE0 : E 0 ≤ 0)
    (hStep : ∀ i : Nat, E (i + 1) ≤ E i + |(G.toJet.coeff i).val| * |r.val| ^ i * W) (n : Nat) :
    E n ≤ (2 : Rat) ^ (G.M + 1) * W := by
  have h1 := geom_accum_disk_step G r hr W hW E hE0 hStep n
  have h_pos : (0 : Rat) ≤ (2 : Rat) ^ (G.M + 1) * (1 / (2 : Rat) ^ n) * W := by positivity
  linarith

/-- Elementary Lipschitz bound on $x^{j+1} - y^{j+1}$ on any disk $|x|, |y| \le r$:
    $$|x^{j+1} - y^{j+1}| \le (j + 1) \cdot r^j \cdot |x - y|.$$ -/
theorem pow_succ_sub_pow_succ_le_disk (x y r : Rat) (hr : 0 ≤ r) (hx : |x| ≤ r) (hy : |y| ≤ r) :
    ∀ j : Nat, |x ^ (j + 1) - y ^ (j + 1)| ≤ ((j + 1 : Nat) : Rat) * r ^ j * |x - y|
  | 0 => by simp
  | j + 1 => by
    have ih := pow_succ_sub_pow_succ_le_disk x y r hr hx hy j
    have h_id : x ^ (j + 2) - y ^ (j + 2) =
        (x - y) * x ^ (j + 1) + y * (x ^ (j + 1) - y ^ (j + 1)) := by ring
    rw [h_id]
    have h_tri := abs_add_le' ((x - y) * x ^ (j + 1)) (y * (x ^ (j + 1) - y ^ (j + 1)))
    rw [abs_mul, abs_mul, abs_pow] at h_tri
    have hx_pow : |x| ^ (j + 1) ≤ r ^ (j + 1) := pow_le_pow_left₀ (abs_nonneg _) hx (j + 1)
    have h1 : |x - y| * |x| ^ (j + 1) ≤ r ^ (j + 1) * |x - y| := by
      have := mul_le_mul_of_nonneg_left hx_pow (abs_nonneg (x - y))
      linarith
    have h2 : |y| * |x ^ (j + 1) - y ^ (j + 1)| ≤
        r * (((j + 1 : Nat) : Rat) * r ^ j * |x - y|) :=
      mul_le_mul hy ih (abs_nonneg _) (by positivity)
    have h2_eq : r * (((j + 1 : Nat) : Rat) * r ^ j * |x - y|) =
        ((j + 1 : Nat) : Rat) * r ^ (j + 1) * |x - y| := by
      rw [pow_succ r j]; ring
    have h_sum : r ^ (j + 1) * |x - y| + ((j + 1 : Nat) : Rat) * r ^ (j + 1) * |x - y| =
        ((j + 1 + 1 : Nat) : Rat) * r ^ (j + 1) * |x - y| := by
      push_cast; ring
    linarith

/-- Uniform Lipschitz bound for `evalPoly` of `F : RadiusJet` on the disk
    $|x|, |y| \le r \le 2^{-(F.R + 2)}$ across all degrees $n \in \mathbb{N}$. -/
theorem evalPoly_lip_disk (F : RadiusJet) (r x y : Q)
    (hr : |r.val| ≤ 1 / (2 : Rat) ^ (F.R + 2))
    (hx : |x.val| ≤ |r.val|) (hy : |y.val| ≤ |r.val|) :
    ∀ n : Nat,
      |(F.toJet.evalPoly n x).val - (F.toJet.evalPoly n y).val| ≤
        (2 : Rat) ^ (F.deriv.M + 1) * |x.val - y.val|
  | 0 => by
    rw [F.toJet.evalPoly_zero, F.toJet.evalPoly_zero, sub_self, abs_zero]
    positivity
  | n + 1 => by
    let E : Nat → Rat := fun m ↦
      |(F.toJet.evalPoly (m + 1) x).val - (F.toJet.evalPoly (m + 1) y).val|
    refine geom_accum_disk_bound F.deriv r hr |x.val - y.val| (abs_nonneg _) E ?_ ?_ n
    · dsimp [E]
      rw [F.toJet.evalPoly_one, F.toJet.evalPoly_one, sub_self, abs_zero]
    · intro i
      dsimp [E]
      have h_id : (F.toJet.evalPoly (i + 2) x).val - (F.toJet.evalPoly (i + 2) y).val =
          ((F.toJet.evalPoly (i + 1) x).val - (F.toJet.evalPoly (i + 1) y).val) +
          (F.toJet.coeff (i + 1)).val * (x.val ^ (i + 1) - y.val ^ (i + 1)) := by
        rw [F.toJet.evalPoly_succ (i + 1) x, F.toJet.evalPoly_succ (i + 1) y]
        ring
      rw [h_id]
      have h_tri := abs_add_le'
        ((F.toJet.evalPoly (i + 1) x).val - (F.toJet.evalPoly (i + 1) y).val)
        ((F.toJet.coeff (i + 1)).val * (x.val ^ (i + 1) - y.val ^ (i + 1)))
      rw [abs_mul] at h_tri
      have h_pow := pow_succ_sub_pow_succ_le_disk x.val y.val |r.val| (abs_nonneg _) hx hy i
      have h_mul : |(F.toJet.coeff (i + 1)).val| * |x.val ^ (i + 1) - y.val ^ (i + 1)| ≤
          |(F.toJet.coeff (i + 1)).val| * (((i + 1 : Nat) : Rat) * |r.val| ^ i * |x.val - y.val|) :=
        mul_le_mul_of_nonneg_left h_pow (abs_nonneg _)
      have h_deriv : |(F.deriv.toJet.coeff i).val| =
          |(F.toJet.coeff (i + 1)).val| * ((i + 1 : Nat) : Rat) := by
        dsimp [RadiusJet.deriv, Jet.deriv]
        rw [Q.val_mul, Q.val_ofNat, abs_mul,
            abs_of_nonneg (by positivity : (0 : Rat) ≤ ((i + 1 : Nat) : Rat))]
        ring
      have h_assoc : |(F.toJet.coeff (i + 1)).val| *
          (((i + 1 : Nat) : Rat) * |r.val| ^ i * |x.val - y.val|) =
          |(F.deriv.toJet.coeff i).val| * |r.val| ^ i * |x.val - y.val| := by
        rw [h_deriv]; ring
      linarith

/-- Radius-weighted second-order Taylor remainder bound on any disk $|x|, |x + h| \le r$:
    $$r \cdot |(x + h)^{j+1} - x^{j+1} - (j + 1) h x^j| \le (j + 1)^2 \cdot r^j \cdot |h|^2.$$ -/
theorem mul_radius_pow_lin_rem_le_disk (x h r : Rat) (hr : 0 ≤ r)
    (hx : |x| ≤ r) (hxh : |x + h| ≤ r) :
    ∀ j : Nat,
      r * |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j| ≤
        ((j + 1 : Nat) : Rat) ^ 2 * r ^ j * |h| ^ 2
  | 0 => by
    have h0 : (x + h) ^ 1 - x ^ 1 - ((1 : Nat) : Rat) * h * x ^ 0 = 0 := by ring
    rw [h0, abs_zero, mul_zero]
    positivity
  | j + 1 => by
    have ih := mul_radius_pow_lin_rem_le_disk x h r hr hx hxh j
    have h_id : (x + h) ^ (j + 2) - x ^ (j + 2) - ((j + 2 : Nat) : Rat) * h * x ^ (j + 1) =
        (x + h) * ((x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j) +
        ((j + 1 : Nat) : Rat) * h ^ 2 * x ^ j := by
      push_cast; ring
    rw [h_id]
    have h_tri := abs_add_le'
      ((x + h) * ((x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j))
      (((j + 1 : Nat) : Rat) * h ^ 2 * x ^ j)
    have h_tri_r := mul_le_mul_of_nonneg_left h_tri hr
    rw [mul_add, abs_mul, abs_mul, abs_mul, abs_pow, sq_abs] at h_tri_r
    rw [sq_abs] at ih
    have hx_pow : |x| ^ j ≤ r ^ j := pow_le_pow_left₀ (abs_nonneg _) hx j
    have h1_swap : r * (|x + h| * |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j|) =
        |x + h| * (r * |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j|) := by ring
    have h1_le : |x + h| * (r * |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j|) ≤
        r * (((j + 1 : Nat) : Rat) ^ 2 * r ^ j * h ^ 2) :=
      mul_le_mul hxh ih (by positivity) hr
    have h1_eq : r * (((j + 1 : Nat) : Rat) ^ 2 * r ^ j * h ^ 2) =
        ((j + 1 : Nat) : Rat) ^ 2 * r ^ (j + 1) * h ^ 2 := by
      rw [pow_succ r j]; ring
    have h2 : r * (|((j + 1 : Nat) : Rat)| * h ^ 2 * |x ^ j|) ≤
        ((j + 1 : Nat) : Rat) * r ^ (j + 1) * h ^ 2 := by
      have hj_pos : (0 : Rat) ≤ ((j + 1 : Nat) : Rat) := by positivity
      rw [abs_of_nonneg hj_pos, abs_pow]
      have h_nonneg : (0 : Rat) ≤ r * ((j + 1 : Nat) : Rat) * h ^ 2 := by positivity
      have h_m := mul_le_mul_of_nonneg_left hx_pow h_nonneg
      have h_lhs : r * ((j + 1 : Nat) : Rat) * h ^ 2 * |x| ^ j =
          r * (((j + 1 : Nat) : Rat) * h ^ 2 * |x| ^ j) := by ring
      have h_rhs : r * ((j + 1 : Nat) : Rat) * h ^ 2 * r ^ j =
          ((j + 1 : Nat) : Rat) * r ^ (j + 1) * h ^ 2 := by
        rw [pow_succ r j]; ring
      linarith
    have h3 : ((j + 1 : Nat) : Rat) ^ 2 * r ^ (j + 1) * h ^ 2 +
        ((j + 1 : Nat) : Rat) * r ^ (j + 1) * h ^ 2 ≤
        ((j + 1 + 1 : Nat) : Rat) ^ 2 * r ^ (j + 1) * |h| ^ 2 := by
      rw [sq_abs]
      have hj_pos : (0 : Rat) ≤ ((j + 1 : Nat) : Rat) := by positivity
      have hrj : (0 : Rat) ≤ r ^ (j + 1) * h ^ 2 := by positivity
      have h_sq : ((j + 1 + 1 : Nat) : Rat) ^ 2 =
          ((j + 1 : Nat) : Rat) ^ 2 + 2 * ((j + 1 : Nat) : Rat) + 1 := by
        push_cast; ring
      rw [h_sq]
      nlinarith
    linarith

/-- Difference-quotient form of `mul_radius_pow_lin_rem_le_disk` for $r > 0$ and $h \ne 0$:
    $$\left|\frac{(x + h)^{j+1} - x^{j+1}}{h} - (j + 1) x^j\right| \le (j + 1)^2 \cdot r^j \cdot \frac{|h|}{r}.$$ -/
theorem pow_diff_quot_le_disk (x h r : Rat) (hr : 0 < r)
    (hx : |x| ≤ r) (hxh : |x + h| ≤ r) (hh : h ≠ 0) (j : Nat) :
    |((x + h) ^ (j + 1) - x ^ (j + 1)) / h - ((j + 1 : Nat) : Rat) * x ^ j| ≤
      ((j + 1 : Nat) : Rat) ^ 2 * r ^ j * (|h| / r) := by
  have h_pos : 0 < |h| := abs_pos.mpr hh
  have h_rem := mul_radius_pow_lin_rem_le_disk x h r (le_of_lt hr) hx hxh j
  have h_eq : ((x + h) ^ (j + 1) - x ^ (j + 1)) / h - ((j + 1 : Nat) : Rat) * x ^ j =
      ((x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j) / h := by
    field_simp
  rw [h_eq, abs_div, div_le_iff₀ h_pos]
  have h_div_r := (le_div_iff₀' hr).mpr h_rem
  have h_rhs : ((j + 1 : Nat) : Rat) ^ 2 * r ^ j * |h| ^ 2 / r =
      ((j + 1 : Nat) : Rat) ^ 2 * r ^ j * (|h| / r) * |h| := by
    field_simp
  linarith

/-- Uniform Difference-Quotient bound for `evalPoly` of `F : RadiusJet` on the disk
    $|x|, |x + h| \le r = 2^{-(F.R + 3)}$ across all degrees $n \in \mathbb{N}$. -/
theorem evalPoly_diff_disk (F : RadiusJet) (n : Nat) (r x h : Q)
    (hr_pos : 0 < r.val)
    (hr : |r.val| ≤ 1 / (2 : Rat) ^ (F.R + 3))
    (hx : |x.val| ≤ |r.val|) (hxh : |(Q.add x h).val| ≤ |r.val|) (hnum : h.num ≠ 0) :
    |((Q.div (Q.sub (F.toJet.evalPoly (n + 1) (Q.add x h)) (F.toJet.evalPoly (n + 1) x)) h).val -
        (F.deriv.toJet.evalPoly n x).val)| ≤
      (2 : Rat) ^ (F.deriv.mulIdxSucc.M + 1) * (|h.val| / |r.val|) := by
  have hh_ne : h.val ≠ 0 := by
    unfold Q.val
    exact div_ne_zero (Int.cast_ne_zero.mpr hnum) h.den_cast_ne_zero
  have hr_abs_pos : 0 < |r.val| := abs_pos.mpr (ne_of_gt hr_pos)
  rw [Q.val_add] at hxh
  let E : Nat → Rat := fun m ↦
    |((Q.div (Q.sub (F.toJet.evalPoly (m + 1) (Q.add x h)) (F.toJet.evalPoly (m + 1) x)) h).val -
        (F.deriv.toJet.evalPoly m x).val)|
  refine geom_accum_disk_bound F.deriv.mulIdxSucc r hr (|h.val| / |r.val|) (by positivity) E ?_ ?_ n
  · dsimp [E]
    rw [Q.val_div _ _ hnum, Q.val_sub, F.toJet.evalPoly_one, F.toJet.evalPoly_one,
        F.deriv.toJet.evalPoly_zero, sub_self, zero_div, sub_zero, abs_zero]
  · intro i
    dsimp [E]
    rw [Q.val_div _ _ hnum, Q.val_sub, Q.val_div _ _ hnum, Q.val_sub]
    have h_step_id :
        ((F.toJet.evalPoly (i + 2) (Q.add x h)).val - (F.toJet.evalPoly (i + 2) x).val) / h.val -
          (F.deriv.toJet.evalPoly (i + 1) x).val =
        (((F.toJet.evalPoly (i + 1) (Q.add x h)).val - (F.toJet.evalPoly (i + 1) x).val) / h.val -
          (F.deriv.toJet.evalPoly i x).val) +
        (F.toJet.coeff (i + 1)).val *
          (((x.val + h.val) ^ (i + 1) - x.val ^ (i + 1)) / h.val - ((i + 1 : Nat) : Rat) * x.val ^ i) := by
      rw [F.toJet.evalPoly_succ (i + 1) (Q.add x h), F.toJet.evalPoly_succ (i + 1) x,
          F.deriv.toJet.evalPoly_succ i x, Q.val_add]
      dsimp [RadiusJet.deriv, Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat]
      field_simp
      ring
    rw [h_step_id]
    have h_tri := abs_add_le'
      (((F.toJet.evalPoly (i + 1) (Q.add x h)).val - (F.toJet.evalPoly (i + 1) x).val) / h.val -
        (F.deriv.toJet.evalPoly i x).val)
      ((F.toJet.coeff (i + 1)).val *
        (((x.val + h.val) ^ (i + 1) - x.val ^ (i + 1)) / h.val - ((i + 1 : Nat) : Rat) * x.val ^ i))
    rw [abs_mul] at h_tri
    have h_dq := pow_diff_quot_le_disk x.val h.val |r.val| hr_abs_pos hx hxh hh_ne i
    have h_mul : |(F.toJet.coeff (i + 1)).val| *
        |((x.val + h.val) ^ (i + 1) - x.val ^ (i + 1)) / h.val - ((i + 1 : Nat) : Rat) * x.val ^ i| ≤
        |(F.toJet.coeff (i + 1)).val| * (((i + 1 : Nat) : Rat) ^ 2 * |r.val| ^ i * (|h.val| / |r.val|)) :=
      mul_le_mul_of_nonneg_left h_dq (abs_nonneg _)
    have h_coeff : |(F.deriv.mulIdxSucc.toJet.coeff i).val| =
        |(F.toJet.coeff (i + 1)).val| * ((i + 1 : Nat) : Rat) ^ 2 := by
      dsimp [mulIdxSucc, RadiusJet.deriv, Jet.deriv]
      rw [Q.val_mul, Q.val_mul, Q.val_ofNat, abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : Rat) ≤ ((i + 1 : Nat) : Rat))]
      ring
    have h_assoc : |(F.toJet.coeff (i + 1)).val| *
        (((i + 1 : Nat) : Rat) ^ 2 * |r.val| ^ i * (|h.val| / |r.val|)) =
        |(F.deriv.mulIdxSucc.toJet.coeff i).val| * |r.val| ^ i * (|h.val| / |r.val|) := by
      rw [h_coeff]; ring
    linarith

/-- Uniform continuity modulus $\omega(k) := (F.M + F.R + 1) + 1 + k$ for `RadiusJet.toE1`.
    Defined directly on `(F.M, F.R)` so `#print axioms RadiusJet.omegaE1` is choice-free. -/
def omegaE1 (F : RadiusJet) (k : Nat) : Nat :=
  (F.M + F.R + 1) + 1 + k

/-- Uniform differentiability step modulus $\delta(k) := (F.M + F.R + 2) + 1 + (F.R + 3) + k$
    for `RadiusJet.toE1`. Defined directly on `(F.M, F.R)` so `#print axioms RadiusJet.deltaE1` is choice-free. -/
def deltaE1 (F : RadiusJet) (k : Nat) : Nat :=
  ((F.M + F.R + 1 + 1) + 1 + (F.R + 3)) + k

/-- **Full `E1` Embedding for `RadiusJet` (`RadiusJet.toE1`)**:
    Every Cauchy–Hadamard jet `F : RadiusJet` (including $\frac{1}{1-x}$, $\ln(1-x)$, $\sec x$, $\tan x$, $\arctan x$)
    is a certified `E1` inhabitant on its dyadic disk $[-2^{-(F.R + 3)}, 2^{-(F.R + 3)}]$ with
    `ev := F.toJet.evalPoly`, `cm k := F.M + 1 + k`, `ω := F.omegaE1`, `δ := F.deltaE1`, `dq _ _ := 1`,
    and approximating derivative `fun n x ↦ F.deriv.toJet.evalPoly (n - 1) x`! -/
def toE1 (F : RadiusJet) : E1 where
  a := Q.neg (D.toQ (D.pow2neg (F.R + 3)))
  b := D.toQ (D.pow2neg (F.R + 3))
  ev := F.toJet.evalPoly
  cm k := F.M + 1 + k
  ω := F.omegaE1
  δ := F.deltaE1
  dq _ _ := 1
  ivl := by
    rw [Q.ltN_eq_one_iff, Q.val_neg, toQ_pow2neg_val]
    have h_pos : (0 : Rat) < 1 / (2 : Rat) ^ (F.R + 3) := by positivity
    linarith
  conv := by
    intro k n m hn hnm x hxa hxb
    rw [Qle_eq_true_iff, Q.val_neg, toQ_pow2neg_val] at hxa
    rw [Qle_eq_true_iff, toQ_pow2neg_val] at hxb
    have hx3 : |x.val| ≤ 1 / (2 : Rat) ^ (F.R + 3) := abs_le.mpr ⟨hxa, hxb⟩
    have h_r_le : (1 : Rat) / (2 : Rat) ^ (F.R + 3) ≤ 1 / (2 : Rat) ^ (F.R + 1) :=
      inv_pow_le (by omega)
    have hx : |x.val| ≤ 1 / (2 : Rat) ^ (F.R + 1) := le_trans hx3 h_r_le
    have hm_eq : m = n + (m - n) := (Nat.add_sub_of_le hnm).symm
    have h_step := F.evalPoly_cauchy_step x hx n (m - n)
    rw [← hm_eq] at h_step
    have h_pos : (0 : Rat) ≤ (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ m) := by positivity
    have h_le1 : |(F.toJet.evalPoly n x).val - (F.toJet.evalPoly m x).val| ≤
        (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ n) := by linarith
    have h_inv : (1 : Rat) / (2 : Rat) ^ n ≤ 1 / (2 : Rat) ^ (F.M + 1 + k) :=
      inv_pow_le hn
    have h_le2 : (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ n) ≤
        (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ (F.M + 1 + k)) :=
      mul_le_mul_of_nonneg_left h_inv (by positivity)
    have h_eq : (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ (F.M + 1 + k)) =
        1 / (2 : Rat) ^ k := by
      rw [pow_add (2 : Rat) (F.M + 1) k]
      field_simp
    rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val]
    linarith
  cont := by
    intro k n x y _ hxa hxb hya hyb hxy
    rw [Qle_eq_true_iff, Q.val_neg, toQ_pow2neg_val] at hxa hya
    rw [Qle_eq_true_iff, toQ_pow2neg_val] at hxb hyb
    rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val] at hxy ⊢
    let r : Q := D.toQ (D.pow2neg (F.R + 3))
    have hr_val : |r.val| = 1 / (2 : Rat) ^ (F.R + 3) := by
      dsimp [r]
      rw [toQ_pow2neg_val, abs_of_pos (by positivity)]
    have hr_le : |r.val| ≤ 1 / (2 : Rat) ^ (F.R + 2) := by
      rw [hr_val]
      exact inv_pow_le (by omega)
    have hx : |x.val| ≤ |r.val| := by rw [hr_val]; exact abs_le.mpr ⟨hxa, hxb⟩
    have hy : |y.val| ≤ |r.val| := by rw [hr_val]; exact abs_le.mpr ⟨hya, hyb⟩
    have h_lip := F.evalPoly_lip_disk r x y hr_le hx hy n
    have h_mul : (2 : Rat) ^ (F.deriv.M + 1) * |x.val - y.val| ≤
        (2 : Rat) ^ (F.deriv.M + 1) * (1 / (2 : Rat) ^ (F.omegaE1 k)) :=
      mul_le_mul_of_nonneg_left hxy (by positivity)
    have h_eq : (2 : Rat) ^ (F.deriv.M + 1) * (1 / (2 : Rat) ^ (F.omegaE1 k)) =
        1 / (2 : Rat) ^ k := by
      change (2 : Rat) ^ (F.deriv.M + 1) * (1 / (2 : Rat) ^ ((F.deriv.M + 1) + k)) =
        1 / (2 : Rat) ^ k
      rw [pow_add (2 : Rat) (F.deriv.M + 1) k]
      field_simp
    linarith
  diff := ⟨fun n x ↦ F.deriv.toJet.evalPoly (n - 1) x, by
    intro k n x h hdq hxa hxb hha hhb hnum hstep
    rw [Qle_eq_true_iff, Q.val_neg, toQ_pow2neg_val] at hxa hha
    rw [Qle_eq_true_iff, toQ_pow2neg_val] at hxb hhb
    rw [Qle_eq_true_iff, Q.val_abs, toQ_pow2neg_val] at hstep
    rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val]
    let r : Q := D.toQ (D.pow2neg (F.R + 3))
    have hr_pos : 0 < r.val := by dsimp [r]; rw [toQ_pow2neg_val]; positivity
    have hr_val : |r.val| = 1 / (2 : Rat) ^ (F.R + 3) := by
      dsimp [r]; rw [toQ_pow2neg_val, abs_of_pos (by positivity)]
    have hx : |x.val| ≤ |r.val| := by rw [hr_val]; exact abs_le.mpr ⟨hxa, hxb⟩
    have hxh : |(Q.add x h).val| ≤ |r.val| := by rw [hr_val]; exact abs_le.mpr ⟨hha, hhb⟩
    have hn_eq : (n - 1) + 1 = n := Nat.sub_add_cancel hdq
    have h_dq := F.evalPoly_diff_disk (n - 1) r x h hr_pos (le_of_eq hr_val) hx hxh hnum
    rw [hn_eq] at h_dq
    have h_div_r : |h.val| / |r.val| = (2 : Rat) ^ (F.R + 3) * |h.val| := by
      rw [hr_val]; field_simp
    rw [h_div_r] at h_dq
    have h_combine : (2 : Rat) ^ (F.deriv.mulIdxSucc.M + 1) * ((2 : Rat) ^ (F.R + 3) * |h.val|) =
        (2 : Rat) ^ (F.deriv.mulIdxSucc.M + 1 + (F.R + 3)) * |h.val| := by
      rw [pow_add (2 : Rat) (F.deriv.mulIdxSucc.M + 1) (F.R + 3)]; ring
    rw [h_combine] at h_dq
    have h_mul : (2 : Rat) ^ (F.deriv.mulIdxSucc.M + 1 + (F.R + 3)) * |h.val| ≤
        (2 : Rat) ^ (F.deriv.mulIdxSucc.M + 1 + (F.R + 3)) * (1 / (2 : Rat) ^ (F.deltaE1 k)) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    have h_eq : (2 : Rat) ^ (F.deriv.mulIdxSucc.M + 1 + (F.R + 3)) *
        (1 / (2 : Rat) ^ (F.deltaE1 k)) = 1 / (2 : Rat) ^ k := by
      change (2 : Rat) ^ (F.deriv.mulIdxSucc.M + 1 + (F.R + 3)) *
          (1 / (2 : Rat) ^ ((F.deriv.mulIdxSucc.M + 1 + (F.R + 3)) + k)) =
        1 / (2 : Rat) ^ k
      rw [pow_add (2 : Rat) (F.deriv.mulIdxSucc.M + 1 + (F.R + 3)) k]
      field_simp
    linarith⟩

end RadiusJet

/-- Elementary factorial growth lemma: $(B + 1)^d \le (B + d)!$ for all $B, d \in \mathbb{N}$. -/
theorem pow_succ_le_fact_add (B : Nat) : ∀ d : Nat,
    (B + 1) ^ d ≤ fact (B + d)
  | 0 => by
    dsimp
    exact fact_pos B
  | d + 1 => by
    have ih := pow_succ_le_fact_add B d
    have h_le : B + 1 ≤ B + d + 1 := by omega
    calc (B + 1) ^ (d + 1) = (B + 1) ^ d * (B + 1) := Nat.pow_succ (B + 1) d
      _ ≤ fact (B + d) * (B + d + 1) := Nat.mul_le_mul ih h_le
      _ = (B + d + 1) * fact (B + d) := Nat.mul_comm _ _
      _ = fact (B + (d + 1)) := by rw [← Nat.add_assoc]; rfl

/-- **Theorem ($\frac{1}{1 - x}$ Is Not of Exponential Type)**:
    For every pair of exponents $(M, R)$, there exists an explicit degree $n$ at which the
    geometric series $\frac{1}{1-x}$ ($c_n = 1$) violates the exponential-type bound
    $|c_n| \cdot n! \le 2^M \cdot (2^R)^n$. Thus `RadiusJet` is strictly larger than `AnalyticJet`. -/
theorem geom_not_analyticJet (M R : Nat) :
    ∃ n : Nat, (2 : Rat) ^ M * ((2 : Rat) ^ R) ^ n <
      |((RadiusJet.geomOneMinusX.toJet).coeff n).val| * (fact n : Rat) := by
  let B : Nat := 2 * 2 ^ R
  let d : Nat := M + R * B + 1
  refine ⟨B + d, ?_⟩
  dsimp [RadiusJet.geomOneMinusX]
  rw [Q.val_ofNat]
  norm_num
  have h_nat : 2 ^ M * (2 ^ R) ^ (B + d) < fact (B + d) := by
    have h1 : 2 ^ M * (2 ^ R) ^ (B + d) = 2 ^ (M + R * B) * (2 ^ R) ^ d := by
      rw [Nat.pow_add (2 ^ R) B d, ← Nat.pow_mul 2 R B, ← Nat.mul_assoc, ← Nat.pow_add 2 M (R * B)]
    have h2 : 2 ^ (M + R * B) < 2 ^ d := by
      dsimp [d]
      rw [Nat.pow_succ]
      have : 0 < 2 ^ (M + R * B) := by positivity
      omega
    have h3 : 2 ^ (M + R * B) * (2 ^ R) ^ d < 2 ^ d * (2 ^ R) ^ d :=
      Nat.mul_lt_mul_of_pos_right h2 (by positivity)
    have h4 : 2 ^ d * (2 ^ R) ^ d = B ^ d := by
      dsimp [B]
      rw [Nat.mul_pow]
    have h5 : B ^ d ≤ (B + 1) ^ d := Nat.pow_le_pow_left (by omega) d
    have h6 : (B + 1) ^ d ≤ fact (B + d) := pow_succ_le_fact_add B d
    omega
  have h_cast : ((2 ^ M * (2 ^ R) ^ (B + d) : Nat) : Rat) < (fact (B + d) : Rat) := by
    exact_mod_cast h_nat
  simpa using h_cast

/-- Elementary factorial dominance in `Nat`: for any base $K \in \mathbb{N}$ and index $n \in \mathbb{N}$,
    $$K^n \le K^K \cdot n!$$ -/
theorem pow_le_pow_mul_fact (K : Nat) : ∀ n : Nat,
    K ^ n ≤ K ^ K * fact n := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · intro n
    cases n with
    | zero => decide
    | succ m =>
      rw [Nat.zero_pow (Nat.succ_pos m)]
      exact Nat.zero_le _
  · intro n
    induction n with
    | zero =>
      dsimp [fact]
      rw [Nat.mul_one]
      exact Nat.one_le_pow K K hK
    | succ m ih =>
      by_cases hle : m + 1 ≤ K
      · calc K ^ (m + 1) ≤ K ^ K := Nat.pow_le_pow_right hK hle
          _ = K ^ K * 1 := (Nat.mul_one _).symm
          _ ≤ K ^ K * fact (m + 1) := Nat.mul_le_mul_left _ (fact_pos (m + 1))
      · have hKm : K ≤ m + 1 := by omega
        calc K ^ (m + 1) = K ^ m * K := Nat.pow_succ K m
          _ ≤ (K ^ K * fact m) * (m + 1) := Nat.mul_le_mul ih hKm
          _ = K ^ K * ((m + 1) * fact m) := by ring
          _ = K ^ K * fact (m + 1) := rfl

namespace AnalyticJet

/-- Pure arithmetic formula for the geometric decay exponent $B(M, R) := M + (R + 1) \cdot 2^{R + 1}$. -/
def expBoundOf (M R : Nat) : Nat :=
  M + (R + 1) * 2 ^ (R + 1)

/-- Geometric decay exponent $B(F) := M + (R + 1) \cdot 2^{R + 1}$ such that
    $|(F.\mathrm{coeff}\; n).\mathrm{val}| \le 2^{B(F)} / 2^n$ for all $n \in \mathbb{N}$.
    Defined purely from `(F.M, F.R)` so that `#print axioms expBound` is 100% axiom-free. -/
def expBound (F : AnalyticJet) : Nat :=
  expBoundOf F.M F.R

/-- Every exponential-type jet `F : AnalyticJet` satisfies the global geometric decay bound
    $|(F.\mathrm{coeff}\; n).\mathrm{val}| \cdot 2^n \le 2^{B(F)}$ for all $n \in \mathbb{N}$. -/
theorem coeff_geom_bound (F : AnalyticJet) (n : Nat) :
    |(F.coeff n).val| * (2 : Rat) ^ n ≤ (2 : Rat) ^ F.expBound := by
  let K : Nat := 2 ^ (F.R + 1)
  have h_nat := pow_le_pow_mul_fact K n
  have h_rat : ((K ^ n : Nat) : Rat) ≤ ((K ^ K * fact n : Nat) : Rat) := by
    exact_mod_cast h_nat
  have h_lhs_eq : ((K ^ n : Nat) : Rat) = ((2 : Rat) ^ F.R) ^ n * (2 : Rat) ^ n := by
    dsimp [K]
    push_cast
    rw [pow_succ (2 : Rat) F.R, mul_pow]
  have h_rhs_eq : ((K ^ K * fact n : Nat) : Rat) =
      (2 : Rat) ^ ((F.R + 1) * 2 ^ (F.R + 1)) * (fact n : Rat) := by
    dsimp [K]
    rw [← Nat.pow_mul]
    push_cast
    rfl
  rw [h_lhs_eq, h_rhs_eq] at h_rat
  have hF := F.majorant_val n
  have h1 : (|(F.coeff n).val| * (2 : Rat) ^ n) * (fact n : Rat) =
      (|(F.coeff n).val| * (fact n : Rat)) * (2 : Rat) ^ n := by ring
  have h2 : (|(F.coeff n).val| * (fact n : Rat)) * (2 : Rat) ^ n ≤
      ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) * (2 : Rat) ^ n :=
    mul_le_mul_of_nonneg_right hF (by positivity)
  have h3 : ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) * (2 : Rat) ^ n =
      (2 : Rat) ^ F.M * (((2 : Rat) ^ F.R) ^ n * (2 : Rat) ^ n) := by ring
  have h4 : (2 : Rat) ^ F.M * (((2 : Rat) ^ F.R) ^ n * (2 : Rat) ^ n) ≤
      (2 : Rat) ^ F.M * ((2 : Rat) ^ ((F.R + 1) * 2 ^ (F.R + 1)) * (fact n : Rat)) :=
    mul_le_mul_of_nonneg_left h_rat (by positivity)
  have h5 : (2 : Rat) ^ F.M * ((2 : Rat) ^ ((F.R + 1) * 2 ^ (F.R + 1)) * (fact n : Rat)) =
      (2 : Rat) ^ F.expBound * (fact n : Rat) := by
    dsimp [expBound, expBoundOf]
    rw [pow_add]
    ring
  have h_fn_pos : (0 : Rat) < (fact n : Rat) := by exact_mod_cast fact_pos n
  exact le_of_mul_le_mul_right (by linarith) h_fn_pos

/-- Telescoping bound on the $n$-th coefficient:
    $|(F.\mathrm{coeff}\; n).\mathrm{val}| \le 2^{B(F) + 1} \cdot (2^{-n} - 2^{-(n+1)})$. -/
theorem coeff_telescope_step (F : AnalyticJet) (n : Nat) :
    |(F.coeff n).val| ≤
      (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + 1)) := by
  have h_geom := F.coeff_geom_bound n
  have h_pow_pos : (0 : Rat) < (2 : Rat) ^ n := by positivity
  have h_div : |(F.coeff n).val| ≤ (2 : Rat) ^ F.expBound / (2 : Rat) ^ n :=
    (le_div_iff₀ h_pow_pos).mpr h_geom
  have h_eq : (2 : Rat) ^ F.expBound / (2 : Rat) ^ n =
      (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + 1)) := by
    rw [pow_succ (2 : Rat) F.expBound, pow_succ (2 : Rat) n]
    field_simp
    ring
  linarith

/-- Telescoping Cauchy tail bound for `evalPoly` on $[-1, 1]$ (`|x.val| ≤ 1`):
    $|\mathrm{evalPoly}(F, n, x) - \mathrm{evalPoly}(F, n + d, x)| \le 2^{B(F) + 1} (2^{-n} - 2^{-(n+d)})$. -/
theorem evalPoly_cauchy_step (F : AnalyticJet) (x : Q) (hx : |x.val| ≤ 1) (n : Nat) :
    ∀ d : Nat,
      |(F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + d) x).val| ≤
        (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + d))
  | 0 => by simp
  | d + 1 => by
    have ih := evalPoly_cauchy_step F x hx n d
    have h_succ := F.toJet.evalPoly_succ (n + d) x
    have h_split : (F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + (d + 1)) x).val =
        ((F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + d) x).val) +
        (-((F.coeff (n + d)).val * x.val ^ (n + d))) := by
      rw [← Nat.add_assoc, h_succ]
      ring
    rw [h_split]
    have h_tri := abs_add_le'
      ((F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + d) x).val)
      (-((F.coeff (n + d)).val * x.val ^ (n + d)))
    rw [abs_neg, abs_mul, abs_pow] at h_tri
    have hx_pow : |x.val| ^ (n + d) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    have h_term1 : |(F.coeff (n + d)).val| * |x.val| ^ (n + d) ≤ |(F.coeff (n + d)).val| := by
      nlinarith [abs_nonneg (F.coeff (n + d)).val]
    have h_term2 := F.coeff_telescope_step (n + d)
    rw [ ← Nat.add_assoc ]
    linarith

/-- **Embedding of `AnalyticJet` into `E0` (`AnalyticJet.toE0`)**:
    Every exponential-type jet `F : AnalyticJet` defines a certified `E0` approximating evaluator
    on $[-1, 1]$ with `ev := F.toJet.evalPoly` and Cauchy modulus `cm k := F.expBound + 1 + k`. -/
def toE0 (F : AnalyticJet) : E0 where
  a := Q.of (-1) 1
  b := Q.ofNat 1
  ev := F.toJet.evalPoly
  cm k := F.expBound + 1 + k
  ivl := by decide
  conv := by
    intro k n m hn hnm x hxa hxb
    rw [Qle_eq_true_iff] at hxa hxb
    have ha_val : (Q.of (-1) 1).val = -1 := by rw [Q.val_of (-1) 1 (by decide)]; norm_num
    have hb_val : (Q.ofNat 1).val = 1 := by rw [Q.val_ofNat]; norm_num
    rw [ha_val] at hxa
    rw [hb_val] at hxb
    have hx : |x.val| ≤ 1 := abs_le.mpr ⟨hxa, hxb⟩
    have hm_eq : m = n + (m - n) := (Nat.add_sub_of_le hnm).symm
    have h_step := F.evalPoly_cauchy_step x hx n (m - n)
    rw [← hm_eq] at h_step
    have h_pos : (0 : Rat) ≤ (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ m) := by positivity
    have h_le1 : |(F.toJet.evalPoly n x).val - (F.toJet.evalPoly m x).val| ≤
        (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ n) := by linarith
    have h_inv : (1 : Rat) / (2 : Rat) ^ n ≤ 1 / (2 : Rat) ^ (F.expBound + 1 + k) :=
      inv_pow_le hn
    have h_le2 : (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ n) ≤
        (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ (F.expBound + 1 + k)) :=
      mul_le_mul_of_nonneg_left h_inv (by positivity)
    have h_eq : (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ (F.expBound + 1 + k)) =
        1 / (2 : Rat) ^ k := by
      rw [pow_add (2 : Rat) (F.expBound + 1) k]
      field_simp
    rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val]
    linarith

/-- Multiplying the $n$-th coefficient of an exponential-type jet $G$ by $(n + 1)$
    produces an exponential-type jet with majorant $(G.M + 1, G.R + 1)$. -/
def mulIdxSucc (G : AnalyticJet) : AnalyticJet where
  toJet := ⟨fun n ↦ Q.mul (Q.ofNat (n + 1)) (G.coeff n)⟩
  M := G.M + 1
  R := G.R + 1
  majorant n := by
    rw [majorant_iff_val]
    dsimp
    rw [Q.val_mul, Q.val_ofNat, abs_mul]
    have hn_pos : (0 : Rat) ≤ ((n + 1 : Nat) : Rat) := by positivity
    rw [abs_of_nonneg hn_pos]
    have hG := G.majorant_val n
    have hn_pow := nat_succ_le_two_mul_pow2 n
    have h_step : ((n + 1 : Nat) : Rat) * (|(G.coeff n).val| * (fact n : Rat)) ≤
        (2 * (2 : Rat) ^ n) * ((2 : Rat) ^ G.M * ((2 : Rat) ^ G.R) ^ n) :=
      mul_le_mul hn_pow hG (by positivity) (by positivity)
    have h_eq : (2 * (2 : Rat) ^ n) * ((2 : Rat) ^ G.M * ((2 : Rat) ^ G.R) ^ n) =
        (2 : Rat) ^ (G.M + 1) * ((2 : Rat) ^ (G.R + 1)) ^ n := by
      rw [pow_succ (2 : Rat) G.M, pow_succ (2 : Rat) G.R, mul_pow]
      ring
    linarith

/-- General geometric error accumulation lemma for any `G : AnalyticJet`. -/
theorem geom_accum_step (G : AnalyticJet) (W : Rat) (hW : 0 ≤ W)
    (E : Nat → Rat) (hE0 : E 0 ≤ 0)
    (hStep : ∀ i : Nat, E (i + 1) ≤ E i + |(G.coeff i).val| * W) :
    ∀ n : Nat, E n ≤ (2 : Rat) ^ (G.expBound + 1) * (1 - 1 / (2 : Rat) ^ n) * W
  | 0 => by simpa using hE0
  | i + 1 => by
    have ih := geom_accum_step G W hW E hE0 hStep i
    have h_step := hStep i
    have h_c := G.coeff_telescope_step i
    have h_cW : |(G.coeff i).val| * W ≤
        (2 : Rat) ^ (G.expBound + 1) * (1 / (2 : Rat) ^ i - 1 / (2 : Rat) ^ (i + 1)) * W :=
      mul_le_mul_of_nonneg_right h_c hW
    linarith

theorem geom_accum_bound (G : AnalyticJet) (W : Rat) (hW : 0 ≤ W)
    (E : Nat → Rat) (hE0 : E 0 ≤ 0)
    (hStep : ∀ i : Nat, E (i + 1) ≤ E i + |(G.coeff i).val| * W) (n : Nat) :
    E n ≤ (2 : Rat) ^ (G.expBound + 1) * W := by
  have h1 := geom_accum_step G W hW E hE0 hStep n
  have h_pos : (0 : Rat) ≤ (2 : Rat) ^ (G.expBound + 1) * (1 / (2 : Rat) ^ n) * W := by positivity
  linarith

/-- Elementary Lipschitz bound on $x^j - y^j$ for $x, y \in [-1, 1]$:
    $|x^j - y^j| \le j \cdot |x - y|$. -/
theorem pow_sub_pow_le_unit (x y : Rat) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    ∀ j : Nat, |x ^ j - y ^ j| ≤ (j : Rat) * |x - y|
  | 0 => by simp
  | j + 1 => by
    have ih := pow_sub_pow_le_unit x y hx hy j
    have h_id : x ^ (j + 1) - y ^ (j + 1) = (x - y) * x ^ j + y * (x ^ j - y ^ j) := by ring
    rw [h_id]
    have h_tri := abs_add_le' ((x - y) * x ^ j) (y * (x ^ j - y ^ j))
    rw [abs_mul, abs_mul, abs_pow] at h_tri
    have hx_pow : |x| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    have h1 : |x - y| * |x| ^ j ≤ |x - y| := by nlinarith [abs_nonneg (x - y)]
    have h2 : |y| * |x ^ j - y ^ j| ≤ (j : Rat) * |x - y| := by
      have : |y| * |x ^ j - y ^ j| ≤ 1 * ((j : Rat) * |x - y|) :=
        mul_le_mul hy ih (abs_nonneg _) (by positivity)
      linarith
    push_cast
    linarith

/-- Uniform Lipschitz bound for `evalPoly` on $[-1, 1]$ across all degrees $n \in \mathbb{N}$:
    $|\mathrm{evalPoly}(F, n, x) - \mathrm{evalPoly}(F, n, y)| \le 2^{B(\mathcal{D}F) + 1} \cdot |x - y|$. -/
theorem evalPoly_lip_unit (F : AnalyticJet) (x y : Q) (hx : |x.val| ≤ 1) (hy : |y.val| ≤ 1) :
    ∀ n : Nat,
      |(F.toJet.evalPoly n x).val - (F.toJet.evalPoly n y).val| ≤
        (2 : Rat) ^ (F.deriv.expBound + 1) * |x.val - y.val|
  | 0 => by
    rw [F.toJet.evalPoly_zero, F.toJet.evalPoly_zero, sub_self, abs_zero]
    positivity
  | n + 1 => by
    let E : Nat → Rat := fun m ↦ |(F.toJet.evalPoly (m + 1) x).val - (F.toJet.evalPoly (m + 1) y).val|
    refine geom_accum_bound F.deriv |x.val - y.val| (abs_nonneg _) E ?_ ?_ n
    · dsimp [E]
      rw [F.toJet.evalPoly_one, F.toJet.evalPoly_one, sub_self, abs_zero]
    · intro i
      dsimp [E]
      have h_id : (F.toJet.evalPoly (i + 2) x).val - (F.toJet.evalPoly (i + 2) y).val =
          ((F.toJet.evalPoly (i + 1) x).val - (F.toJet.evalPoly (i + 1) y).val) +
          (F.coeff (i + 1)).val * (x.val ^ (i + 1) - y.val ^ (i + 1)) := by
        rw [F.toJet.evalPoly_succ (i + 1) x, F.toJet.evalPoly_succ (i + 1) y]
        ring
      rw [h_id]
      have h_tri := abs_add_le'
        ((F.toJet.evalPoly (i + 1) x).val - (F.toJet.evalPoly (i + 1) y).val)
        ((F.coeff (i + 1)).val * (x.val ^ (i + 1) - y.val ^ (i + 1)))
      rw [abs_mul] at h_tri
      have h_pow := pow_sub_pow_le_unit x.val y.val hx hy (i + 1)
      have h_mul : |(F.coeff (i + 1)).val| * |x.val ^ (i + 1) - y.val ^ (i + 1)| ≤
          |(F.coeff (i + 1)).val| * (((i + 1 : Nat) : Rat) * |x.val - y.val|) :=
        mul_le_mul_of_nonneg_left h_pow (abs_nonneg _)
      have h_deriv : |(F.deriv.coeff i).val| = |(F.coeff (i + 1)).val| * ((i + 1 : Nat) : Rat) := by
        dsimp [AnalyticJet.deriv, Jet.deriv]
        rw [Q.val_mul, Q.val_ofNat, abs_mul, abs_of_nonneg (by positivity : (0 : Rat) ≤ ((i + 1 : Nat) : Rat))]
        ring
      have h_assoc : |(F.coeff (i + 1)).val| * (((i + 1 : Nat) : Rat) * |x.val - y.val|) =
          |(F.deriv.coeff i).val| * |x.val - y.val| := by
        rw [h_deriv]; ring
      linarith

/-- Uniform continuity modulus $\omega(k) := B(\mathcal{D}F) + 1 + k$ for `F.toE0` on $[-1, 1]$.
    Defined directly on `(F.M, F.R)` so `#print axioms omegaE1` is 100% axiom-free. -/
def omegaE1 (F : AnalyticJet) (k : Nat) : Nat :=
  expBoundOf (F.M + F.R) F.R + 1 + k

/-- **`E1` Continuity Theorem for `AnalyticJet.toE0` (`toE0_cont_any` / `toE0_cont`)**:
    For every `F : AnalyticJet`, `F.toE0` satisfies `E1.cont` on $[-1, 1]$ with modulus `F.omegaE1`
    at every truncation degree $n \in \mathbb{N}$. -/
theorem toE0_cont_any (F : AnalyticJet) (k n : Nat) (x y : Q)
    (hxa : Qle F.toE0.a x = true) (hxb : Qle x F.toE0.b = true)
    (hya : Qle F.toE0.a y = true) (hyb : Qle y F.toE0.b = true)
    (hxy : Qle (Q.abs (Q.sub x y)) (D.toQ (D.pow2neg (F.omegaE1 k))) = true) :
    Qle (Q.abs (Q.sub (F.toE0.ev n x) (F.toE0.ev n y))) (D.toQ (D.pow2neg k)) = true := by
  dsimp [toE0] at hxa hxb hya hyb ⊢
  rw [Qle_eq_true_iff] at hxa hxb hya hyb hxy ⊢
  have ha_val : (Q.of (-1) 1).val = -1 := by rw [Q.val_of (-1) 1 (by decide)]; norm_num
  have hb_val : (Q.ofNat 1).val = 1 := by rw [Q.val_ofNat]; norm_num
  rw [ha_val] at hxa hya
  rw [hb_val] at hxb hyb
  rw [Q.val_abs, Q.val_sub, toQ_pow2neg_val] at hxy ⊢
  have hx : |x.val| ≤ 1 := abs_le.mpr ⟨hxa, hxb⟩
  have hy : |y.val| ≤ 1 := abs_le.mpr ⟨hya, hyb⟩
  have h_lip := F.evalPoly_lip_unit x y hx hy n
  have h_mul : (2 : Rat) ^ (F.deriv.expBound + 1) * |x.val - y.val| ≤
      (2 : Rat) ^ (F.deriv.expBound + 1) * (1 / (2 : Rat) ^ (F.omegaE1 k)) :=
    mul_le_mul_of_nonneg_left hxy (by positivity)
  have h_eq : (2 : Rat) ^ (F.deriv.expBound + 1) * (1 / (2 : Rat) ^ (F.omegaE1 k)) =
      1 / (2 : Rat) ^ k := by
    change (2 : Rat) ^ (F.deriv.expBound + 1) * (1 / (2 : Rat) ^ ((F.deriv.expBound + 1) + k)) =
      1 / (2 : Rat) ^ k
    rw [pow_add (2 : Rat) (F.deriv.expBound + 1) k]
    field_simp
  linarith

theorem toE0_cont (F : AnalyticJet) (k n : Nat) (x y : Q) (_hn : F.toE0.cm k ≤ n)
    (hxa : Qle F.toE0.a x = true) (hxb : Qle x F.toE0.b = true)
    (hya : Qle F.toE0.a y = true) (hyb : Qle y F.toE0.b = true)
    (hxy : Qle (Q.abs (Q.sub x y)) (D.toQ (D.pow2neg (F.omegaE1 k))) = true) :
    Qle (Q.abs (Q.sub (F.toE0.ev n x) (F.toE0.ev n y))) (D.toQ (D.pow2neg k)) = true :=
  F.toE0_cont_any k n x y hxa hxb hya hyb hxy

/-- Elementary second-order Taylor remainder bound for $(x + h)^{j+1} - x^{j+1} - (j+1) h x^j$
    on $[-1, 1]$:
    $$|(x + h)^{j+1} - x^{j+1} - (j + 1) h x^j| \le (j + 1)^2 \cdot |h|^2.$$ -/
theorem pow_lin_rem_le_unit (x h : Rat) (hx : |x| ≤ 1) (hxh : |x + h| ≤ 1) :
    ∀ j : Nat,
      |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j| ≤
        ((j + 1 : Nat) : Rat) ^ 2 * |h| ^ 2
  | 0 => by
    have h0 : (x + h) ^ 1 - x ^ 1 - ((1 : Nat) : Rat) * h * x ^ 0 = 0 := by ring
    rw [h0, abs_zero]
    positivity
  | j + 1 => by
    have ih := pow_lin_rem_le_unit x h hx hxh j
    have h_id : (x + h) ^ (j + 2) - x ^ (j + 2) - ((j + 2 : Nat) : Rat) * h * x ^ (j + 1) =
        (x + h) * ((x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j) +
        ((j + 1 : Nat) : Rat) * h ^ 2 * x ^ j := by
      push_cast
      ring
    rw [h_id]
    have h_tri := abs_add_le'
      ((x + h) * ((x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j))
      (((j + 1 : Nat) : Rat) * h ^ 2 * x ^ j)
    rw [abs_mul, abs_mul, abs_mul, abs_pow, sq_abs] at h_tri
    rw [sq_abs] at ih
    have hx_pow : |x| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    have h1 : |x + h| * |(x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j| ≤
        ((j + 1 : Nat) : Rat) ^ 2 * h ^ 2 := by
      have := mul_le_mul hxh ih (abs_nonneg _) (by positivity)
      linarith
    have h2 : |((j + 1 : Nat) : Rat)| * h ^ 2 * |x ^ j| ≤ ((j + 1 : Nat) : Rat) * h ^ 2 := by
      have hj_pos : (0 : Rat) ≤ ((j + 1 : Nat) : Rat) := by positivity
      rw [abs_of_nonneg hj_pos, abs_pow]
      have h_nonneg : (0 : Rat) ≤ ((j + 1 : Nat) : Rat) * h ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hx_pow h_nonneg
      linarith
    have h3 : ((j + 1 : Nat) : Rat) ^ 2 * h ^ 2 + ((j + 1 : Nat) : Rat) * h ^ 2 ≤
        ((j + 1 + 1 : Nat) : Rat) ^ 2 * |h| ^ 2 := by
      rw [sq_abs]
      have hj_pos : (0 : Rat) ≤ ((j + 1 : Nat) : Rat) := by positivity
      have h_sq : ((j + 1 + 1 : Nat) : Rat) ^ 2 = ((j + 1 : Nat) : Rat) ^ 2 + 2 * ((j + 1 : Nat) : Rat) + 1 := by
        push_cast; ring
      rw [h_sq]
      nlinarith [sq_nonneg h]
    linarith

/-- Difference-quotient form of `pow_lin_rem_le_unit` for $h \ne 0$:
    $$\left|\frac{(x + h)^{j+1} - x^{j+1}}{h} - (j + 1) x^j\right| \le (j + 1)^2 \cdot |h|.$$ -/
theorem pow_diff_quot_le_unit (x h : Rat) (hx : |x| ≤ 1) (hxh : |x + h| ≤ 1) (hh : h ≠ 0) (j : Nat) :
    |((x + h) ^ (j + 1) - x ^ (j + 1)) / h - ((j + 1 : Nat) : Rat) * x ^ j| ≤
      ((j + 1 : Nat) : Rat) ^ 2 * |h| := by
  have h_pos : 0 < |h| := abs_pos.mpr hh
  have h_rem := pow_lin_rem_le_unit x h hx hxh j
  have h_eq : ((x + h) ^ (j + 1) - x ^ (j + 1)) / h - ((j + 1 : Nat) : Rat) * x ^ j =
      ((x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : Nat) : Rat) * h * x ^ j) / h := by
    field_simp
  rw [h_eq, abs_div, div_le_iff₀ h_pos]
  have h_rhs : ((j + 1 : Nat) : Rat) ^ 2 * |h| * |h| = ((j + 1 : Nat) : Rat) ^ 2 * |h| ^ 2 := by ring
  linarith

/-- Uniform Difference-Quotient bound for `evalPoly` on $[-1, 1]$ across all degrees $n \in \mathbb{N}$:
    $$\left|\frac{\mathrm{evalPoly}(F, n+1, x+h) - \mathrm{evalPoly}(F, n+1, x)}{h} - \mathrm{evalPoly}(\mathcal{D}F, n, x)\right|
      \le 2^{B(\mathrm{mulIdxSucc}(\mathcal{D}F)) + 1} \cdot |h|.$$ -/
theorem evalPoly_diff_unit (F : AnalyticJet) (n : Nat) (x h : Q)
    (hx : |x.val| ≤ 1) (hxh : |(Q.add x h).val| ≤ 1) (hnum : h.num ≠ 0) :
    |((Q.div (Q.sub (F.toJet.evalPoly (n + 1) (Q.add x h)) (F.toJet.evalPoly (n + 1) x)) h).val -
        (F.deriv.toJet.evalPoly n x).val)| ≤
      (2 : Rat) ^ (F.deriv.mulIdxSucc.expBound + 1) * |h.val| := by
  have hh_ne : h.val ≠ 0 := by
    unfold Q.val
    exact div_ne_zero (Int.cast_ne_zero.mpr hnum) h.den_cast_ne_zero
  rw [Q.val_add] at hxh
  let E : Nat → Rat := fun m ↦
    |((Q.div (Q.sub (F.toJet.evalPoly (m + 1) (Q.add x h)) (F.toJet.evalPoly (m + 1) x)) h).val -
        (F.deriv.toJet.evalPoly m x).val)|
  refine geom_accum_bound F.deriv.mulIdxSucc |h.val| (abs_nonneg _) E ?_ ?_ n
  · dsimp [E]
    rw [Q.val_div _ _ hnum, Q.val_sub, F.toJet.evalPoly_one, F.toJet.evalPoly_one,
        F.deriv.toJet.evalPoly_zero, sub_self, zero_div, sub_zero, abs_zero]
  · intro i
    dsimp [E]
    rw [Q.val_div _ _ hnum, Q.val_sub, Q.val_div _ _ hnum, Q.val_sub]
    have h_step_id :
        ((F.toJet.evalPoly (i + 2) (Q.add x h)).val - (F.toJet.evalPoly (i + 2) x).val) / h.val -
          (F.deriv.toJet.evalPoly (i + 1) x).val =
        (((F.toJet.evalPoly (i + 1) (Q.add x h)).val - (F.toJet.evalPoly (i + 1) x).val) / h.val -
          (F.deriv.toJet.evalPoly i x).val) +
        (F.coeff (i + 1)).val *
          (((x.val + h.val) ^ (i + 1) - x.val ^ (i + 1)) / h.val - ((i + 1 : Nat) : Rat) * x.val ^ i) := by
      rw [F.toJet.evalPoly_succ (i + 1) (Q.add x h), F.toJet.evalPoly_succ (i + 1) x,
          F.deriv.toJet.evalPoly_succ i x, Q.val_add]
      dsimp [AnalyticJet.deriv, Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat]
      field_simp
      ring
    rw [h_step_id]
    have h_tri := abs_add_le'
      (((F.toJet.evalPoly (i + 1) (Q.add x h)).val - (F.toJet.evalPoly (i + 1) x).val) / h.val -
        (F.deriv.toJet.evalPoly i x).val)
      ((F.coeff (i + 1)).val *
        (((x.val + h.val) ^ (i + 1) - x.val ^ (i + 1)) / h.val - ((i + 1 : Nat) : Rat) * x.val ^ i))
    rw [abs_mul] at h_tri
    have h_dq := pow_diff_quot_le_unit x.val h.val hx hxh hh_ne i
    have h_mul : |(F.coeff (i + 1)).val| *
        |((x.val + h.val) ^ (i + 1) - x.val ^ (i + 1)) / h.val - ((i + 1 : Nat) : Rat) * x.val ^ i| ≤
        |(F.coeff (i + 1)).val| * (((i + 1 : Nat) : Rat) ^ 2 * |h.val|) :=
      mul_le_mul_of_nonneg_left h_dq (abs_nonneg _)
    have h_coeff : |(F.deriv.mulIdxSucc.coeff i).val| =
        |(F.coeff (i + 1)).val| * ((i + 1 : Nat) : Rat) ^ 2 := by
      dsimp [mulIdxSucc, AnalyticJet.deriv, Jet.deriv]
      rw [Q.val_mul, Q.val_mul, Q.val_ofNat, abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : Rat) ≤ ((i + 1 : Nat) : Rat))]
      ring
    have h_assoc : |(F.coeff (i + 1)).val| * (((i + 1 : Nat) : Rat) ^ 2 * |h.val|) =
        |(F.deriv.mulIdxSucc.coeff i).val| * |h.val| := by
      rw [h_coeff]; ring
    linarith

/-- Uniform differentiability step modulus $\delta(k) := B(\mathrm{mulIdxSucc}(\mathcal{D}F)) + 1 + k$.
    Defined directly on `(F.M, F.R)` so `#print axioms deltaE1` is 100% axiom-free. -/
def deltaE1 (F : AnalyticJet) (k : Nat) : Nat :=
  expBoundOf (F.M + F.R + 1) (F.R + 1) + 1 + k

/-- **`E1` Difference-Quotient Theorem for `AnalyticJet.toE0` (`toE0_diff`)**:
    For every `F : AnalyticJet`, the difference quotient of `F.toE0.ev (n + 1)` at step $h$
    is within $2^{-k}$ of the derivative's approximating evaluator `F.deriv.toE0.ev n x`
    for all $|h| \le 2^{-\delta(k)}$ on $[-1, 1]$. -/
theorem toE0_diff (F : AnalyticJet) (k n : Nat) (x h : Q)
    (hxa : Qle F.toE0.a x = true) (hxb : Qle x F.toE0.b = true)
    (hha : Qle F.toE0.a (Q.add x h) = true) (hhb : Qle (Q.add x h) F.toE0.b = true)
    (hnum : h.num ≠ 0)
    (hstep : Qle (Q.abs h) (D.toQ (D.pow2neg (F.deltaE1 k))) = true) :
    Qle (Q.abs (Q.sub (Q.div (Q.sub (F.toE0.ev (n + 1) (Q.add x h)) (F.toE0.ev (n + 1) x)) h)
                      (F.deriv.toE0.ev n x)))
        (D.toQ (D.pow2neg k)) = true := by
  dsimp [toE0] at hxa hxb hha hhb ⊢
  rw [Qle_eq_true_iff] at hxa hxb hha hhb hstep ⊢
  have ha_val : (Q.of (-1) 1).val = -1 := by rw [Q.val_of (-1) 1 (by decide)]; norm_num
  have hb_val : (Q.ofNat 1).val = 1 := by rw [Q.val_ofNat]; norm_num
  rw [ha_val] at hxa hha
  rw [hb_val] at hxb hhb
  rw [Q.val_abs, toQ_pow2neg_val] at hstep
  rw [Q.val_abs, Q.val_sub, toQ_pow2neg_val]
  have hx : |x.val| ≤ 1 := abs_le.mpr ⟨hxa, hxb⟩
  have hxh : |(Q.add x h).val| ≤ 1 := abs_le.mpr ⟨hha, hhb⟩
  have h_dq := F.evalPoly_diff_unit n x h hx hxh hnum
  have h_mul : (2 : Rat) ^ (F.deriv.mulIdxSucc.expBound + 1) * |h.val| ≤
      (2 : Rat) ^ (F.deriv.mulIdxSucc.expBound + 1) * (1 / (2 : Rat) ^ (F.deltaE1 k)) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have h_eq : (2 : Rat) ^ (F.deriv.mulIdxSucc.expBound + 1) * (1 / (2 : Rat) ^ (F.deltaE1 k)) =
      1 / (2 : Rat) ^ k := by
    change (2 : Rat) ^ (F.deriv.mulIdxSucc.expBound + 1) *
        (1 / (2 : Rat) ^ ((F.deriv.mulIdxSucc.expBound + 1) + k)) =
      1 / (2 : Rat) ^ k
    rw [pow_add (2 : Rat) (F.deriv.mulIdxSucc.expBound + 1) k]
    field_simp
  linarith

/-- **Full `E1` Embedding for `AnalyticJet` (`AnalyticJet.toE1`)**:
    Every exponential-type jet `F : AnalyticJet` is a genuine `E1` inhabitant (from `HAomega/EFTC.lean`)
    on $[-1, 1]$ with `toE0 := F.toE0`, uniform continuity modulus `ω := F.omegaE1`,
    uniform differentiability modulus `δ := F.deltaE1`, `dq _ _ := 1`, and approximating
    derivative `fun n x ↦ F.deriv.toJet.evalPoly (n - 1) x`! -/
def toE1 (F : AnalyticJet) : E1 where
  toE0 := F.toE0
  ω := F.omegaE1
  δ := F.deltaE1
  dq _ _ := 1
  cont := F.toE0_cont
  diff := ⟨fun n x ↦ F.deriv.toJet.evalPoly (n - 1) x, by
    intro k n x h hdq hxa hxb hha hhb hnum hstep
    have hn_eq : (n - 1) + 1 = n := Nat.sub_add_cancel hdq
    have h_diff := F.toE0_diff k (n - 1) x h hxa hxb hha hhb hnum hstep
    dsimp [toE0] at h_diff ⊢
    rwa [hn_eq] at h_diff⟩

/-- **Truncation-Level `E1` Embedding (`AnalyticJet.truncToE1`)**:
    For every degree $N \in \mathbb{N}$, the $(N+1)$-term Taylor polynomial of `F : AnalyticJet`
    is a literal `E1` inhabitant on $[-1, 1]$ whose uniform continuity modulus `F.omegaE1`
    and uniform differentiability modulus `F.deltaE1` are **independent of $N$**,
    with exact rational derivative `fun _ x ↦ F.deriv.toJet.evalPoly N x`. -/
def truncToE1 (F : AnalyticJet) (N : Nat) : E1 where
  a := Q.of (-1) 1
  b := Q.ofNat 1
  ev _ x := F.toJet.evalPoly (N + 1) x
  cm _ := 0
  ivl := by decide
  ω := F.omegaE1
  δ := F.deltaE1
  dq _ _ := 0
  conv := by
    intro k _ _ _ _ x _ _
    rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, sub_self, abs_zero, toQ_pow2neg_val]
    positivity
  cont := by
    intro k _ x y _ hxa hxb hya hyb hxy
    exact F.toE0_cont_any k (N + 1) x y hxa hxb hya hyb hxy
  diff := ⟨fun _ x ↦ F.deriv.toJet.evalPoly N x, fun k _ x h _ hxa hxb hha hhb hnum hstep ↦
    F.toE0_diff k N x h hxa hxb hha hhb hnum hstep⟩

end AnalyticJet

/-! ## 6c. $\forall k\, \exists N$ Jet Convergence Theorem in `Deriv` & Extracted Modulus (`jetCauchyModulusD`) -/

@[derivNorm] theorem tmJetEvalPoly_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetEvalPoly (Γ := Γ)).rename ρ = tmJetEvalPoly := rfl

@[derivNorm] theorem tmJetEvalPoly_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetEvalPoly (Γ := Γ)).subst s = tmJetEvalPoly := rfl

@[derivNorm] theorem qpow2pos_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (qpow2pos (Γ := Γ)).rename ρ = qpow2pos := rfl

@[derivNorm] theorem qpow2pos_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (qpow2pos (Γ := Γ)).subst s = qpow2pos := rfl

@[derivNorm] theorem tmJetDeriv_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetDeriv (Γ := Γ)).rename ρ = tmJetDeriv := rfl

@[derivNorm] theorem tmJetDeriv_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetDeriv (Γ := Γ)).subst s = tmJetDeriv := rfl

/-- Open System T polynomial evaluation `tmJetEvalPoly c n x`. -/
abbrev jetEvalAt {Γ : List Ty} (c : Tm Γ JetTy) (n : Tm Γ .nat) (x : Tm Γ .rat) : Tm Γ .rat :=
  .app (.app (.app tmJetEvalPoly c) n) x

/-- Open System T difference quotient of `tmJetEvalPoly c (n + 1)` at point `x` and step `h`. -/
abbrev jetDiffQuotAt {Γ : List Ty} (c : Tm Γ JetTy) (n : Tm Γ .nat) (x h : Tm Γ .rat) : Tm Γ .rat :=
  .qdiv (.qsub (jetEvalAt c (.succ n) (.qadd x h)) (jetEvalAt c (.succ n) x)) h

/-- Geometric tail premise in `Deriv`: for a jet $c : \mathrm{JetTy}$, majorant exponent $B : \mathrm{nat}$,
    and point $x : \mathrm{rat}$, partial sums from $N(k) + d_1 = (k + (B + 2)) + d_1$ to
    $((k + (B + 2)) + d_1) + d_2$ are within $2^{-(k + d_1)}$. -/
abbrev jetTailPremise (Γ : List Ty) :
    Formula (.rat :: .nat :: JetTy :: Γ) (.arrow .nat (.arrow .nat (.arrow .nat .unit))) :=
  let ctx3 : List Ty := .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx3 .nat := .var .here
  let d1 : Tm ctx3 .nat := .var (.there .here)
  let k  : Tm ctx3 .nat := .var (.there (.there .here))
  let x  : Tm ctx3 .rat := .var (.there (.there (.there .here)))
  let B  : Tm ctx3 .nat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx3 JetTy := .var (.there (.there (.there (.there (.there .here)))))
  let n1 : Tm ctx3 .nat := .add (.add k (.succ (.succ B))) d1
  let n2 : Tm ctx3 .nat := .add n1 d2
  .all .nat (.all .nat (.all .nat
    (.eq (.app (.app (.app qclose (.add k d1)) (jetEvalAt c n1 x)) (jetEvalAt c n2 x))
         (.succ .zero))))

/-- $\forall k\, \exists N$ Cauchy convergence conclusion in `Deriv`:
    $$\forall k : \mathrm{nat},\; \exists N : \mathrm{nat},\; \forall d_1, d_2 : \mathrm{nat},\;
      \mathrm{qclose}\; k\; (\mathrm{evalPoly}\; c\; (N + d_1)\; x)\;
                            (\mathrm{evalPoly}\; c\; ((N + d_1) + d_2)\; x) = 1.$$ -/
abbrev jetCauchyConcl (Γ : List Ty) :
    Formula (.rat :: .nat :: JetTy :: Γ)
      (.arrow .nat (.prod .nat (.arrow .nat (.arrow .nat .unit)))) :=
  let ctx4 : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx4 .nat := .var .here
  let d1 : Tm ctx4 .nat := .var (.there .here)
  let N  : Tm ctx4 .nat := .var (.there (.there .here))
  let k  : Tm ctx4 .nat := .var (.there (.there (.there .here)))
  let x  : Tm ctx4 .rat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx4 JetTy := .var (.there (.there (.there (.there (.there (.there .here))))))
  let m1 : Tm ctx4 .nat := .add N d1
  let m2 : Tm ctx4 .nat := .add m1 d2
  .all .nat (.ex .nat (.all .nat (.all .nat
    (.eq (.app (.app (.app qclose k) (jetEvalAt c m1 x)) (jetEvalAt c m2 x))
         (.succ .zero)))))

/-- Context at the innermost point of `jetCauchyModulusD`. -/
abbrev jetCauchyInnerCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ)
      ((.arrow .nat (.arrow .nat (.arrow .nat .unit))) :: as) :=
  .cons ((((jetTailPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))
    ((((((Δ.wk).wk).wk).wk).wk).wk)

/-- **Theorem ($\forall k\, \exists N$ Jet Cauchy Convergence Modulus in `Deriv`, `jetCauchyModulusD`)**:
    For every coefficient stream $c : \mathrm{JetTy}$, majorant exponent $B : \mathrm{nat}$, and point
    $x : \mathrm{rat}$, derives in $\mathrm{HA}^\omega$ from `jetTailPremise` and `convQCloseMono`
    that the partial sums `tmJetEvalPoly c` are Cauchy with explicit modulus $N(k) = k + (B + 2)$.
    **Superseded, circular:** `jetTailPremise` already states the tail bound at
    $k + (B+2) + d_1$, so the derivation only instantiates its hypothesis. Use
    `jetCauchyModulusGenuineD` (`JetCauchyDeriv.lean`), which derives the tail bound by
    `Deriv.ind` from a per-term, $N$-free premise. Kept for the record. -/
def jetCauchyModulusD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all JetTy (.all .nat (.all .rat
      (.imp (jetTailPremise Γ) (jetCauchyConcl Γ))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.allI ?_))))
  -- Extracted Cauchy modulus witness: N(k) = k + (B + 2)
  refine Deriv.exI (τ := .nat)
    (.add (.var .here) (.succ (.succ (.var (.there (.there .here)))))) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI ?_)
  deriv_norm
  let ctx3 : List Ty := .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx3 .nat := .var .here
  let d1 : Tm ctx3 .nat := .var (.there .here)
  let k  : Tm ctx3 .nat := .var (.there (.there .here))
  let x  : Tm ctx3 .rat := .var (.there (.there (.there .here)))
  let B  : Tm ctx3 .nat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx3 JetTy := .var (.there (.there (.there (.there (.there .here)))))
  let n1 : Tm ctx3 .nat := .add (.add k (.succ (.succ B))) d1
  let n2 : Tm ctx3 .nat := .add n1 d2
  have hPrem : Deriv (jetCauchyInnerCtx Γ Δ)
      ((((jetTailPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)) :=
    Deriv.ax
  have h1 := Deriv.allE (τ := .nat) k hPrem
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .nat) d1 h1
  deriv_norm at h2
  have h3 := Deriv.allE (τ := .nat) d2 h2
  deriv_norm at h3
  exact Deriv.convQCloseMono k d1 (jetEvalAt c n1 x) (jetEvalAt c n2 x) h3

/-- **The Extracted System T Jet Cauchy Modulus (`extractedJetCauchyModulus`)**:
    Extracted directly via `extractClosed jetCauchyModulusD` (`[propext, Quot.sound]`).
    Given a jet `c`, majorant exponent `B`, point `x`, and precision `k`, returns the
    stopping degree $N(k) = k + (B + 2)$. -/
def extractedJetCauchyModulus (c : Nat → Q) (B : Nat) (x : Q) (k : Nat) : Nat :=
  ((((extractClosed (jetCauchyModulusD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    c B x (fun _ _ _ ↦ ())) k).1

theorem extractedJetCauchyModulus_eq (c : Nat → Q) (B : Nat) (x : Q) (k : Nat) :
    extractedJetCauchyModulus c B x k = k + (B + 2) :=
  rfl

/-- Discharging `jetTailPremise` at the value level (`closeVal`) for **every** `F : AnalyticJet`
    and every rational point $x \in [-1, 1]$. -/
theorem AnalyticJet.satisfies_jetTailPremise (F : AnalyticJet) (x : Q)
    (hxa : Qle (Q.of (-1) 1) x = true) (hxb : Qle x (Q.ofNat 1) = true)
    (k d1 d2 : Nat) :
    closeVal (k + d1)
      (F.toJet.evalPoly ((k + (F.expBound + 2)) + d1) x)
      (F.toJet.evalPoly (((k + (F.expBound + 2)) + d1) + d2) x) = 1 := by
  rw [closeVal_eq_one_iff]
  rw [Qle_eq_true_iff] at hxa hxb
  have ha_val : (Q.of (-1) 1).val = -1 := by rw [Q.val_of (-1) 1 (by decide)]; norm_num
  have hb_val : (Q.ofNat 1).val = 1 := by rw [Q.val_ofNat]; norm_num
  rw [ha_val] at hxa
  rw [hb_val] at hxb
  have hx : |x.val| ≤ 1 := abs_le.mpr ⟨hxa, hxb⟩
  let n := (k + (F.expBound + 2)) + d1
  have h_step := F.evalPoly_cauchy_step x hx n d2
  have h_pos : (0 : Rat) ≤ (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ (n + d2)) := by positivity
  have h_le1 : |(F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + d2) x).val| ≤
      (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ n) := by linarith
  have hn_eq : n = (F.expBound + 1) + (k + d1 + 1) := by dsimp [n]; omega
  have h_eq : (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ n) =
      1 / (2 : Rat) ^ (k + d1 + 1) := by
    rw [hn_eq, pow_add (2 : Rat) (F.expBound + 1) (k + d1 + 1)]
    field_simp
  have h_lt : (1 : Rat) / (2 : Rat) ^ (k + d1 + 1) < 1 / (2 : Rat) ^ (k + d1) := by
    have h_p : (0 : Rat) < 1 / (2 : Rat) ^ (k + d1 + 1) := by positivity
    have h_split : (1 : Rat) / (2 : Rat) ^ (k + d1) =
        1 / (2 : Rat) ^ (k + d1 + 1) + 1 / (2 : Rat) ^ (k + d1 + 1) := by
      rw [pow_succ (2 : Rat) (k + d1)]
      field_simp
      ring
    linarith
  linarith

/-- Uniform Lipschitz premise in `Deriv`: for a jet $c : \mathrm{JetTy}$, derivative majorant
    exponent $B_1 : \mathrm{nat}$, and points $x, y : \mathrm{rat}$, every partial sum `jetEvalAt c m`
    is $2^{B_1 + 1}$-Lipschitz in `Q.ltN` vocabulary (`qlt`). -/
abbrev jetLipPremise (Γ : List Ty) :
    Formula (.rat :: .rat :: .nat :: JetTy :: Γ) (.arrow .nat .unit) :=
  let ctx1 : List Ty := .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx1 .nat := .var .here
  let y  : Tm ctx1 .rat := .var (.there .here)
  let x  : Tm ctx1 .rat := .var (.there (.there .here))
  let B1 : Tm ctx1 .nat := .var (.there (.there (.there .here)))
  let c  : Tm ctx1 JetTy := .var (.there (.there (.there (.there .here))))
  .all .nat
    (.eq (.qlt (.qmul (.app qpow2pos (.succ B1)) (.app qabsT (.qsub x y)))
               (.app qabsT (.qsub (jetEvalAt c m x) (jetEvalAt c m y))))
         .zero)

/-- $\forall k\, \exists \omega$ uniform continuity conclusion in `Deriv` for `jetEvalAt`:
    $$\forall k : \mathrm{nat},\; \exists \omega : \mathrm{nat},\; \forall m : \mathrm{nat},\;
      \mathrm{qclose}\; \omega\; x\; y = 1 \to
      \mathrm{qclose}\; k\; (\mathrm{evalPoly}\; c\; m\; x)\; (\mathrm{evalPoly}\; c\; m\; y) = 1.$$ -/
abbrev jetContConcl (Γ : List Ty) :
    Formula (.rat :: .rat :: .nat :: JetTy :: Γ)
      (.arrow .nat (.prod .nat (.arrow .nat (.arrow .unit .unit)))) :=
  let ctx3 : List Ty := .nat :: .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx3 .nat := .var .here
  let om : Tm ctx3 .nat := .var (.there .here)
  let k  : Tm ctx3 .nat := .var (.there (.there .here))
  let y  : Tm ctx3 .rat := .var (.there (.there (.there .here)))
  let x  : Tm ctx3 .rat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx3 JetTy := .var (.there (.there (.there (.there (.there (.there .here))))))
  .all .nat (.ex .nat (.all .nat
    (.imp (.eq (.app (.app (.app qclose om) x) y) (.succ .zero))
          (.eq (.app (.app (.app qclose k) (jetEvalAt c m x)) (jetEvalAt c m y)) (.succ .zero)))))

/-- Context at the innermost point of `jetContModulusD`. -/
abbrev jetContInnerCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ)
      (.unit :: (.arrow .nat .unit) :: as) :=
  let ctx2 : List Ty := .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let k  : Tm ctx2 .nat := .var (.there .here)
  let y  : Tm ctx2 .rat := .var (.there (.there .here))
  let x  : Tm ctx2 .rat := .var (.there (.there (.there .here)))
  let B1 : Tm ctx2 .nat := .var (.there (.there (.there (.there .here))))
  .cons (.eq (.app (.app (.app qclose (.add k (.succ B1))) x) y) (.succ .zero))
    (.cons (((jetLipPremise Γ).wk (σ := .nat)).wk (σ := .nat))
      ((((((Δ.wk).wk).wk).wk).wk).wk))

/-- **Theorem ($\forall k\, \exists \omega$ Jet Uniform Continuity Modulus in `Deriv`, `jetContModulusD`)**:
    For every coefficient stream $c : \mathrm{JetTy}$, derivative majorant exponent $B_1 : \mathrm{nat}$,
    and points $x, y : \mathrm{rat}$, derives in $\mathrm{HA}^\omega$ from `jetLipPremise` and
    `convQLipScale` that the partial sums `tmJetEvalPoly c` are uniformly continuous with
    explicit modulus $\omega(k) = k + (B_1 + 1)$. -/
def jetContModulusD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all JetTy (.all .nat (.all .rat (.all .rat
      (.imp (jetLipPremise Γ) (jetContConcl Γ)))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.allI ?_)))))
  -- Extracted uniform continuity modulus witness: ω(k) = k + (B1 + 1)
  refine Deriv.exI (τ := .nat)
    (.add (.var .here) (.succ (.var (.there (.there (.there .here)))))) ?_
  deriv_norm
  refine Deriv.allI (Deriv.impI ?_)
  let ctx2 : List Ty := .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx2 .nat := .var .here
  let k  : Tm ctx2 .nat := .var (.there .here)
  let y  : Tm ctx2 .rat := .var (.there (.there .here))
  let x  : Tm ctx2 .rat := .var (.there (.there (.there .here)))
  let B1 : Tm ctx2 .nat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx2 JetTy := .var (.there (.there (.there (.there (.there .here)))))
  have hPrem : Deriv (jetContInnerCtx Γ Δ) (((jetLipPremise Γ).wk (σ := .nat)).wk (σ := .nat)) :=
    Deriv.wk Deriv.ax
  have h1 := Deriv.allE (τ := .nat) m hPrem
  deriv_norm at h1
  have hClose : Deriv (jetContInnerCtx Γ Δ)
      (.eq (.app (.app (.app qclose (.add k (.succ B1))) x) y) (.succ .zero)) :=
    Deriv.ax
  exact Deriv.convQLipScale k (.succ B1) x y (jetEvalAt c m x) (jetEvalAt c m y) h1 hClose

/-- **The Extracted System T Jet Uniform Continuity Modulus (`extractedJetContModulus`)**:
    Extracted directly via `extractClosed jetContModulusD` (`[propext, Quot.sound]`). -/
def extractedJetContModulus (c : Nat → Q) (B1 : Nat) (x y : Q) (k : Nat) : Nat :=
  ((((extractClosed (jetContModulusD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    c B1 x y (fun _ ↦ ())) k).1

theorem extractedJetContModulus_eq (c : Nat → Q) (B1 : Nat) (x y : Q) (k : Nat) :
    extractedJetContModulus c B1 x y k = k + (B1 + 1) :=
  rfl

theorem AnalyticJet.extractedJetContModulus_eq_omegaE1 (F : AnalyticJet) (x y : Q) (k : Nat) :
    extractedJetContModulus F.toJet.coeff F.deriv.expBound x y k = F.omegaE1 k := by
  change k + (F.deriv.expBound + 1) = (F.deriv.expBound + 1) + k
  omega

/-- Discharging `jetLipPremise` for **every** `F : AnalyticJet` and all $x, y \in [-1, 1]$. -/
theorem AnalyticJet.satisfies_jetLipPremise (F : AnalyticJet) (x y : Q)
    (hxa : Qle (Q.of (-1) 1) x = true) (hxb : Qle x (Q.ofNat 1) = true)
    (hya : Qle (Q.of (-1) 1) y = true) (hyb : Qle y (Q.ofNat 1) = true)
    (m : Nat) :
    Q.ltN (Q.mul (qpow2posVal (F.deriv.expBound + 1)) (Q.abs (Q.sub x y)))
          (Q.abs (Q.sub (F.toJet.evalPoly m x) (F.toJet.evalPoly m y))) = 0 := by
  rw [Q.ltN_eq_zero_iff, Q.val_mul, qpow2posVal_val, Q.val_abs, Q.val_sub, Q.val_abs, Q.val_sub]
  rw [Qle_eq_true_iff] at hxa hxb hya hyb
  have ha_val : (Q.of (-1) 1).val = -1 := by rw [Q.val_of (-1) 1 (by decide)]; norm_num
  have hb_val : (Q.ofNat 1).val = 1 := by rw [Q.val_ofNat]; norm_num
  rw [ha_val] at hxa hya
  rw [hb_val] at hxb hyb
  exact F.evalPoly_lip_unit x y (abs_le.mpr ⟨hxa, hxb⟩) (abs_le.mpr ⟨hya, hyb⟩) m

/-- Uniform Difference-Quotient premise in `Deriv`: for a jet $c : \mathrm{JetTy}$, second-order
    majorant exponent $B_2 : \mathrm{nat}$, point $x : \mathrm{rat}$, and step $h : \mathrm{rat}$,
    the difference quotient `jetDiffQuotAt c m x h` approximates the formal derivative's
    polynomial evaluation `jetEvalAt (tmJetDeriv c) m x` within $2^{B_2 + 1} |h - 0|$. -/
abbrev jetDiffPremise (Γ : List Ty) :
    Formula (.rat :: .rat :: .nat :: JetTy :: Γ) (.arrow .nat .unit) :=
  let ctx1 : List Ty := .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx1 .nat := .var .here
  let h  : Tm ctx1 .rat := .var (.there .here)
  let x  : Tm ctx1 .rat := .var (.there (.there .here))
  let B2 : Tm ctx1 .nat := .var (.there (.there (.there .here)))
  let c  : Tm ctx1 JetTy := .var (.there (.there (.there (.there .here))))
  .all .nat
    (.eq (.qlt (.qmul (.app qpow2pos (.succ B2)) (.app qabsT (.qsub h (.qnat .zero))))
               (.app qabsT (.qsub (jetDiffQuotAt c m x h)
                                  (jetEvalAt (.app tmJetDeriv c) m x))))
         .zero)

/-- $\forall k\, \exists \delta$ uniform differentiability conclusion in `Deriv`:
    $$\forall k : \mathrm{nat},\; \exists \delta : \mathrm{nat},\; \forall m : \mathrm{nat},\;
      \mathrm{qclose}\; \delta\; h\; 0 = 1 \to
      \mathrm{qclose}\; k\; (\mathrm{jetDiffQuotAt}\; c\; m\; x\; h)\;
                            (\mathrm{evalPoly}\; (\mathcal{D}c)\; m\; x) = 1.$$ -/
abbrev jetDiffConcl (Γ : List Ty) :
    Formula (.rat :: .rat :: .nat :: JetTy :: Γ)
      (.arrow .nat (.prod .nat (.arrow .nat (.arrow .unit .unit)))) :=
  let ctx3 : List Ty := .nat :: .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m   : Tm ctx3 .nat := .var .here
  let del : Tm ctx3 .nat := .var (.there .here)
  let k   : Tm ctx3 .nat := .var (.there (.there .here))
  let h   : Tm ctx3 .rat := .var (.there (.there (.there .here)))
  let x   : Tm ctx3 .rat := .var (.there (.there (.there (.there .here))))
  let c   : Tm ctx3 JetTy := .var (.there (.there (.there (.there (.there (.there .here))))))
  .all .nat (.ex .nat (.all .nat
    (.imp (.eq (.app (.app (.app qclose del) h) (.qnat .zero)) (.succ .zero))
          (.eq (.app (.app (.app qclose k) (jetDiffQuotAt c m x h))
                     (jetEvalAt (.app tmJetDeriv c) m x)) (.succ .zero)))))

/-- Context at the innermost point of `jetDiffModulusD`. -/
abbrev jetDiffInnerCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ)
      (.unit :: (.arrow .nat .unit) :: as) :=
  let ctx2 : List Ty := .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let k  : Tm ctx2 .nat := .var (.there .here)
  let h  : Tm ctx2 .rat := .var (.there (.there .here))
  let B2 : Tm ctx2 .nat := .var (.there (.there (.there (.there .here))))
  .cons (.eq (.app (.app (.app qclose (.add k (.succ B2))) h) (.qnat .zero)) (.succ .zero))
    (.cons (((jetDiffPremise Γ).wk (σ := .nat)).wk (σ := .nat))
      ((((((Δ.wk).wk).wk).wk).wk).wk))

/-- **Theorem ($\forall k\, \exists \delta$ Jet Uniform Differentiability Modulus in `Deriv`, `jetDiffModulusD`)**:
    For every coefficient stream $c : \mathrm{JetTy}$, second-order majorant exponent $B_2 : \mathrm{nat}$,
    point $x : \mathrm{rat}$, and step $h : \mathrm{rat}$, derives in $\mathrm{HA}^\omega$ from `jetDiffPremise`
    and `convQLipScale` that the difference quotient `jetDiffQuotAt c m x h` converges to the
    formal derivative `jetEvalAt (tmJetDeriv c) m x` with explicit modulus $\delta(k) = k + (B_2 + 1)$. -/
def jetDiffModulusD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all JetTy (.all .nat (.all .rat (.all .rat
      (.imp (jetDiffPremise Γ) (jetDiffConcl Γ)))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.allI ?_)))))
  -- Extracted differentiability modulus witness: δ(k) = k + (B2 + 1)
  refine Deriv.exI (τ := .nat)
    (.add (.var .here) (.succ (.var (.there (.there (.there .here)))))) ?_
  deriv_norm
  refine Deriv.allI (Deriv.impI ?_)
  let ctx2 : List Ty := .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx2 .nat := .var .here
  let k  : Tm ctx2 .nat := .var (.there .here)
  let h  : Tm ctx2 .rat := .var (.there (.there .here))
  let x  : Tm ctx2 .rat := .var (.there (.there (.there .here)))
  let B2 : Tm ctx2 .nat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx2 JetTy := .var (.there (.there (.there (.there (.there .here)))))
  have hPrem : Deriv (jetDiffInnerCtx Γ Δ) (((jetDiffPremise Γ).wk (σ := .nat)).wk (σ := .nat)) :=
    Deriv.wk Deriv.ax
  have h1 := Deriv.allE (τ := .nat) m hPrem
  deriv_norm at h1
  have hClose : Deriv (jetDiffInnerCtx Γ Δ)
      (.eq (.app (.app (.app qclose (.add k (.succ B2))) h) (.qnat .zero)) (.succ .zero)) :=
    Deriv.ax
  exact Deriv.convQLipScale k (.succ B2) h (.qnat .zero)
    (jetDiffQuotAt c m x h) (jetEvalAt (.app tmJetDeriv c) m x) h1 hClose

/-- **The Extracted System T Jet Differentiability Modulus (`extractedJetDiffModulus`)**:
    Extracted directly via `extractClosed jetDiffModulusD` (`[propext, Quot.sound]`). -/
def extractedJetDiffModulus (c : Nat → Q) (B2 : Nat) (x h : Q) (k : Nat) : Nat :=
  ((((extractClosed (jetDiffModulusD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    c B2 x h (fun _ ↦ ())) k).1

theorem extractedJetDiffModulus_eq (c : Nat → Q) (B2 : Nat) (x h : Q) (k : Nat) :
    extractedJetDiffModulus c B2 x h k = k + (B2 + 1) :=
  rfl

theorem AnalyticJet.extractedJetDiffModulus_eq_deltaE1 (F : AnalyticJet) (x h : Q) (k : Nat) :
    extractedJetDiffModulus F.toJet.coeff F.deriv.mulIdxSucc.expBound x h k = F.deltaE1 k := by
  change k + (F.deriv.mulIdxSucc.expBound + 1) = (F.deriv.mulIdxSucc.expBound + 1) + k
  omega

/-- Discharging `jetDiffPremise` for **every** `F : AnalyticJet`, $x \in [-1, 1]$, and $x + h \in [-1, 1]$ ($h \ne 0$). -/
theorem AnalyticJet.satisfies_jetDiffPremise (F : AnalyticJet) (x h : Q)
    (hxa : Qle (Q.of (-1) 1) x = true) (hxb : Qle x (Q.ofNat 1) = true)
    (hha : Qle (Q.of (-1) 1) (Q.add x h) = true) (hhb : Qle (Q.add x h) (Q.ofNat 1) = true)
    (hnum : h.num ≠ 0) (m : Nat) :
    Q.ltN (Q.mul (qpow2posVal (F.deriv.mulIdxSucc.expBound + 1)) (Q.abs (Q.sub h (Q.ofNat 0))))
          (Q.abs (Q.sub
            (Q.div (Q.sub (F.toJet.evalPoly (m + 1) (Q.add x h)) (F.toJet.evalPoly (m + 1) x)) h)
            (F.deriv.toJet.evalPoly m x))) = 0 := by
  rw [Q.ltN_eq_zero_iff, Q.val_mul, qpow2posVal_val, Q.val_abs, Q.val_sub,
      Q.val_abs, Q.val_sub, Q.val_ofNat]
  push_cast
  rw [sub_zero]
  rw [Qle_eq_true_iff] at hxa hxb hha hhb
  have ha_val : (Q.of (-1) 1).val = -1 := by rw [Q.val_of (-1) 1 (by decide)]; norm_num
  have hb_val : (Q.ofNat 1).val = 1 := by rw [Q.val_ofNat]; norm_num
  rw [ha_val] at hxa hha
  rw [hb_val] at hxb hhb
  exact F.evalPoly_diff_unit m x h (abs_le.mpr ⟨hxa, hxb⟩) (abs_le.mpr ⟨hha, hhb⟩) hnum

/-- Exact evaluation semantics of `tmNatPred`, `tmNatSub`, and `tmJetMul`. -/
theorem natRecPred_eq (m : Nat) :
    (Nat.rec (motive := fun _ ↦ Nat) 0 (fun j _ ↦ j) m : Nat) = m - 1 := by
  cases m <;> rfl

theorem tmNatPred_eval {Γ : List Ty} (m : Tm Γ .nat) (e : Env Γ) :
    (tmNatPred m).eval e = m.eval e - 1 :=
  natRecPred_eq (m.eval e)

theorem tmNatSub_rec_eq (a : Nat) : ∀ b : Nat,
    (Nat.rec (motive := fun _ ↦ Nat) a
      (fun _ acc ↦ Nat.rec (motive := fun _ ↦ Nat) 0 (fun j _ ↦ j) acc) b : Nat) = a - b
  | 0 => rfl
  | k + 1 => by
    change Nat.rec (motive := fun _ ↦ Nat) 0 (fun j _ ↦ j)
      (Nat.rec (motive := fun _ ↦ Nat) a
        (fun _ acc ↦ Nat.rec (motive := fun _ ↦ Nat) 0 (fun j _ ↦ j) acc) k) = a - (k + 1)
    rw [tmNatSub_rec_eq a k, natRecPred_eq]
    omega

theorem tmNatSub_eval {Γ : List Ty} (a b : Tm Γ .nat) (e : Env Γ) :
    (tmNatSub a b).eval e = a.eval e - b.eval e :=
  tmNatSub_rec_eq (a.eval e) (b.eval e)

theorem tmJetMul_rec_eq (c1 c2 : Nat → Q) (n : Nat) : ∀ r : Nat,
    (Nat.rec (motive := fun _ ↦ Q) Q.zero
      (fun j acc ↦ Q.add acc (Q.mul (c1 j) (c2 (Nat.rec (motive := fun _ ↦ Nat) n
        (fun _ a ↦ Nat.rec (motive := fun _ ↦ Nat) 0 (fun i _ ↦ i) a) j)))) r : Q) =
      Jet.cauchyConvAux ⟨c1⟩ ⟨c2⟩ n r
  | 0 => rfl
  | j + 1 => by
    change Q.add
      (Nat.rec (motive := fun _ ↦ Q) Q.zero
        (fun j acc ↦ Q.add acc (Q.mul (c1 j) (c2 (Nat.rec (motive := fun _ ↦ Nat) n
          (fun _ a ↦ Nat.rec (motive := fun _ ↦ Nat) 0 (fun i _ ↦ i) a) j)))) j)
      (Q.mul (c1 j) (c2 (Nat.rec (motive := fun _ ↦ Nat) n
        (fun _ a ↦ Nat.rec (motive := fun _ ↦ Nat) 0 (fun i _ ↦ i) a) j))) =
      Q.add (Jet.cauchyConvAux ⟨c1⟩ ⟨c2⟩ n j) (Q.mul (c1 j) (c2 (n - j)))
    rw [tmJetMul_rec_eq c1 c2 n j, tmNatSub_rec_eq n j]

theorem tmJetMul_eval {Γ : List Ty} (e : Env Γ) (c1 c2 : Nat → Q) (n : Nat) :
    (((tmJetMul (Γ := Γ)).eval e) c1 c2) n = ((Jet.mk c1).mul (Jet.mk c2)).coeff n :=
  tmJetMul_rec_eq c1 c2 n (n + 1)

/-- **Lookahead $0$ (Causal Prefix) for Cauchy Convolution (`jetMul_lookahead_zero`)**:
    If `a₁, a₂` and `b₁, b₂` agree on indices $< n$, then their Cauchy product
    `Jet.mul` agrees on indices $< n$. -/
theorem cauchyConvAux_congr {a₁ a₂ b₁ b₂ : Nat → Q} {n : Nat}
    (ha : JetAgree n a₁ a₂) (hb : JetAgree n b₁ b₂) (m : Nat) (hm : m < n) :
    ∀ k ≤ m + 1,
      Jet.cauchyConvAux ⟨a₁⟩ ⟨b₁⟩ m k = Jet.cauchyConvAux ⟨a₂⟩ ⟨b₂⟩ m k
  | 0, _ => rfl
  | j + 1, hj => by
    dsimp [Jet.cauchyConvAux]
    rw [cauchyConvAux_congr ha hb m hm j (by omega),
        ha j (by omega), hb (m - j) (by omega)]

theorem jetMul_lookahead_zero (n : Nat) (a₁ a₂ b₁ b₂ : Nat → Q)
    (ha : JetAgree n a₁ a₂) (hb : JetAgree n b₁ b₂) :
    JetAgree n ((Jet.mk a₁).mul (Jet.mk b₁)).coeff ((Jet.mk a₂).mul (Jet.mk b₂)).coeff :=
  fun m hm ↦ cauchyConvAux_congr ha hb m hm (m + 1) (le_refl _)

/-- Kleene–Kreisel Continuity (`Continuity.lean`) of `jetMulD`, `jetEvalPolyD`, and `jetCauchyModulusD`. -/
theorem jetMul_tracked :
    Tracked (.arrow JetTy (.arrow JetTy (.prod JetTy .unit)))
      (fun _ ↦ (extractClosed jetMulD).eval Env.nil) :=
  extract_tracked jetMulD

theorem jetEvalPoly_tracked :
    Tracked (.arrow JetTy (.arrow .nat (.arrow .rat (.prod .rat .unit))))
      (fun _ ↦ (extractClosed jetEvalPolyD).eval Env.nil) :=
  extract_tracked jetEvalPolyD

theorem jetCauchyModulus_tracked :
    Tracked (.arrow JetTy (.arrow .nat (.arrow .rat
      (.arrow (.arrow .nat (.arrow .nat (.arrow .nat .unit)))
        (.arrow .nat (.prod .nat (.arrow .nat (.arrow .nat .unit))))))))
      (fun _ ↦ (extractClosed (jetCauchyModulusD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) :=
  extract_tracked (jetCauchyModulusD (Γ := []) (Δ := Ctx.nil))

theorem jetContModulus_tracked :
    Tracked (.arrow JetTy (.arrow .nat (.arrow .rat (.arrow .rat
      (.arrow (.arrow .nat .unit)
        (.arrow .nat (.prod .nat (.arrow .nat (.arrow .unit .unit)))))))))
      (fun _ ↦ (extractClosed (jetContModulusD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) :=
  extract_tracked (jetContModulusD (Γ := []) (Δ := Ctx.nil))

theorem jetDiffModulus_tracked :
    Tracked (.arrow JetTy (.arrow .nat (.arrow .rat (.arrow .rat
      (.arrow (.arrow .nat .unit)
        (.arrow .nat (.prod .nat (.arrow .nat (.arrow .unit .unit)))))))))
      (fun _ ↦ (extractClosed (jetDiffModulusD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) :=
  extract_tracked (jetDiffModulusD (Γ := []) (Δ := Ctx.nil))

/-! ## 7. Kernel `#guard` Verification of `MajorantDom` -/

-- 1. Divided-power calculus identities: D(E_4) = E_3 and I(E_3) = E_4
#guard (List.range 6).map (fun n ↦ (((Jet.divPow 4).deriv).coeff n).val) ==
       (List.range 6).map (fun n ↦ ((Jet.divPow 3).coeff n).val)

#guard (List.range 6).map (fun n ↦ (((Jet.divPow 3).integ).coeff n).val) ==
       (List.range 6).map (fun n ↦ ((Jet.divPow 4).coeff n).val)

-- 2. Extracted System T Polynomial Evaluator `extractedJetEvalPoly` applied to `tmExpJet`:
-- At N = 5 (terms 0..4: 1 + x + x²/2 + x³/6 + x⁴/24) and x = 1/2,
-- gives 1 + 1/2 + 1/8 + 1/48 + 1/384 = 211/128 (matching ODEDemo's expTaylor 4 (1/2))!
#guard (extractedJetEvalPoly ((tmExpJet (Γ := [])).eval Env.nil) 5 (Q.of 1 2)).val ==
       (Q.of 211 128).val

-- 3. Extracted System T Polynomial Evaluator + Extracted System T Antiderivative (`extractedJetInteg`):
-- FTC2 check entirely inside System T extracted programs!
-- For P(x) = demoPoly, evaluating `extractedJetInteg (tmJetDeriv P)` at N = 4, x = 2/3
-- equals `extractedJetEvalPoly P 4 (2/3) - P(0)`!
#guard (extractedJetEvalPoly
          (extractedJetInteg (((tmJetDeriv (Γ := [])).eval Env.nil) demoPoly.toJet.coeff))
          4 (Q.of 2 3)).val ==
       (extractedJetEvalPoly demoPoly.toJet.coeff 4 (Q.of 2 3)).val - (demoPoly.toJet.coeff 0).val

-- 4. Extracted System T Cauchy Convolution (`extractedJetMul`):
-- Pythagorean Identity in System T: sin²(x) + cos²(x) = 1 + 0*x + 0*x² + 0*x³ + 0*x⁴ + 0*x⁵!
#guard (List.range 6).map (fun n ↦
          ((((tmJetAdd (Γ := [])).eval Env.nil)
            (extractedJetMul ((tmSinJet (Γ := [])).eval Env.nil) ((tmSinJet (Γ := [])).eval Env.nil))
            (extractedJetMul ((tmCosJet (Γ := [])).eval Env.nil) ((tmCosJet (Γ := [])).eval Env.nil))) n).val) ==
       [1, 0, 0, 0, 0, 0]

-- 5. Leibniz Product Rule in System T: D(sin(x) * cos(x)) = cos²(x) - sin²(x)!
#guard (List.range 5).map (fun n ↦
          ((((tmJetDeriv (Γ := [])).eval Env.nil)
            (extractedJetMul ((tmSinJet (Γ := [])).eval Env.nil) ((tmCosJet (Γ := [])).eval Env.nil))) n).val) ==
       (List.range 5).map (fun n ↦
          ((((tmJetSub (Γ := [])).eval Env.nil)
            (extractedJetMul ((tmCosJet (Γ := [])).eval Env.nil) ((tmCosJet (Γ := [])).eval Env.nil))
            (extractedJetMul ((tmSinJet (Γ := [])).eval Env.nil) ((tmSinJet (Γ := [])).eval Env.nil))) n).val)

-- 6. AnalyticJet.mul majorant parameters on sin(x) * cos(x): M = 0 + 0 + 1 = 1, R = max 0 0 + 2 = 2
#guard (AnalyticJet.sin.mul AnalyticJet.cos).M == 1 ∧ (AnalyticJet.sin.mul AnalyticJet.cos).R == 2

-- 7. Full ClosedRingExpr AST compiled to both System T (`extractedClosedRingExpr`) and `AnalyticJet`:
-- Expression: D(I(exp(x) * cos(x))) == exp(x) * cos(x)
def demoRingExpr : ClosedRingExpr :=
  .deriv (.integ (.mul .expX .cosX))

#guard (List.range 6).map (fun n ↦ (ClosedRingExpr.extractedClosedRingExpr demoRingExpr n).val) ==
       (List.range 6).map (fun n ↦ ((demoRingExpr.toAnalyticJet).coeff n).val)

-- 8. RadiusJet closure checks:
-- (1 / (1 - x)) * (1 / (1 - x)) == D(1 / (1 - x)) = 1 + 2x + 3x² + 4x³ + 5x⁴ + 6x⁵!
#guard (List.range 6).map (fun n ↦ ((RadiusJet.geomOneMinusX.mul RadiusJet.geomOneMinusX).toJet.coeff n).val) ==
       (List.range 6).map (fun n ↦ ((RadiusJet.geomOneMinusX.deriv).toJet.coeff n).val)

-- D(-ln(1 - x)) == 1 / (1 - x) = 1 + x + x² + x³ + x⁴ + x⁵!
#guard (List.range 6).map (fun n ↦ ((RadiusJet.logOneMinusX.deriv).toJet.coeff n).val) ==
       (List.range 6).map (fun n ↦ (RadiusJet.geomOneMinusX.toJet.coeff n).val)

-- Multiplicative Inversion in RadiusJet (`RadiusJet.invOneSub`):
-- sec(x) = 1 + x²/2 + 5x⁴/24, tan(x) = x + x³/3 + 2x⁵/15, arctan(x) = x - x³/3 + x⁵/5
#guard (List.range 6).map (fun n ↦ (RadiusJet.sec.toJet.coeff n).val) ==
       [1, 0, 1 / 2, 0, 5 / 24, 0]
#guard (List.range 6).map (fun n ↦ (RadiusJet.tan.toJet.coeff n).val) ==
       [0, 1, 0, 1 / 3, 0, 2 / 15]
#guard (List.range 6).map (fun n ↦ (RadiusJet.arctan.toJet.coeff n).val) ==
       [0, 1, 0, -1 / 3, 0, 1 / 5]

-- Composition in RadiusJet (`RadiusJet.compZero`):
-- exp(tan x) = 1 + x + x²/2 + x³/2 + 3x⁴/8 + 37x⁵/120
#guard (List.range 6).map (fun n ↦ (RadiusJet.expTan.toJet.coeff n).val) ==
       [1, 1, 1 / 2, 1 / 2, 3 / 8, 37 / 120]
-- sin(arctan x) = x / sqrt(1 + x²) = x - x³/2 + 3x⁵/8
#guard (List.range 6).map (fun n ↦ (RadiusJet.sinArctan.toJet.coeff n).val) ==
       [0, 1, 0, -1 / 2, 0, 3 / 8]
-- D(-ln(cos x)) == tan(x) = x + x³/3 + 2x⁵/15!
#guard (List.range 6).map (fun n ↦ ((RadiusJet.negLogCos.deriv).toJet.coeff n).val) ==
       (List.range 6).map (fun n ↦ (RadiusJet.tan.toJet.coeff n).val)

-- Nonlinear Riccati, Blow-Up, and 2D Duffing ODE Closure in RadiusJet:
-- Solution of y' = 1 + y², y(0) = 0 is tan(x) = x + x³/3 + 2x⁵/15;
-- Solution of y' = 1 + x + y², y(0) = 0 is x + x²/2 + x³/3 + x⁴/4 + 11x⁵/60;
-- Solution of y' = y², y(0) = 1 is 1/(1 - x) = 1 + x + x² + x³ + x⁴ + x⁵;
-- Solution of 2D Duffing u' = v, v' = -u - u² matches extractedDuffingJet!
#guard (List.range 6).map (fun n ↦ ((RadiusJet.one.riccatiODE).toJet.coeff n).val) ==
       [0, 1, 0, 1 / 3, 0, 2 / 15]
#guard (List.range 6).map (fun n ↦ (((RadiusJet.one.add RadiusJet.varX).riccatiODE).toJet.coeff n).val) ==
       [0, 1, 1 / 2, 1 / 3, 1 / 4, 11 / 60]
#guard (List.range 6).map (fun n ↦ (RadiusJet.quadBlowupODE.toJet.coeff n).val) ==
       [1, 1, 1, 1, 1, 1]
#guard (List.range 6).map (fun n ↦ (RadiusJet.duffingU.toJet.coeff n).val) ==
       [1, 0, -1, 0, 1 / 4, 0]
#guard (List.range 6).map (fun n ↦ (RadiusJet.duffingV.toJet.coeff n).val) ==
       [0, -2, 0, 1, 0, -7 / 20]

-- 9. Extracted Jet E1 Moduli (`extractedJetCauchyModulus`, `extractedJetContModulus`, `extractedJetDiffModulus`) on exp(x):
-- N(k) = k + (2 + 2) = k + 4, ω(k) = k + (2 + 1) = k + 3, δ(k) = k + (9 + 1) = k + 10 for k = 0..5
#guard (List.range 6).map
  (extractedJetCauchyModulus AnalyticJet.exp.toJet.coeff AnalyticJet.exp.expBound (Q.of 1 2)) ==
  [4, 5, 6, 7, 8, 9]
#guard (List.range 6).map
  (extractedJetContModulus AnalyticJet.exp.toJet.coeff AnalyticJet.exp.deriv.expBound (Q.of 1 2) (Q.of 1 4)) ==
  [3, 4, 5, 6, 7, 8]
#guard (List.range 6).map
  (extractedJetDiffModulus AnalyticJet.exp.toJet.coeff AnalyticJet.exp.deriv.mulIdxSucc.expBound (Q.of 1 2) (Q.of 1 8)) ==
  [10, 11, 12, 13, 14, 15]

-- 10. Certified Haskell Emission (`HsSemantics.hsSupported` & `EmitHaskell.hsTm`) for all extracted
-- System T jet combinators (`ftcAntiderivD`, `picardJetIterD`, `jetMulD`, `jetEvalPolyD`,
-- `jetCauchyModulusD`, `jetContModulusD`, `jetDiffModulusD`):
#guard [hsSupported (extractClosed ftcAntiderivD),
        hsSupported (extractClosed picardJetIterD),
        hsSupported (extractClosed jetMulD),
        hsSupported (extractClosed jetEvalPolyD),
        hsSupported (extractClosed (jetCauchyModulusD (Γ := []) (Δ := Ctx.nil))),
        hsSupported (extractClosed (jetContModulusD (Γ := []) (Δ := Ctx.nil))),
        hsSupported (extractClosed (jetDiffModulusD (Γ := []) (Δ := Ctx.nil)))] ==
       [true, true, true, true, true, true, true]

#guard (EmitHaskell.hsTm (extractClosed (jetCauchyModulusD (Γ := []) (Δ := Ctx.nil))) 0).length > 0
#guard (EmitHaskell.hsTm (extractClosed (jetContModulusD (Γ := []) (Δ := Ctx.nil))) 0).length > 0
#guard (EmitHaskell.hsTm (extractClosed (jetDiffModulusD (Γ := []) (Δ := Ctx.nil))) 0).length > 0

#print axioms jetMulD
#print axioms extractedJetMul
#print axioms jetEvalPolyD
#print axioms extractedJetEvalPoly
#print axioms jetCauchyModulusD
#print axioms extractedJetCauchyModulus
#print axioms jetContModulusD
#print axioms extractedJetContModulus
#print axioms jetDiffModulusD
#print axioms extractedJetDiffModulus
#print axioms AnalyticJet.satisfies_jetTailPremise
#print axioms AnalyticJet.satisfies_jetLipPremise
#print axioms AnalyticJet.satisfies_jetDiffPremise
#print axioms ClosedRingExpr.compileClosedRingExprD
#print axioms ClosedRingExpr.extractedClosedRingExpr
#print axioms ftcGalois_retract_id
#print axioms Jet.deriv_divPow_val
#print axioms Jet.integ_divPow_val
#print axioms Jet.ibp_from_leibniz_val
#print axioms AnalyticJet.expBound
#print axioms AnalyticJet.omegaE1
#print axioms AnalyticJet.deltaE1
#print axioms AnalyticJet.mul
#print axioms AnalyticJet.calculus_trio_step_bounds_unit
#print axioms AnalyticJet.toE0
#print axioms AnalyticJet.toE0_cont
#print axioms AnalyticJet.toE0_diff
#print axioms AnalyticJet.toE1
#print axioms AnalyticJet.truncToE1
#print axioms RadiusJet.add
#print axioms RadiusJet.sub
#print axioms RadiusJet.integ
#print axioms RadiusJet.deriv
#print axioms RadiusJet.mul
#print axioms RadiusJet.invOneSub
#print axioms RadiusJet.sec
#print axioms RadiusJet.tan
#print axioms RadiusJet.arctan
#print axioms RadiusJet.compZero
#print axioms RadiusJet.expTan
#print axioms RadiusJet.sinArctan
#print axioms RadiusJet.negLogCos
#print axioms RadiusJet.riccatiODE
#print axioms RadiusJet.quadBlowupODE
#print axioms RadiusJet.duffingU
#print axioms RadiusJet.duffingV
#print axioms RadiusJet.omegaE1
#print axioms RadiusJet.deltaE1
#print axioms RadiusJet.toE0
#print axioms RadiusJet.toE1
#print axioms geom_not_analyticJet
#print axioms jetMul_lookahead_zero
#print axioms jetMul_tracked
#print axioms jetEvalPoly_tracked
#print axioms jetCauchyModulus_tracked
#print axioms jetContModulus_tracked
#print axioms jetDiffModulus_tracked
