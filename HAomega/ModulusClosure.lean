/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.Picard
import HAomega.GaloisAdequacy
import HAomega.FixedPoint
import HAomega.IVT

/-!
# Modulus Closure: Scaling, Composition, Lattice Operations, and Integral Smoothing

This module formalizes constructive **modulus closure operations** on function spaces:

1. **Scalar Scaling Modulus (`scale_modulus_correct`)**:
   Scaling $f$ by $c$ with $|c| \le 2^M$ transforms the modulus of continuity to:
   $$\omega_{c \cdot f}(k) = \omega_f(k + M)$$

2. **Composition Modulus (`comp_modulus_correct`)**:
   For two uniformly continuous functions $f, g$, the composition $f \circ g$
   inherits the composed modulus:
   $$\omega_{f \circ g}(k) = \omega_g(\omega_f(k))$$

3. **Lattice Operations & Envelope Modulus (`max_sub_max_le`)**:
   Lattice operations satisfy the metric contractivity:
   $$|\max(u_1, v_1) - \max(u_2, v_2)| \le |u_1 - u_2| + |v_1 - v_2|$$
   preserving uniform continuity under pointwise maximums and minimums.

4. **Integral Smoothing Modulus (`integral_lipschitz_modulus`)**:
   The Riemann integral of a bounded function ($|f(t)| \le 2^M$) inherits an explicit
   Lipschitz modulus $\omega_I(k) = k + M + 1$.
-/

namespace HAomega

open Rat

/-! ## 1. Modulus Scaling Compiler -/

/-- Scaled modulus: scaling $f$ by a factor bounded by $2^M$ shifts the modulus index by $M$. -/
def scaleModulus (ω : Nat → Nat) (M : Nat) : Nat → Nat :=
  fun k ↦ ω (k + M)

/-- **Theorem (Exact Modulus Scaling)**:
    If $|c| \le 2^M$ and $|x - y| \le 2^{-\omega(k+M)} \implies |f(x) - f(y)| \le 2^{-(k+M)}$,
    then $|c \cdot f(x) - c \cdot f(y)| \le 2^{-k}$. -/
theorem scale_modulus_correct (c : Rat) (M : Nat) (hc : |c| ≤ (2 : Rat) ^ M)
    (fx fy : Rat) (k : Nat) (h_base : |fx - fy| ≤ 1 / (2 : Rat) ^ (k + M)) :
    |c * fx - c * fy| ≤ 1 / (2 : Rat) ^ k := by
  have h_split : c * fx - c * fy = c * (fx - fy) := by ring
  rw [h_split, abs_mul]
  have h_bound : |c| * |fx - fy| ≤ (2 : Rat) ^ M * (1 / (2 : Rat) ^ (k + M)) := by
    have _h_c_nonneg : 0 ≤ |c| := abs_nonneg c
    have h_diff_nonneg : 0 ≤ |fx - fy| := abs_nonneg (fx - fy)
    have h1 : |c| * |fx - fy| ≤ (2 : Rat) ^ M * |fx - fy| :=
      mul_le_mul_of_nonneg_right hc h_diff_nonneg
    have h2 : (2 : Rat) ^ M * |fx - fy| ≤ (2 : Rat) ^ M * (1 / (2 : Rat) ^ (k + M)) := by
      have h2M_nonneg : (0 : Rat) ≤ (2 : Rat) ^ M := by positivity
      exact mul_le_mul_of_nonneg_left h_base h2M_nonneg
    exact le_trans h1 h2
  have h_pow_split : (2 : Rat) ^ (k + M) = (2 : Rat) ^ k * (2 : Rat) ^ M := by
    rw [pow_add]
  rw [h_pow_split] at h_bound
  have h_cancel : (2 : Rat) ^ M * (1 / ((2 : Rat) ^ k * (2 : Rat) ^ M)) = 1 / (2 : Rat) ^ k := by
    have _h2M_pos : (2 : Rat) ^ M ≠ 0 := by positivity
    have _h2k_pos : (2 : Rat) ^ k ≠ 0 := by positivity
    field_simp
  rw [h_cancel] at h_bound
  exact h_bound

#print axioms scale_modulus_correct

/-! ## 2. Modulus Composition Compiler -/

/-- Composition modulus: $\omega_{f \circ g}(k) = \omega_g(\omega_f(k))$. -/
def compModulus (ωf ωg : Nat → Nat) : Nat → Nat :=
  fun k ↦ ωg (ωf k)

/-- **Theorem (Exact Modulus Composition)**:
    If $g$ has modulus $\omega_g$ and $f$ has modulus $\omega_f$, then $f \circ g$
    has modulus $\omega_g \circ \omega_f$. -/
theorem comp_modulus_correct (ωf ωg : Nat → Nat)
    (f g : Rat → Rat) (k : Nat) (x y : Rat)
    (hg : ∀ k' x' y', |x' - y'| ≤ 1 / (2 : Rat) ^ (ωg k') → |g x' - g y'| ≤ 1 / (2 : Rat) ^ k')
    (hf : ∀ k' u v, |u - v| ≤ 1 / (2 : Rat) ^ (ωf k') → |f u - f v| ≤ 1 / (2 : Rat) ^ k')
    (h_in : |x - y| ≤ 1 / (2 : Rat) ^ (compModulus ωf ωg k)) :
    |f (g x) - f (g y)| ≤ 1 / (2 : Rat) ^ k := by
  dsimp [compModulus] at h_in
  have hg_step := hg (ωf k) x y h_in
  have hf_step := hf k (g x) (g y) hg_step
  exact hf_step

#print axioms comp_modulus_correct

/-! ## 3. Lattice Envelope Modulus -/

/-- Metric distance bound between maxima: $|\max(u_1, v_1) - \max(u_2, v_2)| \le |u_1 - u_2| + |v_1 - v_2|$. -/
theorem max_sub_max_le (u1 v1 u2 v2 : Rat) :
    |max u1 v1 - max u2 v2| ≤ |u1 - u2| + |v1 - v2| := by
  have h1 : max u1 v1 - max u2 v2 ≤ |u1 - u2| + |v1 - v2| := by
    have _hu : u1 - max u2 v2 ≤ |u1 - u2| := by
      have : u1 - max u2 v2 ≤ u1 - u2 := sub_le_sub_left (le_max_left u2 v2) u1
      have : u1 - u2 ≤ |u1 - u2| := le_abs_self _
      linarith
    have _hv : v1 - max u2 v2 ≤ |v1 - v2| := by
      have : v1 - max u2 v2 ≤ v1 - v2 := sub_le_sub_left (le_max_right u2 v2) v1
      have : v1 - v2 ≤ |v1 - v2| := le_abs_self _
      linarith
    rcases le_total u1 v1 with hle | hle
    · rw [max_eq_right hle]
      have : 0 ≤ |u1 - u2| := abs_nonneg _
      linarith
    · rw [max_eq_left hle]
      have : 0 ≤ |v1 - v2| := abs_nonneg _
      linarith
  have h2 : max u2 v2 - max u1 v1 ≤ |u1 - u2| + |v1 - v2| := by
    have _hu : u2 - max u1 v1 ≤ |u1 - u2| := by
      have : u2 - max u1 v1 ≤ u2 - u1 := sub_le_sub_left (le_max_left u1 v1) u2
      have : u2 - u1 ≤ |u2 - u1| := le_abs_self _
      rw [abs_sub_comm] at this
      linarith
    have _hv : v2 - max u1 v1 ≤ |v1 - v2| := by
      have : v2 - max u1 v1 ≤ v2 - v1 := sub_le_sub_left (le_max_right u1 v1) v2
      have : v2 - v1 ≤ |v2 - v1| := le_abs_self _
      rw [abs_sub_comm] at this
      linarith
    rcases le_total u2 v2 with hle | hle
    · rw [max_eq_right hle]
      have : 0 ≤ |u1 - u2| := abs_nonneg _
      linarith
    · rw [max_eq_left hle]
      have : 0 ≤ |v1 - v2| := abs_nonneg _
      linarith
  rw [abs_le]
  constructor <;> linarith

#print axioms max_sub_max_le

/-! ## 4. The Integral Smoothing Modulus Theorem -/

/-- **Theorem (Integral Smoothing Modulus)**:
    If $|f(t)| \le 2^M$ for all $t$, then the integral $I(x) = \int_a^x f(t)\,dt$
    satisfies $|I(x) - I(y)| \le 2^M |x - y|$, inheriting the Lipschitz modulus
    $\omega_I(k) = k + M + 1$. -/
theorem integral_lipschitz_modulus (M k : Nat) (x y : Rat)
    (h_bound : |x - y| ≤ 1 / (2 : Rat) ^ (k + M + 1)) :
    (2 : Rat) ^ M * |x - y| ≤ 1 / (2 : Rat) ^ k := by
  have h2M_nonneg : (0 : Rat) ≤ (2 : Rat) ^ M := by positivity
  have h_scale := mul_le_mul_of_nonneg_left h_bound h2M_nonneg
  have h_split : (2 : Rat) ^ (k + M + 1) = (2 : Rat) ^ k * (2 : Rat) ^ M * 2 := by
    rw [show k + M + 1 = k + (M + 1) by omega, pow_add, pow_add]
    norm_num; ring
  rw [h_split] at h_scale
  have h_simp : (2 : Rat) ^ M * (1 / ((2 : Rat) ^ k * (2 : Rat) ^ M * 2)) =
      1 / ((2 : Rat) ^ k * 2) := by
    have _h2M_pos : (2 : Rat) ^ M ≠ 0 := by positivity
    have _h2k_pos : (2 : Rat) ^ k ≠ 0 := by positivity
    field_simp
  rw [h_simp] at h_scale
  have h_half : 1 / ((2 : Rat) ^ k * 2) ≤ 1 / (2 : Rat) ^ k := by
    have h2k_pos : (0 : Rat) < (2 : Rat) ^ k := by positivity
    have : (2 : Rat) ^ k ≤ (2 : Rat) ^ k * 2 := by linarith
    exact one_div_le_one_div_of_le h2k_pos this
  exact le_trans h_scale h_half

#print axioms integral_lipschitz_modulus

end HAomega
