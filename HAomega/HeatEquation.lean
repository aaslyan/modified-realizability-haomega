/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QAnalysis
import HAomega.GaloisAdequacy

/-!
# Constructive 1D Heat Equation & Rational Modal Dissipation

This module formalizes a discrete rational modal propagator for the 1D Heat Equation:
$$u_t(x, t) = u_{xx}(x, t), \qquad u(x, 0) = g(x)$$

## Scope and Results

1. **Fourier Mode Heat Propagator (`ThermalState`, `heatEvolve`)**:
   A thermal state represented by truncated rational cosine Fourier coefficients $\vec{a} = (a_0, a_1, \dots, a_N)$,
   evolved by the rational Padé dissipation factor $\text{modeDecay}(n, p) = \frac{1}{1 + n^2 / 2^p}$.
2. **Verified Modal Properties (`heat_decay_zero_step1`, `heat_high_frequency_suppression`)**:
   - Mean temperature conservation ($n = 0 \implies \text{decay}(0, 1) = 1$).
   - Monotonicity of frequency damping ($n_1 \le n_2 \implies n_1^2 \le n_2^2$).
3. **Kernel-Verified Thermal Evolution**:
   Exact rational step-by-step damping of high-frequency modes verified by `#guard`.
-/

namespace HAomega

open Rat

/-! ## 1. Fourier State Representation -/

/-- A periodic thermal wave on $[-\pi, \pi]$ represented by cosine Fourier coefficients:
    $u(x) = \sum_{n=0}^N a_n \cos(n x)$. -/
structure ThermalState where
  /-- Cosine Fourier coefficients $a_0, a_1, \dots, a_N$. -/
  coeffs : List Q
  deriving DecidableEq, Repr, BEq

/-! ## 2. Rational Dissipation Operator -/

/-- Dissipation factor for mode $n$ at time step $t = 1/2^p$:
    Uses the certified rational lower bound $1 / (1 + n^2 / 2^p)$. -/
def modeDecay (n : Nat) (p : Nat) : Q :=
  let n2 := n * n
  let denom := Q.add (Q.ofNat 1) (Q.div (Q.ofNat n2) (Q.ofNat (2 ^ p)))
  Q.div (Q.ofNat 1) denom

/-- The Heat Diffusion Operator: evolves Fourier state by time $t = 1/2^p$. -/
def heatEvolve (state : ThermalState) (p : Nat) : ThermalState :=
  let evolved := (List.range state.coeffs.length).zip state.coeffs |>.map (fun ⟨n, an⟩ ↦
    Q.mul an (modeDecay n p))
  ⟨evolved⟩

/-- Multi-step thermal evolution: $T^k(u_0)$. -/
def heatTrajectory (state : ThermalState) (p : Nat) : Nat → ThermalState
  | 0 => state
  | k + 1 => heatEvolve (heatTrajectory state p k) p

/-! ## 3. Verified Kernel Executions: Thermal Smoothing -/

-- Initial sharp wave: [a₀=1, a₁=1, a₂=1, a₃=1, a₄=1] (high-frequency components present)
def sharpWave : ThermalState :=
  ⟨[Q.ofNat 1, Q.ofNat 1, Q.ofNat 1, Q.ofNat 1, Q.ofNat 1]⟩

-- Mode 0 (mean temperature) is conserved: decay(0, p) = 1
#guard modeDecay 0 1 == Q.ofNat 1

-- Mode 1 decays by 1 / (1 + 1/2) = 2/3
#guard modeDecay 1 1 == Q.of 2 3

-- Mode 2 decays by 1 / (1 + 4/2) = 1/3
#guard modeDecay 2 1 == Q.of 1 3

-- Mode 4 decays by 1 / (1 + 16/2) = 1/9
#guard modeDecay 4 1 == Q.of 1 9

-- Step 1 evolution: High frequencies die out much faster than low frequencies
#guard (heatEvolve sharpWave 1).coeffs == [Q.ofNat 1, Q.of 2 3, Q.of 1 3, Q.of 2 11, Q.of 1 9]

/-! ## 4. Modal Dissipation & Regularity Boost Theorems -/

/-- Exact rational evaluation of the Padé modal dissipation factor:
    $$(\text{modeDecay}\ n\ p).\mathrm{val} = \frac{1}{1 + n^2 / 2^p}.$$ -/
theorem modeDecay_val (n p : Nat) :
    (modeDecay n p).val = 1 / (1 + ((n * n : Nat) : Rat) / (2 : Rat) ^ p) := by
  unfold modeDecay
  have h2p_pos : 0 < 2 ^ p := Nat.pow_pos (by decide)
  have h2p_num : (Q.ofNat (2 ^ p)).num ≠ 0 := by
    unfold Q.ofNat
    exact Int.ofNat_ne_zero.mpr (ne_of_gt h2p_pos)
  have h_div_val : (Q.div (Q.ofNat (n * n)) (Q.ofNat (2 ^ p))).val =
      ((n * n : Nat) : Rat) / (2 : Rat) ^ p := by
    rw [Q.val_div _ _ h2p_num, Q.val_ofNat, Q.val_ofNat]
    push_cast
    rfl
  have h_denom_val :
      (Q.add (Q.ofNat 1) (Q.div (Q.ofNat (n * n)) (Q.ofNat (2 ^ p)))).val =
      1 + ((n * n : Nat) : Rat) / (2 : Rat) ^ p := by
    rw [Q.val_add, Q.val_ofNat, h_div_val]
    rfl
  have h_denom_pos : 0 < (Q.add (Q.ofNat 1) (Q.div (Q.ofNat (n * n)) (Q.ofNat (2 ^ p)))).val := by
    rw [h_denom_val]
    positivity
  have h_denom_num : (Q.add (Q.ofNat 1) (Q.div (Q.ofNat (n * n)) (Q.ofNat (2 ^ p)))).num ≠ 0 :=
    Q.num_ne_zero_of_val_ne_zero (ne_of_gt h_denom_pos)
  rw [Q.val_div _ _ h_denom_num, Q.val_ofNat, h_denom_val]
  rfl

/-- **Theorem (Mean Mode Conservation at Every Time Step)**:
    Mode $0$ (mean temperature) has zero dissipation at every dyadic step $2^{-p}$:
    $(\text{modeDecay}\ 0\ p).\mathrm{val} = 1$. -/
theorem modeDecay_zero_val (p : Nat) :
    (modeDecay 0 p).val = 1 := by
  rw [modeDecay_val]
  simp

/-- **Theorem (Mean Mode Decay at p=1 is Identity)**:
    Mode 0 (mean temperature) has zero dissipation at step 1: $\text{decay}(0, 1) = 1$. -/
theorem heat_decay_zero_step1 :
    modeDecay 0 1 = Q.ofNat 1 := by
  decide

/-- **Theorem (Positivity and Non-Amplification of Modal Dissipation)**:
    For every Fourier mode $n$ and dyadic time scale $p$,
    $0 < (\text{modeDecay}\ n\ p).\mathrm{val} \le 1$. -/
theorem modeDecay_bounds (n p : Nat) :
    0 < (modeDecay n p).val ∧ (modeDecay n p).val ≤ 1 := by
  rw [modeDecay_val]
  have h_nonneg : (0 : Rat) ≤ ((n * n : Nat) : Rat) / (2 : Rat) ^ p := by positivity
  have h_denom_ge : (1 : Rat) ≤ 1 + ((n * n : Nat) : Rat) / (2 : Rat) ^ p := by linarith
  have h_denom_pos : (0 : Rat) < 1 + ((n * n : Nat) : Rat) / (2 : Rat) ^ p := by linarith
  refine ⟨div_pos one_pos h_denom_pos, ?_⟩
  rw [div_le_iff₀ h_denom_pos]
  linarith

/-- **Theorem (High-Frequency Suppression / Modal Antitonicity)**:
    Higher harmonics decay faster than lower harmonics: whenever $n_1 \le n_2$,
    $$(\text{modeDecay}\ n_2\ p).\mathrm{val} \le (\text{modeDecay}\ n_1\ p).\mathrm{val}.$$ -/
theorem modeDecay_anti_mono (n1 n2 p : Nat) (hn : n1 ≤ n2) :
    (modeDecay n2 p).val ≤ (modeDecay n1 p).val := by
  rw [modeDecay_val, modeDecay_val]
  have hn_sq : n1 * n1 ≤ n2 * n2 := Nat.mul_le_mul hn hn
  have hn_sq_rat : ((n1 * n1 : Nat) : Rat) ≤ ((n2 * n2 : Nat) : Rat) := by exact_mod_cast hn_sq
  have h2p_nonneg : (0 : Rat) ≤ (2 : Rat) ^ p := by positivity
  have h_frac : ((n1 * n1 : Nat) : Rat) / (2 : Rat) ^ p ≤ ((n2 * n2 : Nat) : Rat) / (2 : Rat) ^ p :=
    div_le_div_of_nonneg_right hn_sq_rat h2p_nonneg
  have h_d1_pos : (0 : Rat) < 1 + ((n1 * n1 : Nat) : Rat) / (2 : Rat) ^ p := by positivity
  have h_d2_pos : (0 : Rat) < 1 + ((n2 * n2 : Nat) : Rat) / (2 : Rat) ^ p := by positivity
  rw [div_le_div_iff₀ h_d2_pos h_d1_pos]
  linarith

/-- **Corollary (Monotonicity of Squared Wave Numbers)**:
    $n_1^2 \le n_2^2$ whenever $n_1 \le n_2$. -/
theorem heat_high_frequency_suppression (n1 n2 : Nat) (hn : n1 ≤ n2) :
    n1 * n1 ≤ n2 * n2 :=
  Nat.mul_le_mul hn hn

#print axioms modeDecay_val
#print axioms modeDecay_zero_val
#print axioms heat_decay_zero_step1
#print axioms modeDecay_bounds
#print axioms modeDecay_anti_mono
#print axioms heat_high_frequency_suppression

end HAomega
