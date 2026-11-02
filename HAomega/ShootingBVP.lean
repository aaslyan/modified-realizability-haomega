/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SystemStep
import HAomega.RootOperator

/-!
# The shooting method for two-point boundary value problems

In an initial-value problem `Y(0) = a`, every component of `a` is known at `x = 0`
and `solFastD F a` computes the Taylor series by primitive recursion on the degree.
In a two-point boundary value problem:

    Y'(x) = F(Y(x)),     Y_w(0) = a₀[w]  (w ≠ u_shoot),     Y_{v_target}(b) = β,

the initial component `s := Y_{u_shoot}(0)` (e.g. the initial slope `y'(0)` of a
second-order ODE) is unknown, so no local recursion at `0` can start on its own.

**The shooting operator (`shootBVP`).** For a trial parameter `s ∈ [s_min, s_max]`,
`shootInit F a₀ u_shoot s` sets component `u_shoot` of the initial data to `s`,
and `shootResidual` evaluates the degree-`N` partial sum of `Y_{v_target}` at `b`
minus `β`. The extracted bisection operator `bisect` (`Bisection.lean`) searches
the grid `rootGrid s_min s_max j k` for a sign change of the residual.

**The certificate (`shootBVP_spec`, `shootBVP_certified`).** By the data-Lipschitz
and truncation theorem `stp_evalPoly_solFastD_diff` (`StepKit.lean`), if the
endpoint signs at `s_min` and `s_max` differ and `|b| ≤ 1 / (4B)` lies in the
uniform disk for initial data bounded by `K`, the returned shooting parameter
`s* = shootBVP ...` satisfies:
1. `s* ∈ [s_min, s_max]`,
2. at `x = 0`, the solution has initial values `a₀[w]` (`w ≠ u_shoot`) and `s*`
   at `u_shoot`, and
3. at `x = b`, every partial sum `N + d` (`d ≥ 0`) satisfies the boundary
   condition within the grid-Lipschitz plus tail bound:
   `|S_{N+d}(Y_{v_target})(b) − β| ≤ 2 · (s_max − s_min) / 2ʲ + 4K · 2⁻ᴺ`.
-/

namespace HAomega

/-- Initial data list of length `F.length` with component `u_shoot` set to `s`
and all other components read from `a₀`. -/
def shootInit (F : List JExprN) (a₀ : List Q) (u_shoot : Nat) (s : Q) : List Q :=
  (List.range F.length).map fun w ↦ if w = u_shoot then s else a₀.getD w Q.zero

/-- Boundary residual `S_N(Y_{v_target})(b) − β` for trial parameter `s`. -/
def shootResidual (F : List JExprN) (a₀ : List Q) (u_shoot v_target : Nat)
    (b β : Q) (N : Nat) (s : Q) : Q :=
  Q.sub (Jet.evalPoly ⟨solFastD F (shootInit F a₀ u_shoot s) v_target⟩ N b) β

/-- Sign coloring of the shooting residual on the grid `rootGrid s_min s_max j k`:
`1` where the residual is negative, `0` where it is non-negative. -/
def shootColor (F : List JExprN) (a₀ : List Q) (u_shoot v_target : Nat)
    (b β s_min s_max : Q) (j N : Nat) (k : Nat) : Nat :=
  Q.ltN (shootResidual F a₀ u_shoot v_target b β N (rootGrid s_min s_max j k)) (Q.ofNat 0)

/-- Grid index returned by bisection on `shootColor`. -/
def shootIndex (F : List JExprN) (a₀ : List Q) (u_shoot v_target : Nat)
    (b β s_min s_max : Q) (j N : Nat) : Nat :=
  bisect j (shootColor F a₀ u_shoot v_target b β s_min s_max j N) 0

/-- **The shooting operator**: returns the initial parameter `s* ∈ [s_min, s_max]`
solving the two-point boundary value problem. -/
def shootBVP (F : List JExprN) (a₀ : List Q) (u_shoot v_target : Nat)
    (b β s_min s_max : Q) (j N : Nat) : Q :=
  rootGrid s_min s_max j (shootIndex F a₀ u_shoot v_target b β s_min s_max j N)

/-! ## Properties of `shootInit` -/

theorem sht_shootInit_length (F : List JExprN) (a₀ : List Q) (u_shoot : Nat) (s : Q) :
    (shootInit F a₀ u_shoot s).length = F.length := by
  simp [shootInit]

theorem sht_shootInit_getD (F : List JExprN) (a₀ : List Q) (u_shoot : Nat) (s : Q)
    (w : Nat) (hw : w < F.length) :
    (shootInit F a₀ u_shoot s).getD w Q.zero =
      if w = u_shoot then s else a₀.getD w Q.zero := by
  have hw' : w < (shootInit F a₀ u_shoot s).length := by simp [shootInit, hw]
  rw [uDeriv_getD_eq_getElem _ Q.zero w hw']
  simp [shootInit]

theorem sht_shootInit_zero_val (F : List JExprN) (a₀ : List Q) (u_shoot : Nat) (s : Q)
    (w : Nat) (hw : w < F.length) :
    (solFastD F (shootInit F a₀ u_shoot s) w 0).val =
      (if w = u_shoot then s else a₀.getD w Q.zero).val := by
  have hw' : w < (shootInit F a₀ u_shoot s).length := by simp [shootInit, hw]
  rw [rct_solFastD_zero F (shootInit F a₀ u_shoot s) w hw',
      ← uDeriv_getD_eq_getElem (shootInit F a₀ u_shoot s) Q.zero w hw',
      sht_shootInit_getD F a₀ u_shoot s w hw]

theorem sht_shootInit_bound (F : List JExprN) (a₀ : List Q) (u_shoot : Nat) (s : Q)
    {K : Rat} (ha₀ : ∀ w < F.length, |(a₀.getD w Q.zero).val| ≤ K) (hs : |s.val| ≤ K)
    (w : Nat) (hw : w < F.length) :
    |((shootInit F a₀ u_shoot s).getD w Q.zero).val| ≤ K := by
  rw [sht_shootInit_getD F a₀ u_shoot s w hw]
  split
  · exact hs
  · exact ha₀ w hw

theorem sht_shootInit_diff_bound (F : List JExprN) (a₀ : List Q) (u_shoot : Nat) (s₁ s₂ : Q)
    (w : Nat) (hw : w < F.length) :
    |((shootInit F a₀ u_shoot s₁).getD w Q.zero).val -
      ((shootInit F a₀ u_shoot s₂).getD w Q.zero).val| ≤ |s₁.val - s₂.val| := by
  rw [sht_shootInit_getD F a₀ u_shoot s₁ w hw,
      sht_shootInit_getD F a₀ u_shoot s₂ w hw]
  split
  · exact le_refl _
  · rw [sub_self, abs_zero]
    exact abs_nonneg _

/-! ## Certificate of the shooting method -/

/-- **Certificate of the shooting operator (`shootBVP_spec`).**
If the shooting residual changes sign between `s_min` and `s_max`, then for
`s* := shootBVP F a₀ u_shoot v_target b β s_min s_max j N` and every `d : Nat`:
1. `s_min ≤ s* ≤ s_max`,
2. at `x = 0`, `solFastD` satisfies the initial condition `a₀` (with `s*` at `u_shoot`),
3. at `x = b`, the degree-`(N + d)` partial sum of `Y_{v_target}` is within
   `2 · (s_max − s_min) / 2ʲ + 4K · 2⁻ᴺ` of the target value `β`. -/
theorem shootBVP_spec (F : List JExprN) (hF : StepEqs F)
    (a₀ : List Q) (u_shoot v_target : Nat) (hv : v_target < F.length)
    (b β s_min s_max : Q) (j N : Nat)
    {K B : Rat} (hK1 : 1 ≤ K) (hB : 4 ≤ B)
    (ha₀ : ∀ w < F.length, |(a₀.getD w Q.zero).val| ≤ K)
    (hs_min : |s_min.val| ≤ K) (hs_max : |s_max.val| ≤ K)
    (hs_le : s_min.val ≤ s_max.val)
    (hStep : ∀ Fv ∈ F, 4 * sbdExprBound Fv K ≤ B)
    (hDiffStep : ∀ Fv ∈ F, 4 * sptDiffBound Fv K 1 ≤ B)
    (hb : |b.val| ≤ 1 / (4 * B))
    (hends : shootColor F a₀ u_shoot v_target b β s_min s_max j N 0 ≠
      shootColor F a₀ u_shoot v_target b β s_min s_max j N (2 ^ j))
    (d : Nat) :
    let s_star := shootBVP F a₀ u_shoot v_target b β s_min s_max j N
    s_min.val ≤ s_star.val ∧ s_star.val ≤ s_max.val ∧
    (∀ w < F.length,
      (solFastD F (shootInit F a₀ u_shoot s_star) w 0).val =
        (if w = u_shoot then s_star else a₀.getD w Q.zero).val) ∧
    |(Jet.evalPoly ⟨solFastD F (shootInit F a₀ u_shoot s_star) v_target⟩ (N + d) b).val - β.val| ≤
      2 * ((s_max.val - s_min.val) / (2 : Rat) ^ j) + 4 * K * (1 / 2 : Rat) ^ N := by
  intro s_star
  set c := shootColor F a₀ u_shoot v_target b β s_min s_max j N with hcdef
  have hb0 : c 0 ≠ c (0 + 2 ^ j) := by rwa [Nat.zero_add]
  obtain ⟨hi, hci⟩ := bisect_spec j c 0 hb0
  set i := bisect j c 0 with hidef
  rw [Nat.zero_add] at hci
  have hstar_eq : s_star = rootGrid s_min s_max j i := rfl
  rw [hstar_eq]
  set x := rootGrid s_min s_max j i with hxdef
  set y := rootGrid s_min s_max j (i + 1) with hydef
  have hxm := rootGrid_mem s_min s_max j i hs_le (le_of_lt hi)
  have hym := rootGrid_mem s_min s_max j (i + 1) hs_le hi
  refine ⟨hxm.1, hxm.2, fun w hw ↦ sht_shootInit_zero_val F a₀ u_shoot x w hw, ?_⟩
  have hK_disk : ∀ z : Q, s_min.val ≤ z.val → z.val ≤ s_max.val → |z.val| ≤ K := by
    intro z h1 h2
    rw [abs_le] at hs_min hs_max ⊢
    constructor <;> linarith [hs_min.1, hs_max.2]
  have hxK : |x.val| ≤ K := hK_disk x hxm.1 hxm.2
  have hyK : |y.val| ≤ K := hK_disk y hym.1 hym.2
  let ax := shootInit F a₀ u_shoot x
  let ay := shootInit F a₀ u_shoot y
  let δ : Rat := (s_max.val - s_min.val) / (2 : Rat) ^ j
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    have : 0 ≤ s_max.val - s_min.val := by linarith
    positivity
  have hstep : |x.val - y.val| = δ := by
    have hst := rootGrid_step s_min s_max j i
    rw [abs_sub_comm, abs_of_nonneg (by
      rw [← hydef, ← hxdef] at hst; rw [hst]; exact hδ)]
    exact hst
  have hax_bd : ∀ w < F.length, |(ax.getD w Q.zero).val| ≤ K :=
    sht_shootInit_bound F a₀ u_shoot x ha₀ hxK
  have hay_bd : ∀ w < F.length, |(ay.getD w Q.zero).val| ≤ K :=
    sht_shootInit_bound F a₀ u_shoot y ha₀ hyK
  have hdiff_xy : ∀ w < F.length, |(ax.getD w Q.zero).val - (ay.getD w Q.zero).val| ≤ δ := by
    intro w hw
    rw [← hstep]
    exact sht_shootInit_diff_bound F a₀ u_shoot x y w hw
  have hdiff_xx : ∀ w < F.length, |(ax.getD w Q.zero).val - (ax.getD w Q.zero).val| ≤ 0 := by
    intro w _
    rw [sub_self, abs_zero]
  have h_lip_xy := stp_evalPoly_solFastD_diff F hF ax ay hK1 hδ hB
    hax_bd hay_bd hStep hdiff_xy hDiffStep b hb (Nat.le_add_right N d) (le_refl N) v_target hv
  have h_lip_xx := stp_evalPoly_solFastD_diff F hF ax ax hK1 (le_refl 0) hB
    hax_bd hax_bd hStep hdiff_xx hDiffStep b hb (Nat.le_add_right N d) (le_refl N) v_target hv
  set Pxd := (Jet.evalPoly ⟨solFastD F ax v_target⟩ (N + d) b).val
  set Px := (Jet.evalPoly ⟨solFastD F ax v_target⟩ N b).val
  set Py := (Jet.evalPoly ⟨solFastD F ay v_target⟩ N b).val
  rw [abs_le] at h_lip_xy h_lip_xx ⊢
  have hrx_val : (shootResidual F a₀ u_shoot v_target b β N x).val = Px - β.val :=
    Q.val_sub _ _
  have hry_val : (shootResidual F a₀ u_shoot v_target b β N y).val = Py - β.val :=
    Q.val_sub _ _
  rcases Q.ltN_eq_zero_or_one (shootResidual F a₀ u_shoot v_target b β N x) (Q.ofNat 0) with hx0 | hx1 <;>
  rcases Q.ltN_eq_zero_or_one (shootResidual F a₀ u_shoot v_target b β N y) (Q.ofNat 0) with hy0 | hy1
  · exact absurd (hx0.trans hy0.symm) hci
  · rw [Q.ltN_eq_zero_iff, Q.val_ofNat_zero, hrx_val] at hx0
    rw [Q.ltN_eq_one_iff, Q.val_ofNat_zero, hry_val] at hy1
    constructor <;> linarith
  · rw [Q.ltN_eq_one_iff, Q.val_ofNat_zero, hrx_val] at hx1
    rw [Q.ltN_eq_zero_iff, Q.val_ofNat_zero, hry_val] at hy0
    constructor <;> linarith
  · exact absurd (hx1.trans hy1.symm) hci

/-- **Uniform disk version of the shooting theorem (`shootBVP_certified`).**
For any flat system `StepEqs F` and initial data bound `2^D`, there is a uniform
radius `R` such that for any boundary point `|b| ≤ 2^{-(R+2)}` and any bracket
`[s_min, s_max] ⊆ [-2^D, 2^D]` with opposite residual signs at degree `N`,
`shootBVP` certifies the boundary value within `2 · (s_max − s_min) / 2ʲ + 4 · 2^D · 2⁻ᴺ`. -/
theorem shootBVP_certified (F : List JExprN) (hF : StepEqs F) (D : Nat) :
    ∃ R : Nat, ∀ (a₀ : List Q) (u_shoot v_target : Nat), v_target < F.length →
      (∀ w < F.length, |(a₀.getD w Q.zero).val| ≤ (2 : Rat) ^ D) →
      ∀ (b β s_min s_max : Q) (j N d : Nat),
      |s_min.val| ≤ (2 : Rat) ^ D → |s_max.val| ≤ (2 : Rat) ^ D →
      s_min.val ≤ s_max.val →
      |b.val| ≤ 1 / (2 : Rat) ^ (R + 2) →
      shootColor F a₀ u_shoot v_target b β s_min s_max j N 0 ≠
        shootColor F a₀ u_shoot v_target b β s_min s_max j N (2 ^ j) →
      let s_star := shootBVP F a₀ u_shoot v_target b β s_min s_max j N
      s_min.val ≤ s_star.val ∧ s_star.val ≤ s_max.val ∧
      (∀ w < F.length,
        (solFastD F (shootInit F a₀ u_shoot s_star) w 0).val =
          (if w = u_shoot then s_star else a₀.getD w Q.zero).val) ∧
      |(Jet.evalPoly ⟨solFastD F (shootInit F a₀ u_shoot s_star) v_target⟩ (N + d) b).val - β.val| ≤
        2 * ((s_max.val - s_min.val) / (2 : Rat) ^ j) + 4 * (2 : Rat) ^ D * (1 / 2 : Rat) ^ N := by
  let K : Rat := (2 : Rat) ^ D
  have hK1 : (1 : Rat) ≤ K := one_le_pow₀ (by norm_num)
  rcases sbd_exists_two_pow_ge
    (max 4 (max (4 * sptMaxPhi K F) (4 * sptMaxPsi K 1 F))) with ⟨R, hR⟩
  let B : Rat := (2 : Rat) ^ R
  have hB : (4 : Rat) ≤ B := le_trans (le_max_left _ _) hR
  have hR_right : max (4 * sptMaxPhi K F) (4 * sptMaxPsi K 1 F) ≤ B :=
    le_trans (le_max_right _ _) hR
  have hStep : ∀ Fv ∈ F, 4 * sbdExprBound Fv K ≤ B := by
    intro Fv hFv
    have h1 := sptMaxPhi_mem K hFv
    have h2 : 4 * sptMaxPhi K F ≤ B := le_trans (le_max_left _ _) hR_right
    linarith
  have hDiffStep : ∀ Fv ∈ F, 4 * sptDiffBound Fv K 1 ≤ B := by
    intro Fv hFv
    have h1 := sptMaxPsi_mem K 1 hFv
    have h2 : 4 * sptMaxPsi K 1 F ≤ B := le_trans (le_max_right _ _) hR_right
    linarith
  have hpow_R2 : (2 : Rat) ^ (R + 2) = 4 * B := by
    change (2 : Rat) ^ (R + 2) = 4 * (2 : Rat) ^ R
    rw [pow_add]
    ring
  refine ⟨R, fun a₀ u_shoot v_target hv ha₀ b β s_min s_max j N d hs_min hs_max hs_le hb hends ↦ ?_⟩
  have hb' : |b.val| ≤ 1 / (4 * B) := by rwa [← hpow_R2]
  exact shootBVP_spec F hF a₀ u_shoot v_target hv b β s_min s_max j N
    hK1 hB ha₀ hs_min hs_max hs_le hStep hDiffStep hb' hends d

/-! ## Checks: Harmonic Oscillator BVP & Nonlinear Duffing BVP

1. **Harmonic oscillator BVP:** `y'' + y = 0` (`y_0' = y_1, y_1' = −y_0`, `memSinCosSys`),
   with `y_0(0) = 0` and `y_0(1/4) = 1/5`, shooting for `s = y_1(0) ∈ [0, 1]`.
   Exact initial slope: `s* = (1/5) / sin(1/4) ≈ 0.8083988892`.
2. **Nonlinear Duffing BVP:** `u' = v, v' = −u − u²` with `u(0) = 0` and
   `u(1/8) = 1/10`, shooting for `s = v(0) ∈ [0, 1]`. -/

/-- Flat right-hand sides for the Duffing system `u' = v, v' = −u − u²`. -/
def shootDuffingEqs : List JExprN :=
  [.var 1, .sub (.sub (.const tmZeroJet) (.var 0)) (.mul (.var 0) (.var 0))]

-- Endpoint sign-change checks:
#guard shootColor (memSinCosSys.map Prod.snd) [Q.zero, Q.zero] 1 0 ⟨1, 3⟩ ⟨1, 4⟩ Q.zero (Q.ofNat 1) 35 16 0 = 1 ∧
       shootColor (memSinCosSys.map Prod.snd) [Q.zero, Q.zero] 1 0 ⟨1, 3⟩ ⟨1, 4⟩ Q.zero (Q.ofNat 1) 35 16 (2 ^ 35) = 0

#guard shootColor shootDuffingEqs [Q.zero, Q.zero] 1 0 ⟨1, 7⟩ ⟨1, 9⟩ Q.zero (Q.ofNat 1) 35 14 0 = 1 ∧
       shootColor shootDuffingEqs [Q.zero, Q.zero] 1 0 ⟨1, 7⟩ ⟨1, 9⟩ Q.zero (Q.ofNat 1) 35 14 (2 ^ 35) = 0

-- 1. Harmonic oscillator BVP: s* agrees with (1/5)/sin(1/4) to 10⁻¹⁰, and residual < 10⁻¹⁰
#guard (let F := memSinCosSys.map Prod.snd
        let s := shootBVP F [Q.zero, Q.zero] 1 0 ⟨1, 3⟩ ⟨1, 4⟩ Q.zero (Q.ofNat 1) 35 16
        let res := shootResidual F [Q.zero, Q.zero] 1 0 ⟨1, 3⟩ ⟨1, 4⟩ 16 s
        (Float.ofInt s.num / Float.ofNat s.den - 0.2 / Float.sin 0.25).abs < 1e-10 ∧
        decide (|res.val| < (1 : Rat) / 10 ^ 10))

-- 2. Nonlinear Duffing BVP: boundary residual at x = 1/8 is < 10⁻¹⁰
#guard (let s := shootBVP shootDuffingEqs [Q.zero, Q.zero] 1 0 ⟨1, 7⟩ ⟨1, 9⟩ Q.zero (Q.ofNat 1) 35 14
        let res := shootResidual shootDuffingEqs [Q.zero, Q.zero] 1 0 ⟨1, 7⟩ ⟨1, 9⟩ 14 s
        decide (|res.val| < (1 : Rat) / 10 ^ 10))

#print axioms shootBVP
#print axioms shootBVP_spec
#print axioms shootBVP_certified

end HAomega
