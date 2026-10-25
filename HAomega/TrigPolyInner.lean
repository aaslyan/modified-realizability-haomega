/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.TrigPoly

/-!
# Mean, inner product, orthogonality and Parseval for trigonometric polynomials

Room 6 of the closed universe, finite part. In the coefficient model of
`TrigPoly.lean` a polynomial is `Σ_{|k| ≤ N} c_k e^{ikx}`, so its **mean** over
a period is `c_0` — by definition here. The link to `(1/2π)∫₀^{2π}` is the
classical computation `∫₀^{2π} e^{ikx} dx = 2π·[k = 0]`; it is not formalized
(no real integral in HA^ω), and nothing below depends on it.

What is proved are the identities of the coefficient algebra that the integral
versions express, with the product the exact convolution `TrigPoly.mul`:

* `mean_deriv` — `mean(p′) = 0`;
* `mean_parts` — `mean(p′·q) = −mean(p·q′)` (integration by parts);
* `inner_modes` — `⟨e_j, e_k⟩ = [j = k]` (orthogonality);
* `parseval` — `⟨p, p⟩ = Σ_{|k| ≤ N} |c_k|²`.

All as values (`toCRat`), in the style of `TrigPoly.lean`.
-/

namespace HAomega

namespace TrigPoly

/-- The mean over a period: the constant coefficient. -/
def mean (p : TrigPoly) : CQ := p.coeff 0

/-- Complex conjugate of the function: `c_k ↦ conj c_{−k}`. -/
def conj (p : TrigPoly) : TrigPoly := ⟨p.deg, fun k ↦ CQ.conj (p.coeff (-k))⟩

/-- The inner product `⟨p, q⟩ := mean(p · conj q)`. -/
def inner (p q : TrigPoly) : CQ := mean (mul p (conj q))

/-- The pure mode `e^{ijx}`. -/
def mode (j : Int) : TrigPoly := ⟨j.natAbs, fun i ↦ if i = j then CQ.one else CQ.zero⟩

/-- `|z|²` for `z : CRat`. -/
def CRat.normSq (z : CRat) : Rat := z.re * z.re + z.im * z.im

/-- `ikCRat (-k)` equals `-ikCRat k` in `CRat`. -/
theorem tpi_ikCRat_neg (k : Int) : ikCRat (-k) = -ikCRat k := by
  ext
  · show (0 : Rat) = -0; ring
  · show ((-k : Int) : Rat) = -(k : Rat); push_cast; ring

/-- `toCRat` commutes with `CQ.conj`. -/
theorem tpi_toCRat_conj (z : CQ) : toCRat (CQ.conj z) = CRat.conj (toCRat z) := by
  ext
  · rfl
  · exact Q.val_neg z.im

/-- Value of `mean (mul p q)` in `CRat` as a sum over `Finset.Icc (-p.deg) p.deg`. -/
theorem tpi_mean_mul (p q : TrigPoly) :
    toCRat (mean (mul p q)) =
      ∑ j ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int),
        toCRat (p.coeff j) * toCRat (q.coeff (-j)) := by
  have h0 : (0 : Int).natAbs ≤ (mul p q).deg := Nat.zero_le _
  unfold mean
  rw [coeff, if_pos h0]
  dsimp [mul]
  rw [toCRat_foldl_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [zero_sub, toCRat_mul]

/-- Coefficient of `conj p` at `-j` in `CRat` is `CRat.conj (toCRat (p.coeff j))`. -/
theorem tpi_toCRat_conj_coeff_neg (p : TrigPoly) (j : Int) :
    toCRat ((conj p).coeff (-j)) = CRat.conj (toCRat (p.coeff j)) := by
  by_cases h : j.natAbs ≤ p.deg
  · have hneg : (-j).natAbs ≤ (conj p).deg := by
      dsimp [conj]
      rw [Int.natAbs_neg]
      exact h
    rw [coeff, if_pos hneg]
    dsimp [conj]
    rw [neg_neg, tpi_toCRat_conj]
  · have hneg : ¬ ((-j).natAbs ≤ (conj p).deg) := by
      dsimp [conj]
      rw [Int.natAbs_neg]
      exact h
    have hp : p.coeff j = CQ.zero := if_neg h
    rw [coeff, if_neg hneg, hp, toCRat_zero]
    ext <;> simp [CRat.conj]

/-- Value of `inner p q` in `CRat` as a sum over `Finset.Icc (-p.deg) p.deg`. -/
theorem tpi_inner_eq_sum (p q : TrigPoly) :
    toCRat (inner p q) =
      ∑ j ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int),
        toCRat (p.coeff j) * CRat.conj (toCRat (q.coeff j)) := by
  unfold inner
  rw [tpi_mean_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [tpi_toCRat_conj_coeff_neg]

/-- Coefficient `i` of `mode k` in `CRat` is `if i = k then 1 else 0`. -/
theorem tpi_toCRat_mode_coeff (k i : Int) :
    toCRat ((mode k).coeff i) = if i = k then 1 else 0 := by
  unfold coeff mode
  dsimp
  by_cases hik : i = k
  · subst hik
    rw [if_pos le_rfl, if_pos rfl, if_pos rfl, toCRat_one]
  · rw [if_neg hik, if_neg hik, ite_self, toCRat_zero]

/-- Multiplying `z : CRat` by its conjugate yields `⟨z.normSq, 0⟩`. -/
theorem tpi_mul_conj_eq_normSq (z : CRat) :
    z * CRat.conj z = ⟨z.normSq, 0⟩ := by
  ext <;> dsimp [CRat.conj, CRat.normSq] <;> ring

/-- **The mean of a derivative is zero.** -/
theorem mean_deriv (p : TrigPoly) : toCRat (mean (deriv p)) = 0 := by
  unfold mean
  rw [toCRat_deriv_coeff]
  ext <;> simp [ikCRat]

/-- **Integration by parts.** -/
theorem mean_parts (p q : TrigPoly) :
    toCRat (mean (mul (deriv p) q)) = -toCRat (mean (mul p (deriv q))) := by
  rw [tpi_mean_mul, tpi_mean_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [toCRat_deriv_coeff, toCRat_deriv_coeff, tpi_ikCRat_neg]
  ring

/-- **Orthogonality of the modes.** -/
theorem inner_modes (j k : Int) :
    toCRat (inner (mode j) (mode k)) = if j = k then 1 else 0 := by
  rw [tpi_inner_eq_sum]
  rw [Finset.sum_eq_single j]
  · rw [tpi_toCRat_mode_coeff, tpi_toCRat_mode_coeff, if_pos rfl, one_mul]
    split_ifs <;> ext <;> simp [CRat.conj]
  · intro i _ hij
    rw [tpi_toCRat_mode_coeff, if_neg hij, zero_mul]
  · intro hj
    exfalso
    apply hj
    rw [Finset.mem_Icc]
    dsimp [mode]
    omega

/-- **Parseval.** -/
theorem parseval (p : TrigPoly) :
    toCRat (inner p p) = ⟨∑ k ∈ Finset.Icc (-(p.deg : Int)) p.deg, (toCRat (p.coeff k)).normSq, 0⟩ := by
  rw [tpi_inner_eq_sum]
  ext
  · rw [CRat.re_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [tpi_mul_conj_eq_normSq]
  · rw [CRat.im_sum]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [tpi_mul_conj_eq_normSq]

/-! ## Checks

`cos(2x)` has `⟨cos 2x, cos 2x⟩ = 1/2` (two coefficients `1/2`), and
`⟨cos 2x, sin 2x⟩ = 0`. -/

#guard (let z := inner (cosMode 2) (cosMode 2); (Q.norm z.re, Q.norm z.im)) == (Q.norm ⟨1, 1⟩, Q.norm Q.zero)
#guard (let z := inner (cosMode 2) (sinMode 2); (Q.norm z.re, Q.norm z.im)) == (Q.norm Q.zero, Q.norm Q.zero)
#guard (let z := inner (mode 3) (mode (-3)); (Q.norm z.re, Q.norm z.im)) == (Q.norm Q.zero, Q.norm Q.zero)

#print axioms mean
#print axioms inner
#print axioms mean_deriv
#print axioms mean_parts
#print axioms inner_modes
#print axioms parseval

end TrigPoly

end HAomega
