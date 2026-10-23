/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PolyODEUnique

/-!
# Composition, proved: `expComp G` is `exp ∘ (G − G(0))`

`ComposeSolve.lean` obtains `exp ∘ (G − G(0))` as the general solver at
`Y = 1 + ∫(G'·Y)` and checked agreement with the metatheory's `Jet.compZero`
only at instances. This module proves it for every closed jet `G`:

* `compZero_exp_solves` — the chain rule, as values: `Jet.compZero Jet.exp G`
  solves `Y = 1 + ∫(G'·Y)` at every index;
* `expComp_eq_compZero` — hence, by `genSolve_unique_val`, the proof-computed
  `expComp G k` agrees with it below degree `k`.
-/

namespace HAomega

open Rat

/-- Multiply a jet `A` by `G(x) - G(0) = x · G.shift(x)`. -/
def mulShift (G A : Jet) : Jet :=
  ⟨fun n ↦ match n with
    | 0 => Q.zero
    | k + 1 => Jet.cauchyConvAux G.shift A k (k + 1)⟩

/-- The `r`-th formal power `(G(x) - G(0))^r` defined via `mulShift`. -/
def hPow (G : Jet) : Nat → Jet
  | 0 => ⟨fun n ↦ match n with | 0 => Q.ofNat 1 | _ + 1 => Q.zero⟩
  | r + 1 => mulShift G (hPow G r)

/-- `compZeroIter F G m n s` expands as the finite sum `∑_{r ≤ m} F_{s+r} · ((hPow G r)_n)`. -/
theorem compZeroIter_val_eq_sum (F G : Jet) : ∀ (m n s : Nat),
    (RadiusJet.compZeroIter F G m n s).val =
      ∑ r ∈ Finset.range (m + 1), (F.coeff (s + r)).val * ((hPow G r).coeff n).val
  | 0, 0, s => by
    simp [RadiusJet.compZeroIter, hPow, Q.val_ofNat]
  | 0, k + 1, s => by
    simp [RadiusJet.compZeroIter, hPow, Q.val_zero]
  | m + 1, 0, s => by
    dsimp [RadiusJet.compZeroIter]
    rw [Finset.sum_range_succ']
    have h0 : ∑ k ∈ Finset.range (m + 1),
        (F.coeff (s + (k + 1))).val * ((hPow G (k + 1)).coeff 0).val = 0 := by
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      dsimp [hPow, mulShift]
      rw [Q.val_zero, mul_zero]
    rw [h0, zero_add, Nat.add_zero]
    dsimp [hPow]
    rw [Q.val_ofNat]
    ring
  | m + 1, k + 1, s => by
    dsimp [RadiusJet.compZeroIter]
    rw [TrigPoly.cauchyConvAux_val]
    have h1 : (∑ a ∈ Finset.range (k + 1),
        (G.shift.coeff a).val * (RadiusJet.compZeroIter F G m (k - a) (s + 1)).val) =
      ∑ a ∈ Finset.range (k + 1),
        ∑ r ∈ Finset.range (m + 1),
          (F.coeff (s + (r + 1))).val * ((G.shift.coeff a).val * ((hPow G r).coeff (k - a)).val) := by
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [compZeroIter_val_eq_sum F G m (k - a) (s + 1), Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      have hsr : s + 1 + r = s + (r + 1) := by omega
      rw [hsr]
      ring
    rw [h1, Finset.sum_comm]
    rw [Finset.sum_range_succ' _ (m + 1)]
    have h0 : (F.coeff (s + 0)).val * ((hPow G 0).coeff (k + 1)).val = 0 := by
      dsimp [hPow]
      rw [Q.val_zero, mul_zero]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [← Finset.mul_sum]
    congr 1
    dsimp [hPow, mulShift]
    rw [TrigPoly.cauchyConvAux_val]

/-- `(hPow G r).coeff n` has value `0` whenever `n < r`. -/
theorem hPow_coeff_val_zero_of_lt (G : Jet) : ∀ (r n : Nat), n < r →
    ((hPow G r).coeff n).val = 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | r + 1, 0, _ => Q.val_zero
  | r + 1, k + 1, h => by
    dsimp [hPow, mulShift]
    rw [TrigPoly.cauchyConvAux_val]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [hPow_coeff_val_zero_of_lt G r (k - j) (by omega), mul_zero]

/-- For any `k ≤ m`, `(Jet.compZero F G).coeff k` equals the `m + 1` partial sum of `hPow G`. -/
theorem compZero_coeff_val_eq_sum (F G : Jet) (m k : Nat) (hkm : k ≤ m) :
    ((Jet.compZero F G).coeff k).val =
      ∑ r ∈ Finset.range (m + 1), (F.coeff r).val * ((hPow G r).coeff k).val := by
  dsimp [Jet.compZero]
  rw [compZeroIter_val_eq_sum F G k k 0]
  simp only [Nat.zero_add]
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun r hr hnot ↦ ?_
  rw [Finset.mem_range] at hr hnot
  rw [hPow_coeff_val_zero_of_lt G r k (by omega), mul_zero]

/-- Summing over `Finset.range (k - j + 1)` equals summing over `Finset.range (k + 1)` with guard `j + i ≤ k`. -/
theorem sum_range_sub_eq_sum_ite (k j : Nat) (hj : j ≤ k) (g : Nat → Rat) :
    (∑ i ∈ Finset.range (k - j + 1), g i) =
      ∑ i ∈ Finset.range (k + 1), if j + i ≤ k then g i else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- Swapping the order of summation in a triangular double sum `j + i ≤ k`. -/
theorem sum_triangle_swap (k : Nat) (f : Nat → Nat → Rat) :
    (∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k - j + 1), f j i) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1), f j i := by
  trans (∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1), if j + i ≤ k then f j i else 0)
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    exact sum_range_sub_eq_sum_ite k j (by omega) (fun i ↦ f j i)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [sum_range_sub_eq_sum_ite k i (by omega) (fun j ↦ f j i)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Nat.add_comm]

/-- `mulShift G` commutes with left Cauchy multiplication by `B`. -/
theorem mulShift_mul_val (G B C : Jet) (n : Nat) :
    ((mulShift G (B.mul C)).coeff n).val = ((B.mul (mulShift G C)).coeff n).val := by
  cases n with
  | zero =>
    dsimp [mulShift, Jet.mul, Jet.cauchyConvAux]
    rw [Q.val_zero, Q.val_add, Q.val_zero, Q.val_mul, Q.val_zero, mul_zero, add_zero]
  | succ k =>
    change (Jet.cauchyConvAux G.shift (B.mul C) k (k + 1)).val =
      (Jet.cauchyConvAux B (mulShift G C) (k + 1) (k + 1 + 1)).val
    rw [TrigPoly.cauchyConvAux_val, TrigPoly.cauchyConvAux_val, Finset.sum_range_succ _ (k + 1)]
    have hlast : (B.coeff (k + 1)).val * ((mulShift G C).coeff (k + 1 - (k + 1))).val = 0 := by
      rw [Nat.sub_self]
      dsimp [mulShift]
      rw [Q.val_zero, mul_zero]
    rw [hlast, add_zero]
    have hL : (∑ j ∈ Finset.range (k + 1),
        (G.shift.coeff j).val * ((B.mul C).coeff (k - j)).val) =
      ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k - j + 1),
        (G.shift.coeff j).val * (B.coeff i).val * (C.coeff (k - j - i)).val := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      dsimp [Jet.mul]
      rw [TrigPoly.cauchyConvAux_val, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have hR : (∑ i ∈ Finset.range (k + 1),
        (B.coeff i).val * ((mulShift G C).coeff (k + 1 - i)).val) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k - i + 1),
        (G.shift.coeff j).val * (B.coeff i).val * (C.coeff (k - j - i)).val := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Finset.mem_range] at hi
      have hsub : k + 1 - i = (k - i) + 1 := by omega
      rw [hsub]
      dsimp [mulShift]
      rw [TrigPoly.cauchyConvAux_val, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hij : k - i - j = k - j - i := by omega
      rw [hij]
      ring
    rw [hL, hR]
    exact sum_triangle_swap k (fun j i ↦
      (G.shift.coeff j).val * (B.coeff i).val * (C.coeff (k - j - i)).val)

/-- Product rule for `mulShift G A`: `D((G - G(0)) · A) = G' · A + (G - G(0)) · D(A)`. -/
theorem deriv_mulShift_val (G A : Jet) (n : Nat) :
    (((mulShift G A).deriv).coeff n).val =
      ((G.deriv.mul A).coeff n).val + ((mulShift G A.deriv).coeff n).val := by
  dsimp [Jet.deriv, mulShift, Jet.mul]
  rw [Q.val_mul, Q.val_ofNat, TrigPoly.cauchyConvAux_val, TrigPoly.cauchyConvAux_val, Finset.mul_sum]
  have hsplit : (∑ a ∈ Finset.range (n + 1),
      ((n + 1 : Nat) : Rat) * ((G.shift.coeff a).val * (A.coeff (n - a)).val)) =
    (∑ a ∈ Finset.range (n + 1),
      (Q.mul (Q.ofNat (a + 1)) (G.coeff (a + 1))).val * (A.coeff (n - a)).val) +
    (∑ a ∈ Finset.range (n + 1),
      (G.shift.coeff a).val * (((n - a : Nat) : Rat) * (A.coeff (n - a)).val)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [Finset.mem_range] at ha
    rw [Q.val_mul, Q.val_ofNat]
    dsimp [Jet.shift]
    have hna : ((n + 1 : Nat) : Rat) = ((a + 1 : Nat) : Rat) + ((n - a : Nat) : Rat) := by
      exact_mod_cast (by omega : n + 1 = (a + 1) + (n - a))
    rw [hna]
    ring
  rw [hsplit]
  congr 1
  cases n with
  | zero =>
    rw [Finset.sum_range_one, Nat.sub_zero, Nat.cast_zero, zero_mul, mul_zero, Q.val_zero]
  | succ k =>
    rw [Finset.sum_range_succ, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    rw [TrigPoly.cauchyConvAux_val]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [Finset.mem_range] at ha
    have hsub : k + 1 - a = (k - a) + 1 := by omega
    rw [hsub]
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat]

/-- Power rule for `hPow G`: `D((G - G(0))^(r + 1)) = (r + 1) · (G' · (G - G(0))^r)`. -/
theorem deriv_hPow_val (G : Jet) : ∀ (r n : Nat),
    (((hPow G (r + 1)).deriv).coeff n).val =
      ((r + 1 : Nat) : Rat) * ((G.deriv.mul (hPow G r)).coeff n).val
  | 0, n => by
    change (((mulShift G (hPow G 0)).deriv).coeff n).val = _
    rw [deriv_mulShift_val]
    have h0 : ((mulShift G (hPow G 0).deriv).coeff n).val = 0 := by
      cases n with
      | zero => exact Q.val_zero
      | succ k =>
        dsimp [mulShift]
        rw [TrigPoly.cauchyConvAux_val]
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        dsimp [Jet.deriv, hPow]
        rw [Q.val_mul, Q.val_zero, mul_zero, mul_zero]
    rw [h0, add_zero, Nat.zero_add, Nat.cast_one, one_mul]
  | r + 1, n => by
    change (((mulShift G (hPow G (r + 1))).deriv).coeff n).val = _
    rw [deriv_mulShift_val]
    have hscale : ((mulShift G (hPow G (r + 1)).deriv).coeff n).val =
        ((r + 1 : Nat) : Rat) * ((mulShift G (G.deriv.mul (hPow G r))).coeff n).val := by
      cases n with
      | zero =>
        dsimp [mulShift]
        rw [Q.val_zero, mul_zero]
      | succ k =>
        dsimp [mulShift]
        rw [TrigPoly.cauchyConvAux_val, TrigPoly.cauchyConvAux_val, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [deriv_hPow_val G r (k - j)]
        ring
    rw [hscale, mulShift_mul_val]
    change ((G.deriv.mul (hPow G (r + 1))).coeff n).val +
        ((r + 1 : Nat) : Rat) * ((G.deriv.mul (hPow G (r + 1))).coeff n).val =
      ((r + 1 + 1 : Nat) : Rat) * ((G.deriv.mul (hPow G (r + 1))).coeff n).val
    push_cast
    ring

/-- Formal chain rule for `Jet.compZero Jet.exp G`: `D(exp ∘ (G - G(0))) = G' · (exp ∘ (G - G(0)))`. -/
theorem deriv_compZero_exp_val (G : Jet) (n : Nat) :
    (((Jet.compZero Jet.exp G).deriv).coeff n).val =
      ((G.deriv.mul (Jet.compZero Jet.exp G)).coeff n).val := by
  have h1 : (((Jet.compZero Jet.exp G).deriv).coeff n).val =
      ((n + 1 : Nat) : Rat) * ((Jet.compZero Jet.exp G).coeff (n + 1)).val := by
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat]
  rw [h1, compZero_coeff_val_eq_sum Jet.exp G (n + 1) (n + 1) (le_refl _)]
  rw [Finset.sum_range_succ']
  have h0 : (Jet.exp.coeff 0).val * ((hPow G 0).coeff (n + 1)).val = 0 := by
    dsimp [hPow]
    rw [Q.val_zero, mul_zero]
  rw [h0, add_zero, Finset.mul_sum]
  have h2 : (∑ r ∈ Finset.range (n + 1),
      ((n + 1 : Nat) : Rat) * ((Jet.exp.coeff (r + 1)).val * ((hPow G (r + 1)).coeff (n + 1)).val)) =
    ∑ r ∈ Finset.range (n + 1),
      (Jet.exp.coeff r).val * ((G.deriv.mul (hPow G r)).coeff n).val := by
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hdh : ((n + 1 : Nat) : Rat) * ((hPow G (r + 1)).coeff (n + 1)).val =
        (((hPow G (r + 1)).deriv).coeff n).val := by
      dsimp [Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat]
    have hexp : ((r + 1 : Nat) : Rat) * (Jet.exp.coeff (r + 1)).val = (Jet.exp.coeff r).val := by
      have he := Jet.exp_deriv_val r
      dsimp [Jet.deriv] at he
      rwa [Q.val_mul, Q.val_ofNat] at he
    calc ((n + 1 : Nat) : Rat) * ((Jet.exp.coeff (r + 1)).val * ((hPow G (r + 1)).coeff (n + 1)).val)
      _ = (Jet.exp.coeff (r + 1)).val * (((n + 1 : Nat) : Rat) * ((hPow G (r + 1)).coeff (n + 1)).val) := by ring
      _ = (Jet.exp.coeff (r + 1)).val * (((hPow G (r + 1)).deriv).coeff n).val := by rw [hdh]
      _ = (Jet.exp.coeff (r + 1)).val * (((r + 1 : Nat) : Rat) * ((G.deriv.mul (hPow G r)).coeff n).val) := by
          rw [deriv_hPow_val G r n]
      _ = (((r + 1 : Nat) : Rat) * (Jet.exp.coeff (r + 1)).val) * ((G.deriv.mul (hPow G r)).coeff n).val := by ring
      _ = (Jet.exp.coeff r).val * ((G.deriv.mul (hPow G r)).coeff n).val := by rw [hexp]
  rw [h2]
  have h3 : (∑ r ∈ Finset.range (n + 1),
      (Jet.exp.coeff r).val * ((G.deriv.mul (hPow G r)).coeff n).val) =
    ∑ r ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      (G.deriv.coeff j).val * ((Jet.exp.coeff r).val * ((hPow G r).coeff (n - j)).val) := by
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    dsimp [Jet.mul]
    rw [TrigPoly.cauchyConvAux_val, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [h3, Finset.sum_comm]
  dsimp [Jet.mul]
  rw [TrigPoly.cauchyConvAux_val]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [← Finset.mul_sum, ← compZero_coeff_val_eq_sum Jet.exp G n (n - j) (by omega)]

/-- The chain rule for `exp`, as values: `exp(G − G(0))` solves `Y = 1 + ∫(G'·Y)`. -/
theorem compZero_exp_solves (G : Tm [] JetTy) (n : Nat) :
    let Z := (Jet.compZero Jet.exp ⟨G.eval Env.nil⟩).coeff
    (((genStep tmConstOneJet (.mul (.const (.app tmJetDeriv G)) .var) (Γ := [])).eval Env.nil
      Z) n).val = (Z n).val := by
  intro Z
  let e : Env [JetTy] := Env.cons Z Env.nil
  cases n with
  | zero =>
    show (Q.add ((Tm.closedWk tmConstOneJet).eval e 0) Q.zero).val = (Z 0).val
    rw [closedWk_eval tmConstOneJet e, Q.val_add, Q.val_zero, add_zero]
    have h1 : (tmConstOneJet (Γ := []).eval Env.nil 0).val = 1 := Q.val_ofNat 1
    have hZ0 : (Z 0).val = 1 := by
      change (Jet.exp.coeff 0).val = 1
      dsimp [Jet.exp, fact]
      have hne : (Q.ofNat 1).num ≠ 0 := by decide
      rw [Q.val_div _ _ hne, Q.val_ofNat]
      norm_num
    rw [h1, hZ0]
  | succ k =>
    have hne : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
    have hrat : ((k + 1 : Nat) : Rat) ≠ 0 := by positivity
    let rhs := (((tmJetMul (Γ := [JetTy])).eval e)
      ((Tm.closedWk (.app tmJetDeriv G)).eval e) Z) k
    show (Q.add ((Tm.closedWk tmConstOneJet).eval e (k + 1))
      (Q.div rhs (Q.ofNat (k + 1)))).val = (Z (k + 1)).val
    rw [closedWk_eval tmConstOneJet e, Q.val_add, Q.val_div _ _ hne, Q.val_ofNat]
    have h0 : (tmConstOneJet (Γ := []).eval Env.nil (k + 1)).val = 0 := Q.val_ofNat 0
    rw [h0, zero_add]
    have hrhs : rhs.val = (((Jet.compZero Jet.exp ⟨G.eval Env.nil⟩).deriv).coeff k).val := by
      dsimp [rhs]
      rw [tmJetMul_eval, closedWk_eval (.app tmJetDeriv G) e]
      exact (deriv_compZero_exp_val ⟨G.eval Env.nil⟩ k).symm
    rw [hrhs]
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat]
    exact mul_div_cancel_left₀ (Z (k + 1)).val hrat

/-- The proof-computed composition agrees with `Jet.compZero` below degree `k`. -/
theorem expComp_eq_compZero (G : Tm [] JetTy) (k i : Nat) (hi : i < k) :
    (expComp G k i).val = ((Jet.compZero Jet.exp ⟨G.eval Env.nil⟩).coeff i).val :=
  genSolve_unique_val tmConstOneJet (.mul (.const (.app tmJetDeriv G)) .var)
    (Jet.compZero Jet.exp ⟨G.eval Env.nil⟩).coeff (compZero_exp_solves G) k i hi

#print axioms compZero_exp_solves
#print axioms expComp_eq_compZero

end HAomega
