/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseInv

/-!
# Composition of jets: the general chain rule and the ring-homomorphism laws

`Jet.compZero F G` is `F(G − G(0))`. `ComposeProof.lean` proved the chain rule
for `F = exp` only; here it is proved for every `F`:

  `D(F ∘ G) = G' · ((D F) ∘ G)`,

together with the facts that composing with `G` is a ring homomorphism and
fixes constants. These are what closing the GPAC universe under composition
needs. Value-level metatheory theorems (`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- **The chain rule**, as values. -/
theorem compZero_deriv_val (F G : Jet) (n : Nat) :
    (((Jet.compZero F G).deriv).coeff n).val =
      ((G.deriv.mul (Jet.compZero F.deriv G)).coeff n).val := by
  have h1 : (((Jet.compZero F G).deriv).coeff n).val =
      ((n + 1 : Nat) : Rat) * ((Jet.compZero F G).coeff (n + 1)).val := by
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat]
  rw [h1, compZero_coeff_val_eq_sum F G (n + 1) (n + 1) (le_refl _)]
  rw [Finset.sum_range_succ']
  have h0 : (F.coeff 0).val * ((hPow G 0).coeff (n + 1)).val = 0 := by
    dsimp [hPow]
    rw [Q.val_zero, mul_zero]
  rw [h0, add_zero, Finset.mul_sum]
  have h2 : (∑ r ∈ Finset.range (n + 1),
      ((n + 1 : Nat) : Rat) * ((F.coeff (r + 1)).val * ((hPow G (r + 1)).coeff (n + 1)).val)) =
    ∑ r ∈ Finset.range (n + 1),
      (F.deriv.coeff r).val * ((G.deriv.mul (hPow G r)).coeff n).val := by
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hdh : ((n + 1 : Nat) : Rat) * ((hPow G (r + 1)).coeff (n + 1)).val =
        (((hPow G (r + 1)).deriv).coeff n).val := by
      dsimp [Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat]
    have hdF : ((r + 1 : Nat) : Rat) * (F.coeff (r + 1)).val = (F.deriv.coeff r).val := by
      dsimp [Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat]
    calc ((n + 1 : Nat) : Rat) * ((F.coeff (r + 1)).val * ((hPow G (r + 1)).coeff (n + 1)).val)
      _ = (F.coeff (r + 1)).val * (((n + 1 : Nat) : Rat) * ((hPow G (r + 1)).coeff (n + 1)).val) := by ring
      _ = (F.coeff (r + 1)).val * (((hPow G (r + 1)).deriv).coeff n).val := by rw [hdh]
      _ = (F.coeff (r + 1)).val * (((r + 1 : Nat) : Rat) * ((G.deriv.mul (hPow G r)).coeff n).val) := by
          rw [deriv_hPow_val G r n]
      _ = (((r + 1 : Nat) : Rat) * (F.coeff (r + 1)).val) * ((G.deriv.mul (hPow G r)).coeff n).val := by ring
      _ = (F.deriv.coeff r).val * ((G.deriv.mul (hPow G r)).coeff n).val := by rw [hdF]
  rw [h2]
  have h3 : (∑ r ∈ Finset.range (n + 1),
      (F.deriv.coeff r).val * ((G.deriv.mul (hPow G r)).coeff n).val) =
    ∑ r ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      (G.deriv.coeff j).val * ((F.deriv.coeff r).val * ((hPow G r).coeff (n - j)).val) := by
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
  rw [← Finset.mul_sum, ← compZero_coeff_val_eq_sum F.deriv G n (n - j) (by omega)]

theorem compZero_add_val (F H G : Jet) (n : Nat) :
    ((Jet.compZero (F.add H) G).coeff n).val =
      (((Jet.compZero F G).add (Jet.compZero H G)).coeff n).val := by
  change ((Jet.compZero (F.add H) G).coeff n).val =
    (Q.add ((Jet.compZero F G).coeff n) ((Jet.compZero H G).coeff n)).val
  rw [Q.val_add,
      compZero_coeff_val_eq_sum (F.add H) G n n (le_refl _),
      compZero_coeff_val_eq_sum F G n n (le_refl _),
      compZero_coeff_val_eq_sum H G n n (le_refl _),
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  dsimp [Jet.add]
  rw [Q.val_add]
  ring

theorem compZero_sub_val (F H G : Jet) (n : Nat) :
    ((Jet.compZero (F.sub H) G).coeff n).val =
      (((Jet.compZero F G).sub (Jet.compZero H G)).coeff n).val := by
  change ((Jet.compZero (F.sub H) G).coeff n).val =
    (Q.sub ((Jet.compZero F G).coeff n) ((Jet.compZero H G).coeff n)).val
  rw [Q.val_sub,
      compZero_coeff_val_eq_sum (F.sub H) G n n (le_refl _),
      compZero_coeff_val_eq_sum F G n n (le_refl _),
      compZero_coeff_val_eq_sum H G n n (le_refl _),
      ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  dsimp [Jet.sub]
  rw [Q.val_sub]
  ring

/-- Value-level commutativity of `Jet.mul`. -/
theorem chain_jetMul_comm_val (A B : Jet) (n : Nat) :
    ((A.mul B).coeff n).val = ((B.mul A).coeff n).val := by
  dsimp [Jet.mul]
  rw [TrigPoly.cauchyConvAux_val, TrigPoly.cauchyConvAux_val]
  exact inv_cauchy_comm (fun i ↦ (A.coeff i).val) (fun i ↦ (B.coeff i).val) n

/-- `mulShift G` respects value equality in its second argument. -/
theorem chain_mulShift_congr_val (G A B : Jet)
    (h : ∀ m, (A.coeff m).val = (B.coeff m).val) (n : Nat) :
    ((mulShift G A).coeff n).val = ((mulShift G B).coeff n).val := by
  cases n with
  | zero => rfl
  | succ k =>
    dsimp [mulShift]
    rw [TrigPoly.cauchyConvAux_val, TrigPoly.cauchyConvAux_val]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [h (k - j)]

/-- Left multiplication by `hPow G 0` acts as the identity in value. -/
theorem chain_hPow_zero_mul_val (G A : Jet) (n : Nat) :
    (((hPow G 0).mul A).coeff n).val = (A.coeff n).val := by
  dsimp [Jet.mul]
  rw [TrigPoly.cauchyConvAux_val, Finset.sum_range_succ']
  have h0 : ∑ i ∈ Finset.range n, ((hPow G 0).coeff (i + 1)).val * (A.coeff (n - (i + 1))).val = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    dsimp [hPow]
    rw [Q.val_zero, zero_mul]
  rw [h0, zero_add, Nat.sub_zero]
  dsimp [hPow]
  rw [Q.val_ofNat]
  ring

/-- Formal power law for `hPow G`: `(hPow G (r + s))_n = ((hPow G r).mul (hPow G s))_n` in value. -/
theorem chain_hPow_add_val (G : Jet) : ∀ (r s n : Nat),
    ((hPow G (r + s)).coeff n).val = (((hPow G r).mul (hPow G s)).coeff n).val
  | 0, s, n => by
    rw [Nat.zero_add, chain_hPow_zero_mul_val]
  | r + 1, s, n => by
    rw [Nat.succ_add]
    change ((mulShift G (hPow G (r + s))).coeff n).val =
      (((mulShift G (hPow G r)).mul (hPow G s)).coeff n).val
    rw [chain_mulShift_congr_val G (hPow G (r + s)) ((hPow G r).mul (hPow G s))
          (chain_hPow_add_val G r s) n,
        chain_mulShift_congr_val G ((hPow G r).mul (hPow G s)) ((hPow G s).mul (hPow G r))
          (chain_jetMul_comm_val (hPow G r) (hPow G s)) n,
        mulShift_mul_val G (hPow G s) (hPow G r) n,
        chain_jetMul_comm_val (hPow G s) (mulShift G (hPow G r)) n]

theorem compZero_mul_val (F H G : Jet) (n : Nat) :
    ((Jet.compZero (F.mul H) G).coeff n).val =
      (((Jet.compZero F G).mul (Jet.compZero H G)).coeff n).val := by
  rw [compZero_coeff_val_eq_sum (F.mul H) G n n (le_refl _)]
  have h1 :
      (∑ m ∈ Finset.range (n + 1), ((F.mul H).coeff m).val * ((hPow G m).coeff n).val) =
      ∑ m ∈ Finset.range (n + 1),
        (∑ r ∈ Finset.range (m + 1), (F.coeff r).val * (H.coeff (m - r)).val) *
          ((hPow G (n - (n - m))).coeff n).val := by
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [Finset.mem_range] at hm
    have hsub : n - (n - m) = m := by omega
    rw [hsub]
    dsimp [Jet.mul]
    rw [TrigPoly.cauchyConvAux_val]
  rw [h1, inv_cauchy_assoc (fun r ↦ (F.coeff r).val) (fun s ↦ (H.coeff s).val)
        (fun k ↦ ((hPow G (n - k)).coeff n).val) n]
  have h2 :
      (∑ r ∈ Finset.range (n + 1),
        (F.coeff r).val *
          (∑ s ∈ Finset.range (n - r + 1),
            (H.coeff s).val * ((hPow G (n - (n - r - s))).coeff n).val)) =
      ∑ r ∈ Finset.range (n + 1),
        (F.coeff r).val *
          (∑ s ∈ Finset.range (n + 1),
            (H.coeff s).val * ((hPow G (r + s)).coeff n).val) := by
    refine Finset.sum_congr rfl fun r hr ↦ ?_
    rw [Finset.mem_range] at hr
    congr 1
    trans (∑ s ∈ Finset.range (n - r + 1), (H.coeff s).val * ((hPow G (r + s)).coeff n).val)
    · refine Finset.sum_congr rfl fun s hs ↦ ?_
      rw [Finset.mem_range] at hs
      have hsub : n - (n - r - s) = r + s := by omega
      rw [hsub]
    · refine Finset.sum_subset (Finset.range_mono (by omega)) fun s hs hnot ↦ ?_
      rw [Finset.mem_range] at hs hnot
      rw [hPow_coeff_val_zero_of_lt G (r + s) n (by omega), mul_zero]
  rw [h2]
  have h3 :
      (∑ r ∈ Finset.range (n + 1),
        (F.coeff r).val *
          (∑ s ∈ Finset.range (n + 1),
            (H.coeff s).val * ((hPow G (r + s)).coeff n).val)) =
      ∑ j ∈ Finset.range (n + 1),
        (∑ r ∈ Finset.range (n + 1), (F.coeff r).val * ((hPow G r).coeff j).val) *
          (∑ s ∈ Finset.range (n + 1), (H.coeff s).val * ((hPow G s).coeff (n - j)).val) := by
    trans (∑ r ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (n + 1),
        ((F.coeff r).val * ((hPow G r).coeff j).val) *
          (∑ s ∈ Finset.range (n + 1), (H.coeff s).val * ((hPow G s).coeff (n - j)).val))
    · refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [Finset.mul_sum]
      trans (∑ s ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          ((F.coeff r).val * ((hPow G r).coeff j).val) *
            ((H.coeff s).val * ((hPow G s).coeff (n - j)).val))
      · refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [chain_hPow_add_val G r s n]
        dsimp [Jet.mul]
        rw [TrigPoly.cauchyConvAux_val, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← Finset.mul_sum]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Finset.sum_mul]
  rw [h3]
  dsimp [Jet.mul]
  rw [TrigPoly.cauchyConvAux_val]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [← compZero_coeff_val_eq_sum F G n j (by omega),
      ← compZero_coeff_val_eq_sum H G n (n - j) (by omega)]

/-- Composition fixes jets that are constant as values. -/
theorem compZero_const_val (F G : Jet) (hF : ∀ n, (F.coeff (n + 1)).val = 0) (n : Nat) :
    ((Jet.compZero F G).coeff n).val = (F.coeff n).val := by
  rw [compZero_coeff_val_eq_sum F G n n (le_refl _), Finset.sum_range_succ']
  have h0 : ∑ r ∈ Finset.range n, (F.coeff (r + 1)).val * ((hPow G (r + 1)).coeff n).val = 0 := by
    refine Finset.sum_eq_zero fun r _ ↦ ?_
    rw [hF r, zero_mul]
  rw [h0, zero_add]
  cases n with
  | zero =>
    dsimp [hPow]
    rw [Q.val_ofNat]
    ring
  | succ k =>
    dsimp [hPow]
    rw [Q.val_zero, mul_zero, hF k]

/-- Composition respects value equality in its first argument. -/
theorem compZero_congr_val (F F' G : Jet) (h : ∀ n, (F.coeff n).val = (F'.coeff n).val) (n : Nat) :
    ((Jet.compZero F G).coeff n).val = ((Jet.compZero F' G).coeff n).val := by
  rw [compZero_coeff_val_eq_sum F G n n (le_refl _),
      compZero_coeff_val_eq_sum F' G n n (le_refl _)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [h r]

#print axioms compZero_deriv_val
#print axioms compZero_mul_val

end HAomega
