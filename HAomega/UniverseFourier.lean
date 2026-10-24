/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseMembers

/-!
# Fourier modes and trigonometric polynomials are in the GPAC universe

`sin(kx)` and `cos(kx)` are members for every frequency `k`, against the
value-level jets `Jet.sinFreq k`, `Jet.cosFreq k` (defined by their coefficient
recursion, not by an ODE). Hence every trigonometric polynomial, through the
Taylor bridge `TrigPoly.toJet`, is a member: `toJet` takes the real part of
each mode, so `toJet p` is a finite sum of rational multiples of
`cos(|k|x)` and `sin(|k|x)`, and the universe is closed under those
operations. No reality condition on `p` is needed.

Value-level metatheory theorems (`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- `tmConstNatJet k` is a constant jet. -/
theorem four_isConstJet_constNat (k : Nat) : IsConstJet (tmConstNatJet k) := by
  intro n
  exact Q.val_ofNat 0

/-- The two-equation constant-data system for `(sin(kx), cos(kx))`: `u = 0 + ∫(k · v)`, `v = 1 + ∫(0 − k · u)`. -/
def fourModeSys (k : Nat) : List (Tm [] JetTy × JExprN) :=
  [(tmZeroJet, .mul (.const (tmConstNatJet k)) (.var 1)),
   (tmConstOneJet, .sub (.const tmZeroJet) (.mul (.const (tmConstNatJet k)) (.var 0)))]

/-- `fourModeSys k` satisfies `GPACSys`. -/
theorem four_modeSys_gpac (k : Nat) : GPACSys (fourModeSys k) := by
  intro p hp
  simp only [fourModeSys, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨trivial, show 1 < 2 by omega⟩, gpac_isConstJet_zero, four_isConstJet_constNat k, trivial⟩
  · exact ⟨⟨trivial, trivial, show 0 < 2 by omega⟩,
      mem_isConstJet_one, gpac_isConstJet_zero, four_isConstJet_constNat k, trivial⟩

/-- Value agreement of `solN (fourModeSys k)` with `((Jet.sinFreq k).coeff, (Jet.cosFreq k).coeff)` at every degree `n`. -/
theorem four_modeSys_solN_val (k n : Nat) :
    (solN (fourModeSys k) 0 n).val = ((Jet.sinFreq k).coeff n).val ∧
    (solN (fourModeSys k) 1 n).val = ((Jet.cosFreq k).coeff n).val := by
  have h2 := genStepN_two_iterate tmZeroJet tmConstOneJet
    (.mul (.const (tmConstNatJet k)) .varV)
    (.sub (.const tmZeroJet) (.mul (.const (tmConstNatJet k)) .varU)) (n + 1)
  have h0 := congrFun (congrArg Prod.fst h2) n
  have h1 := congrFun (congrArg Prod.snd h2) n
  have hsc := mode_iterate_val k (n + 1) n (Nat.lt_succ_self n)
  dsimp only [solN, fourModeSys, JExpr2.toN] at h0 h1 hsc ⊢
  rw [h0, h1]
  exact hsc

theorem InGPAC_sinFreq (k : Nat) : InGPAC (Jet.sinFreq k).coeff :=
  ⟨fourModeSys k, four_modeSys_gpac k, 0, show 0 < 2 by omega,
   fun n ↦ (four_modeSys_solN_val k n).1.symm⟩

theorem InGPAC_cosFreq (k : Nat) : InGPAC (Jet.cosFreq k).coeff :=
  ⟨fourModeSys k, four_modeSys_gpac k, 1, show 1 < 2 by omega,
   fun n ↦ (four_modeSys_solN_val k n).2.symm⟩

/-- `InGPAC` respects pointwise value equality. -/
theorem four_inGPAC_congr_val (f g : Nat → Q) (hf : InGPAC f) (hfg : ∀ n, (f n).val = (g n).val) :
    InGPAC g := by
  rcases hf with ⟨sys, hgpac, v, hv, hf_val⟩
  exact ⟨sys, hgpac, v, hv, fun n ↦ (hfg n).symm.trans (hf_val n)⟩

/-- Partial Cauchy convolution of `Jet.const q` with `⟨f⟩` at degree `j` and length `t + 1` has value `q.val * (f j).val`. -/
theorem four_cauchyConvAux_const_val (q : Q) (f : Nat → Q) (j : Nat) : ∀ t : Nat,
    (Jet.cauchyConvAux (Jet.const q) ⟨f⟩ j (t + 1)).val = q.val * (f j).val
  | 0 => by
    change (Q.add Q.zero (Q.mul q (f j))).val = q.val * (f j).val
    rw [Q.val_add, Q.val_zero, Q.val_mul, zero_add]
  | t + 1 => by
    change (Q.add (Jet.cauchyConvAux (Jet.const q) ⟨f⟩ j (t + 1))
      (Q.mul Q.zero (f (j - (t + 1))))).val = q.val * (f j).val
    rw [Q.val_add, four_cauchyConvAux_const_val q f j t, Q.val_mul, Q.val_zero]
    ring

/-- `InGPAC` is closed under pointwise scalar multiplication by `q : Q`. -/
theorem four_inGPAC_scale (q : Q) (f : Nat → Q) (hf : InGPAC f) :
    InGPAC (fun n ↦ Q.mul q (f n)) := by
  refine four_inGPAC_congr_val (((tmJetMul (Γ := [])).eval Env.nil) (Jet.const q).coeff f)
    (fun n ↦ Q.mul q (f n)) (InGPAC_mul (Jet.const q).coeff f (InGPAC_const q) hf) (fun n ↦ ?_)
  rw [tmJetMul_eval, Q.val_mul]
  exact four_cauchyConvAux_const_val q f n n

/-- The Taylor coefficient stream contributed by frequency `k : Int` of `p : TrigPoly`. -/
def fourModeTerm (p : TrigPoly) (k : Int) : Nat → Q :=
  let c := p.coeff k
  let K := k.natAbs
  if 0 ≤ k then
    fun n ↦ Q.sub (Q.mul c.re ((Jet.cosFreq K).coeff n)) (Q.mul c.im ((Jet.sinFreq K).coeff n))
  else
    fun n ↦ Q.add (Q.mul c.re ((Jet.cosFreq K).coeff n)) (Q.mul c.im ((Jet.sinFreq K).coeff n))

/-- Every mode contribution `fourModeTerm p k` is in `InGPAC`. -/
theorem four_inGPAC_modeTerm (p : TrigPoly) (k : Int) : InGPAC (fourModeTerm p k) := by
  dsimp [fourModeTerm]
  have hcos : InGPAC (fun n ↦ Q.mul (p.coeff k).re ((Jet.cosFreq k.natAbs).coeff n)) :=
    four_inGPAC_scale (p.coeff k).re (Jet.cosFreq k.natAbs).coeff (InGPAC_cosFreq k.natAbs)
  have hsin : InGPAC (fun n ↦ Q.mul (p.coeff k).im ((Jet.sinFreq k.natAbs).coeff n)) :=
    four_inGPAC_scale (p.coeff k).im (Jet.sinFreq k.natAbs).coeff (InGPAC_sinFreq k.natAbs)
  split_ifs
  · exact InGPAC_sub _ _ hcos hsin
  · exact InGPAC_add _ _ hcos hsin

/-- The value of `fourModeTerm p k n` equals `(toCRat (p.coeff k) * (ikCRat k) ^ n).re / (fact n : Rat)`. -/
theorem four_modeTerm_val (p : TrigPoly) (k : Int) (n : Nat) :
    (fourModeTerm p k n).val =
      (TrigPoly.toCRat (p.coeff k) * (TrigPoly.ikCRat k) ^ n).re / (fact n : Rat) := by
  let K := k.natAbs
  have hsc := TrigPoly.sinCosFreqCoeffs_eq_ikCRat_pow K n
  change (fourModeTerm p k n).val = _
  dsimp [fourModeTerm]
  split_ifs with hk
  · have hk_eq : (K : Int) = k := by omega
    rw [Q.val_sub, Q.val_mul, Q.val_mul]
    change (p.coeff k).re.val * ((Jet.sinCosFreqCoeffs K n).2).val -
        (p.coeff k).im.val * ((Jet.sinCosFreqCoeffs K n).1).val = _
    rw [hsc.2, hsc.1, hk_eq]
    dsimp [TrigPoly.toCRat]
    ring
  · have hk_eq : k = -(K : Int) := by omega
    have hconj : (TrigPoly.ikCRat k) ^ n = TrigPoly.CRat.conj ((TrigPoly.ikCRat K) ^ n) := by
      rw [hk_eq, TrigPoly.ikCRat_neg, TrigPoly.CRat.conj_pow]
    have hre : ((TrigPoly.ikCRat k) ^ n).re = ((TrigPoly.ikCRat K) ^ n).re := by
      rw [hconj]; rfl
    have him : ((TrigPoly.ikCRat k) ^ n).im = -((TrigPoly.ikCRat K) ^ n).im := by
      rw [hconj]; rfl
    rw [Q.val_add, Q.val_mul, Q.val_mul]
    change (p.coeff k).re.val * ((Jet.sinCosFreqCoeffs K n).2).val +
        (p.coeff k).im.val * ((Jet.sinCosFreqCoeffs K n).1).val = _
    rw [hsc.2, hsc.1]
    dsimp [TrigPoly.toCRat]
    rw [hre, him]
    ring

/-- Pointwise sum of `fourModeTerm p k` over a list of frequencies `l : List Int`. -/
def fourSumList (p : TrigPoly) : List Int → Nat → Q
  | [], _ => Q.zero
  | k :: tl, n => Q.add (fourModeTerm p k n) (fourSumList p tl n)

/-- `fourSumList p l` is in `InGPAC` for every list `l`. -/
theorem four_inGPAC_sumList (p : TrigPoly) : ∀ l : List Int, InGPAC (fourSumList p l)
  | [] =>
    four_inGPAC_congr_val (Jet.const Q.zero).coeff (fourSumList p []) (InGPAC_const Q.zero)
      (fun n ↦ by cases n <;> rfl)
  | k :: tl =>
    InGPAC_add (fourModeTerm p k) (fourSumList p tl)
      (four_inGPAC_modeTerm p k) (four_inGPAC_sumList p tl)

/-- The value of `fourSumList p l n` equals the sum of `(toCRat (p.coeff k) * (ikCRat k) ^ n).re / (fact n : Rat)` over `l`. -/
theorem four_sumList_val (p : TrigPoly) (n : Nat) : ∀ l : List Int,
    (fourSumList p l n).val =
      (l.map (fun k ↦ (TrigPoly.toCRat (p.coeff k) * (TrigPoly.ikCRat k) ^ n).re / (fact n : Rat))).sum
  | [] => by simp [fourSumList, Q.val_zero]
  | k :: tl => by
    simp only [fourSumList, List.map_cons, List.sum_cons, Q.val_add,
      four_modeTerm_val, four_sumList_val p n tl]

/-- **Every trigonometric polynomial is in the universe** (through `toJet`). -/
theorem InGPAC_trigPoly (p : TrigPoly) : InGPAC (TrigPoly.toJet p).coeff := by
  refine four_inGPAC_congr_val (fourSumList p (TrigPoly.range p.deg)) (TrigPoly.toJet p).coeff
    (four_inGPAC_sumList p (TrigPoly.range p.deg)) (fun n ↦ ?_)
  rw [four_sumList_val, TrigPoly.sum_range_eq_sum_Icc,
      TrigPoly.toJet_coeff_val, TrigPoly.moment, TrigPoly.CRat.re_sum, Finset.sum_div]

#print axioms InGPAC_sinFreq
#print axioms InGPAC_cosFreq
#print axioms InGPAC_trigPoly

end HAomega
