/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseMembers

/-!
# The GPAC universe is closed under reciprocals

If `f` is in the universe and `f(0) ≠ 0`, it has a multiplicative inverse in
the universe. The construction (`invSys`): the system of `f`, `f = A + ∫F`,
and one new variable `h = 1/A(0) + ∫(0 − (D A + F)·h·h)`, i.e. `h' = −f'·h²`,
`h(0) = 1/f(0)`. That `f·h = 1` is proved directly: `p = f·h` has `p(0) = 1`
and `(1 − p)' = −f'·h·(1 − p)`, so `1 − p` vanishes coefficient by
coefficient. No value-level reciprocal is defined; the statement is `f·h = 1`.

Value-level metatheory theorems (`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- The constant jet `1 / c(0)`: `λ c n. rec[1 / c 0 | λ _ _. 0 | n]`. -/
def tmInv0 {Γ : List Ty} : Tm Γ (.arrow JetTy JetTy) :=
  .lam (.lam (.recNat (.qdiv (.qnat (.succ .zero)) (.app (.var (.there .here)) .zero))
    (.lam (.lam (.qnat .zero))) (.var .here)))

/-- The system for `1 / f`. -/
def invSys (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    List (Tm [] JetTy × JExprN) :=
  let A := sys[v].1
  let Df : JExprN := .add (.const (.app tmJetDeriv A)) sys[v].2
  sys ++ [(.app tmInv0 A,
    .sub (.const tmZeroJet) (.mul (.mul Df (.var sys.length)) (.var sys.length)))]

/-- If `q.val ≠ 0`, then `q.num ≠ 0`. -/
theorem inv_num_ne_zero {q : Q} (hq : q.val ≠ 0) : q.num ≠ 0 := by
  intro h
  apply hq
  unfold Q.val
  rw [h]
  simp

/-- `tmInv0 c` is a constant jet for every `c`. -/
theorem inv_isConstJet_inv0 (c : Tm [] JetTy) : IsConstJet (.app tmInv0 c) := by
  intro n
  exact Q.val_ofNat 0

/-- Length of `invSys sys v hv`. -/
theorem inv_invSys_length (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    (invSys sys v hv).length = sys.length + 1 := by
  simp [invSys]

/-- The last equation of `invSys sys v hv` (at index `sys.length`). -/
theorem inv_invSys_getElem_last (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    (invSys sys v hv)[sys.length]'(by rw [inv_invSys_length]; exact Nat.lt_succ_self _) =
      (.app tmInv0 sys[v].1,
       .sub (.const tmZeroJet)
         (.mul (.mul (.add (.const (.app tmJetDeriv sys[v].1)) sys[v].2) (.var sys.length))
           (.var sys.length))) := by
  simp only [invSys]
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

/-- Well-formedness of `invSys sys v hv`. -/
theorem inv_invSys_wf (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    ∀ p ∈ invSys sys v hv, p.2.WF (invSys sys v hv).length := by
  rw [inv_invSys_length]
  intro p hp
  simp only [invSys, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp₁ | rfl
  · exact (hwf p hp₁).mono (by omega)
  · refine ⟨trivial, ⟨⟨trivial, (hwf sys[v] (List.getElem_mem hv)).mono (by omega)⟩,
      Nat.lt_succ_self _⟩, Nat.lt_succ_self _⟩

/-- `invSys` preserves `GPACSys`. -/
theorem inv_gpac_invSys (sys : List (Tm [] JetTy × JExprN))
    (h : GPACSys sys) (v : Nat) (hv : v < sys.length) :
    GPACSys (invSys sys v hv) := by
  intro p hp
  refine ⟨inv_invSys_wf sys (gpac_wf h) v hv p hp, ?_⟩
  simp only [invSys, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp₁ | rfl
  · exact (h p hp₁).2
  · have hpv := h sys[v] (List.getElem_mem hv)
    exact ⟨inv_isConstJet_inv0 sys[v].1, gpac_isConstJet_zero,
      ⟨⟨gpac_isConstJet_deriv hpv.2.1, hpv.2.2⟩, trivial⟩, trivial⟩

/-- Picard iterates of `invSys sys v hv` agree with those of `sys` on variables `< sys.length`. -/
theorem inv_iterate_eq_below (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) (k : Nat) :
    ∀ u < sys.length,
      ((((genStepN (invSys sys v hv) (Γ := [])).eval Env.nil)^[k]
        ((initN (invSys sys v hv) (Γ := [])).eval Env.nil)) u) =
      ((((genStepN sys (Γ := [])).eval Env.nil)^[k]
        ((initN sys (Γ := [])).eval Env.nil)) u) := by
  induction k with
  | zero =>
    intro u hu
    have huS : u < (invSys sys v hv).length := by rw [inv_invSys_length]; omega
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply,
        uDeriv_initN_eval_getElem (invSys sys v hv) u huS,
        uDeriv_initN_eval_getElem sys u hu]
    simp only [invSys, List.getElem_append_left hu]
  | succ k ih =>
    intro u hu
    have huS : u < (invSys sys v hv).length := by rw [inv_invSys_length]; omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        genStepN_eval_getElem (invSys sys v hv) _ u huS,
        genStepN_eval_getElem sys _ u hu]
    have hget : (invSys sys v hv)[u] = sys[u] := by
      simp only [invSys, List.getElem_append_left hu]
    rw [hget]
    exact eqStepEval_of_eq_below sys[u] sys.length (hwf sys[u] (List.getElem_mem hu)) _ _ ih

/-- On variables `< sys.length`, `solN (invSys sys v hv)` equals `solN sys`. -/
theorem inv_solN_eq_below (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    ∀ u < sys.length, solN (invSys sys v hv) u = solN sys u := by
  intro u hu
  funext n
  exact congrFun (inv_iterate_eq_below sys hwf v hv (n + 1) u hu) n

/-- At degree `0`, the new component of `solN (invSys sys v hv)` has value `1 / (solN sys v 0).val`. -/
theorem inv_solN_last_zero_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length)
    (h0 : (solN sys v 0).val ≠ 0) :
    (solN (invSys sys v hv) sys.length 0).val = 1 / (solN sys v 0).val := by
  have hvS : sys.length < (invSys sys v hv).length := by
    rw [inv_invSys_length]
    exact Nat.lt_succ_self _
  rw [uMul_solN_zero_val (invSys sys v hv) (inv_invSys_wf sys hwf v hv) sys.length hvS,
      inv_invSys_getElem_last sys v hv]
  have hA0 : (sys[v].1.eval Env.nil 0).val = (solN sys v 0).val :=
    (uMul_solN_zero_val sys hwf v hv).symm
  have hne : (sys[v].1.eval Env.nil 0).num ≠ 0 := by
    apply inv_num_ne_zero
    rw [hA0]
    exact h0
  change (Q.div (Q.ofNat 1) (sys[v].1.eval Env.nil 0)).val = 1 / (solN sys v 0).val
  rw [Q.val_div _ _ hne, Q.val_ofNat, hA0]
  rfl

/-- Value-level derivative of the new component `h := solN (invSys sys v hv) sys.length` satisfies `h' = -((f' · h) · h)`. -/
theorem inv_solN_last_deriv_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) (j : Nat) :
    let h := solN (invSys sys v hv) sys.length
    let Df_val := ((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys v)
    (((tmJetDeriv (Γ := [])).eval Env.nil) h j).val =
      - (((tmJetMul (Γ := [])).eval Env.nil)
          (((tmJetMul (Γ := [])).eval Env.nil) Df_val h) h j).val := by
  intro h Df_val
  let S := invSys sys v hv
  let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
  let A := sys[v].1
  let Df : JExprN := .add (.const (.app tmJetDeriv A)) sys[v].2
  let F_last : JExprN := .sub (.const tmZeroJet) (.mul (.mul Df (.var sys.length)) (.var sys.length))
  have hvS : sys.length < S.length := by
    rw [inv_invSys_length]
    exact Nat.lt_succ_self _
  have hderiv := uMul_solN_deriv_val S (inv_invSys_wf sys hwf v hv) sys.length hvS j
  rw [inv_invSys_getElem_last sys v hv] at hderiv
  have hA_deriv : (((tmJetDeriv (Γ := [])).eval Env.nil) ((Tm.app tmInv0 A).eval Env.nil) j).val = 0 :=
    gpac_deriv_const_val (inv_isConstJet_inv0 A) j
  have hDf_eval : ∀ m < j + 1, (((Df.toTm (.var .here)).eval eS) m).val = (Df_val m).val := by
    intro m _
    have hFv := sys[v].2.toTm_eval_of_eq_below sys.length
      (hwf sys[v] (List.getElem_mem hv)) eS (Env.cons (σ := WTy) (solN sys) Env.nil)
      (.var .here) (.var .here) (inv_solN_eq_below sys hwf v hv)
    change (Q.add ((Tm.closedWk (.app tmJetDeriv A)).eval eS m)
      (((sys[v].2.toTm (.var .here)).eval eS) m)).val = (Df_val m).val
    rw [closedWk_eval (.app tmJetDeriv A) eS, hFv, Q.val_add]
    exact (uMul_solN_deriv_val sys hwf v hv m).symm
  have hvar : ((JExprN.var sys.length).toTm (.var .here)).eval eS = h := by
    change solN S ((natTm sys.length).eval eS) = h
    rw [natTm_eval]
  have hmul₁ : ∀ m < j + 1,
      ((((JExprN.mul Df (.var sys.length)).toTm (.var .here)).eval eS) m).val =
        (((tmJetMul (Γ := [])).eval Env.nil) Df_val h m).val := by
    intro m hm
    exact tmJetMul_agreeV Env.nil Env.nil (j + 1)
      ((Df.toTm (.var .here)).eval eS) Df_val
      (((JExprN.var sys.length).toTm (.var .here)).eval eS) h
      hDf_eval (by rw [hvar]; exact fun _ _ ↦ rfl) m hm
  have hmul₂ :
      ((((JExprN.mul (.mul Df (.var sys.length)) (.var sys.length)).toTm (.var .here)).eval eS) j).val =
        (((tmJetMul (Γ := [])).eval Env.nil)
          (((tmJetMul (Γ := [])).eval Env.nil) Df_val h) h j).val :=
    tmJetMul_agreeV Env.nil Env.nil (j + 1)
      (((JExprN.mul Df (.var sys.length)).toTm (.var .here)).eval eS)
      (((tmJetMul (Γ := [])).eval Env.nil) Df_val h)
      (((JExprN.var sys.length).toTm (.var .here)).eval eS) h
      hmul₁ (by rw [hvar]; exact fun _ _ ↦ rfl) j (Nat.lt_succ_self j)
  have hFlast : (((F_last.toTm (.var .here)).eval eS) j).val =
      - (((tmJetMul (Γ := [])).eval Env.nil)
          (((tmJetMul (Γ := [])).eval Env.nil) Df_val h) h j).val := by
    change (Q.sub ((Tm.closedWk tmZeroJet).eval eS j)
      ((((JExprN.mul (.mul Df (.var sys.length)) (.var sys.length)).toTm (.var .here)).eval eS) j)).val = _
    rw [closedWk_eval tmZeroJet eS, Q.val_sub, hmul₂]
    have hz : (tmZeroJet.eval Env.nil j).val = 0 := Q.val_ofNat 0
    rw [hz, zero_sub]
  change (((tmJetDeriv (Γ := [])).eval Env.nil) (solN S sys.length) j).val =
      (((tmJetDeriv (Γ := [])).eval Env.nil) ((Tm.app tmInv0 A).eval Env.nil) j).val +
      (((F_last.toTm (.var .here)).eval eS) j).val at hderiv
  rw [hderiv, hA_deriv, hFlast, zero_add]

/-- Commutativity of finite Cauchy convolution over `Rat`. -/
theorem inv_cauchy_comm (A B : Nat → Rat) (n : Nat) :
    (∑ i ∈ Finset.range (n + 1), A i * B (n - i)) =
      ∑ i ∈ Finset.range (n + 1), B i * A (n - i) := by
  refine Finset.sum_bij (fun i _ ↦ n - i) ?_ ?_ ?_ ?_
  · intro i hi
    dsimp
    rw [Finset.mem_range] at hi ⊢
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    rw [Finset.mem_range] at hi₁ hi₂
    dsimp at h
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    refine ⟨n - k, ?_, by dsimp; omega⟩
    rw [Finset.mem_range]
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    dsimp
    have hsub : n - (n - i) = i := by omega
    rw [hsub, mul_comm]

/-- Associativity of finite Cauchy convolution over `Rat`. -/
theorem inv_cauchy_assoc (A B C : Nat → Rat) (n : Nat) :
    (∑ j ∈ Finset.range (n + 1), (∑ i ∈ Finset.range (j + 1), A i * B (j - i)) * C (n - j)) =
      ∑ i ∈ Finset.range (n + 1), A i * (∑ k ∈ Finset.range (n - i + 1), B k * C (n - i - k)) := by
  induction n generalizing A with
  | zero => simp [mul_assoc]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have hsplit :
        (∑ j ∈ Finset.range (n + 1),
          (∑ i ∈ Finset.range (j + 2), A i * B (j + 1 - i)) * C (n + 1 - (j + 1))) =
        (∑ j ∈ Finset.range (n + 1),
          (∑ i ∈ Finset.range (j + 1), A (i + 1) * B (j - i)) * C (n - j)) +
        ∑ j ∈ Finset.range (n + 1), A 0 * (B (j + 1) * C (n - j)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.sum_range_succ' (fun i ↦ A i * B (j + 1 - i)) (j + 1)]
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      ring
    rw [hsplit, ih (fun i ↦ A (i + 1))]
    have h0 :
        (∑ j ∈ Finset.range (n + 1), A 0 * (B (j + 1) * C (n - j))) +
          (∑ i ∈ Finset.range 1, A i * B (0 - i)) * C (n + 1 - 0) =
        A 0 * (∑ k ∈ Finset.range (n + 2), B k * C (n + 1 - k)) := by
      rw [Finset.sum_range_one, Nat.sub_zero, ← Finset.mul_sum,
          Finset.sum_range_succ' (fun k ↦ B k * C (n + 1 - k)) (n + 1)]
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      ring
    rw [add_assoc, h0, Finset.sum_range_succ'
      (fun i ↦ A i * ∑ k ∈ Finset.range (n + 1 - i + 1), B k * C (n + 1 - i - k)) (n + 1)]
    simp only [Nat.add_sub_add_right, Nat.sub_zero]

/-- Rational value of `tmJetMul a b n` as a `Finset.range (n + 1)` sum. -/
theorem inv_jetMul_val (a b : Nat → Q) (n : Nat) :
    (((tmJetMul (Γ := [])).eval Env.nil) a b n).val =
      ∑ i ∈ Finset.range (n + 1), (a i).val * (b (n - i)).val := by
  rw [tmJetMul_eval]
  exact TrigPoly.cauchyConvAux_val ⟨a⟩ ⟨b⟩ n (n + 1)

/-- Value-level commutativity of `tmJetMul`. -/
theorem inv_jetMul_comm_val (a b : Nat → Q) (n : Nat) :
    (((tmJetMul (Γ := [])).eval Env.nil) a b n).val =
      (((tmJetMul (Γ := [])).eval Env.nil) b a n).val := by
  rw [inv_jetMul_val, inv_jetMul_val]
  exact inv_cauchy_comm (fun i ↦ (a i).val) (fun i ↦ (b i).val) n

/-- Value-level associativity of `tmJetMul`. -/
theorem inv_jetMul_assoc_val (a b c : Nat → Q) (n : Nat) :
    (((tmJetMul (Γ := [])).eval Env.nil) (((tmJetMul (Γ := [])).eval Env.nil) a b) c n).val =
      (((tmJetMul (Γ := [])).eval Env.nil) a (((tmJetMul (Γ := [])).eval Env.nil) b c) n).val := by
  rw [inv_jetMul_val, inv_jetMul_val]
  have h1 :
      (∑ j ∈ Finset.range (n + 1),
        (((tmJetMul (Γ := [])).eval Env.nil) a b j).val * (c (n - j)).val) =
      ∑ j ∈ Finset.range (n + 1),
        (∑ i ∈ Finset.range (j + 1), (a i).val * (b (j - i)).val) * (c (n - j)).val := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [inv_jetMul_val]
  have h2 :
      (∑ i ∈ Finset.range (n + 1),
        (a i).val * (((tmJetMul (Γ := [])).eval Env.nil) b c (n - i)).val) =
      ∑ i ∈ Finset.range (n + 1),
        (a i).val * (∑ k ∈ Finset.range (n - i + 1), (b k).val * (c (n - i - k)).val) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inv_jetMul_val]
  rw [h1, h2]
  exact inv_cauchy_assoc (fun i ↦ (a i).val) (fun i ↦ (b i).val) (fun i ↦ (c i).val) n

/-- Convolution of `g` with `Jet.const (Q.ofNat 1)` at degree `n` has value `(g n).val`. -/
theorem inv_mul_one_val (g : Nat → Q) (n : Nat) :
    (∑ i ∈ Finset.range (n + 1), (g i).val * ((Jet.const (Q.ofNat 1)).coeff (n - i)).val) =
      (g n).val := by
  rw [Finset.sum_range_succ]
  have h0 : ∑ i ∈ Finset.range n, (g i).val * ((Jet.const (Q.ofNat 1)).coeff (n - i)).val = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    have hsub : n - i = (n - 1 - i) + 1 := by omega
    rw [hsub]
    change (g i).val * Q.zero.val = 0
    rw [Q.val_zero, mul_zero]
  rw [h0, zero_add, Nat.sub_self]
  change (g n).val * (Q.ofNat 1).val = (g n).val
  rw [Q.val_ofNat]
  ring

/-- A rational sequence `q` with `q 0 = 0` and `(n + 1) * q (n + 1) = - ∑ i ≤ n, a i * q (n - i)` vanishes identically. -/
theorem inv_zero_of_linear_rec (a q : Nat → Rat) (hq0 : q 0 = 0)
    (hrec : ∀ n, ((n + 1 : Nat) : Rat) * q (n + 1) =
      - ∑ i ∈ Finset.range (n + 1), a i * q (n - i)) :
    ∀ n, q n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hq0
    | succ m =>
      have hsum : ∑ i ∈ Finset.range (m + 1), a i * q (m - i) = 0 := by
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        rw [Finset.mem_range] at hi
        rw [ih (m - i) (by omega), mul_zero]
      have hm := hrec m
      rw [hsum, neg_zero] at hm
      have hne : ((m + 1 : Nat) : Rat) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hm).resolve_left hne

/-- **Closure under reciprocals.** -/
theorem InGPAC_inv (f : Nat → Q) (hf : InGPAC f) (h0 : (f 0).val ≠ 0) :
    ∃ h : Nat → Q, InGPAC h ∧
      ∀ n, (((tmJetMul (Γ := [])).eval Env.nil) f h n).val = ((Jet.const (Q.ofNat 1)).coeff n).val := by
  rcases hf with ⟨sys, hgpac, v, hv, hf_val⟩
  have hwf : ∀ p ∈ sys, p.2.WF sys.length := gpac_wf hgpac
  let S := invSys sys v hv
  let f₀ := solN sys v
  let h := solN S sys.length
  have hvS : sys.length < S.length := by
    rw [inv_invSys_length]
    exact Nat.lt_succ_self _
  have hh_gpac : InGPAC h := ⟨S, inv_gpac_invSys sys hgpac v hv, sys.length, hvS, fun _ ↦ rfl⟩
  refine ⟨h, hh_gpac, fun n ↦ ?_⟩
  have hfh : (((tmJetMul (Γ := [])).eval Env.nil) f h n).val =
      (((tmJetMul (Γ := [])).eval Env.nil) f₀ h n).val :=
    tmJetMul_agreeV Env.nil Env.nil (n + 1) f f₀ h h
      (fun i _ ↦ hf_val i) (fun _ _ ↦ rfl) n (Nat.lt_succ_self n)
  rw [hfh]
  let mul := (tmJetMul (Γ := [])).eval Env.nil
  let deriv := (tmJetDeriv (Γ := [])).eval Env.nil
  let p := mul f₀ h
  let g := mul (deriv f₀) h
  let q : Nat → Rat := fun m ↦ ((Jet.const (Q.ofNat 1)).coeff m).val - (p m).val
  have hf₀0 : (f₀ 0).val ≠ 0 := by
    rw [← hf_val 0]
    exact h0
  have hq0 : q 0 = 0 := by
    dsimp [q, p, mul]
    rw [uMul_zero_val, inv_solN_last_zero_val sys hwf v hv hf₀0]
    change (Q.ofNat 1).val - (f₀ 0).val * (1 / (f₀ 0).val) = 0
    rw [Q.val_ofNat]
    field_simp
    ring
  have hrec : ∀ m, ((m + 1 : Nat) : Rat) * q (m + 1) =
      - ∑ i ∈ Finset.range (m + 1), (g i).val * q (m - i) := by
    intro m
    have h_f_dh : (mul f₀ (deriv h) m).val = - (mul f₀ (mul g h) m).val := by
      rw [inv_jetMul_val, inv_jetMul_val, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [inv_solN_last_deriv_val sys hwf v hv (m - i)]
      ring
    have h_reassoc : (mul f₀ (mul g h) m).val = (mul g p m).val := by
      rw [← inv_jetMul_assoc_val f₀ g h m,
          tmJetMul_agreeV Env.nil Env.nil (m + 1) (mul f₀ g) (mul g f₀) h h
            (fun i _ ↦ inv_jetMul_comm_val f₀ g i) (fun _ _ ↦ rfl) m (Nat.lt_succ_self m),
          inv_jetMul_assoc_val g f₀ h m]
    have h_dp : ((m + 1 : Nat) : Rat) * (p (m + 1)).val = (g m).val - (mul g p m).val := by
      have hleib := jetMul_leibniz_val f₀ h m
      change (Q.mul (Q.ofNat (m + 1)) (p (m + 1))).val =
        (g m).val + (mul f₀ (deriv h) m).val at hleib
      rw [Q.val_mul, Q.val_ofNat, h_f_dh, h_reassoc] at hleib
      linarith
    have h_rhs : (g m).val - (mul g p m).val =
        ∑ i ∈ Finset.range (m + 1), (g i).val * q (m - i) := by
      dsimp [q]
      rw [← inv_mul_one_val g m, inv_jetMul_val g p m, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    dsimp [q]
    change ((m + 1 : Nat) : Rat) * (Q.zero.val - (p (m + 1)).val) = _
    rw [Q.val_zero, zero_sub, mul_neg, h_dp, h_rhs]
  have hqn := inv_zero_of_linear_rec (fun i ↦ (g i).val) q hq0 hrec n
  dsimp [q] at hqn
  linarith

#print axioms InGPAC_inv

end HAomega
