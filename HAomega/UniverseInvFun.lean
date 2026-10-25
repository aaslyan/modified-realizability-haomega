/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseComp
import HAomega.UniverseInv
import HAomega.SystemFast

/-!
# The local inverse function theorem in the universe

If `g` is in the universe with `g(0) = 0` and `g′(0) ≠ 0`, the formal inverse
`y = g⁻¹` (`g(y(x)) = x`) is in the universe too. The unknown `y` sits inside
`g`, as in the general recursive equations `F(f) = G(f)` of the 1997
dissertation (`docs/foundations/DISSERTATION_1997.md`); differentiation turns
the implicit law into an explicit polynomial system.

**Construction.** Write `g = Z_v` for a flat system `Z = A + ∫F(Z)`
(`InGPAC_noInteg`). Along `y`, with `W := Z ∘ y`, `u := 1/g′(y)`:

    y = 0 + ∫ u,
    W_w = A_w + ∫ F_w(W)·u                  (chain rule: (Z∘y)′ = F(Z∘y)·y′),
    u = 1/g′(0) + ∫ (−u³·H(W)),            H := symbolic derivative of F_v,

all polynomial with constant data, so `y` is a solution component of a
`GPACSys`. Then `(u·g′(y))′ = u²H·(1 − u·g′(y))` with value `1` at `0` forces
`u·g′(y) = 1` by uniqueness, and `(g∘y)′ = g′(y)·u = 1`, `(g∘y)(0) = 0`.

The equation is stated with `Jet.compZero` (composition `F(G − G(0))`), which
for `y(0) = 0` is `g ∘ y`.
-/

namespace HAomega

/-- The inverse-function system for component `v` of `sys` (meant for a flat
`sys`): the variables `W_w = Z_w ∘ y` at the old indices, then `y` at index
`sys.length`, then `u = 1/g′(y)` at `sys.length + 1`. -/
def invFunSys (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    List (Tm [] JetTy × JExprN) :=
  let n := sys.length
  let Dg : JExprN := .add (.const (.app tmJetDeriv sys[v].1)) sys[v].2
  let H := Dg.derivSym sys
  let u : JExprN := .var (n + 1)
  sys.map (fun p ↦ (p.1, .mul p.2 u)) ++
    [(tmZeroJet, u),
     (.app tmInv0 (.app (.app tmJetAdd (.app tmJetDeriv sys[v].1)) (sys[v].2.toTm (initN sys))),
      .sub (.const tmZeroJet) (.mul (.mul (.mul u u) u) H))]

/-- `tmJetMul` evaluates identically in any environment. -/
theorem ivf_tmJetMul_eval {Γ : List Ty} (e : Env Γ) (a b : Nat → Q) :
    ((tmJetMul (Γ := Γ)).eval e) a b = ((tmJetMul (Γ := [])).eval Env.nil) a b := by
  funext n
  rw [tmJetMul_eval, tmJetMul_eval]

/-- Evaluating `(JExprN.mul a b).toTm (.var .here)` in `e` equals `tmJetMul` in `Env.nil` applied to the evaluations of `a` and `b`. -/
theorem ivf_toTm_mul_eval (a b : JExprN) (e : Env [WTy]) :
    ((JExprN.mul a b).toTm (.var .here)).eval e =
      ((tmJetMul (Γ := [])).eval Env.nil) ((a.toTm (.var .here)).eval e) ((b.toTm (.var .here)).eval e) :=
  ivf_tmJetMul_eval e _ _

/-- Symbolic differentiation `JExprN.derivSym sys` preserves `JExprN.NoInteg` when `sys` is `∫`-free and `F.WF sys.length`. -/
theorem ivf_derivSym_noInteg (sys : List (Tm [] JetTy × JExprN))
    (hno : ∀ p ∈ sys, p.2.NoInteg) (F : JExprN) (hF_wf : F.WF sys.length) (hF_no : F.NoInteg) :
    (F.derivSym sys).NoInteg := by
  induction F with
  | var u =>
    dsimp only [JExprN.derivSym]
    rw [uDeriv_getD_eq_getElem sys _ u hF_wf]
    exact ⟨trivial, hno sys[u] (List.getElem_mem hF_wf)⟩
  | const _ => trivial
  | add _ _ iha ihb => exact ⟨iha hF_wf.1 hF_no.1, ihb hF_wf.2 hF_no.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF_wf.1 hF_no.1, ihb hF_wf.2 hF_no.2⟩
  | mul _ _ iha ihb =>
    exact ⟨⟨iha hF_wf.1 hF_no.1, hF_no.2⟩, ⟨hF_no.1, ihb hF_wf.2 hF_no.2⟩⟩
  | integ _ _ => exact False.elim hF_no

/-- Length of `invFunSys sys v hv`. -/
theorem ivf_invFunSys_length (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    (invFunSys sys v hv).length = sys.length + 2 := by
  simp [invFunSys]

/-- Equation `w < sys.length` of `invFunSys sys v hv`. -/
theorem ivf_invFunSys_getElem_lt (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length)
    (w : Nat) (hw : w < sys.length) :
    (invFunSys sys v hv)[w]'(by rw [ivf_invFunSys_length]; omega) =
      (sys[w].1, .mul sys[w].2 (.var (sys.length + 1))) := by
  simp only [invFunSys]
  rw [List.getElem_append_left (by simp [hw]), List.getElem_map]

/-- Equation `sys.length` (the `y` component) of `invFunSys sys v hv`. -/
theorem ivf_invFunSys_getElem_y (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    (invFunSys sys v hv)[sys.length]'(by rw [ivf_invFunSys_length]; omega) =
      (tmZeroJet, .var (sys.length + 1)) := by
  simp only [invFunSys]
  rw [List.getElem_append_right (by simp)]
  simp

/-- Equation `sys.length + 1` (the `u` component) of `invFunSys sys v hv`. -/
theorem ivf_invFunSys_getElem_u (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    (invFunSys sys v hv)[sys.length + 1]'(by rw [ivf_invFunSys_length]; omega) =
      (.app tmInv0 (.app (.app tmJetAdd (.app tmJetDeriv sys[v].1)) (sys[v].2.toTm (initN sys))),
       .sub (.const tmZeroJet)
         (.mul (.mul (.mul (.var (sys.length + 1)) (.var (sys.length + 1))) (.var (sys.length + 1)))
           ((JExprN.add (.const (.app tmJetDeriv sys[v].1)) sys[v].2).derivSym sys))) := by
  simp only [invFunSys]
  rw [List.getElem_append_right (by simp)]
  simp

/-- Well-formedness of `invFunSys sys v hv`. -/
theorem ivf_invFunSys_wf (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    ∀ p ∈ invFunSys sys v hv, p.2.WF (invFunSys sys v hv).length := by
  rw [ivf_invFunSys_length]
  intro p hp
  simp only [invFunSys, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨q, hq, rfl⟩ | rfl | rfl
  · exact ⟨(hwf q hq).mono (by omega), by show sys.length + 1 < sys.length + 2; omega⟩
  · show sys.length + 1 < sys.length + 2
    omega
  · have hDg_wf : (JExprN.add (.const (.app tmJetDeriv sys[v].1)) sys[v].2).WF sys.length :=
      ⟨trivial, hwf sys[v] (List.getElem_mem hv)⟩
    have hH_wf := (uDeriv_derivSym_wf sys hwf _ hDg_wf).mono (by omega : sys.length ≤ sys.length + 2)
    have hu_wf : (JExprN.var (sys.length + 1)).WF (sys.length + 2) := by
      show sys.length + 1 < sys.length + 2; omega
    exact ⟨trivial, ⟨⟨hu_wf, hu_wf⟩, hu_wf⟩, hH_wf⟩

/-- `invFunSys` preserves `GPACSys`. -/
theorem ivf_gpac_invFunSys (sys : List (Tm [] JetTy × JExprN))
    (h : GPACSys sys) (v : Nat) (hv : v < sys.length) :
    GPACSys (invFunSys sys v hv) := by
  intro p hp
  refine ⟨ivf_invFunSys_wf sys (gpac_wf h) v hv p hp, ?_⟩
  simp only [invFunSys, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨q, hq, rfl⟩ | rfl | rfl
  · have hq_gpac := h q hq
    exact ⟨hq_gpac.2.1, hq_gpac.2.2, trivial⟩
  · exact ⟨gpac_isConstJet_zero, trivial⟩
  · have hpv := h sys[v] (List.getElem_mem hv)
    have hDg_wf : (JExprN.add (.const (.app tmJetDeriv sys[v].1)) sys[v].2).WF sys.length :=
      ⟨trivial, hpv.1⟩
    have hDg_cc : (JExprN.add (.const (.app tmJetDeriv sys[v].1)) sys[v].2).ConstsConst :=
      ⟨gpac_isConstJet_deriv hpv.2.1, hpv.2.2⟩
    exact ⟨inv_isConstJet_inv0 _, gpac_isConstJet_zero,
      ⟨⟨trivial, trivial⟩, trivial⟩,
      gpac_derivSym_constsConst sys h _ hDg_wf hDg_cc⟩

/-- Component `sys.length` of `solN (invFunSys sys v hv)` has value `0` at degree `0`. -/
theorem ivf_solN_y_zero_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    (solN (invFunSys sys v hv) sys.length 0).val = 0 := by
  let S := invFunSys sys v hv
  have hy : sys.length < S.length := by rw [ivf_invFunSys_length]; omega
  rw [uMul_solN_zero_val S (ivf_invFunSys_wf sys hwf v hv) sys.length hy,
      ivf_invFunSys_getElem_y sys v hv]
  exact Q.val_ofNat 0

/-- Derivative of component `sys.length` of `solN (invFunSys sys v hv)` equals component `sys.length + 1` in value. -/
theorem ivf_solN_y_deriv_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) (j : Nat) :
    let S := invFunSys sys v hv
    (((tmJetDeriv (Γ := [])).eval Env.nil) (solN S sys.length) j).val =
      (solN S (sys.length + 1) j).val := by
  intro S
  have hy : sys.length < S.length := by rw [ivf_invFunSys_length]; omega
  have hderiv := uMul_solN_deriv_val S (ivf_invFunSys_wf sys hwf v hv) sys.length hy j
  rw [ivf_invFunSys_getElem_y sys v hv] at hderiv
  have h0 : (((tmJetDeriv (Γ := [])).eval Env.nil) (tmZeroJet.eval Env.nil) j).val = 0 :=
    gpac_deriv_const_val gpac_isConstJet_zero j
  have hvar : (((JExprN.var (sys.length + 1)).toTm (.var .here)).eval
      (Env.cons (σ := WTy) (solN S) Env.nil)) = solN S (sys.length + 1) := by
    change solN S ((natTm (sys.length + 1)).eval (Env.cons (σ := WTy) (solN S) Env.nil)) = _
    rw [natTm_eval]
  dsimp only at hderiv
  rw [hderiv, h0, hvar, zero_add]

/-- Target state for `invFunSys`: `Jet.compZero ⟨solN sys w⟩ ⟨y⟩` for `w < sys.length`, and `solN S w` for `w ≥ sys.length`. -/
def ivfTargetState (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    Nat → Nat → Q :=
  let S := invFunSys sys v hv
  fun w n ↦
    if w < sys.length then (Jet.compZero ⟨solN sys w⟩ ⟨solN S sys.length⟩).coeff n
    else solN S w n

/-- Evaluating equation `w < sys.length` of `invFunSys sys v hv` on `ivfTargetState` yields `ivfTargetState` at `w`. -/
theorem ivf_eqStepEval_lt_val (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (hno : ∀ p ∈ sys, p.2.NoInteg)
    (v : Nat) (hv : v < sys.length) (w : Nat) (hw : w < sys.length) (n : Nat) :
    let S := invFunSys sys v hv
    let hwS : w < S.length := by rw [ivf_invFunSys_length]; omega
    (eqStepEval S[w] (ivfTargetState sys v hv) n).val =
      (ivfTargetState sys v hv w n).val := by
  intro S hwS
  rw [ivf_invFunSys_getElem_lt sys v hv w hw]
  unfold ivfTargetState
  rw [if_pos hw]
  let T := ivfTargetState sys v hv
  let eT : Env [WTy] := Env.cons (σ := WTy) T Env.nil
  let Y : Jet := ⟨solN S sys.length⟩
  let Fw : Jet := ⟨solN sys w⟩
  have hwf : ∀ q ∈ sys, q.2.WF sys.length := gpac_wf hgpac
  have hp_gpac := hgpac sys[w] (List.getElem_mem hw)
  have hp_no := hno sys[w] (List.getElem_mem hw)
  let W_comp : Nat → Nat → Q := fun i ↦ (Jet.compZero ⟨solN sys i⟩ Y).coeff
  have hTW : ∀ i < sys.length, T i = W_comp i := by
    intro i hi; funext m; exact if_pos hi
  cases n with
  | zero =>
    unfold eqStepEval
    change (Q.add (sys[w].1.eval Env.nil 0) (Q.ofNat 0)).val = ((Jet.compZero Fw Y).coeff 0).val
    have h0 : (Q.add (sys[w].1.eval Env.nil 0) (Q.ofNat 0)).val = (sys[w].1.eval Env.nil 0).val := by
      rw [Q.val_add, Q.val_ofNat]; ring
    rw [h0, ← uMul_solN_zero_val sys hwf w hw,
        compZero_coeff_val_eq_sum Fw Y 0 0 (le_refl 0),
        Finset.sum_range_one]
    dsimp [Fw, hPow]
    rw [Q.val_ofNat]
    ring
  | succ j =>
    have hF_eval : ∀ m < j + 1,
        (((sys[w].2.toTm (.var .here)).eval eT) m).val =
          ((Jet.compZero Fw.deriv Y).coeff m).val := by
      intro m _
      have heq := sys[w].2.toTm_eval_of_eq_below sys.length hp_gpac.1
        eT (Env.cons (σ := WTy) W_comp Env.nil) (.var .here) (.var .here) hTW
      rw [heq, comp_toTm_compZero_val sys Y sys[w].2 hp_gpac.2.2 hp_no m]
      refine compZero_congr_val
        ⟨(sys[w].2.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sys) Env.nil)⟩
        Fw.deriv Y (fun k ↦ ?_) m
      have hderiv_w := uMul_solN_deriv_val sys hwf w hw k
      have hA_zero := gpac_deriv_const_val hp_gpac.2.1 k
      change (((sys[w].2.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sys) Env.nil)) k).val =
        (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys w) k).val
      linarith
    have hu_eval : ∀ m < j + 1,
        ((((JExprN.var (sys.length + 1)).toTm (.var .here)).eval eT) m).val =
          (Y.deriv.coeff m).val := by
      intro m _
      have hvar : (((JExprN.var (sys.length + 1)).toTm (.var .here)).eval eT) m =
          solN S (sys.length + 1) m := by
        change T ((natTm (sys.length + 1)).eval eT) m = _
        rw [natTm_eval]
        unfold T ivfTargetState
        exact if_neg (by omega)
      rw [hvar]
      exact (ivf_solN_y_deriv_val sys hwf v hv m).symm
    have hmul :
        ((((JExprN.mul sys[w].2 (.var (sys.length + 1))).toTm (.var .here)).eval eT) j).val =
          (((Jet.compZero Fw Y).deriv).coeff j).val := by
      have hm := tmJetMul_agreeV Env.nil Env.nil (j + 1)
        ((sys[w].2.toTm (.var .here)).eval eT) (Jet.compZero Fw.deriv Y).coeff
        (((JExprN.var (sys.length + 1)).toTm (.var .here)).eval eT) Y.deriv.coeff
        hF_eval hu_eval j (Nat.lt_succ_self j)
      rw [ivf_toTm_mul_eval, hm, inv_jetMul_comm_val, tmJetMul_eval, ← compZero_deriv_val Fw Y j]
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    have hne_rat : ((j + 1 : Nat) : Rat) ≠ 0 := by positivity
    unfold eqStepEval
    change (Q.add (sys[w].1.eval Env.nil (j + 1))
      (Q.div ((((JExprN.mul sys[w].2 (.var (sys.length + 1))).toTm (.var .here)).eval eT) j)
        (Q.ofNat (j + 1)))).val = ((Jet.compZero Fw Y).coeff (j + 1)).val
    rw [Q.val_add, hp_gpac.2.1 j, zero_add, Q.val_div _ _ hne, Q.val_ofNat, hmul]
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat]
    field_simp

/-- `solN (invFunSys sys v hv)` agrees in value with `ivfTargetState sys v hv` at all variables and degrees. -/
theorem ivf_solN_eq_target_val (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (hno : ∀ p ∈ sys, p.2.NoInteg)
    (v : Nat) (hv : v < sys.length) (m : Nat) :
    ∀ w, (solN (invFunSys sys v hv) w m).val = (ivfTargetState sys v hv w m).val := by
  let S := invFunSys sys v hv
  have hwfS := ivf_invFunSys_wf sys (gpac_wf hgpac) v hv
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro w
    by_cases hw : w < sys.length
    · have hwS : w < S.length := by rw [ivf_invFunSys_length]; omega
      have hag := genStepN_agreeV_succ S hwfS m (solN S) (ivfTargetState sys v hv)
        (fun u _ k hk ↦ ih k hk u) w m (Nat.lt_succ_self m)
      rw [← solN_fixed S hwfS w hwS m, hag, genStepN_eval_getElem S _ w hwS]
      exact ivf_eqStepEval_lt_val sys hgpac hno v hv w hw m
    · unfold ivfTargetState
      rw [if_neg hw]

/-- For `w < sys.length`, component `w` of `solN (invFunSys sys v hv)` equals `Jet.compZero ⟨solN sys w⟩ ⟨y⟩` in value. -/
theorem ivf_solN_eq_compZero_val (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (hno : ∀ p ∈ sys, p.2.NoInteg)
    (v : Nat) (hv : v < sys.length) (w : Nat) (hw : w < sys.length) (m : Nat) :
    let S := invFunSys sys v hv
    (solN S w m).val = ((Jet.compZero ⟨solN sys w⟩ ⟨solN S sys.length⟩).coeff m).val := by
  intro S
  have h := ivf_solN_eq_target_val sys hgpac hno v hv m w
  unfold ivfTargetState at h
  rwa [if_pos hw] at h

/-- Evaluating an `∫`-free `F` with constant leaves and `F.WF sys.length` on `solN (invFunSys sys v hv)` equals composing `F` evaluated on `solN sys` with `y`. -/
theorem ivf_toTm_solN_eq_compZero_val (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (hno : ∀ p ∈ sys, p.2.NoInteg)
    (v : Nat) (hv : v < sys.length)
    (F : JExprN) (hF_wf : F.WF sys.length) (hF_cc : F.ConstsConst) (hF_no : F.NoInteg) (m : Nat) :
    let S := invFunSys sys v hv
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    let eSys : Env [WTy] := Env.cons (σ := WTy) (solN sys) Env.nil
    (((F.toTm (.var .here)).eval eS) m).val =
      ((Jet.compZero ⟨(F.toTm (.var .here)).eval eSys⟩ ⟨solN S sys.length⟩).coeff m).val := by
  intro S eS eSys
  let Y : Jet := ⟨solN S sys.length⟩
  let W_comp : Nat → Nat → Q := fun u ↦ (Jet.compZero ⟨solN sys u⟩ Y).coeff
  let eC : Env [WTy] := Env.cons (σ := WTy) W_comp Env.nil
  have hag := F.toTm_agreeV sys.length hF_wf eS eC (.var .here) (.var .here) (m + 1)
    (fun u hu k _ ↦ ivf_solN_eq_compZero_val sys hgpac hno v hv u hu k) m (Nat.lt_succ_self m)
  exact hag.trans (comp_toTm_compZero_val sys Y F hF_cc hF_no m)

/-- At degree `0`, `Dg` evaluated on `solN (invFunSys sys v hv)` has value `(solN sys v 1).val`. -/
theorem ivf_dg_zero_val (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (hno : ∀ p ∈ sys, p.2.NoInteg)
    (v : Nat) (hv : v < sys.length) :
    let S := invFunSys sys v hv
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    let Dg : JExprN := .add (.const (.app tmJetDeriv sys[v].1)) sys[v].2
    (((Dg.toTm (.var .here)).eval eS) 0).val = (solN sys v 1).val := by
  intro S eS Dg
  have hwf := gpac_wf hgpac
  have hpv := hgpac sys[v] (List.getElem_mem hv)
  have hDg_wf : Dg.WF sys.length := ⟨trivial, hpv.1⟩
  have hDg_cc : Dg.ConstsConst := ⟨gpac_isConstJet_deriv hpv.2.1, hpv.2.2⟩
  have hDg_no : Dg.NoInteg := ⟨trivial, hno sys[v] (List.getElem_mem hv)⟩
  rw [ivf_toTm_solN_eq_compZero_val sys hgpac hno v hv Dg hDg_wf hDg_cc hDg_no 0]
  let eSys : Env [WTy] := Env.cons (σ := WTy) (solN sys) Env.nil
  let Dg_sys : Jet := ⟨(Dg.toTm (.var .here)).eval eSys⟩
  let Y : Jet := ⟨solN S sys.length⟩
  rw [compZero_coeff_val_eq_sum Dg_sys Y 0 0 (le_refl 0), Finset.sum_range_one]
  have hpow0 : ((hPow Y 0).coeff 0).val = 1 := Q.val_ofNat 1
  have hDg0 : (Dg_sys.coeff 0).val = (solN sys v 1).val := by
    have hd := (uMul_solN_deriv_val sys hwf v hv 0).symm
    have h0 : (Dg_sys.coeff 0).val =
        (((tmJetDeriv (Γ := [])).eval Env.nil) (sys[v].1.eval Env.nil) 0).val +
        (((sys[v].2.toTm (.var .here)).eval eSys) 0).val := by
      change (Q.add ((Tm.closedWk (.app tmJetDeriv sys[v].1)).eval eSys 0)
        (((sys[v].2.toTm (.var .here)).eval eSys) 0)).val = _
      rw [closedWk_eval (.app tmJetDeriv sys[v].1) eSys, Q.val_add]
      rfl
    rw [h0, hd]
    change (Q.mul (Q.ofNat 1) (solN sys v 1)).val = (solN sys v 1).val
    rw [Q.val_mul, Q.val_ofNat]
    ring
  rw [hpow0, hDg0, mul_one]

/-- The value-level derivative of `Dg` evaluated on `solN S` equals `u · H(solN S)`. -/
theorem ivf_dg_deriv_val (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (hno : ∀ p ∈ sys, p.2.NoInteg)
    (v : Nat) (hv : v < sys.length) (j : Nat) :
    let S := invFunSys sys v hv
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    let Dg : JExprN := .add (.const (.app tmJetDeriv sys[v].1)) sys[v].2
    let H := Dg.derivSym sys
    let G1 := (Dg.toTm (.var .here)).eval eS
    let H_eval := (H.toTm (.var .here)).eval eS
    let u := solN S (sys.length + 1)
    (((tmJetDeriv (Γ := [])).eval Env.nil) G1 j).val =
      (((tmJetMul (Γ := [])).eval Env.nil) u H_eval j).val := by
  intro S eS Dg H G1 H_eval u
  let eSys : Env [WTy] := Env.cons (σ := WTy) (solN sys) Env.nil
  let Y : Jet := ⟨solN S sys.length⟩
  let Dg_sys : Jet := ⟨(Dg.toTm (.var .here)).eval eSys⟩
  let H_sys : Jet := ⟨(H.toTm (.var .here)).eval eSys⟩
  have hwf := gpac_wf hgpac
  have hpv := hgpac sys[v] (List.getElem_mem hv)
  have hDg_wf : Dg.WF sys.length := ⟨trivial, hpv.1⟩
  have hDg_cc : Dg.ConstsConst := ⟨gpac_isConstJet_deriv hpv.2.1, hpv.2.2⟩
  have hDg_no : Dg.NoInteg := ⟨trivial, hno sys[v] (List.getElem_mem hv)⟩
  have hH_wf : H.WF sys.length := uDeriv_derivSym_wf sys hwf Dg hDg_wf
  have hH_cc : H.ConstsConst := gpac_derivSym_constsConst sys hgpac Dg hDg_wf hDg_cc
  have hH_no : H.NoInteg := ivf_derivSym_noInteg sys hno Dg hDg_wf hDg_no
  have hG1_deriv : (((tmJetDeriv (Γ := [])).eval Env.nil) G1 j).val =
      (((Jet.compZero Dg_sys Y).deriv).coeff j).val := by
    change (Q.mul (Q.ofNat (j + 1)) (G1 (j + 1))).val =
      (Q.mul (Q.ofNat (j + 1)) ((Jet.compZero Dg_sys Y).coeff (j + 1))).val
    rw [Q.val_mul, Q.val_mul,
        ivf_toTm_solN_eq_compZero_val sys hgpac hno v hv Dg hDg_wf hDg_cc hDg_no (j + 1)]
  rw [hG1_deriv, compZero_deriv_val Dg_sys Y j, ← tmJetMul_eval Env.nil]
  refine tmJetMul_agreeV Env.nil Env.nil (j + 1)
    Y.deriv.coeff u (Jet.compZero Dg_sys.deriv Y).coeff H_eval
    (fun m _ ↦ ivf_solN_y_deriv_val sys hwf v hv m) (fun m _ ↦ ?_) j (Nat.lt_succ_self j)
  rw [ivf_toTm_solN_eq_compZero_val sys hgpac hno v hv H hH_wf hH_cc hH_no m]
  exact compZero_congr_val Dg_sys.deriv H_sys Y
    (fun k ↦ (uDeriv_derivSym_val sys hwf Dg hDg_wf k).symm) m

/-- At degree `0`, component `sys.length + 1` of `solN (invFunSys sys v hv)` has value `1 / (solN sys v 1).val`. -/
theorem ivf_solN_u_zero_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length)
    (h1 : (solN sys v 1).val ≠ 0) :
    (solN (invFunSys sys v hv) (sys.length + 1) 0).val = 1 / (solN sys v 1).val := by
  let S := invFunSys sys v hv
  have hu : sys.length + 1 < S.length := by rw [ivf_invFunSys_length]; omega
  rw [uMul_solN_zero_val S (ivf_invFunSys_wf sys hwf v hv) (sys.length + 1) hu,
      ivf_invFunSys_getElem_u sys v hv]
  let Ah : Tm [] JetTy :=
    .app (.app tmJetAdd (.app tmJetDeriv sys[v].1)) (sys[v].2.toTm (initN sys))
  have hF : sys[v].2.WF sys.length := hwf sys[v] (List.getElem_mem hv)
  have hAh0 : (Ah.eval Env.nil 0).val = (solN sys v 1).val := by
    change (Q.add (((tmJetDeriv (Γ := [])).eval Env.nil) (sys[v].1.eval Env.nil) 0)
                  (((sys[v].2.toTm (initN sys)).eval Env.nil) 0)).val = _
    rw [Q.val_add, uDeriv_toTm_initN_zero_val sys hwf sys[v].2 hF,
        ← uMul_solN_deriv_val sys hwf v hv 0]
    change (Q.mul (Q.ofNat 1) (solN sys v 1)).val = (solN sys v 1).val
    rw [Q.val_mul, Q.val_ofNat]
    ring
  have hne : (Ah.eval Env.nil 0).num ≠ 0 := by
    apply inv_num_ne_zero
    rw [hAh0]
    exact h1
  change (Q.div (Q.ofNat 1) (Ah.eval Env.nil 0)).val = 1 / (solN sys v 1).val
  rw [Q.val_div _ _ hne, Q.val_ofNat, hAh0]
  rfl

/-- Derivative of component `sys.length + 1` of `solN (invFunSys sys v hv)` satisfies `u' = -(((u · u) · u) · H(solN S))`. -/
theorem ivf_solN_u_deriv_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) (j : Nat) :
    let S := invFunSys sys v hv
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    let Dg : JExprN := .add (.const (.app tmJetDeriv sys[v].1)) sys[v].2
    let H := Dg.derivSym sys
    let H_eval := (H.toTm (.var .here)).eval eS
    let u := solN S (sys.length + 1)
    let mul := (tmJetMul (Γ := [])).eval Env.nil
    (((tmJetDeriv (Γ := [])).eval Env.nil) u j).val =
      - (mul (mul (mul u u) u) H_eval j).val := by
  intro S eS Dg H H_eval u mul
  have hu : sys.length + 1 < S.length := by rw [ivf_invFunSys_length]; omega
  have hderiv := uMul_solN_deriv_val S (ivf_invFunSys_wf sys hwf v hv) (sys.length + 1) hu j
  rw [ivf_invFunSys_getElem_u sys v hv] at hderiv
  let Ah : Tm [] JetTy :=
    .app (.app tmJetAdd (.app tmJetDeriv sys[v].1)) (sys[v].2.toTm (initN sys))
  have hA_deriv : (((tmJetDeriv (Γ := [])).eval Env.nil) ((Tm.app tmInv0 Ah).eval Env.nil) j).val = 0 :=
    gpac_deriv_const_val (inv_isConstJet_inv0 Ah) j
  have hvar : ((JExprN.var (sys.length + 1)).toTm (.var .here)).eval eS = u := by
    change solN S ((natTm (sys.length + 1)).eval eS) = u
    rw [natTm_eval]
  have hmul : ((((JExprN.mul (.mul (.mul (.var (sys.length + 1)) (.var (sys.length + 1)))
      (.var (sys.length + 1))) H).toTm (.var .here)).eval eS) j) =
      mul (mul (mul u u) u) H_eval j := by
    rw [ivf_toTm_mul_eval, ivf_toTm_mul_eval, ivf_toTm_mul_eval, hvar]
  have hFlast : ((((JExprN.sub (.const tmZeroJet)
      (.mul (.mul (.mul (.var (sys.length + 1)) (.var (sys.length + 1)))
        (.var (sys.length + 1))) H)).toTm (.var .here)).eval eS) j).val =
      - (mul (mul (mul u u) u) H_eval j).val := by
    change (Q.sub ((Tm.closedWk tmZeroJet).eval eS j)
      ((((JExprN.mul (.mul (.mul (.var (sys.length + 1)) (.var (sys.length + 1)))
        (.var (sys.length + 1))) H).toTm (.var .here)).eval eS) j)).val = _
    rw [closedWk_eval tmZeroJet eS, Q.val_sub, hmul]
    have hz : (tmZeroJet.eval Env.nil j).val = 0 := Q.val_ofNat 0
    rw [hz, zero_sub]
  dsimp only at hderiv
  rw [hderiv, hA_deriv, hFlast, zero_add]

/-- In `invFunSys sys v hv`, the product `Dg(solN S) · u` equals the constant jet `1` in value. -/
theorem ivf_mul_dg_u_eq_one_val (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (hno : ∀ p ∈ sys, p.2.NoInteg)
    (v : Nat) (hv : v < sys.length) (h1 : (solN sys v 1).val ≠ 0) (n : Nat) :
    let S := invFunSys sys v hv
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    let Dg : JExprN := .add (.const (.app tmJetDeriv sys[v].1)) sys[v].2
    let G1 := (Dg.toTm (.var .here)).eval eS
    let u := solN S (sys.length + 1)
    (((tmJetMul (Γ := [])).eval Env.nil) G1 u n).val =
      ((Jet.const (Q.ofNat 1)).coeff n).val := by
  intro S eS Dg G1 u
  have hwf := gpac_wf hgpac
  let mul := (tmJetMul (Γ := [])).eval Env.nil
  let deriv := (tmJetDeriv (Γ := [])).eval Env.nil
  let H := Dg.derivSym sys
  let H_eval := (H.toTm (.var .here)).eval eS
  let p := mul G1 u
  let K := mul (deriv G1) u
  let q : Nat → Rat := fun m ↦ ((Jet.const (Q.ofNat 1)).coeff m).val - (p m).val
  have hq0 : q 0 = 0 := by
    dsimp [q, p, mul]
    rw [uMul_zero_val, ivf_dg_zero_val sys hgpac hno v hv, ivf_solN_u_zero_val sys hwf v hv h1]
    change (Q.ofNat 1).val - (solN sys v 1).val * (1 / (solN sys v 1).val) = 0
    rw [Q.val_ofNat]
    field_simp
    ring
  have hdu : ∀ j, (deriv u j).val = - (mul K u j).val := by
    intro j
    rw [ivf_solN_u_deriv_val sys hwf v hv j]
    refine congrArg Neg.neg ?_
    rw [inv_jetMul_assoc_val (mul u u) u H_eval j,
        inv_jetMul_comm_val (mul u u) (mul u H_eval) j,
        ← inv_jetMul_assoc_val (mul u H_eval) u u j]
    refine tmJetMul_agreeV Env.nil Env.nil (j + 1)
      (mul (mul u H_eval) u) K u u (fun m _ ↦ ?_) (fun _ _ ↦ rfl) j (Nat.lt_succ_self j)
    exact tmJetMul_agreeV Env.nil Env.nil (m + 1)
      (mul u H_eval) (deriv G1) u u
      (fun i _ ↦ (ivf_dg_deriv_val sys hgpac hno v hv i).symm) (fun _ _ ↦ rfl)
      m (Nat.lt_succ_self m)
  have hrec : ∀ m, ((m + 1 : Nat) : Rat) * q (m + 1) =
      - ∑ i ∈ Finset.range (m + 1), (K i).val * q (m - i) := by
    intro m
    have h_G1_du : (mul G1 (deriv u) m).val = - (mul G1 (mul K u) m).val := by
      rw [inv_jetMul_val, inv_jetMul_val, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hdu (m - i)]
      ring
    have h_reassoc : (mul G1 (mul K u) m).val = (mul K p m).val := by
      rw [← inv_jetMul_assoc_val G1 K u m,
          tmJetMul_agreeV Env.nil Env.nil (m + 1) (mul G1 K) (mul K G1) u u
            (fun i _ ↦ inv_jetMul_comm_val G1 K i) (fun _ _ ↦ rfl) m (Nat.lt_succ_self m),
          inv_jetMul_assoc_val K G1 u m]
    have h_dp : ((m + 1 : Nat) : Rat) * (p (m + 1)).val = (K m).val - (mul K p m).val := by
      have hleib := jetMul_leibniz_val G1 u m
      change (Q.mul (Q.ofNat (m + 1)) (p (m + 1))).val =
        (K m).val + (mul G1 (deriv u) m).val at hleib
      rw [Q.val_mul, Q.val_ofNat, h_G1_du, h_reassoc] at hleib
      linarith
    have h_rhs : (K m).val - (mul K p m).val =
        ∑ i ∈ Finset.range (m + 1), (K i).val * q (m - i) := by
      dsimp [q]
      rw [← inv_mul_one_val K m, inv_jetMul_val K p m, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    dsimp [q]
    change ((m + 1 : Nat) : Rat) * (Q.zero.val - (p (m + 1)).val) = _
    rw [Q.val_zero, zero_sub, mul_neg, h_dp, h_rhs]
  have hqn := inv_zero_of_linear_rec (fun i ↦ (K i).val) q hq0 hrec n
  dsimp [q] at hqn
  linarith

/-- In `invFunSys sys v hv`, if `(solN sys v 0).val = 0` and `(solN sys v 1).val ≠ 0`, then component `v` of `solN S` has value `if n = 1 then 1 else 0`. -/
theorem ivf_solN_v_val (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (hno : ∀ p ∈ sys, p.2.NoInteg)
    (v : Nat) (hv : v < sys.length)
    (h0 : (solN sys v 0).val = 0) (h1 : (solN sys v 1).val ≠ 0) (n : Nat) :
    (solN (invFunSys sys v hv) v n).val = if n = 1 then 1 else 0 := by
  let S := invFunSys sys v hv
  have hgpacS := ivf_gpac_invFunSys sys hgpac v hv
  have hwf := gpac_wf hgpac
  have hwfS := gpac_wf hgpacS
  have hvS : v < S.length := by rw [ivf_invFunSys_length]; omega
  cases n with
  | zero =>
    rw [uMul_solN_zero_val S hwfS v hvS, ivf_invFunSys_getElem_lt sys v hv v hv]
    dsimp only
    rw [← uMul_solN_zero_val sys hwf v hv, h0]
    rfl
  | succ j =>
    rw [sbd_solN_succ_val S hgpacS v hvS j, ivf_invFunSys_getElem_lt sys v hv v hv]
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    let Dg : JExprN := .add (.const (.app tmJetDeriv sys[v].1)) sys[v].2
    let G1 := (Dg.toTm (.var .here)).eval eS
    let u := solN S (sys.length + 1)
    have hpv := hgpac sys[v] (List.getElem_mem hv)
    have hFv_eq_G1 : ∀ m < j + 1, (((sys[v].2.toTm (.var .here)).eval eS) m).val = (G1 m).val := by
      intro m _
      have h0 := gpac_deriv_const_val hpv.2.1 m
      have hG1 : (G1 m).val =
          (((tmJetDeriv (Γ := [])).eval Env.nil) (sys[v].1.eval Env.nil) m).val +
          (((sys[v].2.toTm (.var .here)).eval eS) m).val := by
        change (Q.add ((Tm.closedWk (.app tmJetDeriv sys[v].1)).eval eS m)
          (((sys[v].2.toTm (.var .here)).eval eS) m)).val = _
        rw [closedWk_eval (.app tmJetDeriv sys[v].1) eS, Q.val_add]
        rfl
      linarith
    have hvar : ((JExprN.var (sys.length + 1)).toTm (.var .here)).eval eS = u := by
      change solN S ((natTm (sys.length + 1)).eval eS) = u
      rw [natTm_eval]
    have hsbd : (sbdEvalExpr (.mul sys[v].2 (.var (sys.length + 1))) (solN S) j).val =
        ((Jet.const (Q.ofNat 1)).coeff j).val := by
      have hm := tmJetMul_agreeV Env.nil Env.nil (j + 1)
        ((sys[v].2.toTm (.var .here)).eval eS) G1
        (((JExprN.var (sys.length + 1)).toTm (.var .here)).eval eS) u
        hFv_eq_G1 (by rw [hvar]; exact fun _ _ ↦ rfl) j (Nat.lt_succ_self j)
      exact hm.trans (ivf_mul_dg_u_eq_one_val sys hgpac hno v hv h1 j)
    dsimp only
    rw [hsbd]
    cases j with
    | zero =>
      change (Q.ofNat 1).val / ((0 + 1 : Nat) : Rat) = if 0 + 1 = 1 then 1 else 0
      rw [Q.val_ofNat]
      norm_num
    | succ k =>
      change Q.zero.val / ((k + 1 + 1 : Nat) : Rat) = if k + 1 + 1 = 1 then 1 else 0
      rw [Q.val_zero, zero_div, if_neg (by omega)]

/-- **Local inverse function theorem.** -/
theorem InGPAC_invFun (g : Nat → Q) (hg : InGPAC g) (h0 : (g 0).val = 0)
    (h1 : (g 1).val ≠ 0) :
    ∃ y : Nat → Q, InGPAC y ∧ (y 0).val = 0 ∧
      ∀ n, ((Jet.compZero ⟨g⟩ ⟨y⟩).coeff n).val = if n = 1 then 1 else 0 := by
  obtain ⟨sys, hgpac, hno, v, hv, hg_val⟩ := InGPAC_noInteg g hg
  let S := invFunSys sys v hv
  let y := solN S sys.length
  have hgpacS := ivf_gpac_invFunSys sys hgpac v hv
  have hy_idx : sys.length < S.length := by rw [ivf_invFunSys_length]; omega
  have hy_gpac : InGPAC y := ⟨S, hgpacS, sys.length, hy_idx, fun _ ↦ rfl⟩
  have hy0 : (y 0).val = 0 := ivf_solN_y_zero_val sys (gpac_wf hgpac) v hv
  have hsol0 : (solN sys v 0).val = 0 := by rw [← hg_val 0]; exact h0
  have hsol1 : (solN sys v 1).val ≠ 0 := by rw [← hg_val 1]; exact h1
  refine ⟨y, hy_gpac, hy0, fun n ↦ ?_⟩
  rw [compZero_congr_val ⟨g⟩ ⟨solN sys v⟩ ⟨y⟩ hg_val n,
      ← ivf_solN_eq_compZero_val sys hgpac hno v hv v hv n]
  exact ivf_solN_v_val sys hgpac hno v hv hsol0 hsol1 n

/-! ## Check: `arcsin`

From the `(sin, cos)` system, the `y` component is `arcsin`:
`x + x³/6 + 3x⁵/40 + 5x⁷/112` (read from the memoized table `solFast`,
proved equal to `solN` in `SystemFast.lean`). -/

#guard (List.range 9).map (fun n ↦ Q.norm (solFast (invFunSys memSinCosSys 0 (by decide)) 2 n))
  == [Q.zero, Q.ofNat 1, Q.zero, ⟨1, 5⟩, Q.zero, ⟨3, 39⟩, Q.zero, ⟨5, 111⟩, Q.zero].map Q.norm

#print axioms invFunSys
#print axioms InGPAC_invFun

end HAomega
