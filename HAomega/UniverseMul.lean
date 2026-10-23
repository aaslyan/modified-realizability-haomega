/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseTrial

/-!
# The polynomial-ODE universe is closed under `×`

`InUniverse_mul`: if `f` and `g` are components of solutions of well-formed
polynomial–integral systems, so is their Cauchy product `f · g`.

The proof builds a system for `f · g` (`mulSys`): the system of `f`, the system
of `g` with its variables renumbered after it, and one new variable
`h = A_f·A_g + ∫(f'·g + f·g' − D(A_f·A_g))`, where `f' = D A_f + F_f`,
`g' = D A_g + F_g` (derivatives read off the equations `f = A_f + ∫F_f`,
`g = A_g + ∫F_g`). The value-level product rule `jetMul_leibniz_val` makes
`f · g` a fixed point of that equation, and `genSolveN_unique_val` identifies
it with the proof-computed solution. Value-level metatheory theorems
(`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- **Product rule on coefficient streams**, as rational values:
    `D(a·b) = D a · b + a · D b`. -/
theorem jetMul_leibniz_val (a b : Nat → Q) (n : Nat) :
    (((tmJetDeriv (Γ := [])).eval Env.nil) (((tmJetMul (Γ := [])).eval Env.nil) a b) n).val =
      (((tmJetMul (Γ := [])).eval Env.nil) (((tmJetDeriv (Γ := [])).eval Env.nil) a) b n).val +
      (((tmJetMul (Γ := [])).eval Env.nil) a (((tmJetDeriv (Γ := [])).eval Env.nil) b) n).val := by
  change (Q.mul (Q.ofNat (n + 1)) (((tmJetMul (Γ := [])).eval Env.nil) a b (n + 1))).val =
    (((tmJetMul (Γ := [])).eval Env.nil) (((tmJetDeriv (Γ := [])).eval Env.nil) a) b n).val +
    (((tmJetMul (Γ := [])).eval Env.nil) a (((tmJetDeriv (Γ := [])).eval Env.nil) b) n).val
  rw [Q.val_mul, Q.val_ofNat, tmJetMul_eval, tmJetMul_eval, tmJetMul_eval]
  simp only [Jet.mul, TrigPoly.cauchyConvAux_val]
  let f₁ : Nat → Rat := fun i ↦ ((i : Nat) : Rat) * (a i).val * (b (n + 1 - i)).val
  let f₂ : Nat → Rat := fun i ↦ (a i).val * (((n + 1 - i : Nat) : Rat) * (b (n + 1 - i)).val)
  have h1 : (∑ i ∈ Finset.range (n + 1),
      ((((tmJetDeriv (Γ := [])).eval Env.nil) a i).val * (b (n - i)).val)) =
      ∑ i ∈ Finset.range (n + 2), f₁ i := by
    rw [Finset.sum_range_succ' f₁ (n + 1)]
    have hf1_zero : f₁ 0 = 0 := by dsimp [f₁]; ring
    rw [hf1_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change (Q.mul (Q.ofNat (i + 1)) (a (i + 1))).val * (b (n - i)).val =
      ((i + 1 : Nat) : Rat) * (a (i + 1)).val * (b (n + 1 - (i + 1))).val
    rw [Q.val_mul, Q.val_ofNat, Nat.add_sub_add_right]
  have h2 : (∑ i ∈ Finset.range (n + 1),
      ((a i).val * (((tmJetDeriv (Γ := [])).eval Env.nil) b (n - i)).val)) =
      ∑ i ∈ Finset.range (n + 2), f₂ i := by
    rw [Finset.sum_range_succ f₂ (n + 1)]
    have hf2_last : f₂ (n + 1) = 0 := by
      dsimp [f₂]
      rw [Nat.sub_self]
      ring
    rw [hf2_last, add_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    have hsub : n + 1 - i = n - i + 1 := by omega
    change (a i).val * (Q.mul (Q.ofNat (n - i + 1)) (b (n - i + 1))).val =
      (a i).val * (((n + 1 - i : Nat) : Rat) * (b (n + 1 - i)).val)
    rw [Q.val_mul, Q.val_ofNat, hsub]
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  dsimp [f₁, f₂]
  have hadd : ((i : Nat) : Rat) + ((n + 1 - i : Nat) : Rat) = ((n + 1 : Nat) : Rat) := by
    exact_mod_cast (by omega : i + (n + 1 - i) = n + 1)
  calc ((n + 1 : Nat) : Rat) * ((a i).val * (b (n + 1 - i)).val)
      = (((i : Nat) : Rat) + ((n + 1 - i : Nat) : Rat)) * ((a i).val * (b (n + 1 - i)).val) := by
        rw [hadd]
    _ = (i : Rat) * (a i).val * (b (n + 1 - i)).val +
        (a i).val * (((n + 1 - i : Nat) : Rat) * (b (n + 1 - i)).val) := by ring

/-- The combined system for `f · g`: `sys₁`, `sys₂` with variables shifted by
    `sys₁.length`, and the product equation
    `(A₁·A₂, (f'·g + f·g') − D(A₁·A₂))` with `f' = D A₁ + F₁`, `g' = D A₂ + F₂`. -/
def mulSys (sys₁ sys₂ : List (Tm [] JetTy × JExprN)) (v₁ v₂ : Nat)
    (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) : List (Tm [] JetTy × JExprN) :=
  let A₁ := sys₁[v₁].1
  let A₂ := sys₂[v₂].1
  let A₁₂ : Tm [] JetTy := .app (.app tmJetMul A₁) A₂
  let Df : JExprN := .add (.const (.app tmJetDeriv A₁)) sys₁[v₁].2
  let Dg : JExprN := .add (.const (.app tmJetDeriv A₂)) (sys₂[v₂].2.shiftVars sys₁.length)
  (sys₁ ++ sys₂.map (fun p ↦ (p.1, p.2.shiftVars sys₁.length))) ++
    [(A₁₂,
      .sub (.add (.mul Df (.var (sys₁.length + v₂))) (.mul (.var v₁) Dg))
        (.const (.app tmJetDeriv A₁₂)))]

/-- At degree `0`, `solN sys v 0` has the same rational value as `sys[v].1` at `0`. -/
theorem uMul_solN_zero_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    (solN sys v 0).val = (sys[v].1.eval Env.nil 0).val := by
  have hfix := (solN_fixed sys hwf v hv 0).symm
  rw [genStepN_eval_getElem sys (solN sys) v hv] at hfix
  unfold eqStepEval at hfix
  change (solN sys v 0).val = (Q.add (sys[v].1.eval Env.nil 0) (Q.ofNat 0)).val at hfix
  rw [hfix, Q.val_add, Q.val_ofNat]
  ring

/-- Value-level derivative of `solN sys v` at degree `j` equals `(D A_v)(j) + F_v(solN sys)(j)`. -/
theorem uMul_solN_deriv_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) (j : Nat) :
    (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys v) j).val =
      (((tmJetDeriv (Γ := [])).eval Env.nil) (sys[v].1.eval Env.nil) j).val +
      (((sys[v].2.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sys) Env.nil)) j).val := by
  have hfix := (solN_fixed sys hwf v hv (j + 1)).symm
  rw [genStepN_eval_getElem sys (solN sys) v hv] at hfix
  unfold eqStepEval at hfix
  set Fv := (sys[v].2.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sys) Env.nil)
  have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
  have hne_rat : ((j + 1 : Nat) : Rat) ≠ 0 := by positivity
  change (solN sys v (j + 1)).val =
    (Q.add (sys[v].1.eval Env.nil (j + 1)) (Q.div (Fv j) (Q.ofNat (j + 1)))).val at hfix
  rw [Q.val_add, Q.val_div _ _ hne, Q.val_ofNat] at hfix
  change (Q.mul (Q.ofNat (j + 1)) (solN sys v (j + 1))).val =
    (Q.mul (Q.ofNat (j + 1)) (sys[v].1.eval Env.nil (j + 1))).val + (Fv j).val
  rw [Q.val_mul, Q.val_mul, Q.val_ofNat, hfix]
  field_simp

/-- At degree `0`, `tmJetMul a b 0` has rational value `(a 0).val * (b 0).val`. -/
theorem uMul_zero_val (a b : Nat → Q) :
    (((tmJetMul (Γ := [])).eval Env.nil) a b 0).val = (a 0).val * (b 0).val := by
  rw [tmJetMul_eval]
  simp [Jet.mul, Jet.cauchyConvAux, Q.val_add, Q.val_mul, Q.val_zero]

/-- Length of `mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂`. -/
theorem mulSys_length (sys₁ sys₂ : List (Tm [] JetTy × JExprN)) (v₁ v₂ : Nat)
    (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    (mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂).length = sys₁.length + sys₂.length + 1 := by
  simp [mulSys, Nat.add_assoc]

/-- Well-formedness of `mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂`. -/
theorem mulSys_wf (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (hwf₁ : ∀ p ∈ sys₁, p.2.WF sys₁.length) (hwf₂ : ∀ p ∈ sys₂, p.2.WF sys₂.length)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    ∀ p ∈ mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂, p.2.WF (mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂).length := by
  rw [mulSys_length]
  intro p hp
  simp only [mulSys, List.mem_append, List.mem_map, List.mem_singleton] at hp
  rcases hp with (hp₁ | ⟨q, hq, rfl⟩) | rfl
  · exact (hwf₁ p hp₁).mono (by omega)
  · exact (q.2.shiftVars_wf sys₁.length sys₂.length (hwf₂ q hq)).mono (by omega)
  · refine ⟨⟨⟨⟨trivial, (hwf₁ sys₁[v₁] (List.getElem_mem hv₁)).mono (by omega)⟩,
        show sys₁.length + v₂ < sys₁.length + sys₂.length + 1 by omega⟩,
      ⟨show v₁ < sys₁.length + sys₂.length + 1 by omega, ⟨trivial, ?_⟩⟩⟩, trivial⟩
    exact (sys₂[v₂].2.shiftVars_wf sys₁.length sys₂.length
      (hwf₂ sys₂[v₂] (List.getElem_mem hv₂))).mono (by omega)

/-- Target solution state for `mulSys`: `solN sys₁` on `[0, n₁)`, `solN sys₂` shifted on `[n₁, n₁ + n₂)`, and `tmJetMul (solN sys₁ v₁) (solN sys₂ v₂)` at `n₁ + n₂`. -/
def uMulTargetState (sys₁ sys₂ : List (Tm [] JetTy × JExprN)) (v₁ v₂ : Nat) : Nat → Nat → Q :=
  fun w n ↦
    if w < sys₁.length then solN sys₁ w n
    else if w < sys₁.length + sys₂.length then solN sys₂ (w - sys₁.length) n
    else ((tmJetMul (Γ := [])).eval Env.nil) (solN sys₁ v₁) (solN sys₂ v₂) n

/-- Evaluating the product equation of `mulSys` on `uMulTargetState` yields the value of `tmJetMul (solN sys₁ v₁) (solN sys₂ v₂)`. -/
theorem uMul_eqStepEval_last_val (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (hwf₁ : ∀ p ∈ sys₁, p.2.WF sys₁.length) (hwf₂ : ∀ p ∈ sys₂, p.2.WF sys₂.length)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) (n : Nat) :
    let A₁ := sys₁[v₁].1
    let A₂ := sys₂[v₂].1
    let A₁₂ : Tm [] JetTy := .app (.app tmJetMul A₁) A₂
    let Df : JExprN := .add (.const (.app tmJetDeriv A₁)) sys₁[v₁].2
    let Dg : JExprN := .add (.const (.app tmJetDeriv A₂)) (sys₂[v₂].2.shiftVars sys₁.length)
    let F_last : JExprN :=
      .sub (.add (.mul Df (.var (sys₁.length + v₂))) (.mul (.var v₁) Dg))
        (.const (.app tmJetDeriv A₁₂))
    (eqStepEval (A₁₂, F_last) (uMulTargetState sys₁ sys₂ v₁ v₂) n).val =
      (((tmJetMul (Γ := [])).eval Env.nil) (solN sys₁ v₁) (solN sys₂ v₂) n).val := by
  intro A₁ A₂ A₁₂ Df Dg F_last
  let Z := uMulTargetState sys₁ sys₂ v₁ v₂
  let eZ : Env [WTy] := Env.cons (σ := WTy) Z Env.nil
  have hZ₁ : ∀ u < sys₁.length, Z u = solN sys₁ u := by
    intro u hu; funext m; exact if_pos hu
  have hZ₂ : ∀ u < sys₂.length, Z (sys₁.length + u) = solN sys₂ u := by
    intro u hu
    funext m
    unfold Z uMulTargetState
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  cases n with
  | zero =>
    unfold eqStepEval
    change (Q.add (A₁₂.eval Env.nil 0) (Q.ofNat 0)).val =
      (((tmJetMul (Γ := [])).eval Env.nil) (solN sys₁ v₁) (solN sys₂ v₂) 0).val
    have h0 : (Q.add (A₁₂.eval Env.nil 0) (Q.ofNat 0)).val = (A₁₂.eval Env.nil 0).val := by
      rw [Q.val_add, Q.val_ofNat]; ring
    rw [h0]
    change (((tmJetMul (Γ := [])).eval Env.nil) (A₁.eval Env.nil) (A₂.eval Env.nil) 0).val = _
    rw [uMul_zero_val, uMul_zero_val,
        uMul_solN_zero_val sys₁ hwf₁ v₁ hv₁, uMul_solN_zero_val sys₂ hwf₂ v₂ hv₂]
  | succ j =>
    have hDf : ∀ m < j + 1,
        (((Df.toTm (.var .here)).eval eZ) m).val =
          (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys₁ v₁) m).val := by
      intro m _
      have hF₁ := sys₁[v₁].2.toTm_eval_of_eq_below sys₁.length
        (hwf₁ sys₁[v₁] (List.getElem_mem hv₁)) eZ (Env.cons (σ := WTy) (solN sys₁) Env.nil)
        (.var .here) (.var .here) hZ₁
      change (Q.add ((Tm.closedWk (.app tmJetDeriv A₁)).eval eZ m)
        ((sys₁[v₁].2.toTm (.var .here)).eval eZ m)).val = _
      rw [closedWk_eval (.app tmJetDeriv A₁) eZ, hF₁, Q.val_add,
          uMul_solN_deriv_val sys₁ hwf₁ v₁ hv₁ m]
      rfl
    have hDg : ∀ m < j + 1,
        (((Dg.toTm (.var .here)).eval eZ) m).val =
          (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys₂ v₂) m).val := by
      intro m _
      have hF₂ := sys₂[v₂].2.shiftVars_toTm_eval sys₁.length sys₂.length
        (hwf₂ sys₂[v₂] (List.getElem_mem hv₂)) eZ (Env.cons (σ := WTy) (solN sys₂) Env.nil)
        (.var .here) (.var .here) hZ₂
      change (Q.add ((Tm.closedWk (.app tmJetDeriv A₂)).eval eZ m)
        (((sys₂[v₂].2.shiftVars sys₁.length).toTm (.var .here)).eval eZ m)).val = _
      rw [closedWk_eval (.app tmJetDeriv A₂) eZ, hF₂, Q.val_add,
          uMul_solN_deriv_val sys₂ hwf₂ v₂ hv₂ m]
      rfl
    have hvar₂ : ((JExprN.var (sys₁.length + v₂)).toTm (.var .here)).eval eZ = solN sys₂ v₂ := by
      change Z ((natTm (sys₁.length + v₂)).eval eZ) = solN sys₂ v₂
      rw [natTm_eval]
      exact hZ₂ v₂ hv₂
    have hvar₁ : ((JExprN.var v₁).toTm (.var .here)).eval eZ = solN sys₁ v₁ := by
      change Z ((natTm v₁).eval eZ) = solN sys₁ v₁
      rw [natTm_eval]
      exact hZ₁ v₁ hv₁
    have hmul₁ : ((((JExprN.mul Df (.var (sys₁.length + v₂))).toTm (.var .here)).eval eZ) j).val =
        (((tmJetMul (Γ := [])).eval Env.nil)
          (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys₁ v₁)) (solN sys₂ v₂) j).val := by
      have hm := tmJetMul_agreeV Env.nil Env.nil (j + 1)
        ((Df.toTm (.var .here)).eval eZ) (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys₁ v₁))
        (((JExprN.var (sys₁.length + v₂)).toTm (.var .here)).eval eZ) (solN sys₂ v₂)
        hDf (by rw [hvar₂]; exact fun _ _ ↦ rfl) j (Nat.lt_succ_self j)
      exact hm
    have hmul₂ : ((((JExprN.mul (.var v₁) Dg).toTm (.var .here)).eval eZ) j).val =
        (((tmJetMul (Γ := [])).eval Env.nil)
          (solN sys₁ v₁) (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys₂ v₂)) j).val := by
      have hm := tmJetMul_agreeV Env.nil Env.nil (j + 1)
        (((JExprN.var v₁).toTm (.var .here)).eval eZ) (solN sys₁ v₁)
        ((Dg.toTm (.var .here)).eval eZ) (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys₂ v₂))
        (by rw [hvar₁]; exact fun _ _ ↦ rfl) hDg j (Nat.lt_succ_self j)
      exact hm
    have hFlast : (((F_last.toTm (.var .here)).eval eZ) j).val =
        (((tmJetDeriv (Γ := [])).eval Env.nil)
          (((tmJetMul (Γ := [])).eval Env.nil) (solN sys₁ v₁) (solN sys₂ v₂)) j).val -
        (((tmJetDeriv (Γ := [])).eval Env.nil) (A₁₂.eval Env.nil) j).val := by
      change (Q.sub
        (Q.add ((((JExprN.mul Df (.var (sys₁.length + v₂))).toTm (.var .here)).eval eZ) j)
               ((((JExprN.mul (.var v₁) Dg).toTm (.var .here)).eval eZ) j))
        ((Tm.closedWk (.app tmJetDeriv A₁₂)).eval eZ j)).val = _
      rw [Q.val_sub, Q.val_add, hmul₁, hmul₂, ← jetMul_leibniz_val,
          closedWk_eval (.app tmJetDeriv A₁₂) eZ]
      rfl
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    have hne_rat : ((j + 1 : Nat) : Rat) ≠ 0 := by positivity
    unfold eqStepEval
    change (Q.add (A₁₂.eval Env.nil (j + 1))
      (Q.div (((F_last.toTm (.var .here)).eval eZ) j) (Q.ofNat (j + 1)))).val = _
    rw [Q.val_add, Q.val_div _ _ hne, Q.val_ofNat, hFlast]
    change (A₁₂.eval Env.nil (j + 1)).val +
      ((Q.mul (Q.ofNat (j + 1))
          (((tmJetMul (Γ := [])).eval Env.nil) (solN sys₁ v₁) (solN sys₂ v₂) (j + 1))).val -
       (Q.mul (Q.ofNat (j + 1)) (A₁₂.eval Env.nil (j + 1))).val) / ((j + 1 : Nat) : Rat) = _
    rw [Q.val_mul, Q.val_mul, Q.val_ofNat]
    field_simp
    ring

/-- `uMulTargetState` is a value-level fixed point of `genStepN (mulSys ...)`. -/
theorem uMulTargetState_fixed (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (hwf₁ : ∀ p ∈ sys₁, p.2.WF sys₁.length) (hwf₂ : ∀ p ∈ sys₂, p.2.WF sys₂.length)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    ∀ w < (mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂).length, ∀ n,
      ((((genStepN (mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂) (Γ := [])).eval Env.nil)
        (uMulTargetState sys₁ sys₂ v₁ v₂)) w n).val =
        (uMulTargetState sys₁ sys₂ v₁ v₂ w n).val := by
  intro w hw n
  rw [genStepN_eval_getElem _ _ w hw]
  have hw_len : w < sys₁.length + sys₂.length + 1 := by rwa [mulSys_length] at hw
  have hZ₁ : ∀ u < sys₁.length, uMulTargetState sys₁ sys₂ v₁ v₂ u = solN sys₁ u := by
    intro u hu; funext m; exact if_pos hu
  have hZ₂ : ∀ u < sys₂.length, uMulTargetState sys₁ sys₂ v₁ v₂ (sys₁.length + u) = solN sys₂ u := by
    intro u hu
    funext m
    unfold uMulTargetState
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  by_cases hw₁ : w < sys₁.length
  · have hget : (mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂)[w] = sys₁[w] := by
      simp only [mulSys]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hw₁]
    rw [hget, eqStepEval_of_eq_below sys₁[w] sys₁.length (hwf₁ sys₁[w] (List.getElem_mem hw₁)) _ _ hZ₁,
        ← genStepN_eval_getElem sys₁ (solN sys₁) w hw₁]
    unfold uMulTargetState
    rw [if_pos hw₁]
    exact solN_fixed sys₁ hwf₁ w hw₁ n
  · by_cases hw₂ : w < sys₁.length + sys₂.length
    · have hu : w - sys₁.length < sys₂.length := by omega
      have hget : (mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂)[w] =
          (sys₂[w - sys₁.length].1, sys₂[w - sys₁.length].2.shiftVars sys₁.length) := by
        simp only [mulSys]
        rw [List.getElem_append_left (by simp; omega),
            List.getElem_append_right (Nat.not_lt.mp hw₁), List.getElem_map]
      rw [hget, eqStepEval_shiftVars sys₂[w - sys₁.length] sys₁.length sys₂.length
            (hwf₂ sys₂[w - sys₁.length] (List.getElem_mem hu)) _ _ hZ₂,
          ← genStepN_eval_getElem sys₂ (solN sys₂) (w - sys₁.length) hu]
      unfold uMulTargetState
      rw [if_neg hw₁, if_pos hw₂]
      exact solN_fixed sys₂ hwf₂ (w - sys₁.length) hu n
    · have hw_eq : w = sys₁.length + sys₂.length := by omega
      have hget : (mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂)[w] =
          (let A₁ := sys₁[v₁].1
           let A₂ := sys₂[v₂].1
           let A₁₂ : Tm [] JetTy := .app (.app tmJetMul A₁) A₂
           let Df : JExprN := .add (.const (.app tmJetDeriv A₁)) sys₁[v₁].2
           let Dg : JExprN := .add (.const (.app tmJetDeriv A₂)) (sys₂[v₂].2.shiftVars sys₁.length)
           (A₁₂,
            .sub (.add (.mul Df (.var (sys₁.length + v₂))) (.mul (.var v₁) Dg))
              (.const (.app tmJetDeriv A₁₂)))) := by
        simp only [mulSys]
        rw [List.getElem_append_right (by simp; omega)]
        simp [hw_eq]
      rw [hget, uMul_eqStepEval_last_val sys₁ sys₂ hwf₁ hwf₂ v₁ v₂ hv₁ hv₂ n]
      unfold uMulTargetState
      rw [if_neg hw₁, if_neg hw₂]

/-- **Closure under `×`.** -/
theorem InUniverse_mul (f g : Nat → Q) (hf : InUniverse f) (hg : InUniverse g) :
    InUniverse (((tmJetMul (Γ := [])).eval Env.nil) f g) := by
  rcases hf with ⟨sys₁, hwf₁, v₁, hv₁, hf_val⟩
  rcases hg with ⟨sys₂, hwf₂, v₂, hv₂, hg_val⟩
  let S := mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂
  have hwfS := mulSys_wf sys₁ sys₂ hwf₁ hwf₂ v₁ v₂ hv₁ hv₂
  have hvS : sys₁.length + sys₂.length < S.length := by
    rw [mulSys_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hwfS, sys₁.length + sys₂.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (uMulTargetState sys₁ sys₂ v₁ v₂)
    (uMulTargetState_fixed sys₁ sys₂ hwf₁ hwf₂ v₁ v₂ hv₁ hv₂)
    (n + 1) (sys₁.length + sys₂.length) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  have hfg := tmJetMul_agreeV Env.nil Env.nil (n + 1) f (solN sys₁ v₁) g (solN sys₂ v₂)
    (fun i _ ↦ hf_val i) (fun i _ ↦ hg_val i) n (Nat.lt_succ_self n)
  change ((((tmJetMul (Γ := [])).eval Env.nil) f g) n).val =
    ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
      (sys₁.length + sys₂.length) n).val
  rw [huniq]
  unfold uMulTargetState
  rw [if_neg (by omega), if_neg (by omega)]
  exact hfg

#print axioms jetMul_leibniz_val
#print axioms InUniverse_mul

end HAomega
