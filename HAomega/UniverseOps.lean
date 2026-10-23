/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseMul

/-!
# The polynomial-ODE universe is closed under `−`, `∫` and `d/dx`

Each closure builds a system and identifies its new variable with the target
by `genSolveN_unique_val`, as for `+` and `×`.

* `−`: `subSys`, the two systems and `h = (A_f − A_g) + ∫(F_f − F_g)`.
* `∫`: `integSys`, the system and `h = 0 + ∫f`.
* `d/dx`: `derivSys`. From `f = A + ∫F(W)`, `f' = D A + F(W)`, and
  `f'' = D(D A) + (D F)(W)`, where `JExprN.derivSym` differentiates a
  right-hand side symbolically (each variable `u` by its own equation,
  `D(var u) = D A_u + F_u`; product rule; `D(∫a) = a`). The new variable is
  `h = A_h + ∫(D(D A) + (D F)(W) − D A_h)` with the closed initial jet
  `A_h = D A + F(initN)`; `F(initN)` has the right constant coefficient
  because coefficient `0` of `F(W)` depends only on coefficient `0` of `W`.

Value-level metatheory theorems (`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- The combined system for `f − g`. -/
def subSys (sys₁ sys₂ : List (Tm [] JetTy × JExprN)) (v₁ v₂ : Nat)
    (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) : List (Tm [] JetTy × JExprN) :=
  (sys₁ ++ sys₂.map (fun p ↦ (p.1, p.2.shiftVars sys₁.length))) ++
    [(.app (.app tmJetSub sys₁[v₁].1) sys₂[v₂].1,
      .sub sys₁[v₁].2 (sys₂[v₂].2.shiftVars sys₁.length))]

/-- The system for `∫f`. -/
def integSys (sys : List (Tm [] JetTy × JExprN)) (v : Nat) : List (Tm [] JetTy × JExprN) :=
  sys ++ [(tmZeroJet, .var v)]

/-- Symbolic derivative of a right-hand side over the system `sys`. -/
def JExprN.derivSym (sys : List (Tm [] JetTy × JExprN)) : JExprN → JExprN
  | .var u =>
      let p := sys.getD u (tmZeroJet, .const tmZeroJet)
      .add (.const (.app tmJetDeriv p.1)) p.2
  | .const c => .const (.app tmJetDeriv c)
  | .add a b => .add (a.derivSym sys) (b.derivSym sys)
  | .sub a b => .sub (a.derivSym sys) (b.derivSym sys)
  | .mul a b => .add (.mul (a.derivSym sys) b) (.mul a (b.derivSym sys))
  | .integ a => a

/-- The system for `f'`. -/
def derivSys (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    List (Tm [] JetTy × JExprN) :=
  let A := sys[v].1
  let F := sys[v].2
  let Ah : Tm [] JetTy := .app (.app tmJetAdd (.app tmJetDeriv A)) (F.toTm (initN sys))
  sys ++ [(Ah,
    .sub (.add (.const (.app tmJetDeriv (.app tmJetDeriv A))) (F.derivSym sys))
      (.const (.app tmJetDeriv Ah)))]

/-- Evaluating the difference equation `(A₁ − A₂, F₁ − F₂.shiftVars n₁)` on `W` gives the value difference of `eqStepEval p₁ W₁` and `eqStepEval p₂ W₂`. -/
theorem uSub_eqStepEval_val (p₁ p₂ : Tm [] JetTy × JExprN) (n₁ n₂ : Nat)
    (hp₁ : p₁.2.WF n₁) (hp₂ : p₂.2.WF n₂)
    (W W₁ W₂ : Nat → Nat → Q)
    (hw₁ : ∀ u < n₁, W u = W₁ u) (hw₂ : ∀ u < n₂, W (n₁ + u) = W₂ u) (n : Nat) :
    (eqStepEval (.app (.app tmJetSub p₁.1) p₂.1, .sub p₁.2 (p₂.2.shiftVars n₁)) W n).val =
      (eqStepEval p₁ W₁ n).val - (eqStepEval p₂ W₂ n).val := by
  unfold eqStepEval
  dsimp only [JExprN.toTm, Tm.eval]
  rw [p₁.2.toTm_eval_of_eq_below n₁ hp₁ (Env.cons (σ := WTy) W Env.nil)
        (Env.cons (σ := WTy) W₁ Env.nil) (.var .here) (.var .here) hw₁,
      p₂.2.shiftVars_toTm_eval n₁ n₂ hp₂ (Env.cons (σ := WTy) W Env.nil)
        (Env.cons (σ := WTy) W₂ Env.nil) (.var .here) (.var .here) hw₂]
  set F₁ := (p₁.2.toTm (.var .here)).eval (Env.cons (σ := WTy) W₁ Env.nil)
  set F₂ := (p₂.2.toTm (.var .here)).eval (Env.cons (σ := WTy) W₂ Env.nil)
  cases n with
  | zero =>
    change (Q.add (Q.sub (p₁.1.eval Env.nil 0) (p₂.1.eval Env.nil 0)) (Q.ofNat 0)).val =
      (Q.add (p₁.1.eval Env.nil 0) (Q.ofNat 0)).val - (Q.add (p₂.1.eval Env.nil 0) (Q.ofNat 0)).val
    simp only [Q.val_add, Q.val_sub, Q.val_ofNat]
    ring
  | succ j =>
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    change (Q.add (Q.sub (p₁.1.eval Env.nil (j + 1)) (p₂.1.eval Env.nil (j + 1)))
        (Q.div (Q.sub (F₁ j) (F₂ j)) (Q.ofNat (j + 1)))).val =
      (Q.add (p₁.1.eval Env.nil (j + 1)) (Q.div (F₁ j) (Q.ofNat (j + 1)))).val -
      (Q.add (p₂.1.eval Env.nil (j + 1)) (Q.div (F₂ j) (Q.ofNat (j + 1)))).val
    rw [Q.val_add, Q.val_sub, Q.val_add, Q.val_add,
        Q.val_div _ _ hne, Q.val_div _ _ hne, Q.val_div _ _ hne, Q.val_sub]
    ring

/-- Length of `subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂`. -/
theorem uSub_subSys_length (sys₁ sys₂ : List (Tm [] JetTy × JExprN)) (v₁ v₂ : Nat)
    (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    (subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂).length = sys₁.length + sys₂.length + 1 := by
  simp [subSys, Nat.add_assoc]

/-- Well-formedness of `subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂`. -/
theorem uSub_subSys_wf (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (hwf₁ : ∀ p ∈ sys₁, p.2.WF sys₁.length) (hwf₂ : ∀ p ∈ sys₂, p.2.WF sys₂.length)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    ∀ p ∈ subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂, p.2.WF (subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂).length := by
  rw [uSub_subSys_length]
  intro p hp
  simp only [subSys, List.mem_append, List.mem_map, List.mem_singleton] at hp
  rcases hp with (hp₁ | ⟨q, hq, rfl⟩) | rfl
  · exact (hwf₁ p hp₁).mono (by omega)
  · exact (q.2.shiftVars_wf sys₁.length sys₂.length (hwf₂ q hq)).mono (by omega)
  · refine ⟨(hwf₁ sys₁[v₁] (List.getElem_mem hv₁)).mono (by omega), ?_⟩
    exact (sys₂[v₂].2.shiftVars_wf sys₁.length sys₂.length
      (hwf₂ sys₂[v₂] (List.getElem_mem hv₂))).mono (by omega)

/-- Target solution state for `subSys`: `solN sys₁` on `[0, n₁)`, `solN sys₂` shifted on `[n₁, n₁ + n₂)`, and `solN sys₁ v₁ − solN sys₂ v₂` at `n₁ + n₂`. -/
def uSubTargetState (sys₁ sys₂ : List (Tm [] JetTy × JExprN)) (v₁ v₂ : Nat) : Nat → Nat → Q :=
  fun w n ↦
    if w < sys₁.length then solN sys₁ w n
    else if w < sys₁.length + sys₂.length then solN sys₂ (w - sys₁.length) n
    else Q.sub (solN sys₁ v₁ n) (solN sys₂ v₂ n)

/-- `uSubTargetState` is a value-level fixed point of `genStepN (subSys ...)`. -/
theorem uSubTargetState_fixed (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (hwf₁ : ∀ p ∈ sys₁, p.2.WF sys₁.length) (hwf₂ : ∀ p ∈ sys₂, p.2.WF sys₂.length)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    ∀ w < (subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂).length, ∀ n,
      ((((genStepN (subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂) (Γ := [])).eval Env.nil)
        (uSubTargetState sys₁ sys₂ v₁ v₂)) w n).val =
        (uSubTargetState sys₁ sys₂ v₁ v₂ w n).val := by
  intro w hw n
  rw [genStepN_eval_getElem _ _ w hw]
  have hw_len : w < sys₁.length + sys₂.length + 1 := by rwa [uSub_subSys_length] at hw
  have hZ₁ : ∀ u < sys₁.length, uSubTargetState sys₁ sys₂ v₁ v₂ u = solN sys₁ u := by
    intro u hu; funext m; exact if_pos hu
  have hZ₂ : ∀ u < sys₂.length, uSubTargetState sys₁ sys₂ v₁ v₂ (sys₁.length + u) = solN sys₂ u := by
    intro u hu
    funext m
    unfold uSubTargetState
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  by_cases hw₁ : w < sys₁.length
  · have hget : (subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂)[w] = sys₁[w] := by
      simp only [subSys]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hw₁]
    rw [hget, eqStepEval_of_eq_below sys₁[w] sys₁.length (hwf₁ sys₁[w] (List.getElem_mem hw₁)) _ _ hZ₁,
        ← genStepN_eval_getElem sys₁ (solN sys₁) w hw₁]
    unfold uSubTargetState
    rw [if_pos hw₁]
    exact solN_fixed sys₁ hwf₁ w hw₁ n
  · by_cases hw₂ : w < sys₁.length + sys₂.length
    · have hu : w - sys₁.length < sys₂.length := by omega
      have hget : (subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂)[w] =
          (sys₂[w - sys₁.length].1, sys₂[w - sys₁.length].2.shiftVars sys₁.length) := by
        simp only [subSys]
        rw [List.getElem_append_left (by simp; omega),
            List.getElem_append_right (Nat.not_lt.mp hw₁), List.getElem_map]
      rw [hget, eqStepEval_shiftVars sys₂[w - sys₁.length] sys₁.length sys₂.length
            (hwf₂ sys₂[w - sys₁.length] (List.getElem_mem hu)) _ _ hZ₂,
          ← genStepN_eval_getElem sys₂ (solN sys₂) (w - sys₁.length) hu]
      unfold uSubTargetState
      rw [if_neg hw₁, if_pos hw₂]
      exact solN_fixed sys₂ hwf₂ (w - sys₁.length) hu n
    · have hw_eq : w = sys₁.length + sys₂.length := by omega
      have hget : (subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂)[w] =
          (.app (.app tmJetSub sys₁[v₁].1) sys₂[v₂].1,
           .sub sys₁[v₁].2 (sys₂[v₂].2.shiftVars sys₁.length)) := by
        simp only [subSys]
        rw [List.getElem_append_right (by simp; omega)]
        simp [hw_eq]
      rw [hget, uSub_eqStepEval_val sys₁[v₁] sys₂[v₂] sys₁.length sys₂.length
            (hwf₁ sys₁[v₁] (List.getElem_mem hv₁)) (hwf₂ sys₂[v₂] (List.getElem_mem hv₂))
            _ _ _ hZ₁ hZ₂ n,
          ← genStepN_eval_getElem sys₁ (solN sys₁) v₁ hv₁,
          ← genStepN_eval_getElem sys₂ (solN sys₂) v₂ hv₂,
          solN_fixed sys₁ hwf₁ v₁ hv₁ n, solN_fixed sys₂ hwf₂ v₂ hv₂ n]
      unfold uSubTargetState
      rw [if_neg hw₁, if_neg hw₂, Q.val_sub]

/-- **Closure under `−`.** -/
theorem InUniverse_sub (f g : Nat → Q) (hf : InUniverse f) (hg : InUniverse g) :
    InUniverse (fun n ↦ Q.sub (f n) (g n)) := by
  rcases hf with ⟨sys₁, hwf₁, v₁, hv₁, hf_val⟩
  rcases hg with ⟨sys₂, hwf₂, v₂, hv₂, hg_val⟩
  let S := subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂
  have hwfS := uSub_subSys_wf sys₁ sys₂ hwf₁ hwf₂ v₁ v₂ hv₁ hv₂
  have hvS : sys₁.length + sys₂.length < S.length := by
    rw [uSub_subSys_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hwfS, sys₁.length + sys₂.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (uSubTargetState sys₁ sys₂ v₁ v₂)
    (uSubTargetState_fixed sys₁ sys₂ hwf₁ hwf₂ v₁ v₂ hv₁ hv₂)
    (n + 1) (sys₁.length + sys₂.length) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (Q.sub (f n) (g n)).val =
    ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
      (sys₁.length + sys₂.length) n).val
  rw [huniq]
  unfold uSubTargetState
  rw [if_neg (by omega), if_neg (by omega), Q.val_sub, Q.val_sub, hf_val n, hg_val n]

/-- Length of `integSys sys v`. -/
theorem uInteg_integSys_length (sys : List (Tm [] JetTy × JExprN)) (v : Nat) :
    (integSys sys v).length = sys.length + 1 := by
  simp [integSys]

/-- Well-formedness of `integSys sys v`. -/
theorem uInteg_integSys_wf (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    ∀ p ∈ integSys sys v, p.2.WF (integSys sys v).length := by
  rw [uInteg_integSys_length]
  intro p hp
  simp only [integSys, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp₁ | rfl
  · exact (hwf p hp₁).mono (by omega)
  · show v < sys.length + 1
    omega

/-- Target solution state for `integSys`: `solN sys` on `[0, sys.length)` and `tmJetInteg (solN sys v)` at `sys.length`. -/
def uIntegTargetState (sys : List (Tm [] JetTy × JExprN)) (v : Nat) : Nat → Nat → Q :=
  fun w n ↦
    if w < sys.length then solN sys w n
    else ((tmJetInteg (Γ := [])).eval Env.nil) (solN sys v) n

/-- Evaluating the integral equation `(tmZeroJet, .var v)` on `uIntegTargetState` yields the value of `tmJetInteg (solN sys v)`. -/
theorem uInteg_eqStepEval_last_val (sys : List (Tm [] JetTy × JExprN))
    (v : Nat) (hv : v < sys.length) (n : Nat) :
    (eqStepEval (tmZeroJet, .var v) (uIntegTargetState sys v) n).val =
      (((tmJetInteg (Γ := [])).eval Env.nil) (solN sys v) n).val := by
  unfold eqStepEval
  have hvar : ((JExprN.var v).toTm (.var .here)).eval
      (Env.cons (σ := WTy) (uIntegTargetState sys v) Env.nil) = solN sys v := by
    change uIntegTargetState sys v ((natTm v).eval
      (Env.cons (σ := WTy) (uIntegTargetState sys v) Env.nil)) = solN sys v
    rw [natTm_eval]
    funext m
    exact if_pos hv
  rw [hvar]
  change (Q.add (Q.ofNat 0) ((((tmJetInteg (Γ := [])).eval Env.nil) (solN sys v)) n)).val = _
  rw [Q.val_add, Q.val_ofNat]
  ring

/-- `uIntegTargetState` is a value-level fixed point of `genStepN (integSys sys v)`. -/
theorem uIntegTargetState_fixed (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    ∀ w < (integSys sys v).length, ∀ n,
      ((((genStepN (integSys sys v) (Γ := [])).eval Env.nil)
        (uIntegTargetState sys v)) w n).val =
        (uIntegTargetState sys v w n).val := by
  intro w hw n
  rw [genStepN_eval_getElem _ _ w hw]
  have hw_len : w < sys.length + 1 := by rwa [uInteg_integSys_length] at hw
  have hZ : ∀ u < sys.length, uIntegTargetState sys v u = solN sys u := by
    intro u hu; funext m; exact if_pos hu
  by_cases hw₁ : w < sys.length
  · have hget : (integSys sys v)[w] = sys[w] := by
      simp only [integSys]
      exact List.getElem_append_left hw₁
    rw [hget, eqStepEval_of_eq_below sys[w] sys.length (hwf sys[w] (List.getElem_mem hw₁)) _ _ hZ,
        ← genStepN_eval_getElem sys (solN sys) w hw₁]
    unfold uIntegTargetState
    rw [if_pos hw₁]
    exact solN_fixed sys hwf w hw₁ n
  · have hw_eq : w = sys.length := by omega
    have hget : (integSys sys v)[w] = (tmZeroJet, .var v) := by
      simp only [integSys]
      rw [List.getElem_append_right (Nat.not_lt.mp hw₁)]
      simp [hw_eq]
    rw [hget, uInteg_eqStepEval_last_val sys v hv n]
    unfold uIntegTargetState
    rw [if_neg hw₁]

/-- **Closure under `∫`.** -/
theorem InUniverse_integ (f : Nat → Q) (hf : InUniverse f) :
    InUniverse (((tmJetInteg (Γ := [])).eval Env.nil) f) := by
  rcases hf with ⟨sys, hwf, v, hv, hf_val⟩
  let S := integSys sys v
  have hwfS := uInteg_integSys_wf sys hwf v hv
  have hvS : sys.length < S.length := by
    rw [uInteg_integSys_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hwfS, sys.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (uIntegTargetState sys v)
    (uIntegTargetState_fixed sys hwf v hv)
    (n + 1) sys.length n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  have hInt := tmJetInteg_agreeV_succ Env.nil Env.nil n f (solN sys v)
    (fun i _ ↦ hf_val i) n (Nat.lt_succ_self n)
  change ((((tmJetInteg (Γ := [])).eval Env.nil) f) n).val =
    ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
      sys.length n).val
  rw [huniq]
  unfold uIntegTargetState
  rw [if_neg (Nat.lt_irrefl _)]
  exact hInt

/-- For `u < xs.length`, `xs.getD u d = xs[u]`. -/
theorem uDeriv_getD_eq_getElem {α : Type} (xs : List α) (d : α) (u : Nat) (hu : u < xs.length) :
    xs.getD u d = xs[u] := by
  induction xs generalizing u with
  | nil => exact absurd hu (Nat.not_lt_zero u)
  | cons hd tl ih =>
    cases u with
    | zero => rfl
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ hu)

/-- Symbolic differentiation `JExprN.derivSym sys` preserves `.WF sys.length` when `sys` is well-formed. -/
theorem uDeriv_derivSym_wf (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (F : JExprN) (hF : F.WF sys.length) :
    (F.derivSym sys).WF sys.length := by
  induction F with
  | var u =>
    dsimp only [JExprN.derivSym]
    rw [uDeriv_getD_eq_getElem sys _ u hF]
    exact ⟨trivial, hwf sys[u] (List.getElem_mem hF)⟩
  | const _ => trivial
  | add _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | mul _ _ iha ihb => exact ⟨⟨iha hF.1, hF.2⟩, ⟨hF.1, ihb hF.2⟩⟩
  | integ _ _ => exact hF

/-- Length of `derivSys sys v hv`. -/
theorem uDeriv_derivSys_length (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    (derivSys sys v hv).length = sys.length + 1 := by
  simp [derivSys]

/-- Well-formedness of `derivSys sys v hv`. -/
theorem uDeriv_derivSys_wf (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    ∀ p ∈ derivSys sys v hv, p.2.WF (derivSys sys v hv).length := by
  rw [uDeriv_derivSys_length]
  intro p hp
  simp only [derivSys, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp₁ | rfl
  · exact (hwf p hp₁).mono (by omega)
  · refine ⟨⟨trivial, ?_⟩, trivial⟩
    exact (uDeriv_derivSym_wf sys hwf sys[v].2 (hwf sys[v] (List.getElem_mem hv))).mono (by omega)

/-- Evaluating `(F.derivSym sys).toTm` on `solN sys` has the same rational values as differentiating `F.toTm` on `solN sys`. -/
theorem uDeriv_derivSym_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (F : JExprN) (hF : F.WF sys.length) (n : Nat) :
    ((((F.derivSym sys).toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sys) Env.nil)) n).val =
      (((tmJetDeriv (Γ := [])).eval Env.nil)
        (((F.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sys) Env.nil))) n).val := by
  let eS : Env [WTy] := Env.cons (σ := WTy) (solN sys) Env.nil
  induction F generalizing n with
  | var u =>
    dsimp only [JExprN.derivSym]
    rw [uDeriv_getD_eq_getElem sys _ u hF]
    change (Q.add ((Tm.closedWk (.app tmJetDeriv sys[u].1)).eval eS n)
      (((sys[u].2.toTm (.var .here)).eval eS) n)).val =
      (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys ((natTm u).eval eS)) n).val
    rw [closedWk_eval (.app tmJetDeriv sys[u].1) eS, natTm_eval, Q.val_add,
        uMul_solN_deriv_val sys hwf u hF n]
    rfl
  | const c =>
    dsimp only [JExprN.derivSym, JExprN.toTm]
    rw [closedWk_eval (.app tmJetDeriv c) eS, closedWk_eval c eS]
    rfl
  | add a b iha ihb =>
    change (Q.add ((((a.derivSym sys).toTm (.var .here)).eval eS) n)
                  ((((b.derivSym sys).toTm (.var .here)).eval eS) n)).val =
      (Q.mul (Q.ofNat (n + 1))
        (Q.add (((a.toTm (.var .here)).eval eS) (n + 1))
               (((b.toTm (.var .here)).eval eS) (n + 1)))).val
    rw [Q.val_add, iha hF.1 n, ihb hF.2 n]
    change (Q.mul (Q.ofNat (n + 1)) (((a.toTm (.var .here)).eval eS) (n + 1))).val +
        (Q.mul (Q.ofNat (n + 1)) (((b.toTm (.var .here)).eval eS) (n + 1))).val = _
    rw [Q.val_mul, Q.val_mul, Q.val_mul, Q.val_add, Q.val_ofNat]
    ring
  | sub a b iha ihb =>
    change (Q.sub ((((a.derivSym sys).toTm (.var .here)).eval eS) n)
                  ((((b.derivSym sys).toTm (.var .here)).eval eS) n)).val =
      (Q.mul (Q.ofNat (n + 1))
        (Q.sub (((a.toTm (.var .here)).eval eS) (n + 1))
               (((b.toTm (.var .here)).eval eS) (n + 1)))).val
    rw [Q.val_sub, iha hF.1 n, ihb hF.2 n]
    change (Q.mul (Q.ofNat (n + 1)) (((a.toTm (.var .here)).eval eS) (n + 1))).val -
        (Q.mul (Q.ofNat (n + 1)) (((b.toTm (.var .here)).eval eS) (n + 1))).val = _
    rw [Q.val_mul, Q.val_mul, Q.val_mul, Q.val_sub, Q.val_ofNat]
    ring
  | mul a b iha ihb =>
    let ea := (a.toTm (.var .here)).eval eS
    let eb := (b.toTm (.var .here)).eval eS
    have hm₁ : ((((JExprN.mul (a.derivSym sys) b).toTm (.var .here)).eval eS) n).val =
        (((tmJetMul (Γ := [])).eval Env.nil)
          (((tmJetDeriv (Γ := [])).eval Env.nil) ea) eb n).val :=
      tmJetMul_agreeV Env.nil Env.nil (n + 1)
        (((a.derivSym sys).toTm (.var .here)).eval eS) (((tmJetDeriv (Γ := [])).eval Env.nil) ea)
        eb eb (fun m _ ↦ iha hF.1 m) (fun _ _ ↦ rfl) n (Nat.lt_succ_self n)
    have hm₂ : ((((JExprN.mul a (b.derivSym sys)).toTm (.var .here)).eval eS) n).val =
        (((tmJetMul (Γ := [])).eval Env.nil)
          ea (((tmJetDeriv (Γ := [])).eval Env.nil) eb) n).val :=
      tmJetMul_agreeV Env.nil Env.nil (n + 1)
        ea ea (((b.derivSym sys).toTm (.var .here)).eval eS) (((tmJetDeriv (Γ := [])).eval Env.nil) eb)
        (fun _ _ ↦ rfl) (fun m _ ↦ ihb hF.2 m) n (Nat.lt_succ_self n)
    change (Q.add ((((JExprN.mul (a.derivSym sys) b).toTm (.var .here)).eval eS) n)
                  ((((JExprN.mul a (b.derivSym sys)).toTm (.var .here)).eval eS) n)).val =
      (((tmJetDeriv (Γ := [])).eval Env.nil) (((tmJetMul (Γ := [])).eval Env.nil) ea eb) n).val
    rw [Q.val_add, hm₁, hm₂, ← jetMul_leibniz_val]
  | integ a _ =>
    dsimp only [JExprN.derivSym, JExprN.toTm, Tm.eval]
    exact ((Jet.mk ((a.toTm (.var .here)).eval eS)).deriv_integ_val n).symm

/-- Evaluating `selectInit tail tv` at index `v < tail.length` yields `tail[v].1.eval Env.nil`. -/
theorem uDeriv_selectInit_eval_getElem (tail : List (Tm [] JetTy × JExprN))
    {Γ : List Ty} (e : Env Γ) (tv : Tm Γ .nat) (v : Nat) (hv : v < tail.length)
    (htv : tv.eval e = v) :
    (selectInit tail tv).eval e = tail[v].1.eval Env.nil := by
  induction tail generalizing Γ v with
  | nil => exact absurd hv (Nat.not_lt_zero v)
  | cons hd rest ih =>
    rcases hd with ⟨A, B⟩
    let z := (Tm.closedWk A).eval e
    let s : Nat → (Nat → Q) → (Nat → Q) := fun u acc ↦
      (selectInit rest (.var (.there .here))).eval
        (Env.cons (σ := JetTy) acc (Env.cons (σ := .nat) u e))
    change Nat.rec (motive := fun _ ↦ Nat → Q) z s (tv.eval e) = ((A, B) :: rest)[v].1.eval Env.nil
    rw [htv]
    cases v with
    | zero => exact closedWk_eval A e
    | succ u =>
      let acc := Nat.rec (motive := fun _ ↦ Nat → Q) z s u
      let e' : Env (JetTy :: .nat :: Γ) := Env.cons (σ := JetTy) acc (Env.cons (σ := .nat) u e)
      exact ih e' (.var (.there .here)) u (Nat.lt_of_succ_lt_succ hv) rfl

/-- Evaluating `initN sys` at variable `v < sys.length` yields `sys[v].1.eval Env.nil`. -/
theorem uDeriv_initN_eval_getElem (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    ((initN sys (Γ := [])).eval Env.nil) v = sys[v].1.eval Env.nil :=
  uDeriv_selectInit_eval_getElem sys (Env.cons (σ := .nat) v Env.nil) (.var .here) v hv rfl

/-- At degree `0`, `F.toTm (initN sys)` and `F.toTm` on `solN sys` have the same rational value. -/
theorem uDeriv_toTm_initN_zero_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (F : JExprN) (hF : F.WF sys.length) :
    (((F.toTm (initN sys (Γ := []))).eval Env.nil) 0).val =
      (((F.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sys) Env.nil)) 0).val := by
  let e₁ : Env [WTy] := Env.cons (σ := WTy) ((initN sys (Γ := [])).eval Env.nil) Env.nil
  let e₂ : Env [WTy] := Env.cons (σ := WTy) (solN sys) Env.nil
  rw [F.toTm_eval_eq Env.nil e₁ (initN sys) (.var .here) rfl]
  refine F.toTm_agreeV sys.length hF e₁ e₂ (.var .here) (.var .here) 1 (fun u hu i hi ↦ ?_) 0 (Nat.succ_pos 0)
  have hi0 : i = 0 := by omega
  subst hi0
  change ((((initN sys (Γ := [])).eval Env.nil) u) 0).val = (solN sys u 0).val
  rw [uDeriv_initN_eval_getElem sys u hu, uMul_solN_zero_val sys hwf u hu]

/-- Target solution state for `derivSys`: `solN sys` on `[0, sys.length)` and `tmJetDeriv (solN sys v)` at `sys.length`. -/
def uDerivTargetState (sys : List (Tm [] JetTy × JExprN)) (v : Nat) : Nat → Nat → Q :=
  fun w n ↦
    if w < sys.length then solN sys w n
    else ((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys v) n

/-- Evaluating the derivative equation of `derivSys` on `uDerivTargetState` yields the value of `tmJetDeriv (solN sys v)`. -/
theorem uDeriv_eqStepEval_last_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) (n : Nat) :
    let A := sys[v].1
    let F := sys[v].2
    let Ah : Tm [] JetTy := .app (.app tmJetAdd (.app tmJetDeriv A)) (F.toTm (initN sys))
    let F_last : JExprN :=
      .sub (.add (.const (.app tmJetDeriv (.app tmJetDeriv A))) (F.derivSym sys))
        (.const (.app tmJetDeriv Ah))
    (eqStepEval (Ah, F_last) (uDerivTargetState sys v) n).val =
      (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys v) n).val := by
  intro A F Ah F_last
  let Z := uDerivTargetState sys v
  let eZ : Env [WTy] := Env.cons (σ := WTy) Z Env.nil
  let eS : Env [WTy] := Env.cons (σ := WTy) (solN sys) Env.nil
  have hF : F.WF sys.length := hwf sys[v] (List.getElem_mem hv)
  have hZ : ∀ u < sys.length, Z u = solN sys u := by
    intro u hu; funext m; exact if_pos hu
  cases n with
  | zero =>
    unfold eqStepEval
    change (Q.add (Ah.eval Env.nil 0) (Q.ofNat 0)).val =
      (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys v) 0).val
    have h0 : (Q.add (Ah.eval Env.nil 0) (Q.ofNat 0)).val = (Ah.eval Env.nil 0).val := by
      rw [Q.val_add, Q.val_ofNat]; ring
    rw [h0]
    change (Q.add (((tmJetDeriv (Γ := [])).eval Env.nil) (A.eval Env.nil) 0)
                  (((F.toTm (initN sys)).eval Env.nil) 0)).val = _
    rw [Q.val_add, uDeriv_toTm_initN_zero_val sys hwf F hF, uMul_solN_deriv_val sys hwf v hv 0]
  | succ j =>
    have hDF_eq : ((F.derivSym sys).toTm (.var .here)).eval eZ =
        ((F.derivSym sys).toTm (.var .here)).eval eS :=
      (F.derivSym sys).toTm_eval_of_eq_below sys.length
        (uDeriv_derivSym_wf sys hwf F hF) eZ eS (.var .here) (.var .here) hZ
    have hFlast : (((F_last.toTm (.var .here)).eval eZ) j).val =
        ((j + 1 : Nat) : Rat) * (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys v) (j + 1)).val -
        ((j + 1 : Nat) : Rat) * (Ah.eval Env.nil (j + 1)).val := by
      change (Q.sub
        (Q.add ((Tm.closedWk (.app tmJetDeriv (.app tmJetDeriv A))).eval eZ j)
               ((((F.derivSym sys).toTm (.var .here)).eval eZ) j))
        ((Tm.closedWk (.app tmJetDeriv Ah)).eval eZ j)).val = _
      rw [closedWk_eval (.app tmJetDeriv (.app tmJetDeriv A)) eZ,
          closedWk_eval (.app tmJetDeriv Ah) eZ,
          hDF_eq, Q.val_sub, Q.val_add, uDeriv_derivSym_val sys hwf F hF j]
      change (Q.mul (Q.ofNat (j + 1)) (((tmJetDeriv (Γ := [])).eval Env.nil) (A.eval Env.nil) (j + 1))).val +
          (Q.mul (Q.ofNat (j + 1)) (((F.toTm (.var .here)).eval eS) (j + 1))).val -
          (Q.mul (Q.ofNat (j + 1)) (Ah.eval Env.nil (j + 1))).val = _
      rw [Q.val_mul, Q.val_mul, Q.val_mul, Q.val_ofNat, uMul_solN_deriv_val sys hwf v hv (j + 1)]
      ring
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    have hne_rat : ((j + 1 : Nat) : Rat) ≠ 0 := by positivity
    unfold eqStepEval
    change (Q.add (Ah.eval Env.nil (j + 1))
      (Q.div (((F_last.toTm (.var .here)).eval eZ) j) (Q.ofNat (j + 1)))).val = _
    rw [Q.val_add, Q.val_div _ _ hne, Q.val_ofNat, hFlast]
    field_simp
    ring

/-- `uDerivTargetState` is a value-level fixed point of `genStepN (derivSys sys v hv)`. -/
theorem uDerivTargetState_fixed (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    ∀ w < (derivSys sys v hv).length, ∀ n,
      ((((genStepN (derivSys sys v hv) (Γ := [])).eval Env.nil)
        (uDerivTargetState sys v)) w n).val =
        (uDerivTargetState sys v w n).val := by
  intro w hw n
  rw [genStepN_eval_getElem _ _ w hw]
  have hw_len : w < sys.length + 1 := by rwa [uDeriv_derivSys_length] at hw
  have hZ : ∀ u < sys.length, uDerivTargetState sys v u = solN sys u := by
    intro u hu; funext m; exact if_pos hu
  by_cases hw₁ : w < sys.length
  · have hget : (derivSys sys v hv)[w] = sys[w] := by
      simp only [derivSys]
      exact List.getElem_append_left hw₁
    rw [hget, eqStepEval_of_eq_below sys[w] sys.length (hwf sys[w] (List.getElem_mem hw₁)) _ _ hZ,
        ← genStepN_eval_getElem sys (solN sys) w hw₁]
    unfold uDerivTargetState
    rw [if_pos hw₁]
    exact solN_fixed sys hwf w hw₁ n
  · have hw_eq : w = sys.length := by omega
    have hget : (derivSys sys v hv)[w] =
        (let A := sys[v].1
         let F := sys[v].2
         let Ah : Tm [] JetTy := .app (.app tmJetAdd (.app tmJetDeriv A)) (F.toTm (initN sys))
         (Ah,
          .sub (.add (.const (.app tmJetDeriv (.app tmJetDeriv A))) (F.derivSym sys))
            (.const (.app tmJetDeriv Ah)))) := by
      simp only [derivSys]
      rw [List.getElem_append_right (Nat.not_lt.mp hw₁)]
      simp [hw_eq]
    rw [hget, uDeriv_eqStepEval_last_val sys hwf v hv n]
    unfold uDerivTargetState
    rw [if_neg hw₁]

/-- **Closure under `d/dx`.** -/
theorem InUniverse_deriv (f : Nat → Q) (hf : InUniverse f) :
    InUniverse (((tmJetDeriv (Γ := [])).eval Env.nil) f) := by
  rcases hf with ⟨sys, hwf, v, hv, hf_val⟩
  let S := derivSys sys v hv
  have hwfS := uDeriv_derivSys_wf sys hwf v hv
  have hvS : sys.length < S.length := by
    rw [uDeriv_derivSys_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hwfS, sys.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (uDerivTargetState sys v)
    (uDerivTargetState_fixed sys hwf v hv)
    (n + 1) sys.length n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  have hD : ((((tmJetDeriv (Γ := [])).eval Env.nil) f) n).val =
      ((((tmJetDeriv (Γ := [])).eval Env.nil) (solN sys v)) n).val := by
    change (Q.mul (Q.ofNat (n + 1)) (f (n + 1))).val =
      (Q.mul (Q.ofNat (n + 1)) (solN sys v (n + 1))).val
    rw [Q.val_mul, Q.val_mul, hf_val (n + 1)]
  change ((((tmJetDeriv (Γ := [])).eval Env.nil) f) n).val =
    ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
      sys.length n).val
  rw [huniq]
  unfold uDerivTargetState
  rw [if_neg (Nat.lt_irrefl _)]
  exact hD

#print axioms InUniverse_sub
#print axioms InUniverse_integ
#print axioms InUniverse_deriv

end HAomega
