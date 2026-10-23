/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseOps

/-!
# The GPAC universe: polynomial ODE systems with constant data

`InUniverse` lets the initial jets `A_v` and the constant leaves `.const c` of a
system be *arbitrary* closed System T jets, so the system `[(A, const 0)]` puts
every System T–definable jet into it: that class is closed for trivial reasons.
The intended universe (QUESTIONS.md item 19) is the polynomial-ODE class, whose
data are constants: `InGPAC` requires every initial jet and every constant leaf
to be a constant series (coefficients `≥ 1` have value `0`).

The closure constructions of `UniverseTrial`, `UniverseMul` and `UniverseOps`
already have constant data, except `derivSys`, whose initial jet
`D A + F(initN)` is not constant. `derivSysC` truncates it to its constant
term (`tmTrunc0`), which is all the equation reads of it.

Value-level metatheory theorems (`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- A closed jet whose coefficients of degree `≥ 1` have value `0`. -/
def IsConstJet (c : Tm [] JetTy) : Prop := ∀ n, ((c.eval Env.nil) (n + 1)).val = 0

/-- Every constant leaf of `F` is a constant jet. -/
def JExprN.ConstsConst : JExprN → Prop
  | .var _ => True
  | .const c => IsConstJet c
  | .add a b => a.ConstsConst ∧ b.ConstsConst
  | .sub a b => a.ConstsConst ∧ b.ConstsConst
  | .mul a b => a.ConstsConst ∧ b.ConstsConst
  | .integ a => a.ConstsConst

/-- A well-formed system with constant data. -/
def GPACSys (sys : List (Tm [] JetTy × JExprN)) : Prop :=
  ∀ p ∈ sys, p.2.WF sys.length ∧ IsConstJet p.1 ∧ p.2.ConstsConst

/-- **The universe**: `f` is, as values, a component of the solution of a
    polynomial ODE system with constant data. -/
def InGPAC (f : Nat → Q) : Prop :=
  ∃ (sys : List (Tm [] JetTy × JExprN)) (_ : GPACSys sys) (v : Nat),
    v < sys.length ∧ ∀ n, (f n).val = (solN sys v n).val

/-- The constant term of a jet: `λ c n. rec[c 0 | λ _ _. 0 | n]`. -/
def tmTrunc0 {Γ : List Ty} : Tm Γ (.arrow JetTy JetTy) :=
  .lam (.lam (.recNat (.app (.var (.there .here)) .zero) (.lam (.lam (.qnat .zero))) (.var .here)))

/-- The system for `f'` with a constant initial jet. -/
def derivSysC (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    List (Tm [] JetTy × JExprN) :=
  let A := sys[v].1
  let F := sys[v].2
  let Ah : Tm [] JetTy :=
    .app tmTrunc0 (.app (.app tmJetAdd (.app tmJetDeriv A)) (F.toTm (initN sys)))
  sys ++ [(Ah,
    .sub (.add (.const (.app tmJetDeriv (.app tmJetDeriv A))) (F.derivSym sys))
      (.const (.app tmJetDeriv Ah)))]

/-- Every member of the GPAC universe is in `InUniverse`. -/
theorem InGPAC.inUniverse {f : Nat → Q} (hf : InGPAC f) : InUniverse f := by
  rcases hf with ⟨sys, hgpac, v, hv, hf_val⟩
  exact ⟨sys, fun p hp ↦ (hgpac p hp).1, v, hv, hf_val⟩

/-- Extract well-formedness from `GPACSys`. -/
theorem gpac_wf {sys : List (Tm [] JetTy × JExprN)} (h : GPACSys sys) :
    ∀ p ∈ sys, p.2.WF sys.length :=
  fun p hp ↦ (h p hp).1

/-- `tmZeroJet` is a constant jet. -/
theorem gpac_isConstJet_zero : IsConstJet tmZeroJet := by
  intro n
  exact Q.val_ofNat 0

/-- `tmJetAdd` preserves `IsConstJet`. -/
theorem gpac_isConstJet_add {a b : Tm [] JetTy} (ha : IsConstJet a) (hb : IsConstJet b) :
    IsConstJet (.app (.app tmJetAdd a) b) := by
  intro n
  change (Q.add (a.eval Env.nil (n + 1)) (b.eval Env.nil (n + 1))).val = 0
  rw [Q.val_add, ha n, hb n, add_zero]

/-- `tmJetSub` preserves `IsConstJet`. -/
theorem gpac_isConstJet_sub {a b : Tm [] JetTy} (ha : IsConstJet a) (hb : IsConstJet b) :
    IsConstJet (.app (.app tmJetSub a) b) := by
  intro n
  change (Q.sub (a.eval Env.nil (n + 1)) (b.eval Env.nil (n + 1))).val = 0
  rw [Q.val_sub, ha n, hb n, sub_zero]

/-- `tmJetMul` preserves `IsConstJet`. -/
theorem gpac_isConstJet_mul {a b : Tm [] JetTy} (ha : IsConstJet a) (hb : IsConstJet b) :
    IsConstJet (.app (.app tmJetMul a) b) := by
  intro n
  change (((tmJetMul (Γ := [])).eval Env.nil) (a.eval Env.nil) (b.eval Env.nil) (n + 1)).val = 0
  rw [tmJetMul_eval]
  simp only [Jet.mul, TrigPoly.cauchyConvAux_val]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  cases j with
  | zero =>
    rw [Nat.sub_zero, hb n, mul_zero]
  | succ k =>
    rw [ha k, zero_mul]

/-- If `IsConstJet c`, then `tmJetDeriv c` has rational value `0` at every degree `n`. -/
theorem gpac_deriv_const_val {c : Tm [] JetTy} (hc : IsConstJet c) (n : Nat) :
    (((tmJetDeriv (Γ := [])).eval Env.nil) (c.eval Env.nil) n).val = 0 := by
  change (Q.mul (Q.ofNat (n + 1)) (c.eval Env.nil (n + 1))).val = 0
  rw [Q.val_mul, hc n, mul_zero]

/-- `tmJetDeriv c` is a constant jet whenever `c` is a constant jet. -/
theorem gpac_isConstJet_deriv {c : Tm [] JetTy} (hc : IsConstJet c) :
    IsConstJet (.app tmJetDeriv c) :=
  fun n ↦ gpac_deriv_const_val hc (n + 1)

/-- `tmTrunc0 c` is a constant jet for every `c`. -/
theorem gpac_isConstJet_trunc0 (c : Tm [] JetTy) :
    IsConstJet (.app tmTrunc0 c) := by
  intro n
  exact Q.val_ofNat 0

/-- `JExprN.shiftVars` preserves `JExprN.ConstsConst`. -/
theorem gpac_shiftVars_constsConst (F : JExprN) (offset : Nat) (hF : F.ConstsConst) :
    (F.shiftVars offset).ConstsConst := by
  induction F with
  | var _ => trivial
  | const _ => exact hF
  | add _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | mul _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | integ _ iha => exact iha hF

/-- `JExprN.derivSym sys` preserves `JExprN.ConstsConst` when `GPACSys sys` and `F.WF sys.length`. -/
theorem gpac_derivSym_constsConst (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (F : JExprN) (hF_wf : F.WF sys.length) (hF_cc : F.ConstsConst) :
    (F.derivSym sys).ConstsConst := by
  induction F with
  | var u =>
    dsimp only [JExprN.derivSym]
    rw [uDeriv_getD_eq_getElem sys _ u hF_wf]
    have hp := hgpac sys[u] (List.getElem_mem hF_wf)
    exact ⟨gpac_isConstJet_deriv hp.2.1, hp.2.2⟩
  | const _ => exact gpac_isConstJet_deriv hF_cc
  | add _ _ iha ihb => exact ⟨iha hF_wf.1 hF_cc.1, ihb hF_wf.2 hF_cc.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF_wf.1 hF_cc.1, ihb hF_wf.2 hF_cc.2⟩
  | mul _ _ iha ihb =>
    exact ⟨⟨iha hF_wf.1 hF_cc.1, hF_cc.2⟩, ⟨hF_cc.1, ihb hF_wf.2 hF_cc.2⟩⟩
  | integ _ _ => exact hF_cc

/-- `sumSys` preserves `GPACSys`. -/
theorem gpac_sumSys (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (h₁ : GPACSys sys₁) (h₂ : GPACSys sys₂)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    GPACSys (sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂) := by
  intro p hp
  refine ⟨sumSys_wf sys₁ sys₂ (gpac_wf h₁) (gpac_wf h₂) v₁ v₂ hv₁ hv₂ p hp, ?_⟩
  simp only [sumSys, List.mem_append, List.mem_map, List.mem_singleton] at hp
  rcases hp with (hp₁ | ⟨q, hq, rfl⟩) | rfl
  · exact (h₁ p hp₁).2
  · exact ⟨(h₂ q hq).2.1, gpac_shiftVars_constsConst q.2 sys₁.length (h₂ q hq).2.2⟩
  · have hpv₁ := h₁ sys₁[v₁] (List.getElem_mem hv₁)
    have hpv₂ := h₂ sys₂[v₂] (List.getElem_mem hv₂)
    exact ⟨gpac_isConstJet_add hpv₁.2.1 hpv₂.2.1,
           hpv₁.2.2, gpac_shiftVars_constsConst sys₂[v₂].2 sys₁.length hpv₂.2.2⟩

theorem InGPAC_add (f g : Nat → Q) (hf : InGPAC f) (hg : InGPAC g) :
    InGPAC (fun n ↦ Q.add (f n) (g n)) := by
  rcases hf with ⟨sys₁, h₁, v₁, hv₁, hf_val⟩
  rcases hg with ⟨sys₂, h₂, v₂, hv₂, hg_val⟩
  let S := sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂
  have hgpacS := gpac_sumSys sys₁ sys₂ h₁ h₂ v₁ v₂ hv₁ hv₂
  have hwfS := gpac_wf hgpacS
  have hvS : sys₁.length + sys₂.length < S.length := by
    rw [sumSys_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hgpacS, sys₁.length + sys₂.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (sumTargetState sys₁ sys₂ v₁ v₂)
    (sumTargetState_fixed sys₁ sys₂ (gpac_wf h₁) (gpac_wf h₂) v₁ v₂ hv₁ hv₂)
    (n + 1) (sys₁.length + sys₂.length) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (Q.add (f n) (g n)).val =
    ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
      (sys₁.length + sys₂.length) n).val
  rw [huniq]
  unfold sumTargetState
  rw [if_neg (by omega), if_neg (by omega), Q.val_add, Q.val_add, hf_val n, hg_val n]

/-- `subSys` preserves `GPACSys`. -/
theorem gpac_subSys (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (h₁ : GPACSys sys₁) (h₂ : GPACSys sys₂)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    GPACSys (subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂) := by
  intro p hp
  refine ⟨uSub_subSys_wf sys₁ sys₂ (gpac_wf h₁) (gpac_wf h₂) v₁ v₂ hv₁ hv₂ p hp, ?_⟩
  simp only [subSys, List.mem_append, List.mem_map, List.mem_singleton] at hp
  rcases hp with (hp₁ | ⟨q, hq, rfl⟩) | rfl
  · exact (h₁ p hp₁).2
  · exact ⟨(h₂ q hq).2.1, gpac_shiftVars_constsConst q.2 sys₁.length (h₂ q hq).2.2⟩
  · have hpv₁ := h₁ sys₁[v₁] (List.getElem_mem hv₁)
    have hpv₂ := h₂ sys₂[v₂] (List.getElem_mem hv₂)
    exact ⟨gpac_isConstJet_sub hpv₁.2.1 hpv₂.2.1,
           hpv₁.2.2, gpac_shiftVars_constsConst sys₂[v₂].2 sys₁.length hpv₂.2.2⟩

theorem InGPAC_sub (f g : Nat → Q) (hf : InGPAC f) (hg : InGPAC g) :
    InGPAC (fun n ↦ Q.sub (f n) (g n)) := by
  rcases hf with ⟨sys₁, h₁, v₁, hv₁, hf_val⟩
  rcases hg with ⟨sys₂, h₂, v₂, hv₂, hg_val⟩
  let S := subSys sys₁ sys₂ v₁ v₂ hv₁ hv₂
  have hgpacS := gpac_subSys sys₁ sys₂ h₁ h₂ v₁ v₂ hv₁ hv₂
  have hwfS := gpac_wf hgpacS
  have hvS : sys₁.length + sys₂.length < S.length := by
    rw [uSub_subSys_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hgpacS, sys₁.length + sys₂.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (uSubTargetState sys₁ sys₂ v₁ v₂)
    (uSubTargetState_fixed sys₁ sys₂ (gpac_wf h₁) (gpac_wf h₂) v₁ v₂ hv₁ hv₂)
    (n + 1) (sys₁.length + sys₂.length) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (Q.sub (f n) (g n)).val =
    ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
      (sys₁.length + sys₂.length) n).val
  rw [huniq]
  unfold uSubTargetState
  rw [if_neg (by omega), if_neg (by omega), Q.val_sub, Q.val_sub, hf_val n, hg_val n]

/-- `mulSys` preserves `GPACSys`. -/
theorem gpac_mulSys (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (h₁ : GPACSys sys₁) (h₂ : GPACSys sys₂)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    GPACSys (mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂) := by
  intro p hp
  refine ⟨mulSys_wf sys₁ sys₂ (gpac_wf h₁) (gpac_wf h₂) v₁ v₂ hv₁ hv₂ p hp, ?_⟩
  simp only [mulSys, List.mem_append, List.mem_map, List.mem_singleton] at hp
  rcases hp with (hp₁ | ⟨q, hq, rfl⟩) | rfl
  · exact (h₁ p hp₁).2
  · exact ⟨(h₂ q hq).2.1, gpac_shiftVars_constsConst q.2 sys₁.length (h₂ q hq).2.2⟩
  · have hpv₁ := h₁ sys₁[v₁] (List.getElem_mem hv₁)
    have hpv₂ := h₂ sys₂[v₂] (List.getElem_mem hv₂)
    have hA₁₂ : IsConstJet (.app (.app tmJetMul sys₁[v₁].1) sys₂[v₂].1) :=
      gpac_isConstJet_mul hpv₁.2.1 hpv₂.2.1
    refine ⟨hA₁₂, ⟨⟨⟨gpac_isConstJet_deriv hpv₁.2.1, hpv₁.2.2⟩, trivial⟩,
      ⟨trivial, gpac_isConstJet_deriv hpv₂.2.1,
        gpac_shiftVars_constsConst sys₂[v₂].2 sys₁.length hpv₂.2.2⟩⟩,
      gpac_isConstJet_deriv hA₁₂⟩

theorem InGPAC_mul (f g : Nat → Q) (hf : InGPAC f) (hg : InGPAC g) :
    InGPAC (((tmJetMul (Γ := [])).eval Env.nil) f g) := by
  rcases hf with ⟨sys₁, h₁, v₁, hv₁, hf_val⟩
  rcases hg with ⟨sys₂, h₂, v₂, hv₂, hg_val⟩
  let S := mulSys sys₁ sys₂ v₁ v₂ hv₁ hv₂
  have hgpacS := gpac_mulSys sys₁ sys₂ h₁ h₂ v₁ v₂ hv₁ hv₂
  have hwfS := gpac_wf hgpacS
  have hvS : sys₁.length + sys₂.length < S.length := by
    rw [mulSys_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hgpacS, sys₁.length + sys₂.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (uMulTargetState sys₁ sys₂ v₁ v₂)
    (uMulTargetState_fixed sys₁ sys₂ (gpac_wf h₁) (gpac_wf h₂) v₁ v₂ hv₁ hv₂)
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

/-- `integSys` preserves `GPACSys`. -/
theorem gpac_integSys (sys : List (Tm [] JetTy × JExprN))
    (h : GPACSys sys) (v : Nat) (hv : v < sys.length) :
    GPACSys (integSys sys v) := by
  intro p hp
  refine ⟨uInteg_integSys_wf sys (gpac_wf h) v hv p hp, ?_⟩
  simp only [integSys, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp₁ | rfl
  · exact (h p hp₁).2
  · exact ⟨gpac_isConstJet_zero, trivial⟩

theorem InGPAC_integ (f : Nat → Q) (hf : InGPAC f) :
    InGPAC (((tmJetInteg (Γ := [])).eval Env.nil) f) := by
  rcases hf with ⟨sys, h, v, hv, hf_val⟩
  let S := integSys sys v
  have hgpacS := gpac_integSys sys h v hv
  have hwfS := gpac_wf hgpacS
  have hvS : sys.length < S.length := by
    rw [uInteg_integSys_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hgpacS, sys.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (uIntegTargetState sys v)
    (uIntegTargetState_fixed sys (gpac_wf h) v hv)
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

/-- Length of `derivSysC sys v hv`. -/
theorem gpac_derivSysC_length (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    (derivSysC sys v hv).length = sys.length + 1 := by
  simp [derivSysC]

/-- Well-formedness of `derivSysC sys v hv`. -/
theorem gpac_derivSysC_wf (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    ∀ p ∈ derivSysC sys v hv, p.2.WF (derivSysC sys v hv).length := by
  rw [gpac_derivSysC_length]
  intro p hp
  simp only [derivSysC, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp₁ | rfl
  · exact (hwf p hp₁).mono (by omega)
  · refine ⟨⟨trivial, ?_⟩, trivial⟩
    exact (uDeriv_derivSym_wf sys hwf sys[v].2 (hwf sys[v] (List.getElem_mem hv))).mono (by omega)

/-- `derivSysC` preserves `GPACSys`. -/
theorem gpac_derivSysC (sys : List (Tm [] JetTy × JExprN))
    (h : GPACSys sys) (v : Nat) (hv : v < sys.length) :
    GPACSys (derivSysC sys v hv) := by
  intro p hp
  refine ⟨gpac_derivSysC_wf sys (gpac_wf h) v hv p hp, ?_⟩
  simp only [derivSysC, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp₁ | rfl
  · exact (h p hp₁).2
  · have hpv := h sys[v] (List.getElem_mem hv)
    have hAh : IsConstJet (.app tmTrunc0 (.app (.app tmJetAdd (.app tmJetDeriv sys[v].1))
        (sys[v].2.toTm (initN sys)))) :=
      gpac_isConstJet_trunc0 _
    refine ⟨hAh, ⟨gpac_isConstJet_deriv (gpac_isConstJet_deriv hpv.2.1),
      gpac_derivSym_constsConst sys h sys[v].2 hpv.1 hpv.2.2⟩,
      gpac_isConstJet_deriv hAh⟩

/-- Evaluating the derivative equation of `derivSysC` on `uDerivTargetState` yields the value of `tmJetDeriv (solN sys v)`. -/
theorem gpac_eqStepEval_derivSysC_last_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) (n : Nat) :
    let A := sys[v].1
    let F := sys[v].2
    let Ah : Tm [] JetTy :=
      .app tmTrunc0 (.app (.app tmJetAdd (.app tmJetDeriv A)) (F.toTm (initN sys)))
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

/-- `uDerivTargetState` is a value-level fixed point of `genStepN (derivSysC sys v hv)`. -/
theorem gpac_derivSysC_fixed (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) :
    ∀ w < (derivSysC sys v hv).length, ∀ n,
      ((((genStepN (derivSysC sys v hv) (Γ := [])).eval Env.nil)
        (uDerivTargetState sys v)) w n).val =
        (uDerivTargetState sys v w n).val := by
  intro w hw n
  rw [genStepN_eval_getElem _ _ w hw]
  have hw_len : w < sys.length + 1 := by rwa [gpac_derivSysC_length] at hw
  have hZ : ∀ u < sys.length, uDerivTargetState sys v u = solN sys u := by
    intro u hu; funext m; exact if_pos hu
  by_cases hw₁ : w < sys.length
  · have hget : (derivSysC sys v hv)[w] = sys[w] := by
      simp only [derivSysC]
      exact List.getElem_append_left hw₁
    rw [hget, eqStepEval_of_eq_below sys[w] sys.length (hwf sys[w] (List.getElem_mem hw₁)) _ _ hZ,
        ← genStepN_eval_getElem sys (solN sys) w hw₁]
    unfold uDerivTargetState
    rw [if_pos hw₁]
    exact solN_fixed sys hwf w hw₁ n
  · have hw_eq : w = sys.length := by omega
    have hget : (derivSysC sys v hv)[w] =
        (let A := sys[v].1
         let F := sys[v].2
         let Ah : Tm [] JetTy :=
           .app tmTrunc0 (.app (.app tmJetAdd (.app tmJetDeriv A)) (F.toTm (initN sys)))
         (Ah,
          .sub (.add (.const (.app tmJetDeriv (.app tmJetDeriv A))) (F.derivSym sys))
            (.const (.app tmJetDeriv Ah)))) := by
      simp only [derivSysC]
      rw [List.getElem_append_right (Nat.not_lt.mp hw₁)]
      simp [hw_eq]
    rw [hget, gpac_eqStepEval_derivSysC_last_val sys hwf v hv n]
    unfold uDerivTargetState
    rw [if_neg hw₁]

theorem InGPAC_deriv (f : Nat → Q) (hf : InGPAC f) :
    InGPAC (((tmJetDeriv (Γ := [])).eval Env.nil) f) := by
  rcases hf with ⟨sys, h, v, hv, hf_val⟩
  let S := derivSysC sys v hv
  have hgpacS := gpac_derivSysC sys h v hv
  have hwfS := gpac_wf hgpacS
  have hvS : sys.length < S.length := by
    rw [gpac_derivSysC_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hgpacS, sys.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (uDerivTargetState sys v)
    (gpac_derivSysC_fixed sys (gpac_wf h) v hv)
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

#print axioms InGPAC_add
#print axioms InGPAC_sub
#print axioms InGPAC_mul
#print axioms InGPAC_integ
#print axioms InGPAC_deriv

end HAomega
