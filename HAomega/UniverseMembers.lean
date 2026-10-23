/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseGPAC

/-!
# Members of the GPAC universe

Rational constants, the coordinate `x`, `exp`, `sin` and `cos` are in `InGPAC`,
each stated against its independent value-level jet (`Jet.const`, `Jet.varX`,
`Jet.exp`, `Jet.sin`, `Jet.cos` of `ClosedCalculus.lean`, which are defined by
their coefficient formulas, not by an ODE). With the closure theorems of
`UniverseGPAC.lean`, every expression built from these by `+ − × ∫ d/dx` is
in the universe and has a proof-computed solver.

Value-level metatheory theorems (`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- General constructor for `InGPAC` from a single-equation constant-data system `[(A, F)]`. -/
theorem mem_one_eq_inGPAC (A : Tm [] JetTy) (F : JExprN) (f : Nat → Q)
    (hA : IsConstJet A) (hF_wf : F.WF 1) (hF_cc : F.ConstsConst)
    (hfix : ∀ n, (eqStepEval (A, F) (fun _ ↦ f) n).val = (f n).val) :
    InGPAC f := by
  let S : List (Tm [] JetTy × JExprN) := [(A, F)]
  have hgpac : GPACSys S := by
    intro p hp
    simp only [S, List.mem_singleton] at hp
    subst hp
    exact ⟨hF_wf, hA, hF_cc⟩
  have hwf : ∀ p ∈ S, p.2.WF S.length := gpac_wf hgpac
  have hZ : ∀ w < S.length, ∀ n,
      ((((genStepN S (Γ := [])).eval Env.nil) (fun _ ↦ f)) w n).val = (f n).val := by
    intro w hw n
    rw [genStepN_eval_getElem S (fun _ ↦ f) w hw]
    have hw0 : w = 0 := by change w < 1 at hw; omega
    subst hw0
    exact hfix n
  refine ⟨S, hgpac, 0, Nat.succ_pos 0, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwf (fun _ ↦ f) hZ
    (n + 1) 0 n (Nat.succ_pos 0) (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  exact huniq.symm

/-- `tmConstOneJet` is a constant jet. -/
theorem mem_isConstJet_one : IsConstJet tmConstOneJet := by
  intro n
  exact Q.val_ofNat 0

/-- System T rational term representing an integer `z`. -/
def memIntTm (z : Int) {Γ : List Ty} : Tm Γ .rat :=
  match z with
  | .ofNat m => .qnat (natTm m)
  | .negSucc m => .qsub (.qnat .zero) (.qnat (natTm (m + 1)))

/-- Evaluating `memIntTm z` in any environment has rational value `(z : Rat)`. -/
theorem memIntTm_val (z : Int) {Γ : List Ty} (e : Env Γ) :
    ((memIntTm z).eval e).val = (z : Rat) := by
  cases z with
  | ofNat m =>
    change (Q.ofNat ((natTm m).eval e)).val = (Int.ofNat m : Rat)
    rw [natTm_eval, Q.val_ofNat]
    rfl
  | negSucc m =>
    change (Q.sub (Q.ofNat 0) (Q.ofNat ((natTm (m + 1)).eval e))).val = (Int.negSucc m : Rat)
    rw [natTm_eval, Q.val_sub, Q.val_ofNat, Q.val_ofNat]
    push_cast
    ring

/-- System T rational term with rational value `q.val`. -/
def memRatTm (q : Q) {Γ : List Ty} : Tm Γ .rat :=
  .qdiv (memIntTm q.num) (.qnat (natTm q.den))

/-- Evaluating `memRatTm q` in any environment has rational value `q.val`. -/
theorem memRatTm_val (q : Q) {Γ : List Ty} (e : Env Γ) :
    ((memRatTm q).eval e).val = q.val := by
  have hne : (Q.ofNat ((natTm q.den).eval e)).num ≠ 0 := by
    rw [natTm_eval]
    exact Int.ofNat_ne_zero.mpr q.den_ne_zero
  change (Q.div ((memIntTm q.num).eval e) (Q.ofNat ((natTm q.den).eval e))).val = q.val
  rw [Q.val_div _ _ hne, memIntTm_val, natTm_eval, Q.val_ofNat]
  rfl

/-- Closed constant jet with coefficient `0` of value `q.val` and higher coefficients `0`. -/
def memConstJet (q : Q) : Tm [] JetTy :=
  .lam (.recNat (memRatTm q) (.lam (.lam (.qnat .zero))) (.var .here))

/-- `memConstJet q` is a constant jet. -/
theorem mem_isConstJet_const (q : Q) : IsConstJet (memConstJet q) := by
  intro n
  exact Q.val_ofNat 0

theorem InGPAC_const (q : Q) : InGPAC (Jet.const q).coeff := by
  refine mem_one_eq_inGPAC (memConstJet q) (.const tmZeroJet) (Jet.const q).coeff
    (mem_isConstJet_const q) trivial gpac_isConstJet_zero (fun n ↦ ?_)
  cases n with
  | zero =>
    unfold eqStepEval
    change (Q.add ((memRatTm q (Γ := [.nat])).eval (Env.cons (σ := .nat) 0 Env.nil)) (Q.ofNat 0)).val = q.val
    rw [Q.val_add, memRatTm_val, Q.val_ofNat]
    ring
  | succ j =>
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    unfold eqStepEval
    change (Q.add (Q.ofNat 0) (Q.div (Q.ofNat 0) (Q.ofNat (j + 1)))).val = Q.zero.val
    rw [Q.val_add, Q.val_div _ _ hne, Q.val_ofNat, Q.val_ofNat, Q.val_zero]
    ring

theorem InGPAC_varX : InGPAC Jet.varX.coeff := by
  refine mem_one_eq_inGPAC tmZeroJet (.const tmConstOneJet) Jet.varX.coeff
    gpac_isConstJet_zero trivial mem_isConstJet_one (fun n ↦ ?_)
  cases n with
  | zero =>
    unfold eqStepEval
    change (Q.add (Q.ofNat 0) (Q.ofNat 0)).val = Q.zero.val
    rw [Q.val_add, Q.val_ofNat, Q.val_zero]
    ring
  | succ j =>
    cases j with
    | zero =>
      have hne : (Q.ofNat 1).num ≠ 0 := by decide
      unfold eqStepEval
      change (Q.add (Q.ofNat 0) (Q.div (Q.ofNat 1) (Q.ofNat 1))).val = (Q.ofNat 1).val
      rw [Q.val_add, Q.val_div _ _ hne, Q.val_ofNat, Q.val_ofNat]
      ring
    | succ k =>
      have hne : (Q.ofNat (k + 2)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero (k + 1))
      unfold eqStepEval
      change (Q.add (Q.ofNat 0) (Q.div (Q.ofNat 0) (Q.ofNat (k + 2)))).val = Q.zero.val
      rw [Q.val_add, Q.val_div _ _ hne, Q.val_ofNat, Q.val_ofNat, Q.val_zero]
      ring

theorem InGPAC_exp : InGPAC Jet.exp.coeff := by
  refine mem_one_eq_inGPAC tmConstOneJet (.var 0) Jet.exp.coeff
    mem_isConstJet_one (Nat.succ_pos 0) trivial (fun n ↦ ?_)
  cases n with
  | zero =>
    have hne : (Q.ofNat 1).num ≠ 0 := by decide
    unfold eqStepEval
    change (Q.add (Q.ofNat 1) (Q.ofNat 0)).val = (Q.div (Q.ofNat 1) (Q.ofNat 1)).val
    rw [Q.val_add, Q.val_div _ _ hne, Q.val_ofNat, Q.val_ofNat]
    ring
  | succ j =>
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    have hne_rat : ((j + 1 : Nat) : Rat) ≠ 0 := by positivity
    have hexp : ((j + 1 : Nat) : Rat) * (Jet.exp.coeff (j + 1)).val = (Jet.exp.coeff j).val := by
      have he := Jet.exp_deriv_val j
      dsimp [Jet.deriv] at he
      rwa [Q.val_mul, Q.val_ofNat] at he
    unfold eqStepEval
    change (Q.add (Q.ofNat 0) (Q.div (Jet.exp.coeff j) (Q.ofNat (j + 1)))).val =
      (Jet.exp.coeff (j + 1)).val
    rw [Q.val_add, Q.val_div _ _ hne, Q.val_ofNat, Q.val_ofNat, ← hexp]
    field_simp
    ring

/-- The two-equation constant-data system for `(sin, cos)`: `u = 0 + ∫v`, `v = 1 + ∫(0 − u)`. -/
def memSinCosSys : List (Tm [] JetTy × JExprN) :=
  [(tmZeroJet, .var 1), (tmConstOneJet, .sub (.const tmZeroJet) (.var 0))]

/-- `memSinCosSys` satisfies `GPACSys`. -/
theorem mem_sinCosSys_gpac : GPACSys memSinCosSys := by
  intro p hp
  simp only [memSinCosSys, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨show 1 < 2 by omega, gpac_isConstJet_zero, trivial⟩
  · exact ⟨⟨trivial, show 0 < 2 by omega⟩, mem_isConstJet_one, gpac_isConstJet_zero, trivial⟩

/-- Value agreement of `solN memSinCosSys` with `(Jet.sin.coeff, Jet.cos.coeff)` at every degree `n`. -/
theorem mem_sinCosSys_solN_val (n : Nat) :
    (solN memSinCosSys 0 n).val = (Jet.sin.coeff n).val ∧
    (solN memSinCosSys 1 n).val = (Jet.cos.coeff n).val := by
  have h2 := genStepN_two_iterate tmZeroJet tmConstOneJet .varV
    (.sub (.const tmZeroJet) .varU) (n + 1)
  have h0 := congrFun (congrArg Prod.fst h2) n
  have h1 := congrFun (congrArg Prod.snd h2) n
  have hsc := sinCos_iterate_val (n + 1) n (Nat.lt_succ_self n)
  dsimp only [solN, memSinCosSys, JExpr2.toN] at h0 h1 hsc ⊢
  rw [h0, h1]
  exact hsc

theorem InGPAC_sin : InGPAC Jet.sin.coeff :=
  ⟨memSinCosSys, mem_sinCosSys_gpac, 0, by decide, fun n ↦ (mem_sinCosSys_solN_val n).1.symm⟩

theorem InGPAC_cos : InGPAC Jet.cos.coeff :=
  ⟨memSinCosSys, mem_sinCosSys_gpac, 1, by decide, fun n ↦ (mem_sinCosSys_solN_val n).2.symm⟩

#print axioms InGPAC_const
#print axioms InGPAC_varX
#print axioms InGPAC_exp
#print axioms InGPAC_sin
#print axioms InGPAC_cos

end HAomega
