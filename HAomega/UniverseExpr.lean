/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseComp

/-!
# Expressions of the closed universe

`UExpr` is the language of the universe: rational constants, `x`, `exp`, `sin`,
`cos`, closed under `+ − ×`, reciprocal, `∫`, `d/dx` and composition. Its
semantics `UExpr.eval` is the Taylor coefficient stream, defined by
coefficient formulas only (`Jet.recip` is the usual recursion
`h₀ = 1/f₀`, `hₙ = −(Σ_{1≤j≤n} f_j h_{n−j})/f₀`); no ODE is involved.

`UExpr.compile` compiles an expression to a polynomial–integral system with
constant data and a variable index, by the closure constructions (`sumSys`,
`subSys`, `mulSys`, `invSys`, `integSys`, `derivSysC`, `compSys` after the
`∫`-flattening `flatSys`). `UExpr.compile_correct`: for every defined
expression (reciprocals only of series with nonzero constant term) the system
has constant data and its solution — computed by the proof-computed solver
`genSolveND` — is the expression's Taylor series, as values.

Value-level metatheory theorems (`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- Coefficients `0 … n` of the reciprocal of `f`. -/
def recipList (f : Nat → Q) : Nat → List Q
  | 0 => [Q.div (Q.ofNat 1) (f 0)]
  | n + 1 =>
    let l := recipList f n
    l ++ [Q.div (Q.neg ((List.range (n + 1)).foldl
      (fun acc j ↦ Q.add acc (Q.mul (f (j + 1)) (l.getD (n - j) Q.zero))) Q.zero)) (f 0)]

/-- The reciprocal series. -/
def Jet.recip (f : Nat → Q) (n : Nat) : Q := (recipList f n).getD n Q.zero

/-- Expressions of the universe. -/
inductive UExpr : Type where
  | const : Q → UExpr
  | x : UExpr
  | exp : UExpr
  | sin : UExpr
  | cos : UExpr
  | add : UExpr → UExpr → UExpr
  | sub : UExpr → UExpr → UExpr
  | mul : UExpr → UExpr → UExpr
  | inv : UExpr → UExpr
  | integ : UExpr → UExpr
  | deriv : UExpr → UExpr
  | comp : UExpr → UExpr → UExpr

/-- The Taylor coefficients of an expression. `comp a b` is `a ∘ (b − b(0))`. -/
def UExpr.eval : UExpr → Nat → Q
  | .const q => (Jet.const q).coeff
  | .x => Jet.varX.coeff
  | .exp => Jet.exp.coeff
  | .sin => Jet.sin.coeff
  | .cos => Jet.cos.coeff
  | .add a b => fun n ↦ Q.add (a.eval n) (b.eval n)
  | .sub a b => fun n ↦ Q.sub (a.eval n) (b.eval n)
  | .mul a b => ((tmJetMul (Γ := [])).eval Env.nil) a.eval b.eval
  | .inv a => Jet.recip a.eval
  | .integ a => ((tmJetInteg (Γ := [])).eval Env.nil) a.eval
  | .deriv a => ((tmJetDeriv (Γ := [])).eval Env.nil) a.eval
  | .comp a b => (Jet.compZero ⟨a.eval⟩ ⟨b.eval⟩).coeff

/-- Every reciprocal is of a series with nonzero constant term. -/
def UExpr.Defined : UExpr → Prop
  | .const _ | .x | .exp | .sin | .cos => True
  | .add a b | .sub a b | .mul a b | .comp a b => a.Defined ∧ b.Defined
  | .inv a => a.Defined ∧ (a.eval 0).val ≠ 0
  | .integ a | .deriv a => a.Defined

/-- `∫`-flattening with fuel: move the first `∫a` of a right-hand side into a
    new variable `z = 0 + ∫a`, until none is left (fuel: the number of `∫`s). -/
def flatSys : Nat → List (Tm [] JetTy × JExprN) → List (Tm [] JetTy × JExprN)
  | 0, sys => sys
  | k + 1, sys =>
    match flatSysOne sys.length sys with
    | (sys', some e) => flatSys k (sys' ++ [(tmZeroJet, e)])
    | (_, none) => sys

/-- `flatSys` with fuel the total `∫` count. -/
def flatAll (sys : List (Tm [] JetTy × JExprN)) : List (Tm [] JetTy × JExprN) :=
  flatSys (sys.map (fun p ↦ flatCount p.2)).sum sys

/-- `flatSysOne` preserves the length of the equation list. -/
theorem ux_flatSysOne_length (idx : Nat) (tail : List (Tm [] JetTy × JExprN)) :
    (flatSysOne idx tail).1.length = tail.length := by
  induction tail with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨A, F⟩
    dsimp [flatSysOne]
    split
    · rfl
    · split
      · rename_i rest' e hrest
        have h1 : rest' = (flatSysOne idx rest).1 := (congrArg Prod.fst hrest).symm
        simp [h1, ih]
      · rfl

/-- `flatSys k sys` has length at least `sys.length`. -/
theorem ux_flatSys_length_ge (k : Nat) (sys : List (Tm [] JetTy × JExprN)) :
    sys.length ≤ (flatSys k sys).length := by
  induction k generalizing sys with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    dsimp [flatSys]
    split
    · rename_i sys' e h
      have hlen : sys'.length = sys.length := by
        have h1 : sys' = (flatSysOne sys.length sys).1 := (congrArg Prod.fst h).symm
        rw [h1, ux_flatSysOne_length]
      have hstep : sys.length ≤ (sys' ++ [(tmZeroJet, e)]).length := by
        simp [hlen]
      exact Nat.le_trans hstep (ih (sys' ++ [(tmZeroJet, e)]))
    · exact Nat.le_refl _

/-- `flatAll` keeps the existing variables (it only appends equations). -/
theorem flatAll_length_ge (sys : List (Tm [] JetTy × JExprN)) :
    sys.length ≤ (flatAll sys).length :=
  ux_flatSys_length_ge _ sys

/-- A compiled expression: a system and the variable holding the expression. -/
structure CSys where
  sys : List (Tm [] JetTy × JExprN)
  v : Nat
  hv : v < sys.length

/-- **The compiler** from expressions to systems. -/
def UExpr.compile : UExpr → CSys
  | .const q => ⟨[(memConstJet q, .const tmZeroJet)], 0, Nat.zero_lt_one⟩
  | .x => ⟨[(tmZeroJet, .const tmConstOneJet)], 0, by decide⟩
  | .exp => ⟨[(tmConstOneJet, .var 0)], 0, by decide⟩
  | .sin => ⟨memSinCosSys, 0, by decide⟩
  | .cos => ⟨memSinCosSys, 1, by decide⟩
  | .add a b =>
    let A := a.compile; let B := b.compile
    ⟨sumSys A.sys B.sys A.v B.v A.hv B.hv, A.sys.length + B.sys.length,
      by rw [sumSys_length]; omega⟩
  | .sub a b =>
    let A := a.compile; let B := b.compile
    ⟨subSys A.sys B.sys A.v B.v A.hv B.hv, A.sys.length + B.sys.length,
      by simp [subSys]⟩
  | .mul a b =>
    let A := a.compile; let B := b.compile
    ⟨mulSys A.sys B.sys A.v B.v A.hv B.hv, A.sys.length + B.sys.length,
      by rw [mulSys_length]; omega⟩
  | .inv a =>
    let A := a.compile
    ⟨invSys A.sys A.v A.hv, A.sys.length, by simp [invSys]⟩
  | .integ a =>
    let A := a.compile
    ⟨integSys A.sys A.v, A.sys.length, by simp [integSys]⟩
  | .deriv a =>
    let A := a.compile
    ⟨derivSysC A.sys A.v A.hv, A.sys.length, by simp [derivSysC]⟩
  | .comp a b =>
    let A := a.compile; let B := b.compile
    ⟨compSys (flatAll A.sys) B.sys B.v B.hv, B.sys.length + A.v,
      by have := flatAll_length_ge A.sys; have := A.hv; simp [compSys]; omega⟩

/-- `recipList f n` has length `n + 1`. -/
theorem ux_recipList_length (f : Nat → Q) : ∀ n : Nat, (recipList f n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [recipList, ux_recipList_length f n]

/-- One-step prefix stability of `recipList`: for `m ≤ n`, `(recipList f (n + 1)).getD m Q.zero = (recipList f n).getD m Q.zero`. -/
theorem ux_recipList_getD_step (f : Nat → Q) (n m : Nat) (hm : m ≤ n) :
    (recipList f (n + 1)).getD m Q.zero = (recipList f n).getD m Q.zero := by
  have hm₁ : m < (recipList f n).length := by rw [ux_recipList_length]; omega
  have hm₂ : m < (recipList f (n + 1)).length := by rw [ux_recipList_length]; omega
  rw [uDeriv_getD_eq_getElem _ _ m hm₂, uDeriv_getD_eq_getElem _ _ m hm₁]
  dsimp only [recipList]
  exact List.getElem_append_left hm₁

/-- Prefix stability of `recipList`: for `m ≤ n`, `(recipList f n).getD m Q.zero = Jet.recip f m`. -/
theorem ux_recipList_getD_eq_recip (f : Nat → Q) (m n : Nat) (hmn : m ≤ n) :
    (recipList f n).getD m Q.zero = Jet.recip f m := by
  induction n with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    rfl
  | succ k ih =>
    by_cases hmk : m ≤ k
    · exact (ux_recipList_getD_step f k m hmk).trans (ih hmk)
    · have hm_eq : m = k + 1 := by omega
      subst hm_eq
      rfl

/-- Unfolding `Jet.recip f (n + 1)`. -/
theorem ux_recip_succ (f : Nat → Q) (n : Nat) :
    Jet.recip f (n + 1) =
      let l := recipList f n
      Q.div (Q.neg ((List.range (n + 1)).foldl
        (fun acc j ↦ Q.add acc (Q.mul (f (j + 1)) (l.getD (n - j) Q.zero))) Q.zero)) (f 0) := by
  unfold Jet.recip
  have hn : n + 1 < (recipList f (n + 1)).length := by rw [ux_recipList_length]; omega
  rw [uDeriv_getD_eq_getElem _ _ (n + 1) hn]
  dsimp only [recipList]
  have hlen : (recipList f n).length = n + 1 := ux_recipList_length f n
  rw [List.getElem_append_right (by omega)]
  simp [hlen]

/-- Rational value of a left fold of `Q.add` over a list. -/
theorem ux_foldl_add_val {α : Type} (l : List α) (g : α → Q) (init : Q) :
    (l.foldl (fun acc j ↦ Q.add acc (g j)) init).val =
      init.val + (l.map (fun j ↦ (g j).val)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, Q.val_add]
    ring

/-- Summing `h` mapped over `List.range m` equals `∑ j ∈ Finset.range m, h j`. -/
theorem ux_sum_map_range (m : Nat) (h : Nat → Rat) :
    ((List.range m).map h).sum = ∑ j ∈ Finset.range m, h j := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        Finset.sum_range_succ, ih]

/-- Rational value of `Jet.recip f (n + 1)` when `(f 0).val ≠ 0`. -/
theorem ux_recip_succ_val (f : Nat → Q) (h0 : (f 0).val ≠ 0) (n : Nat) :
    (Jet.recip f (n + 1)).val =
      - (∑ j ∈ Finset.range (n + 1), (f (j + 1)).val * (Jet.recip f (n - j)).val) / (f 0).val := by
  rw [ux_recip_succ, Q.val_div _ _ (inv_num_ne_zero h0), Q.val_neg,
      ux_foldl_add_val, Q.val_zero, zero_add, ux_sum_map_range]
  congr 2
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [Q.val_mul, ux_recipList_getD_eq_recip f (n - j) n (by omega)]

/-- `Jet.recip f` is the reciprocal: `f · recip f = 1`, as values. -/
theorem Jet.recip_spec (f : Nat → Q) (h0 : (f 0).val ≠ 0) (n : Nat) :
    (((tmJetMul (Γ := [])).eval Env.nil) f (Jet.recip f) n).val =
      ((Jet.const (Q.ofNat 1)).coeff n).val := by
  cases n with
  | zero =>
    rw [uMul_zero_val]
    change (f 0).val * (Q.div (Q.ofNat 1) (f 0)).val = (Q.ofNat 1).val
    rw [Q.val_div _ _ (inv_num_ne_zero h0), Q.val_ofNat]
    field_simp
  | succ m =>
    rw [inv_jetMul_val, Finset.sum_range_succ' (fun i ↦ (f i).val * (Jet.recip f (m + 1 - i)).val) (m + 1)]
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [ux_recip_succ_val f h0 m]
    change (∑ k ∈ Finset.range (m + 1), (f (k + 1)).val * (Jet.recip f (m - k)).val) +
      (f 0).val * (- (∑ j ∈ Finset.range (m + 1), (f (j + 1)).val * (Jet.recip f (m - j)).val) / (f 0).val) =
      Q.zero.val
    rw [Q.val_zero]
    field_simp
    ring

/-- Any right inverse `h` of `f` (in value) agrees in value with `Jet.recip f`. -/
theorem ux_inv_unique_val (f h : Nat → Q) (h0 : (f 0).val ≠ 0)
    (hfh : ∀ m, (((tmJetMul (Γ := [])).eval Env.nil) f h m).val =
      ((Jet.const (Q.ofNat 1)).coeff m).val) (n : Nat) :
    (Jet.recip f n).val = (h n).val := by
  let mul := (tmJetMul (Γ := [])).eval Env.nil
  let r := Jet.recip f
  let one := (Jet.const (Q.ofNat 1)).coeff
  have hr_eq : (r n).val = (mul r (mul f h) n).val := by
    have h1 : (mul r (mul f h) n).val = (mul r one n).val :=
      tmJetMul_agreeV Env.nil Env.nil (n + 1) r r (mul f h) one
        (fun _ _ ↦ rfl) (fun i _ ↦ hfh i) n (Nat.lt_succ_self n)
    rw [h1, inv_jetMul_val, inv_mul_one_val]
  have hh_eq : (h n).val = (mul (mul r f) h n).val := by
    have h1 : (mul (mul r f) h n).val = (mul (mul f r) h n).val :=
      tmJetMul_agreeV Env.nil Env.nil (n + 1) (mul r f) (mul f r) h h
        (fun i _ ↦ inv_jetMul_comm_val r f i) (fun _ _ ↦ rfl) n (Nat.lt_succ_self n)
    have h2 : (mul (mul f r) h n).val = (mul one h n).val :=
      tmJetMul_agreeV Env.nil Env.nil (n + 1) (mul f r) one h h
        (fun i _ ↦ Jet.recip_spec f h0 i) (fun _ _ ↦ rfl) n (Nat.lt_succ_self n)
    rw [h1, h2, inv_jetMul_comm_val one h n, inv_jetMul_val, inv_mul_one_val]
  rw [hr_eq, hh_eq, inv_jetMul_assoc_val r f h n]

/-- The new variable `solN (invSys sys v hv) sys.length` is a right inverse of `f` in value. -/
theorem ux_invSys_mul_val (f : Nat → Q) (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (v : Nat) (hv : v < sys.length)
    (hf_val : ∀ n, (f n).val = (solN sys v n).val) (h0 : (f 0).val ≠ 0) (n : Nat) :
    (((tmJetMul (Γ := [])).eval Env.nil) f (solN (invSys sys v hv) sys.length) n).val =
      ((Jet.const (Q.ofNat 1)).coeff n).val := by
  have hwf : ∀ p ∈ sys, p.2.WF sys.length := gpac_wf hgpac
  let S := invSys sys v hv
  let f₀ := solN sys v
  let h := solN S sys.length
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

/-- Properties of `flatSys k sys` when `(sys.map (fun p ↦ flatCount p.2)).sum ≤ k`. -/
theorem ux_flatSys_props (k : Nat) (sys : List (Tm [] JetTy × JExprN))
    (hgpac : GPACSys sys) (hsum : (sys.map (fun p ↦ flatCount p.2)).sum ≤ k) :
    GPACSys (flatSys k sys) ∧
    (∀ p ∈ flatSys k sys, p.2.NoInteg) ∧
    (∀ v < sys.length, ∀ n, (solN sys v n).val = (solN (flatSys k sys) v n).val) := by
  induction k generalizing sys with
  | zero =>
    dsimp [flatSys]
    cases h : flatSysOne sys.length sys with
    | mk sys' opt =>
      cases opt with
      | none =>
        exact ⟨hgpac, flat_noInteg_of_flatSysOne_none sys.length sys (congrArg Prod.snd h),
          fun _ _ _ ↦ rfl⟩
      | some e =>
        have hstep := flat_step_solN_val sys sys' e hgpac h
        omega
  | succ k ih =>
    dsimp [flatSys]
    split
    · rename_i sys' e h
      obtain ⟨hS_len, hS_gpac, hS_sum, hS_val⟩ := flat_step_solN_val sys sys' e hgpac h
      obtain ⟨hgpacF, hnoF, hvalF⟩ := ih (sys' ++ [(tmZeroJet, e)]) hS_gpac (by omega)
      exact ⟨hgpacF, hnoF, fun v hv n ↦ (hS_val v hv n).trans (hvalF v (by omega) n)⟩
    · rename_i h
      exact ⟨hgpac, flat_noInteg_of_flatSysOne_none sys.length sys (congrArg Prod.snd h),
        fun _ _ _ ↦ rfl⟩

/-- `flatAll sys` preserves `GPACSys`, eliminates all `.integ` nodes, and preserves `solN` on `< sys.length`. -/
theorem ux_flatAll_props (sys : List (Tm [] JetTy × JExprN)) (hgpac : GPACSys sys) :
    GPACSys (flatAll sys) ∧
    (∀ p ∈ flatAll sys, p.2.NoInteg) ∧
    (∀ v < sys.length, ∀ n, (solN sys v n).val = (solN (flatAll sys) v n).val) :=
  ux_flatSys_props _ sys hgpac (le_refl _)

/-- Correctness of a single-equation constant-data system `[(A, F)]`. -/
theorem ux_one_eq_correct (A : Tm [] JetTy) (F : JExprN) (f : Nat → Q)
    (hA : IsConstJet A) (hF_wf : F.WF 1) (hF_cc : F.ConstsConst)
    (hfix : ∀ n, (eqStepEval (A, F) (fun _ ↦ f) n).val = (f n).val) :
    GPACSys [(A, F)] ∧ ∀ n, (f n).val = (solN [(A, F)] 0 n).val := by
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
  refine ⟨hgpac, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwf (fun _ ↦ f) hZ
    (n + 1) 0 n (Nat.succ_pos 0) (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  exact huniq.symm

/-- **The compiler is correct.** -/
theorem UExpr.compile_correct (e : UExpr) (he : e.Defined) :
    GPACSys e.compile.sys ∧
      ∀ n, (e.eval n).val = (solN e.compile.sys e.compile.v n).val := by
  induction e with
  | const q =>
    refine ux_one_eq_correct (memConstJet q) (.const tmZeroJet) (Jet.const q).coeff
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
  | x =>
    refine ux_one_eq_correct tmZeroJet (.const tmConstOneJet) Jet.varX.coeff
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
  | exp =>
    refine ux_one_eq_correct tmConstOneJet (.var 0) Jet.exp.coeff
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
  | sin =>
    exact ⟨mem_sinCosSys_gpac, fun n ↦ (mem_sinCosSys_solN_val n).1.symm⟩
  | cos =>
    exact ⟨mem_sinCosSys_gpac, fun n ↦ (mem_sinCosSys_solN_val n).2.symm⟩
  | add a b iha ihb =>
    obtain ⟨h₁, ha_val⟩ := iha he.1
    obtain ⟨h₂, hb_val⟩ := ihb he.2
    let A := a.compile; let B := b.compile
    let S := sumSys A.sys B.sys A.v B.v A.hv B.hv
    have hgpacS := gpac_sumSys A.sys B.sys h₁ h₂ A.v B.v A.hv B.hv
    have hwfS := gpac_wf hgpacS
    have hvS : A.sys.length + B.sys.length < S.length := by
      rw [sumSys_length]; exact Nat.lt_succ_self _
    refine ⟨hgpacS, fun n ↦ ?_⟩
    have huniq := genSolveN_unique_val S hwfS (sumTargetState A.sys B.sys A.v B.v)
      (sumTargetState_fixed A.sys B.sys (gpac_wf h₁) (gpac_wf h₂) A.v B.v A.hv B.hv)
      (n + 1) (A.sys.length + B.sys.length) n hvS (Nat.lt_succ_self n)
    rw [extractClosed_genSolveND_fst] at huniq
    change (Q.add (a.eval n) (b.eval n)).val =
      ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
        (A.sys.length + B.sys.length) n).val
    rw [huniq]
    unfold sumTargetState
    rw [if_neg (by omega), if_neg (by omega), Q.val_add, Q.val_add, ha_val n, hb_val n]
  | sub a b iha ihb =>
    obtain ⟨h₁, ha_val⟩ := iha he.1
    obtain ⟨h₂, hb_val⟩ := ihb he.2
    let A := a.compile; let B := b.compile
    let S := subSys A.sys B.sys A.v B.v A.hv B.hv
    have hgpacS := gpac_subSys A.sys B.sys h₁ h₂ A.v B.v A.hv B.hv
    have hwfS := gpac_wf hgpacS
    have hvS : A.sys.length + B.sys.length < S.length := by
      rw [uSub_subSys_length]; exact Nat.lt_succ_self _
    refine ⟨hgpacS, fun n ↦ ?_⟩
    have huniq := genSolveN_unique_val S hwfS (uSubTargetState A.sys B.sys A.v B.v)
      (uSubTargetState_fixed A.sys B.sys (gpac_wf h₁) (gpac_wf h₂) A.v B.v A.hv B.hv)
      (n + 1) (A.sys.length + B.sys.length) n hvS (Nat.lt_succ_self n)
    rw [extractClosed_genSolveND_fst] at huniq
    change (Q.sub (a.eval n) (b.eval n)).val =
      ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
        (A.sys.length + B.sys.length) n).val
    rw [huniq]
    unfold uSubTargetState
    rw [if_neg (by omega), if_neg (by omega), Q.val_sub, Q.val_sub, ha_val n, hb_val n]
  | mul a b iha ihb =>
    obtain ⟨h₁, ha_val⟩ := iha he.1
    obtain ⟨h₂, hb_val⟩ := ihb he.2
    let A := a.compile; let B := b.compile
    let S := mulSys A.sys B.sys A.v B.v A.hv B.hv
    have hgpacS := gpac_mulSys A.sys B.sys h₁ h₂ A.v B.v A.hv B.hv
    have hwfS := gpac_wf hgpacS
    have hvS : A.sys.length + B.sys.length < S.length := by
      rw [mulSys_length]; exact Nat.lt_succ_self _
    refine ⟨hgpacS, fun n ↦ ?_⟩
    have huniq := genSolveN_unique_val S hwfS (uMulTargetState A.sys B.sys A.v B.v)
      (uMulTargetState_fixed A.sys B.sys (gpac_wf h₁) (gpac_wf h₂) A.v B.v A.hv B.hv)
      (n + 1) (A.sys.length + B.sys.length) n hvS (Nat.lt_succ_self n)
    rw [extractClosed_genSolveND_fst] at huniq
    have hfg := tmJetMul_agreeV Env.nil Env.nil (n + 1) a.eval (solN A.sys A.v) b.eval (solN B.sys B.v)
      (fun i _ ↦ ha_val i) (fun i _ ↦ hb_val i) n (Nat.lt_succ_self n)
    change ((((tmJetMul (Γ := [])).eval Env.nil) a.eval b.eval) n).val =
      ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
        (A.sys.length + B.sys.length) n).val
    rw [huniq]
    unfold uMulTargetState
    rw [if_neg (by omega), if_neg (by omega)]
    exact hfg
  | inv a iha =>
    obtain ⟨h₁, ha_val⟩ := iha he.1
    let A := a.compile
    exact ⟨inv_gpac_invSys A.sys h₁ A.v A.hv, fun n ↦
      ux_inv_unique_val a.eval (solN (invSys A.sys A.v A.hv) A.sys.length) he.2
        (ux_invSys_mul_val a.eval A.sys h₁ A.v A.hv ha_val he.2) n⟩
  | integ a iha =>
    obtain ⟨h₁, ha_val⟩ := iha he
    let A := a.compile
    let S := integSys A.sys A.v
    have hgpacS := gpac_integSys A.sys h₁ A.v A.hv
    have hwfS := gpac_wf hgpacS
    have hvS : A.sys.length < S.length := by
      rw [uInteg_integSys_length]; exact Nat.lt_succ_self _
    refine ⟨hgpacS, fun n ↦ ?_⟩
    have huniq := genSolveN_unique_val S hwfS (uIntegTargetState A.sys A.v)
      (uIntegTargetState_fixed A.sys (gpac_wf h₁) A.v A.hv)
      (n + 1) A.sys.length n hvS (Nat.lt_succ_self n)
    rw [extractClosed_genSolveND_fst] at huniq
    have hInt := tmJetInteg_agreeV_succ Env.nil Env.nil n a.eval (solN A.sys A.v)
      (fun i _ ↦ ha_val i) n (Nat.lt_succ_self n)
    change ((((tmJetInteg (Γ := [])).eval Env.nil) a.eval) n).val =
      ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
        A.sys.length n).val
    rw [huniq]
    unfold uIntegTargetState
    rw [if_neg (Nat.lt_irrefl _)]
    exact hInt
  | deriv a iha =>
    obtain ⟨h₁, ha_val⟩ := iha he
    let A := a.compile
    let S := derivSysC A.sys A.v A.hv
    have hgpacS := gpac_derivSysC A.sys h₁ A.v A.hv
    have hwfS := gpac_wf hgpacS
    have hvS : A.sys.length < S.length := by
      rw [gpac_derivSysC_length]; exact Nat.lt_succ_self _
    refine ⟨hgpacS, fun n ↦ ?_⟩
    have huniq := genSolveN_unique_val S hwfS (uDerivTargetState A.sys A.v)
      (gpac_derivSysC_fixed A.sys (gpac_wf h₁) A.v A.hv)
      (n + 1) A.sys.length n hvS (Nat.lt_succ_self n)
    rw [extractClosed_genSolveND_fst] at huniq
    have hD : ((((tmJetDeriv (Γ := [])).eval Env.nil) a.eval) n).val =
        ((((tmJetDeriv (Γ := [])).eval Env.nil) (solN A.sys A.v)) n).val := by
      change (Q.mul (Q.ofNat (n + 1)) (a.eval (n + 1))).val =
        (Q.mul (Q.ofNat (n + 1)) (solN A.sys A.v (n + 1))).val
      rw [Q.val_mul, Q.val_mul, ha_val (n + 1)]
    change ((((tmJetDeriv (Γ := [])).eval Env.nil) a.eval) n).val =
      ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
        A.sys.length n).val
    rw [huniq]
    unfold uDerivTargetState
    rw [if_neg (Nat.lt_irrefl _)]
    exact hD
  | comp a b iha ihb =>
    obtain ⟨h₁, ha_val⟩ := iha he.1
    obtain ⟨h₂, hb_val⟩ := ihb he.2
    let A := a.compile; let B := b.compile
    obtain ⟨hgpacF, hnoF, hvalF⟩ := ux_flatAll_props A.sys h₁
    have hf_val : ∀ n, (a.eval n).val = (solN (flatAll A.sys) A.v n).val :=
      fun n ↦ (ha_val n).trans (hvalF A.v A.hv n)
    let S := compSys (flatAll A.sys) B.sys B.v B.hv
    have hgpacS := comp_gpac_compSys (flatAll A.sys) B.sys hgpacF h₂ B.v B.hv
    have hwfS := gpac_wf hgpacS
    have hvS : B.sys.length + A.v < S.length := by
      have := flatAll_length_ge A.sys
      have := A.hv
      rw [comp_compSys_length]
      omega
    refine ⟨hgpacS, fun n ↦ ?_⟩
    have huniq := genSolveN_unique_val S hwfS (compTargetState (flatAll A.sys) B.sys B.v)
      (compTargetState_fixed (flatAll A.sys) B.sys hgpacF hnoF (gpac_wf h₂) B.v B.hv)
      (n + 1) (B.sys.length + A.v) n hvS (Nat.lt_succ_self n)
    rw [extractClosed_genSolveND_fst] at huniq
    change ((Jet.compZero ⟨a.eval⟩ ⟨b.eval⟩).coeff n).val =
      ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
        (B.sys.length + A.v) n).val
    rw [huniq]
    unfold compTargetState
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
    exact (compZero_congr_val ⟨a.eval⟩ ⟨solN (flatAll A.sys) A.v⟩ ⟨b.eval⟩ hf_val n).trans
      (comp_compZero_congr_right_val ⟨solN (flatAll A.sys) A.v⟩ ⟨b.eval⟩ ⟨solN B.sys B.v⟩ hb_val n)

/-- **Every defined expression is in the universe.** -/
theorem UExpr.inGPAC (e : UExpr) (he : e.Defined) : InGPAC e.eval := by
  obtain ⟨hgpac, hval⟩ := e.compile_correct he
  exact ⟨e.compile.sys, hgpac, e.compile.v, e.compile.hv, hval⟩

#print axioms Jet.recip_spec
#print axioms UExpr.compile_correct
#print axioms UExpr.inGPAC

end HAomega
