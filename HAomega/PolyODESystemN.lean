/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.JExprN

/-!
# One proof-computed solver for every polynomial–integral system in `n` variables

A system is a list `sys = [(A₀, F₀), …, (A_{n−1}, F_{n−1})]` of closed initial
jets and right-hand sides `F_v : JExprN` over the variables `0 … n−1`. Its
Picard operator on states `W : ℕ → JetTy` is `P(W)(v) = A_v + ∫F_v(W)`
(`genStepN`; the `v`-th equation is selected inside System T by `recNat` on
`v`, `selectStep`). `genSolveND` proves, for every well-formed system,

  `∀k ∃W. ∀v < n. ∀i < k. P(W)(v)(i) = W(v)(i)`

(both bounds written `x + succ e = m`) by `Deriv.ind` on `k`, using
`JExprN.prefixT`. The statement names the system, never the iteration; the
extract is the Picard iteration from the initial state (`initN`), and by
`genSolveN_unique_val` it computes the unique solution's coefficients.
-/

namespace HAomega

/-- `A_v + ∫F_v(w)` for the `v`-th equation, selected by `recNat` on `v`; the
    zero jet beyond the end of the list. -/
def selectStep : List (Tm [] JetTy × JExprN) → {Γ : List Ty} → Tm Γ WTy → Tm Γ .nat → Tm Γ JetTy
  | [], _, _, _ => Tm.closedWk tmZeroJet
  | (A, F) :: rest, _, w, v =>
      .recNat (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm w)))
        (.lam (.lam (selectStep rest w.wk.wk (.var (.there .here)))))
        v

/-- `A_v` for the `v`-th equation, selected by `recNat` on `v`. -/
def selectInit : List (Tm [] JetTy × JExprN) → {Γ : List Ty} → Tm Γ .nat → Tm Γ JetTy
  | [], _, _ => Tm.closedWk tmZeroJet
  | (A, _) :: rest, _, v =>
      .recNat (Tm.closedWk A) (.lam (.lam (selectInit rest (.var (.there .here))))) v

/-- The Picard operator `P(W)(v) = A_v + ∫F_v(W)`. -/
def genStepN (sys : List (Tm [] JetTy × JExprN)) {Γ : List Ty} : Tm Γ (.arrow WTy WTy) :=
  .lam (.lam (selectStep sys (.var (.there .here)) (.var .here)))

/-- The initial state `v ↦ A_v`. -/
def initN (sys : List (Tm [] JetTy × JExprN)) {Γ : List Ty} : Tm Γ WTy :=
  .lam (selectInit sys (.var .here))

/-- Invariant over `.nat :: []`:
    `∃W. ∀v ∀e. v + succ e = n → ∀i ∀d. i + succ d = k → P(W)(v)(i) = W(v)(i)`. -/
abbrev genSolveNInv (sys : List (Tm [] JetTy × JExprN)) :=
  let c3 : List Ty := .nat :: .nat :: WTy :: .nat :: []
  let e3 : Tm c3 .nat := .var .here
  let v3 : Tm c3 .nat := .var (.there .here)
  let c5 : List Ty := .nat :: .nat :: .nat :: .nat :: WTy :: .nat :: []
  let d : Tm c5 .nat := .var .here
  let i : Tm c5 .nat := .var (.there .here)
  let v : Tm c5 .nat := .var (.there (.there (.there .here)))
  let W : Tm c5 WTy := .var (.there (.there (.there (.there .here))))
  let k : Tm c5 .nat := .var (.there (.there (.there (.there (.there .here)))))
  (Formula.ex WTy
    (.all .nat (.all .nat
      (.imp (.eq (.add v3 (.succ e3)) (natTm sys.length))
        (.all .nat (.all .nat
          (.imp (.eq (.add i (.succ d)) k)
            (.eq (.app (.app (.app (genStepN sys (Γ := c5)) W) v) i) (.app (.app W v) i)))))))) :
    Formula (.nat :: []) _)

/-- Renaming leaves `natTm m` unchanged. -/
@[derivNorm] theorem natTm_rename (m : Nat) {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (natTm m (Γ := Γ)).rename ρ = natTm m (Γ := Δ) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg Tm.succ ih

/-- Renaming commutes with `JExprN.toTm`. -/
@[derivNorm] theorem JExprN.toTm_rename (F : JExprN) {Γ Δ : List Ty}
    (w : Tm Γ WTy) (ρ : Ren Γ Δ) :
    (F.toTm w).rename ρ = F.toTm (w.rename ρ) := by
  induction F with
  | var i => simp only [JExprN.toTm, Tm.rename, natTm_rename]
  | const c => exact closedWk_rename c ρ
  | add a b iha ihb => simp only [JExprN.toTm, Tm.rename, tmJetAdd_rename, iha, ihb]
  | sub a b iha ihb => simp only [JExprN.toTm, Tm.rename, tmJetSub_rename, iha, ihb]
  | mul a b iha ihb => simp only [JExprN.toTm, Tm.rename, tmJetMul_rename, iha, ihb]
  | integ a iha => simp only [JExprN.toTm, Tm.rename, tmJetInteg_rename, iha]

/-- Substitution commutes with `JExprN.toTm`. -/
@[derivNorm] theorem JExprN.toTm_subst (F : JExprN) {Γ Δ : List Ty}
    (w : Tm Γ WTy) (s : Sub Γ Δ) :
    (F.toTm w).subst s = F.toTm (w.subst s) := by
  induction F with
  | var i => simp only [JExprN.toTm, Tm.subst, natTm_subst]
  | const c => exact closedWk_subst c s
  | add a b iha ihb => simp only [JExprN.toTm, Tm.subst, tmJetAdd_subst, iha, ihb]
  | sub a b iha ihb => simp only [JExprN.toTm, Tm.subst, tmJetSub_subst, iha, ihb]
  | mul a b iha ihb => simp only [JExprN.toTm, Tm.subst, tmJetMul_subst, iha, ihb]
  | integ a iha => simp only [JExprN.toTm, Tm.subst, tmJetInteg_subst, iha]

/-- Renaming commutes with `selectStep`. -/
@[derivNorm] theorem selectStep_rename (sys : List (Tm [] JetTy × JExprN)) {Γ Δ : List Ty}
    (w : Tm Γ WTy) (v : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (selectStep sys w v).rename ρ = selectStep sys (w.rename ρ) (v.rename ρ) := by
  induction sys generalizing Γ Δ with
  | nil => exact closedWk_rename tmZeroJet ρ
  | cons hd tl ih =>
    rcases hd with ⟨A, F⟩
    simp only [selectStep, Tm.rename, tmJetAdd_rename, closedWk_rename, tmJetInteg_rename,
      JExprN.toTm_rename, ih, Tm.wk, rename_ext_rename_wk]
    rfl

/-- Substitution commutes with `selectStep`. -/
@[derivNorm] theorem selectStep_subst (sys : List (Tm [] JetTy × JExprN)) {Γ Δ : List Ty}
    (w : Tm Γ WTy) (v : Tm Γ .nat) (s : Sub Γ Δ) :
    (selectStep sys w v).subst s = selectStep sys (w.subst s) (v.subst s) := by
  induction sys generalizing Γ Δ with
  | nil => exact closedWk_subst tmZeroJet s
  | cons hd tl ih =>
    rcases hd with ⟨A, F⟩
    simp only [selectStep, Tm.subst, tmJetAdd_subst, closedWk_subst, tmJetInteg_subst,
      JExprN.toTm_subst, ih, Tm.wk, subst_ext_rename]
    rfl

/-- Renaming commutes with `selectInit`. -/
@[derivNorm] theorem selectInit_rename (sys : List (Tm [] JetTy × JExprN)) {Γ Δ : List Ty}
    (v : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (selectInit sys v).rename ρ = selectInit sys (v.rename ρ) := by
  induction sys generalizing Γ Δ with
  | nil => exact closedWk_rename tmZeroJet ρ
  | cons hd tl ih =>
    rcases hd with ⟨A, _⟩
    simp only [selectInit, Tm.rename, closedWk_rename, ih]
    rfl

/-- Substitution commutes with `selectInit`. -/
@[derivNorm] theorem selectInit_subst (sys : List (Tm [] JetTy × JExprN)) {Γ Δ : List Ty}
    (v : Tm Γ .nat) (s : Sub Γ Δ) :
    (selectInit sys v).subst s = selectInit sys (v.subst s) := by
  induction sys generalizing Γ Δ with
  | nil => exact closedWk_subst tmZeroJet s
  | cons hd tl ih =>
    rcases hd with ⟨A, _⟩
    simp only [selectInit, Tm.subst, closedWk_subst, ih]
    rfl

/-- Renaming leaves `genStepN sys` unchanged. -/
@[derivNorm] theorem genStepN_rename (sys : List (Tm [] JetTy × JExprN))
    {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (genStepN sys (Γ := Γ)).rename ρ = genStepN sys (Γ := Δ) := by
  simp only [genStepN, Tm.rename, selectStep_rename]
  rfl

/-- Substitution leaves `genStepN sys` unchanged. -/
@[derivNorm] theorem genStepN_subst (sys : List (Tm [] JetTy × JExprN))
    {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (genStepN sys (Γ := Γ)).subst s = genStepN sys (Γ := Δ) := by
  simp only [genStepN, Tm.subst, selectStep_subst]
  rfl

/-- Renaming leaves `initN sys` unchanged. -/
@[derivNorm] theorem initN_rename (sys : List (Tm [] JetTy × JExprN))
    {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (initN sys (Γ := Γ)).rename ρ = initN sys (Γ := Δ) := by
  simp only [initN, Tm.rename, selectInit_rename]
  rfl

/-- Substitution leaves `initN sys` unchanged. -/
@[derivNorm] theorem initN_subst (sys : List (Tm [] JetTy × JExprN))
    {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (initN sys (Γ := Γ)).subst s = initN sys (Γ := Δ) := by
  simp only [initN, Tm.subst, selectInit_subst]
  rfl

/-- Applying `genStepN sys` to `W` and `v` converts to `selectStep sys W v` inside `Deriv`. -/
def genStepN_appD (sys : List (Tm [] JetTy × JExprN)) {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ WTy) (v : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (genStepN sys (Γ := Γ)) W) v) (selectStep sys W v)) := by
  have hb1 := Deriv.convBeta (Δ := Δ) (c := WTy)
    (.lam (selectStep sys (.var (.there .here)) (.var .here))) W
  deriv_norm at hb1
  have hb2 := Deriv.convBeta (Δ := Δ) (c := .nat)
    (selectStep sys W.wk (.var .here)) v
  deriv_norm at hb2
  exact Deriv.transE (Deriv.congFun hb1 v) hb2

/-- `selectStep ((A, F) :: rest) w .zero` converts to `A + ∫F(w)` inside `Deriv`. -/
def selectStep_zeroD (A : Tm [] JetTy) (F : JExprN) (rest : List (Tm [] JetTy × JExprN))
    {Γ as : List Ty} {Δ : Ctx Γ as} (w : Tm Γ WTy) :
    Deriv Δ (.eq (selectStep ((A, F) :: rest) w .zero)
                 (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm w)))) :=
  Deriv.convRecZero (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm w)))
    (.lam (.lam (selectStep rest w.wk.wk (.var (.there .here)))))

/-- `selectStep ((A, F) :: rest) w (.succ u)` converts to `selectStep rest w u` inside `Deriv`. -/
def selectStep_succD (A : Tm [] JetTy) (F : JExprN) (rest : List (Tm [] JetTy × JExprN))
    {Γ as : List Ty} {Δ : Ctx Γ as} (w : Tm Γ WTy) (u : Tm Γ .nat) :
    Deriv Δ (.eq (selectStep ((A, F) :: rest) w (.succ u)) (selectStep rest w u)) := by
  let z : Tm Γ JetTy := .app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm w))
  let s : Tm Γ (.arrow .nat (.arrow JetTy JetTy)) :=
    .lam (.lam (selectStep rest w.wk.wk (.var (.there .here))))
  have hr := Deriv.convRecSucc (Δ := Δ) z s u
  have hb1 := Deriv.convBeta (Δ := Δ) (c := .nat) (d := .arrow JetTy JetTy)
    (.lam (selectStep rest w.wk.wk (.var (.there .here)))) u
  deriv_norm at hb1
  have hb2 := Deriv.convBeta (Δ := Δ) (c := JetTy) (d := JetTy)
    (selectStep rest (w.wk (σ := JetTy)) (u.wk (σ := JetTy))) (.recNat z s u)
  deriv_norm at hb2
  exact Deriv.transE hr (Deriv.transE (Deriv.congFun hb1 (.recNat z s u)) hb2)

/-- `(A + ∫F(w))(0)` converts to `A(0) + 0` inside `Deriv`. -/
def selectStep_head_zeroD (A : Tm [] JetTy) (F : JExprN) {Γ as : List Ty} {Δ : Ctx Γ as}
    (w : Tm Γ WTy) :
    Deriv Δ (.eq (.app (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm w))) .zero)
                 (.qadd (.app (Tm.closedWk A) .zero) (.qnat .zero))) :=
  Deriv.transE (tmJetAdd_appD (Tm.closedWk A) (.app tmJetInteg (F.toTm w)) .zero)
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) .zero))
      (Deriv.transE (tmJetInteg_appD (F.toTm w) .zero) (jetIntegZeroD (F.toTm w))))

/-- `(A + ∫F(w))(succ j)` converts to `A(succ j) + F(w)(j) / (j + 1)` inside `Deriv`. -/
def selectStep_head_succD (A : Tm [] JetTy) (F : JExprN) {Γ as : List Ty} {Δ : Ctx Γ as}
    (w : Tm Γ WTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm w))) (.succ j))
                 (.qadd (.app (Tm.closedWk A) (.succ j))
                        (.qdiv (.app (F.toTm w) j) (.qnat (.succ j))))) :=
  Deriv.transE (tmJetAdd_appD (Tm.closedWk A) (.app tmJetInteg (F.toTm w)) (.succ j))
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) (.succ j)))
      (Deriv.transE (tmJetInteg_appD (F.toTm w) (.succ j)) (jetIntegSuccD (F.toTm w) j)))

/-- Step case of `selectStep_cons_allD` in context `.nat :: Γ`. -/
def selectStep_cons_stepD (A : Tm [] JetTy) (F : JExprN) (rest : List (Tm [] JetTy × JExprN))
    {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as} (W₁ W₂ : Tm Γ WTy) (i : Tm Γ .nat)
    (h_ih_rest : Deriv Δ (.all .nat
      (.eq (.app (selectStep rest W₁.wk.wk (.var .here)) i.wk.wk)
           (.app (selectStep rest W₂.wk.wk (.var .here)) i.wk.wk)))) :
    Deriv Δ (.eq (.app (selectStep ((A, F) :: rest) W₁.wk (.succ (.var .here))) i.wk)
                 (.app (selectStep ((A, F) :: rest) W₂.wk (.succ (.var .here))) i.wk)) := by
  let u : Tm (.nat :: Γ) .nat := .var .here
  have h_rest_u := Deriv.allE u h_ih_rest
  deriv_norm at h_rest_u
  exact Deriv.transE (Deriv.congFun (selectStep_succD A F rest W₁.wk u) i.wk)
    (Deriv.transE h_rest_u
      (Deriv.symmE (Deriv.congFun (selectStep_succD A F rest W₂.wk u) i.wk)))

/-- Combine head equality at `v = 0` and tail equality at all `u` into `selectStep ((A, F) :: rest)` equality at all `v`, by `Deriv.ind` on `v`. -/
def selectStep_cons_allD (A : Tm [] JetTy) (F : JExprN) (rest : List (Tm [] JetTy × JExprN))
    {Γ as : List Ty} {Δ : Ctx Γ as} (W₁ W₂ : Tm Γ WTy) (i : Tm Γ .nat)
    (h_head : Deriv Δ
      (.eq (.app (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm W₁))) i)
           (.app (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm W₂))) i)))
    (ih_rest : Deriv Δ (.all .nat
      (.eq (.app (selectStep rest W₁.wk (.var .here)) i.wk)
           (.app (selectStep rest W₂.wk (.var .here)) i.wk)))) :
    Deriv Δ (.all .nat
      (.eq (.app (selectStep ((A, F) :: rest) W₁.wk (.var .here)) i.wk)
           (.app (selectStep ((A, F) :: rest) W₂.wk (.var .here)) i.wk))) := by
  refine Deriv.impE ?_ ih_rest
  refine Deriv.impI ?_
  refine Deriv.ind ?_ ?_
  · deriv_norm
    exact Deriv.transE (Deriv.congFun (selectStep_zeroD A F rest W₁) i)
      (Deriv.transE (Deriv.wk h_head)
        (Deriv.symmE (Deriv.congFun (selectStep_zeroD A F rest W₂) i)))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact selectStep_cons_stepD A F rest W₁ W₂ i (Deriv.wk Deriv.ax)

/-- For any system `tail`, `(selectStep tail W₁ v)(0) = (selectStep tail W₂ v)(0)` for all `v`. -/
def selectStep_eq_zero_allD (tail : List (Tm [] JetTy × JExprN))
    {Γ as : List Ty} {Δ : Ctx Γ as} (W₁ W₂ : Tm Γ WTy) :
    Deriv Δ (.all .nat
      (.eq (.app (selectStep tail W₁.wk (.var .here)) .zero)
           (.app (selectStep tail W₂.wk (.var .here)) .zero))) := by
  induction tail with
  | nil => exact Deriv.allI (Deriv.eqRefl _)
  | cons hd rest ih =>
    rcases hd with ⟨A, F⟩
    have h_head : Deriv Δ
        (.eq (.app (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm W₁))) .zero)
             (.app (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm W₂))) .zero)) :=
      Deriv.transE (selectStep_head_zeroD A F W₁) (Deriv.symmE (selectStep_head_zeroD A F W₂))
    exact selectStep_cons_allD A F rest W₁ W₂ .zero h_head ih

/-- For any well-formed `tail`, if `prefixAgreeN n W₁ W₂ j`, then `(selectStep tail W₁ v)(succ j) = (selectStep tail W₂ v)(succ j)` for all `v`. -/
def selectStep_eq_succ_allD (n : Nat) (tail : List (Tm [] JetTy × JExprN))
    (htail : ∀ p ∈ tail, p.2.WF n)
    {Γ as : List Ty} {Δ : Ctx Γ as} (W₁ W₂ : Tm Γ WTy) (j : Tm Γ .nat)
    (h_agree : Deriv Δ (prefixAgreeN n W₁ W₂ j)) :
    Deriv Δ (.all .nat
      (.eq (.app (selectStep tail W₁.wk (.var .here)) (.succ j.wk))
           (.app (selectStep tail W₂.wk (.var .here)) (.succ j.wk)))) := by
  induction tail with
  | nil => exact Deriv.allI (Deriv.eqRefl _)
  | cons hd rest ih =>
    rcases hd with ⟨A, F⟩
    have hF : F.WF n := htail (A, F) (.head _)
    have hrest : ∀ p ∈ rest, p.2.WF n := fun p hp ↦ htail p (.tail _ hp)
    have h_F_eq : Deriv Δ (.eq (.app (F.toTm W₁) j) (.app (F.toTm W₂) j)) :=
      prefixAgreeElimT (F.prefixT n hF W₁ W₂ j h_agree) (Deriv.convAddZero j)
    have h_head : Deriv Δ
        (.eq (.app (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm W₁))) (.succ j))
             (.app (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm W₂))) (.succ j))) :=
      Deriv.transE (selectStep_head_succD A F W₁ j)
        (Deriv.transE
          (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) (.succ j)))
            (Deriv.congQDivNum (.qnat (.succ j)) h_F_eq))
          (Deriv.symmE (selectStep_head_succD A F W₂ j)))
    exact selectStep_cons_allD A F rest W₁ W₂ (.succ j) h_head (ih hrest)

/-- Instantiate `selectStep_eq_zero_allD` at `v`. -/
def selectStep_eq_zeroD (tail : List (Tm [] JetTy × JExprN))
    {Γ as : List Ty} {Δ : Ctx Γ as} (W₁ W₂ : Tm Γ WTy) (v : Tm Γ .nat) :
    Deriv Δ (.eq (.app (selectStep tail W₁ v) .zero)
                 (.app (selectStep tail W₂ v) .zero)) := by
  have h := Deriv.allE v (selectStep_eq_zero_allD (Δ := Δ) tail W₁ W₂)
  deriv_norm at h
  exact h

/-- Instantiate `selectStep_eq_succ_allD` at `v`. -/
def selectStep_eq_succD (n : Nat) (tail : List (Tm [] JetTy × JExprN))
    (htail : ∀ p ∈ tail, p.2.WF n)
    {Γ as : List Ty} {Δ : Ctx Γ as} (W₁ W₂ : Tm Γ WTy) (j v : Tm Γ .nat)
    (h_agree : Deriv Δ (prefixAgreeN n W₁ W₂ j)) :
    Deriv Δ (.eq (.app (selectStep tail W₁ v) (.succ j))
                 (.app (selectStep tail W₂ v) (.succ j))) := by
  have h := Deriv.allE v (selectStep_eq_succ_allD (Δ := Δ) n tail htail W₁ W₂ j h_agree)
  deriv_norm at h
  exact h

/-- Parameterized body `∀v ∀e. v + succ e = n → ∀i ∀d. i + succ d = k → P(W)(v)(i) = W(v)(i)` in any context `Γ`. -/
abbrev genSolveNAt (sys : List (Tm [] JetTy × JExprN)) {Γ : List Ty}
    (W : Tm Γ WTy) (k : Tm Γ .nat) :=
  let c2 : List Ty := .nat :: .nat :: Γ
  let e2 : Tm c2 .nat := .var .here
  let v2 : Tm c2 .nat := .var (.there .here)
  let c4 : List Ty := .nat :: .nat :: .nat :: .nat :: Γ
  let d0 : Tm c4 .nat := .var .here
  let i0 : Tm c4 .nat := .var (.there .here)
  let v0 : Tm c4 .nat := .var (.there (.there (.there .here)))
  let W4 : Tm c4 WTy := W.wk.wk.wk.wk
  let k4 : Tm c4 .nat := k.wk.wk.wk.wk
  (Formula.all .nat (.all .nat
    (.imp (.eq (.add v2 (.succ e2)) (natTm sys.length))
      (.all .nat (.all .nat
        (.imp (.eq (.add i0 (.succ d0)) k4)
          (.eq (.app (.app (.app (genStepN sys (Γ := c4)) W4) v0) i0)
               (.app (.app W4 v0) i0))))))) :
    Formula Γ _)

/-- Existential body of `genSolveNInv sys`. -/
abbrev genSolveNBody (sys : List (Tm [] JetTy × JExprN)) :
    Formula (WTy :: .nat :: [])
      (.arrow .nat (.arrow .nat (.arrow .unit (.arrow .nat (.arrow .nat (.arrow .unit .unit)))))) :=
  genSolveNAt sys (.var .here) (.var (.there .here))

/-- Inner step of `genSolveNIHPrefixT` in context `.nat :: .nat :: .nat :: .nat :: Γ`. -/
def genSolveNIHPrefixInnerT (sys : List (Tm [] JetTy × JExprN)) {Γ as : List Ty}
    {Δ : Ctx (.nat :: .nat :: .nat :: .nat :: Γ) as}
    (W : Tm Γ WTy) (k j d : Tm Γ .nat)
    (h_ih_wk : Deriv Δ (genSolveNAt sys W.wk.wk.wk.wk k.wk.wk.wk.wk))
    (h_succ_wk : Deriv Δ (.eq (.add (.succ j.wk.wk.wk.wk) (.succ d.wk.wk.wk.wk)) (.succ k.wk.wk.wk.wk)))
    (h_ve : Deriv Δ (.eq (.add (.var (.there (.there (.there .here))))
      (.succ (.var (.there (.there .here))))) (natTm sys.length)))
    (h_me : Deriv Δ (.eq (.add (.var (.there .here)) (.var .here)) (j.wk.wk.wk.wk))) :
    Deriv Δ (.eq
      (.app (.app (.app (genStepN sys) (W.wk.wk.wk.wk)) (.var (.there (.there (.there .here))))) (.var (.there .here)))
      (.app (.app (W.wk.wk.wk.wk) (.var (.there (.there (.there .here))))) (.var (.there .here)))) := by
  let c4 : List Ty := .nat :: .nat :: .nat :: .nat :: Γ
  let e2 : Tm c4 .nat := .var .here
  let m : Tm c4 .nat := .var (.there .here)
  let e1 : Tm c4 .nat := .var (.there (.there .here))
  let v1 : Tm c4 .nat := .var (.there (.there (.there .here)))
  let d4 : Tm c4 .nat := d.wk.wk.wk.wk
  have h_jk := succAddSuccInjT h_succ_wk
  have h_mk := leLtTransAddT h_me h_jk
  have h_inst1 := Deriv.allE e1 (Deriv.allE v1 h_ih_wk)
  deriv_norm at h_inst1
  have h_imp1 := Deriv.impE h_inst1 h_ve
  have h_inst2 := Deriv.allE (.add e2 d4) (Deriv.allE m h_imp1)
  deriv_norm at h_inst2
  exact Deriv.impE h_inst2 h_mk

/-- From `genSolveNAt sys W k` and `succ j + succ d = succ k`, derive `prefixAgreeN sys.length (P(W)) W j`. -/
def genSolveNIHPrefixT (sys : List (Tm [] JetTy × JExprN)) {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ WTy) (k j d : Tm Γ .nat)
    (h_ih : Deriv Δ (genSolveNAt sys W k))
    (h_eq_succ : Deriv Δ (.eq (.add (.succ j) (.succ d)) (.succ k))) :
    Deriv Δ (prefixAgreeN sys.length (.app (genStepN sys) W) W j) := by
  refine Deriv.impE (Deriv.impE ?_ h_ih) h_eq_succ
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_)))))
  deriv_norm
  exact genSolveNIHPrefixInnerT sys W k j d
    (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax)))
    (Deriv.wk (Deriv.wk Deriv.ax))
    (Deriv.wk Deriv.ax)
    Deriv.ax

/-- Base case (`k = 0`) of `genSolveND`: `initN sys` vacuously solves below `0`. -/
def genSolveNBaseD (sys : List (Tm [] JetTy × JExprN)) :
    Deriv Ctx.nil ((genSolveNInv sys).subst1 .zero) := by
  refine Deriv.exI (initN sys (Γ := [])) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_)))))
  let c4 : List Ty := .nat :: .nat :: .nat :: .nat :: []
  let d : Tm c4 .nat := .var .here
  let i : Tm c4 .nat := .var (.there .here)
  exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.add i d))
    (Deriv.transE (Deriv.symmE (Deriv.convAddSucc i d)) Deriv.ax))

/-- Inner certificate of `genSolveNStepD`: `P(W)` solves `Z = P(Z)` in all `v < n` below degree `succ k`. -/
def genSolveNStepCertD (sys : List (Tm [] JetTy × JExprN)) (hwf : ∀ p ∈ sys, p.2.WF sys.length) :
    Deriv (.cons (genSolveNBody sys) (Ctx.cons (genSolveNInv sys) Ctx.nil).wk)
      ((((genSolveNBody sys).subst (Sub.ext Sub.succHere)).rename (Ren.ext (Ren.wk WTy))).subst1
        (.app (genStepN sys) (.var .here))) := by
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let c4 : List Ty := .nat :: .nat :: .nat :: WTy :: .nat :: []
    let v₀ : Tm c4 .nat := .var (.there (.there .here))
    let W₀ : Tm c4 WTy := .var (.there (.there (.there .here)))
    let P₀ : Tm c4 (.arrow WTy WTy) := genStepN sys
    exact Deriv.transE (Deriv.congFun (genStepN_appD sys (.app P₀ W₀) v₀) .zero)
      (Deriv.transE (selectStep_eq_zeroD sys (.app P₀ W₀) W₀ v₀)
        (Deriv.symmE (Deriv.congFun (genStepN_appD sys W₀ v₀) .zero)))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    let c5 : List Ty := .nat :: .nat :: .nat :: .nat :: WTy :: .nat :: []
    let d : Tm c5 .nat := .var .here
    let j : Tm c5 .nat := .var (.there .here)
    let v : Tm c5 .nat := .var (.there (.there (.there .here)))
    let Ws : Tm c5 WTy := .var (.there (.there (.there (.there .here))))
    let ks : Tm c5 .nat := .var (.there (.there (.there (.there (.there .here)))))
    let Ps : Tm c5 (.arrow WTy WTy) := genStepN sys
    exact Deriv.transE (Deriv.congFun (genStepN_appD sys (.app Ps Ws) v) (.succ j))
      (Deriv.transE
        (selectStep_eq_succD sys.length sys hwf (.app Ps Ws) Ws j v
          (genSolveNIHPrefixT sys Ws ks j d (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))) Deriv.ax))
        (Deriv.symmE (Deriv.congFun (genStepN_appD sys Ws v) (.succ j))))

/-- Inductive step (`k → succ k`) of `genSolveND`: map `W ↦ P(W)` and split on `i` via `Deriv.ind`. -/
def genSolveNStepD (sys : List (Tm [] JetTy × JExprN)) (hwf : ∀ p ∈ sys, p.2.WF sys.length) :
    Deriv Ctx.nil (.all .nat (.imp (genSolveNInv sys) ((genSolveNInv sys).subst Sub.succHere))) :=
  Deriv.allI (Deriv.impI
    (Deriv.exE (ψ := (genSolveNInv sys).subst Sub.succHere) Deriv.ax
      (Deriv.exI (.app (genStepN sys) (.var .here)) (genSolveNStepCertD sys hwf))))

/-- **The general n-variable solver**, by `Deriv.ind` on `k`. -/
def genSolveND (sys : List (Tm [] JetTy × JExprN)) (hwf : ∀ p ∈ sys, p.2.WF sys.length) :
    Deriv Ctx.nil (.all .nat (genSolveNInv sys)) :=
  Deriv.ind (genSolveNBaseD sys) (genSolveNStepD sys hwf)

/-- First projection of the extracted base case `genSolveNBaseD sys`. -/
theorem extract_genSolveNBaseD_fst (sys : List (Tm [] JetTy × JExprN)) :
    ((extract (genSolveNBaseD sys)).eval Env.nil).1 = (initN sys (Γ := [])).eval Env.nil :=
  extract_exI_fst (initN sys (Γ := [])) _

/-- First projection of the extracted induction step `genSolveNStepD sys hwf`. -/
theorem extract_genSolveNStepD_fst (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (m : Nat)
    (ih : (Ty.prod WTy (.arrow .nat (.arrow .nat (.arrow .unit (.arrow .nat (.arrow .nat (.arrow .unit .unit))))))).interp) :
    (((extract (genSolveNStepD sys hwf)).eval Env.nil) m ih).1 =
      ((genStepN sys (Γ := [])).eval Env.nil) ih.1 := by
  unfold genSolveNStepD
  rw [extract_step_exI_fst (body := genSolveNBody sys)
    (.app (genStepN sys) (.var .here)) (genSolveNStepCertD sys hwf) m ih]
  dsimp [Tm.eval]
  rw [← genStepN_rename sys (Γ := [.nat]) (Δ := [WTy, .nat]) (Ren.wk WTy),
       ← genStepN_rename sys (Γ := []) (Δ := [.nat]) (Ren.wk .nat),
       Tm.eval_wk, Tm.eval_wk]
  rfl

/-- The extracted solver at `k` is the `k`-th Picard iterate from `initN`. -/
theorem extractClosed_genSolveND_fst (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (k : Nat) :
    (((extractClosed (genSolveND sys hwf)).eval Env.nil) k).1 =
      ((genStepN sys (Γ := [])).eval Env.nil)^[k] ((initN sys (Γ := [])).eval Env.nil) := by
  induction k with
  | zero =>
    have h0 := congrArg Prod.fst
      (extractClosed_ind_eval (genSolveNBaseD sys) (genSolveNStepD sys hwf) 0)
    exact h0.trans (extract_genSolveNBaseD_fst sys)
  | succ m ih =>
    have hm := congrArg Prod.fst
      (extractClosed_ind_eval (genSolveNBaseD sys) (genSolveNStepD sys hwf) m)
    have hs := congrArg Prod.fst
      (extractClosed_ind_eval (genSolveNBaseD sys) (genSolveNStepD sys hwf) (m + 1))
    have hstep := extract_genSolveNStepD_fst sys hwf m
      (Nat.rec (motive := fun _ ↦ (Ty.prod WTy (.arrow .nat (.arrow .nat (.arrow .unit (.arrow .nat (.arrow .nat (.arrow .unit .unit))))))).interp)
        ((extract (genSolveNBaseD sys)).eval Env.nil)
        (fun j acc ↦ ((extract (genSolveNStepD sys hwf)).eval Env.nil) j acc) m)
    rw [← hm] at hstep
    rw [Function.iterate_succ_apply']
    exact hs.trans (hstep.trans (congrArg ((genStepN sys (Γ := [])).eval Env.nil) ih))

/-- Evaluating `F.toTm` on state streams agreeing in all variables `< n` up to degree `deg` preserves `AgreeV deg`. -/
theorem JExprN.toTm_agreeV (F : JExprN) (n : Nat) (hF : F.WF n)
    {Γ : List Ty} (e₁ e₂ : Env Γ) (w₁ w₂ : Tm Γ WTy) (deg : Nat)
    (hw : ∀ u < n, AgreeV deg (w₁.eval e₁ u) (w₂.eval e₂ u)) :
    AgreeV deg ((F.toTm w₁).eval e₁) ((F.toTm w₂).eval e₂) := by
  induction F with
  | var i =>
    change AgreeV deg (w₁.eval e₁ ((natTm i).eval e₁)) (w₂.eval e₂ ((natTm i).eval e₂))
    rw [natTm_eval, natTm_eval]
    exact hw i hF
  | const c =>
    intro m _
    dsimp only [JExprN.toTm]
    rw [closedWk_eval c e₁, closedWk_eval c e₂]
  | add a b iha ihb =>
    exact tmJetAdd_agreeV e₁ e₂ deg _ _ _ _ (iha hF.1) (ihb hF.2)
  | sub a b iha ihb =>
    exact tmJetSub_agreeV e₁ e₂ deg _ _ _ _ (iha hF.1) (ihb hF.2)
  | mul a b iha ihb =>
    exact tmJetMul_agreeV e₁ e₂ deg _ _ _ _ (iha hF.1) (ihb hF.2)
  | integ a iha =>
    intro m hm
    exact tmJetInteg_agreeV_succ e₁ e₂ deg _ _ (iha hF) m (Nat.lt_succ_of_lt hm)

/-- Evaluating `selectStep tail` on state streams agreeing in all variables `< n` up to degree `deg` yields `AgreeV (deg + 1)`. -/
theorem selectStep_agreeV_succ (n : Nat) (tail : List (Tm [] JetTy × JExprN))
    (htail : ∀ p ∈ tail, p.2.WF n)
    {Γ : List Ty} (e₁ e₂ : Env Γ) (w₁ w₂ : Tm Γ WTy) (tv₁ tv₂ : Tm Γ .nat)
    (deg v : Nat)
    (hw : ∀ u < n, AgreeV deg (w₁.eval e₁ u) (w₂.eval e₂ u))
    (hv₁ : tv₁.eval e₁ = v) (hv₂ : tv₂.eval e₂ = v) :
    AgreeV (deg + 1) ((selectStep tail w₁ tv₁).eval e₁) ((selectStep tail w₂ tv₂).eval e₂) := by
  induction tail generalizing Γ v with
  | nil =>
    intro m _
    dsimp only [selectStep]
    rw [closedWk_eval tmZeroJet e₁, closedWk_eval tmZeroJet e₂]
  | cons hd rest ih =>
    rcases hd with ⟨A, F⟩
    have hF : F.WF n := htail (A, F) (.head _)
    have hrest : ∀ p ∈ rest, p.2.WF n := fun p hp ↦ htail p (.tail _ hp)
    let z₁ := (Tm.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm w₁))).eval e₁
    let z₂ := (Tm.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm w₂))).eval e₂
    let s₁ : Nat → (Nat → Q) → (Nat → Q) := fun u acc ↦
      (selectStep rest w₁.wk.wk (.var (.there .here))).eval
        (Env.cons (σ := JetTy) acc (Env.cons (σ := .nat) u e₁))
    let s₂ : Nat → (Nat → Q) → (Nat → Q) := fun u acc ↦
      (selectStep rest w₂.wk.wk (.var (.there .here))).eval
        (Env.cons (σ := JetTy) acc (Env.cons (σ := .nat) u e₂))
    change AgreeV (deg + 1)
      (Nat.rec (motive := fun _ ↦ Nat → Q) z₁ s₁ (tv₁.eval e₁))
      (Nat.rec (motive := fun _ ↦ Nat → Q) z₂ s₂ (tv₂.eval e₂))
    rw [hv₁, hv₂]
    cases v with
    | zero =>
      have hA : AgreeV (deg + 1) ((Tm.closedWk A).eval e₁) ((Tm.closedWk A).eval e₂) := by
        intro m _
        rw [closedWk_eval A e₁, closedWk_eval A e₂]
      have hF_ag : AgreeV deg ((F.toTm w₁).eval e₁) ((F.toTm w₂).eval e₂) :=
        F.toTm_agreeV n hF e₁ e₂ w₁ w₂ deg hw
      exact tmJetAdd_agreeV e₁ e₂ (deg + 1) _ _ _ _ hA (tmJetInteg_agreeV_succ e₁ e₂ deg _ _ hF_ag)
    | succ u =>
      let acc₁ := Nat.rec (motive := fun _ ↦ Nat → Q) z₁ s₁ u
      let acc₂ := Nat.rec (motive := fun _ ↦ Nat → Q) z₂ s₂ u
      let e₁' : Env (JetTy :: .nat :: Γ) := Env.cons (σ := JetTy) acc₁ (Env.cons (σ := .nat) u e₁)
      let e₂' : Env (JetTy :: .nat :: Γ) := Env.cons (σ := JetTy) acc₂ (Env.cons (σ := .nat) u e₂)
      have hw' : ∀ idx < n, AgreeV deg (w₁.wk.wk.eval e₁' idx) (w₂.wk.wk.eval e₂' idx) := by
        intro idx hidx
        have hw1 : w₁.wk.wk.eval e₁' = w₁.eval e₁ :=
          (Tm.eval_wk (σ := JetTy) w₁.wk acc₁ (Env.cons (σ := .nat) u e₁)).trans
            (Tm.eval_wk (σ := .nat) w₁ u e₁)
        have hw2 : w₂.wk.wk.eval e₂' = w₂.eval e₂ :=
          (Tm.eval_wk (σ := JetTy) w₂.wk acc₂ (Env.cons (σ := .nat) u e₂)).trans
            (Tm.eval_wk (σ := .nat) w₂ u e₂)
        rw [hw1, hw2]
        exact hw idx hidx
      exact ih hrest e₁' e₂' w₁.wk.wk w₂.wk.wk (.var (.there .here)) (.var (.there .here)) u hw' rfl rfl

/-- `genStepN sys` maps state agreement below degree `deg` (in all variables `< sys.length`) to agreement below degree `deg + 1`. -/
theorem genStepN_agreeV_succ (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (deg : Nat) (W₁ W₂ : Nat → Nat → Q)
    (hw : ∀ u < sys.length, AgreeV deg (W₁ u) (W₂ u)) (v : Nat) :
    AgreeV (deg + 1) ((((genStepN sys (Γ := [])).eval Env.nil) W₁) v)
                     ((((genStepN sys (Γ := [])).eval Env.nil) W₂) v) := by
  let e₁ : Env [.nat, WTy] := Env.cons (σ := .nat) v (Env.cons (σ := WTy) W₁ Env.nil)
  let e₂ : Env [.nat, WTy] := Env.cons (σ := .nat) v (Env.cons (σ := WTy) W₂ Env.nil)
  exact selectStep_agreeV_succ sys.length sys hwf e₁ e₂
    (.var (.there .here)) (.var (.there .here)) (.var .here) (.var .here) deg v hw rfl rfl

/-- If `Z` is a value-level fixed point of `genStepN sys` on variables `< sys.length`, then the `k`-th Picard iterate from `initN sys` agrees with `Z` below degree `k`. -/
theorem genStepN_iterate_agreeV (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (Z : Nat → Nat → Q)
    (hZ : ∀ v < sys.length, ∀ n,
      ((((genStepN sys (Γ := [])).eval Env.nil) Z) v n).val = (Z v n).val) :
    ∀ k v : Nat, v < sys.length →
      AgreeV k ((((genStepN sys (Γ := [])).eval Env.nil)^[k] ((initN sys (Γ := [])).eval Env.nil)) v) (Z v)
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, v, hv, i, hi => by
    rw [Function.iterate_succ_apply']
    have hstep := genStepN_agreeV_succ sys hwf k
      (((genStepN sys (Γ := [])).eval Env.nil)^[k] ((initN sys (Γ := [])).eval Env.nil))
      Z (genStepN_iterate_agreeV sys hwf Z hZ k) v i hi
    exact hstep.trans (hZ v hv i)

/-- Uniqueness: every value-level solution `Z` agrees, in every variable `v < n`,
    with the `k`-th proof-computed iterate below degree `k`. -/
theorem genSolveN_unique_val (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (Z : Nat → Nat → Q)
    (hZ : ∀ v < sys.length, ∀ n,
      ((((genStepN sys (Γ := [])).eval Env.nil) Z) v n).val = (Z v n).val)
    (k v i : Nat) (hv : v < sys.length) (hi : i < k) :
    ((((extractClosed (genSolveND sys hwf)).eval Env.nil) k).1 v i).val = (Z v i).val := by
  rw [extractClosed_genSolveND_fst]
  exact genStepN_iterate_agreeV sys hwf Z hZ k v hv i hi

#print axioms genSolveND
#print axioms extractClosed_genSolveND_fst
#print axioms genSolveN_unique_val

end HAomega
