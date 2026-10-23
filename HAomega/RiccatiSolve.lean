/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QuadBlowupSolve

/-!
# A proof-computed jet solver for the Riccati equation `y' = 1 + y²`, `y(0) = 0`

Same specification shape as `PicardExpSolve.lean` (#27) and
`QuadBlowupSolve.lean` (#28), for the Picard operator
`P(Y) = ∫(1 + Y·Y)` (`tmRiccatiStep`), whose solution is `tan`:

  `∀k ∃Y. ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)`

The nonlinear step rests on `jetMulPrefixT` (`QuadBlowupSolve.lean`).
`riccatiSolveD` proves the specification by `Deriv.ind` on `k`; the extracted
solver's recursion comes from the induction. Out of scope: the differential
form, and Duffing.
-/

namespace HAomega

/-- Invariant over `.nat :: []`: `∃Y. ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)`
    for `P = tmRiccatiStep`. -/
abbrev riccatiSolveInv :=
  let ctx : List Ty := .nat :: .nat :: JetTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let Y : Tm ctx JetTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  (Formula.ex JetTy
    (.all .nat (.all .nat
      (.imp (.eq (.add i (.succ d)) k)
        (.eq (.app (.app (tmRiccatiStep (Γ := ctx)) Y) i) (.app Y i))))) :
    Formula (.nat :: []) _)

/-- Renaming leaves `tmZeroJet` unchanged. -/
@[derivNorm] theorem tmZeroJet_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmZeroJet (Γ := Γ)).rename ρ = tmZeroJet (Γ := Δ) := rfl

/-- Substitution leaves `tmZeroJet` unchanged. -/
@[derivNorm] theorem tmZeroJet_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmZeroJet (Γ := Γ)).subst s = tmZeroJet (Γ := Δ) := rfl

/-- Renaming leaves `tmRiccatiStep` unchanged. -/
@[derivNorm] theorem tmRiccatiStep_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmRiccatiStep (Γ := Γ)).rename ρ = tmRiccatiStep (Γ := Δ) := rfl

/-- Substitution leaves `tmRiccatiStep` unchanged. -/
@[derivNorm] theorem tmRiccatiStep_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmRiccatiStep (Γ := Γ)).subst s = tmRiccatiStep (Γ := Δ) := rfl

/-- Applying `tmRiccatiStep` to `U, i` converts to `jetIntegAt (1 + U·U) i` inside `Deriv`. -/
def tmRiccatiStep_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (tmRiccatiStep (Γ := Γ)) U) i)
                 (jetIntegAt (.app (.app tmJetAdd tmConstOneJet) (.app (.app tmJetMul U) U)) i)) := by
  let U_sq : Tm Γ JetTy := .app (.app tmJetMul U) U
  let one_plus_U_sq : Tm Γ JetTy := .app (.app tmJetAdd tmConstOneJet) U_sq
  have h1 : Deriv Δ (.eq (.app (tmRiccatiStep (Γ := Γ)) U)
      (.app tmJetInteg one_plus_U_sq)) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.app tmJetInteg
        (.app (.app tmJetAdd tmConstOneJet) (.app (.app tmJetMul (.var .here)) (.var .here)))) U
    deriv_norm at hb
    exact hb
  have h2 := tmJetInteg_appD (Δ := Δ) one_plus_U_sq i
  exact Deriv.transE (Deriv.congFun h1 i) h2

/-- `tmRiccatiStep` applied to `U` at `0` converts to `0` inside `Deriv`. -/
def tmRiccatiStep_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} (U : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app (tmRiccatiStep (Γ := Γ)) U) .zero) (.qnat .zero)) :=
  Deriv.transE (tmRiccatiStep_appD U .zero)
    (jetIntegZeroD (.app (.app tmJetAdd tmConstOneJet) (.app (.app tmJetMul U) U)))

/-- `tmRiccatiStep` applied to `U` at `succ j` converts to `(1(j) + (U·U)(j)) / (j + 1)` inside `Deriv`. -/
def tmRiccatiStep_succD {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (tmRiccatiStep (Γ := Γ)) U) (.succ j))
                 (.qdiv (.qadd (.app tmConstOneJet j) (tmJetMulAt U U j))
                        (.qnat (.succ j)))) := by
  let U_sq : Tm Γ JetTy := .app (.app tmJetMul U) U
  let one_plus_U_sq : Tm Γ JetTy := .app (.app tmJetAdd tmConstOneJet) U_sq
  have h1 := tmRiccatiStep_appD (Δ := Δ) U (.succ j)
  have h2 := jetIntegSuccD (Δ := Δ) one_plus_U_sq j
  have h3 := tmJetAdd_appD (Δ := Δ) tmConstOneJet U_sq j
  have h4 := Deriv.congQAdd (Δ := Δ) (Deriv.eqRefl (.app tmConstOneJet j))
    (tmJetMul_appD (Δ := Δ) U U j)
  have h5 := Deriv.congQDivNum (.qnat (.succ j)) (Deriv.transE h3 h4)
  exact Deriv.transE h1 (Deriv.transE h2 h5)

/-- Inner step of `riccatiIHPrefixT` in context `e :: m :: d :: j :: Y :: k :: []`. -/
def riccatiIHPrefixInnerT {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: .nat :: .nat :: JetTy :: .nat :: []) as}
    (h_ih_wk : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.eq (.app (.app tmRiccatiStep (.var (.there (.there (.there (.there (.there (.there .here))))))))
              (.var (.there .here)))
          (.app (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var (.there .here))))))))
    (h_succ_wk : Deriv Δ (.eq
      (.add (.succ (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there .here)))))
      (.succ (.var (.there (.there (.there (.there (.there .here)))))))))
    (h_me : Deriv Δ (.eq (.add (.var (.there .here)) (.var .here))
      (.var (.there (.there (.there .here)))))) :
    Deriv Δ (.eq
      (.app (.app tmRiccatiStep (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))
      (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here)))) := by
  let ctx6 : List Ty := .nat :: .nat :: .nat :: .nat :: JetTy :: .nat :: []
  let e : Tm ctx6 .nat := .var .here
  let m : Tm ctx6 .nat := .var (.there .here)
  let d : Tm ctx6 .nat := .var (.there (.there .here))
  have h_jk := succAddSuccInjT h_succ_wk
  have h_mk := leLtTransAddT h_me h_jk
  have h_inst := Deriv.allE (.add e d) (Deriv.allE m h_ih_wk)
  deriv_norm at h_inst
  exact Deriv.impE h_inst h_mk

/-- From outer IH `∀i ∀d'. i + succ d' = k → P(Y)(i) = Y(i)` and `succ j + succ d = succ k`, derive prefix agreement `∀m ∀e. m + e = j → P(Y)(m) = Y(m)`. -/
def riccatiIHPrefixT {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: JetTy :: .nat :: []) as}
    (h_ih_all : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there .here)))))))
        (.eq (.app (.app tmRiccatiStep (.var (.there (.there (.there (.there .here))))))
              (.var (.there .here)))
          (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here))))))))
    (h_eq_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there (.there .here))))))) :
    Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here))
              ((Tm.var (.there .here) : Tm (.nat :: .nat :: JetTy :: .nat :: []) .nat).wk.wk))
        (.eq (.app ((Tm.app tmRiccatiStep (.var (.there (.there .here))) :
                Tm (.nat :: .nat :: JetTy :: .nat :: []) JetTy).wk.wk) (.var (.there .here)))
          (.app ((Tm.var (.there (.there .here)) :
                Tm (.nat :: .nat :: JetTy :: .nat :: []) JetTy).wk.wk) (.var (.there .here))))))) := by
  refine Deriv.impE (Deriv.impE ?_ h_ih_all) h_eq_succ
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  exact riccatiIHPrefixInnerT (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax

/-- Base case (`k = 0`) of `riccatiSolveD`: `Y₀ = 0` vacuously solves below `0`. -/
def riccatiSolveBaseD : Deriv Ctx.nil (riccatiSolveInv.subst1 .zero) := by
  refine Deriv.exI (tmZeroJet (Γ := [])) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let d : Tm (.nat :: .nat :: []) .nat := .var .here
  let i : Tm (.nat :: .nat :: []) .nat := .var (.there .here)
  exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.add i d))
    (Deriv.transE (Deriv.symmE (Deriv.convAddSucc i d)) Deriv.ax))

/-- Existential body of `riccatiSolveInv`. -/
abbrev riccatiSolveBody :
    Formula (JetTy :: .nat :: []) (.arrow .nat (.arrow .nat (.arrow .unit .unit))) :=
  let ctx : List Ty := .nat :: .nat :: JetTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let Y : Tm ctx JetTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  .all .nat (.all .nat
    (.imp (.eq (.add i (.succ d)) k)
      (.eq (.app (.app (tmRiccatiStep (Γ := ctx)) Y) i) (.app Y i))))

/-- Inner certificate of `riccatiSolveStepD`: `P(Y)` solves `Z = P(Z)` below degree `succ k`. -/
def riccatiSolveStepCertD :
    Deriv (.cons riccatiSolveBody (Ctx.cons riccatiSolveInv Ctx.nil).wk)
      (((riccatiSolveBody.subst (Sub.ext Sub.succHere)).rename (Ren.ext (Ren.wk JetTy))).subst1
        (.app tmRiccatiStep (.var .here))) := by
  deriv_norm
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let Y₀ : Tm (.nat :: JetTy :: .nat :: []) JetTy := .var (.there .here)
    let P₀ : Tm (.nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := tmRiccatiStep
    exact Deriv.transE (tmRiccatiStep_zeroD (.app P₀ Y₀))
      (Deriv.symmE (tmRiccatiStep_zeroD Y₀))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let j : Tm (.nat :: .nat :: JetTy :: .nat :: []) .nat := .var (.there .here)
    let Ys : Tm (.nat :: .nat :: JetTy :: .nat :: []) JetTy := .var (.there (.there .here))
    let Ps : Tm (.nat :: .nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := tmRiccatiStep
    exact Deriv.transE (tmRiccatiStep_succD (.app Ps Ys) j)
      (Deriv.transE
        (Deriv.congQDivNum (.qnat (.succ j))
          (Deriv.congQAdd (Deriv.eqRefl (.app tmConstOneJet j))
            (jetMulPrefixT (.app Ps Ys) Ys (.app Ps Ys) Ys j
              (riccatiIHPrefixT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax)
              (riccatiIHPrefixT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax))))
        (Deriv.symmE (tmRiccatiStep_succD Ys j)))

/-- Inductive step (`k → succ k`) of `riccatiSolveD`: map `Y ↦ P(Y)` and split on `i` via `Deriv.ind`. -/
def riccatiSolveStepD :
    Deriv Ctx.nil (.all .nat (.imp riccatiSolveInv (riccatiSolveInv.subst Sub.succHere))) :=
  Deriv.allI (Deriv.impI
    (Deriv.exE (ψ := riccatiSolveInv.subst Sub.succHere) Deriv.ax
      (Deriv.exI (.app tmRiccatiStep (.var .here)) riccatiSolveStepCertD)))

/-- `∀k ∃Y. Y solves Y = ∫(1 + Y·Y) below degree k`, proved by `Deriv.ind` on `k`. -/
def riccatiSolveD : Deriv Ctx.nil (.all .nat riccatiSolveInv) :=
  Deriv.ind riccatiSolveBaseD riccatiSolveStepD

/-- First projection of the extracted base case `riccatiSolveBaseD`. -/
theorem extract_riccatiSolveBaseD_fst :
    ((extract riccatiSolveBaseD).eval Env.nil).1 = (tmZeroJet (Γ := [])).eval Env.nil :=
  extract_exI_fst (tmZeroJet (Γ := [])) _

/-- First projection of the extracted induction step `riccatiSolveStepD`. -/
theorem extract_riccatiSolveStepD_fst
    (m : Nat) (ih : (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp) :
    (((extract riccatiSolveStepD).eval Env.nil) m ih).1 =
      ((tmRiccatiStep (Γ := [])).eval Env.nil) ih.1 := by
  unfold riccatiSolveStepD
  rw [extract_step_exI_fst (body := riccatiSolveBody)
    (.app tmRiccatiStep (.var .here)) riccatiSolveStepCertD m ih]
  dsimp [Tm.eval]
  rw [← tmRiccatiStep_rename (Γ := [.nat]) (Δ := [JetTy, .nat]) (Ren.wk JetTy),
      ← tmRiccatiStep_rename (Γ := []) (Δ := [.nat]) (Ren.wk .nat),
      Tm.eval_wk, Tm.eval_wk]
  rfl

/-- The extracted solver at `k` is the `k`-th Picard iterate for the Riccati equation. -/
theorem extractClosed_riccatiSolveD_fst (k : Nat) :
    (((extractClosed riccatiSolveD).eval Env.nil) k).1 = extractedRiccatiJet k := by
  induction k with
  | zero =>
    have h0 := congrArg Prod.fst
      (extractClosed_ind_eval riccatiSolveBaseD riccatiSolveStepD 0)
    exact h0.trans (extract_riccatiSolveBaseD_fst.trans
      (extractClosed_iterSequenceD_zero JetTy tmZeroJet tmRiccatiStep).symm)
  | succ m ih =>
    have hm := congrArg Prod.fst
      (extractClosed_ind_eval riccatiSolveBaseD riccatiSolveStepD m)
    have hs := congrArg Prod.fst
      (extractClosed_ind_eval riccatiSolveBaseD riccatiSolveStepD (m + 1))
    have hstep := extract_riccatiSolveStepD_fst m
      (Nat.rec (motive := fun _ ↦ (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp)
        ((extract riccatiSolveBaseD).eval Env.nil)
        (fun j acc ↦ ((extract riccatiSolveStepD).eval Env.nil) j acc) m)
    rw [← hm] at hstep
    exact hs.trans (hstep.trans ((congrArg ((tmRiccatiStep (Γ := [])).eval Env.nil) ih).trans
      (extractClosed_iterSequenceD_succ JetTy tmZeroJet tmRiccatiStep m).symm))

#print axioms riccatiSolveD
#print axioms extractClosed_riccatiSolveD_fst

end HAomega
