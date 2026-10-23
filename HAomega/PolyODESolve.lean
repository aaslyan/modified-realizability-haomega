/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PolyJetPrefix

/-!
# One proof-computed jet solver for every polynomial–integral ODE

For a closed initial jet `A` and any right-hand side `F : JExpr`, the Picard
operator of `y' = F(y)` with `y = A` at the start is `P(Y) = A + ∫F(Y)`
(`genStep A F`). This module proves, once and for all `A` and `F`,

  `∀k ∃Y. ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)`

— `Y` solves the integral equation below degree `k` — by `Deriv.ind` on `k`,
using `JExpr.prefixT`. The statement names the equation, never the iteration;
the extracted solver is the Picard recursion `Y₀ = A`, `Y_{k+1} = P(Y_k)`
(`extractClosed_genSolveD_fst`).

Instances include `y' = y` (`A = 1, F = Y`), `y' = y²` (`A = 1, F = Y·Y`) and
Riccati (`A = 0, F = 1 + Y·Y`). Systems (Duffing) are not covered: `JExpr`
has one jet variable.
-/

namespace HAomega

/-- The Picard operator `P(Y) = A + ∫F(Y)`. -/
def genStep (A : Tm [] JetTy) (F : JExpr) {Γ : List Ty} : Tm Γ (.arrow JetTy JetTy) :=
  .lam (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm (.var .here))))

/-- Invariant over `.nat :: []`: `∃Y. ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)`. -/
abbrev genSolveInv (A : Tm [] JetTy) (F : JExpr) :=
  let ctx : List Ty := .nat :: .nat :: JetTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let Y : Tm ctx JetTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  (Formula.ex JetTy
    (.all .nat (.all .nat
      (.imp (.eq (.add i (.succ d)) k)
        (.eq (.app (.app (genStep A F (Γ := ctx)) Y) i) (.app Y i))))) :
    Formula (.nat :: []) _)

/-- Renaming leaves `Tm.closedWk` unchanged. -/
@[derivNorm] theorem closedWk_rename {Γ Δ : List Ty} {τ : Ty} (c : Tm [] τ) (ρ : Ren Γ Δ) :
    (Tm.closedWk (Γ := Γ) c).rename ρ = Tm.closedWk (Γ := Δ) c := by
  unfold Tm.closedWk
  rw [Tm.rename_rename]
  congr 1
  funext σ v
  cases v

/-- Substitution leaves `Tm.closedWk` unchanged. -/
@[derivNorm] theorem closedWk_subst {Γ Δ : List Ty} {τ : Ty} (c : Tm [] τ) (s : Sub Γ Δ) :
    (Tm.closedWk (Γ := Γ) c).subst s = Tm.closedWk (Γ := Δ) c := by
  unfold Tm.closedWk
  rw [Tm.subst_rename, ← Tm.subst_id (c.rename _), Tm.subst_rename]
  congr 1
  funext σ v
  cases v

/-- Renaming commutes with `JExpr.toTm`. -/
@[derivNorm] theorem JExpr.toTm_rename (F : JExpr) {Γ Δ : List Ty}
    (y : Tm Γ JetTy) (ρ : Ren Γ Δ) :
    (F.toTm y).rename ρ = F.toTm (y.rename ρ) := by
  induction F with
  | var => rfl
  | const c => exact closedWk_rename c ρ
  | add a b iha ihb =>
    simp only [JExpr.toTm, Tm.rename, tmJetAdd_rename, iha, ihb]
  | sub a b iha ihb =>
    simp only [JExpr.toTm, Tm.rename, tmJetSub_rename, iha, ihb]
  | mul a b iha ihb =>
    simp only [JExpr.toTm, Tm.rename, tmJetMul_rename, iha, ihb]
  | integ a iha =>
    simp only [JExpr.toTm, Tm.rename, tmJetInteg_rename, iha]

/-- Substitution commutes with `JExpr.toTm`. -/
@[derivNorm] theorem JExpr.toTm_subst (F : JExpr) {Γ Δ : List Ty}
    (y : Tm Γ JetTy) (s : Sub Γ Δ) :
    (F.toTm y).subst s = F.toTm (y.subst s) := by
  induction F with
  | var => rfl
  | const c => exact closedWk_subst c s
  | add a b iha ihb =>
    simp only [JExpr.toTm, Tm.subst, tmJetAdd_subst, iha, ihb]
  | sub a b iha ihb =>
    simp only [JExpr.toTm, Tm.subst, tmJetSub_subst, iha, ihb]
  | mul a b iha ihb =>
    simp only [JExpr.toTm, Tm.subst, tmJetMul_subst, iha, ihb]
  | integ a iha =>
    simp only [JExpr.toTm, Tm.subst, tmJetInteg_subst, iha]

/-- Renaming leaves `genStep A F` unchanged. -/
@[derivNorm] theorem genStep_rename (A : Tm [] JetTy) (F : JExpr) {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (genStep A F (Γ := Γ)).rename ρ = genStep A F (Γ := Δ) := by
  simp only [genStep, Tm.rename, tmJetAdd_rename, closedWk_rename, tmJetInteg_rename,
    JExpr.toTm_rename]
  rfl

/-- Substitution leaves `genStep A F` unchanged. -/
@[derivNorm] theorem genStep_subst (A : Tm [] JetTy) (F : JExpr) {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (genStep A F (Γ := Γ)).subst s = genStep A F (Γ := Δ) := by
  simp only [genStep, Tm.subst, tmJetAdd_subst, closedWk_subst, tmJetInteg_subst,
    JExpr.toTm_subst]
  rfl

/-- Applying `genStep A F` to `U, i` converts to `A(i) + jetIntegAt (F.toTm U) i` inside `Deriv`. -/
def genStep_appD (A : Tm [] JetTy) (F : JExpr) {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (genStep A F (Γ := Γ)) U) i)
                 (.qadd (.app (Tm.closedWk A) i) (jetIntegAt (F.toTm U) i))) := by
  have h1 : Deriv Δ (.eq (.app (genStep A F (Γ := Γ)) U)
      (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm U)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm (.var .here)))) U
    deriv_norm at hb
    exact hb
  have h2 := tmJetAdd_appD (Δ := Δ) (Tm.closedWk A) (.app tmJetInteg (F.toTm U)) i
  have h3 := Deriv.congQAdd (Δ := Δ) (Deriv.eqRefl (.app (Tm.closedWk A) i))
    (tmJetInteg_appD (F.toTm U) i)
  exact Deriv.transE (Deriv.congFun h1 i) (Deriv.transE h2 h3)

/-- `genStep A F` applied to `U` at `0` converts to `A(0) + 0` inside `Deriv`. -/
def genStep_zeroD (A : Tm [] JetTy) (F : JExpr) {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app (genStep A F (Γ := Γ)) U) .zero)
                 (.qadd (.app (Tm.closedWk A) .zero) (.qnat .zero))) :=
  Deriv.transE (genStep_appD A F U .zero)
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) .zero))
      (jetIntegZeroD (F.toTm U)))

/-- `genStep A F` applied to `U` at `succ j` converts to `A(succ j) + F(U)(j) / (j + 1)` inside `Deriv`. -/
def genStep_succD (A : Tm [] JetTy) (F : JExpr) {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (genStep A F (Γ := Γ)) U) (.succ j))
                 (.qadd (.app (Tm.closedWk A) (.succ j))
                        (.qdiv (.app (F.toTm U) j) (.qnat (.succ j))))) :=
  Deriv.transE (genStep_appD A F U (.succ j))
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) (.succ j)))
      (jetIntegSuccD (F.toTm U) j))

/-- Inner step of `genSolveIHPrefixT` in context `e :: m :: d :: j :: Y :: k :: []`. -/
def genSolveIHPrefixInnerT (A : Tm [] JetTy) (F : JExpr) {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: .nat :: .nat :: JetTy :: .nat :: []) as}
    (h_ih_wk : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.eq (.app (.app (genStep A F) (.var (.there (.there (.there (.there (.there (.there .here))))))))
              (.var (.there .here)))
          (.app (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var (.there .here))))))))
    (h_succ_wk : Deriv Δ (.eq
      (.add (.succ (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there .here)))))
      (.succ (.var (.there (.there (.there (.there (.there .here)))))))))
    (h_me : Deriv Δ (.eq (.add (.var (.there .here)) (.var .here))
      (.var (.there (.there (.there .here)))))) :
    Deriv Δ (.eq
      (.app (.app (genStep A F) (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))
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

/-- From outer IH `∀i ∀d'. i + succ d' = k → P(Y)(i) = Y(i)` and `succ j + succ d = succ k`, derive `prefixAgree (P(Y)) Y j`. -/
def genSolveIHPrefixT (A : Tm [] JetTy) (F : JExpr) {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: JetTy :: .nat :: []) as}
    (h_ih_all : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there .here)))))))
        (.eq (.app (.app (genStep A F) (.var (.there (.there (.there (.there .here))))))
              (.var (.there .here)))
          (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here))))))))
    (h_eq_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there (.there .here))))))) :
    Deriv Δ (prefixAgree
      (.app (genStep A F (Γ := .nat :: .nat :: JetTy :: .nat :: [])) (.var (.there (.there .here))))
      (.var (.there (.there .here)))
      (.var (.there .here))) := by
  refine Deriv.impE (Deriv.impE ?_ h_ih_all) h_eq_succ
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  exact genSolveIHPrefixInnerT A F (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax

/-- Base case (`k = 0`) of `genSolveD`: `Y₀ = A` vacuously solves below `0`. -/
def genSolveBaseD (A : Tm [] JetTy) (F : JExpr) : Deriv Ctx.nil ((genSolveInv A F).subst1 .zero) := by
  refine Deriv.exI (Tm.closedWk A) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let d : Tm (.nat :: .nat :: []) .nat := .var .here
  let i : Tm (.nat :: .nat :: []) .nat := .var (.there .here)
  exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.add i d))
    (Deriv.transE (Deriv.symmE (Deriv.convAddSucc i d)) Deriv.ax))

/-- Existential body of `genSolveInv A F`. -/
abbrev genSolveBody (A : Tm [] JetTy) (F : JExpr) :
    Formula (JetTy :: .nat :: []) (.arrow .nat (.arrow .nat (.arrow .unit .unit))) :=
  let ctx : List Ty := .nat :: .nat :: JetTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let Y : Tm ctx JetTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  .all .nat (.all .nat
    (.imp (.eq (.add i (.succ d)) k)
      (.eq (.app (.app (genStep A F (Γ := ctx)) Y) i) (.app Y i))))

/-- Inner certificate of `genSolveStepD`: `P(Y)` solves `Z = P(Z)` below degree `succ k`. -/
def genSolveStepCertD (A : Tm [] JetTy) (F : JExpr) :
    Deriv (.cons (genSolveBody A F) (Ctx.cons (genSolveInv A F) Ctx.nil).wk)
      ((((genSolveBody A F).subst (Sub.ext Sub.succHere)).rename (Ren.ext (Ren.wk JetTy))).subst1
        (.app (genStep A F) (.var .here))) := by
  deriv_norm
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let Y₀ : Tm (.nat :: JetTy :: .nat :: []) JetTy := .var (.there .here)
    let P₀ : Tm (.nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := genStep A F
    exact Deriv.transE (genStep_zeroD A F (.app P₀ Y₀))
      (Deriv.symmE (genStep_zeroD A F Y₀))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    let j : Tm (.nat :: .nat :: JetTy :: .nat :: []) .nat := .var (.there .here)
    let Ys : Tm (.nat :: .nat :: JetTy :: .nat :: []) JetTy := .var (.there (.there .here))
    let Ps : Tm (.nat :: .nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := genStep A F
    exact Deriv.transE (genStep_succD A F (.app Ps Ys) j)
      (Deriv.transE
        (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) (.succ j)))
          (Deriv.congQDivNum (.qnat (.succ j))
            (prefixAgreeElimT
              (F.prefixT (.app Ps Ys) Ys j
                (genSolveIHPrefixT A F (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax))
              (Deriv.convAddZero j))))
        (Deriv.symmE (genStep_succD A F Ys j)))

/-- Inductive step (`k → succ k`) of `genSolveD`: map `Y ↦ P(Y)` and split on `i` via `Deriv.ind`. -/
def genSolveStepD (A : Tm [] JetTy) (F : JExpr) :
    Deriv Ctx.nil (.all .nat (.imp (genSolveInv A F) ((genSolveInv A F).subst Sub.succHere))) :=
  Deriv.allI (Deriv.impI
    (Deriv.exE (ψ := (genSolveInv A F).subst Sub.succHere) Deriv.ax
      (Deriv.exI (.app (genStep A F) (.var .here)) (genSolveStepCertD A F))))

/-- Evaluating `Tm.closedWk A` in `Env.nil` yields `A.eval Env.nil`. -/
theorem closedWk_nil_eval {τ : Ty} (A : Tm [] τ) :
    (Tm.closedWk (Γ := []) A).eval Env.nil = A.eval Env.nil := by
  unfold Tm.closedWk
  rw [Tm.eval_rename]
  congr 1
  funext σ v
  cases v

/-- First projection of the extracted base case `genSolveBaseD A F`. -/
theorem extract_genSolveBaseD_fst (A : Tm [] JetTy) (F : JExpr) :
    ((extract (genSolveBaseD A F)).eval Env.nil).1 = A.eval Env.nil :=
  (extract_exI_fst (Tm.closedWk (Γ := []) A) _).trans (closedWk_nil_eval A)

/-- First projection of the extracted induction step `genSolveStepD A F`. -/
theorem extract_genSolveStepD_fst (A : Tm [] JetTy) (F : JExpr)
    (m : Nat) (ih : (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp) :
    (((extract (genSolveStepD A F)).eval Env.nil) m ih).1 =
      ((genStep A F (Γ := [])).eval Env.nil) ih.1 := by
  unfold genSolveStepD
  rw [extract_step_exI_fst (body := genSolveBody A F)
    (.app (genStep A F) (.var .here)) (genSolveStepCertD A F) m ih]
  dsimp [Tm.eval]
  rw [← genStep_rename A F (Γ := [.nat]) (Δ := [JetTy, .nat]) (Ren.wk JetTy),
      ← genStep_rename A F (Γ := []) (Δ := [.nat]) (Ren.wk .nat),
      Tm.eval_wk, Tm.eval_wk]
  rfl

/-- **The general solver.** For every `A` and `F`: `∀k ∃Y. Y solves Y = A + ∫F(Y)
    below degree k`, proved by `Deriv.ind` on `k`. -/
def genSolveD (A : Tm [] JetTy) (F : JExpr) : Deriv Ctx.nil (.all .nat (genSolveInv A F)) :=
  Deriv.ind (genSolveBaseD A F) (genSolveStepD A F)

/-- The extracted solver at `k` is the `k`-th Picard iterate from `A`. -/
theorem extractClosed_genSolveD_fst (A : Tm [] JetTy) (F : JExpr) (k : Nat) :
    (((extractClosed (genSolveD A F)).eval Env.nil) k).1 =
      ((genStep A F (Γ := [])).eval Env.nil)^[k] (A.eval Env.nil) := by
  induction k with
  | zero =>
    have h0 := congrArg Prod.fst
      (extractClosed_ind_eval (genSolveBaseD A F) (genSolveStepD A F) 0)
    exact h0.trans (extract_genSolveBaseD_fst A F)
  | succ m ih =>
    have hm := congrArg Prod.fst
      (extractClosed_ind_eval (genSolveBaseD A F) (genSolveStepD A F) m)
    have hs := congrArg Prod.fst
      (extractClosed_ind_eval (genSolveBaseD A F) (genSolveStepD A F) (m + 1))
    have hstep := extract_genSolveStepD_fst A F m
      (Nat.rec (motive := fun _ ↦ (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp)
        ((extract (genSolveBaseD A F)).eval Env.nil)
        (fun j acc ↦ ((extract (genSolveStepD A F)).eval Env.nil) j acc) m)
    rw [← hm] at hstep
    rw [Function.iterate_succ_apply']
    exact hs.trans (hstep.trans (congrArg ((genStep A F (Γ := [])).eval Env.nil) ih))

#print axioms genSolveD
#print axioms extractClosed_genSolveD_fst

end HAomega
