/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PolyODESystem

/-!
# Proof-computed inverses: fixed points guarded by the shift `x·F`

Closed-universe pillar 4. `1/(1 − G)` for `G(0) = 0` is the solution of
`Y = 1 + G·Y`, but on the unnormalized `Q` the guard `G(0)·Y(i)` is not
structurally `0` (`0·x` keeps `x`'s denominator). The guard is made
structural instead: every `G` with `G(0) = 0` is `x·H` for the shift
`(x·F)(0) = 0`, `(x·F)(n+1) = F(n)` (`tmJetShift`), which guards like `∫`
but without division.

`shiftSolveD A F`, for every closed `A` and every `F : JExpr`, proves

  `∀k ∃Y. ∀i ∀d. i + succ d = k → (A + x·F(Y))(i) = Y(i)`

by `Deriv.ind` on `k`, resting on `JExpr.prefixT`; the extract is the
fixed-point iteration. Instances: `1/(1 − x·H)` is `A = 1, F = H·Y`; with
`H = 1 + x` it is the Fibonacci generating function `1/(1 − x − x²)`, whose
coefficients the extract reproduces (`shiftSolve_fib`).
-/

namespace HAomega

/-- The shift `(x·c)(0) = 0`, `(x·c)(n+1) = c(n)`. -/
def tmJetShift {Γ : List Ty} : Tm Γ (.arrow JetTy JetTy) :=
  .lam (.lam (.recNat (.qnat .zero)
    (.lam (.lam (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))))
    (.var .here)))

/-- The guarded operator `P(Y) = A + x·F(Y)`. -/
def shiftStep (A : Tm [] JetTy) (F : JExpr) {Γ : List Ty} : Tm Γ (.arrow JetTy JetTy) :=
  .lam (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetShift (F.toTm (.var .here))))

/-- Invariant over `.nat :: []`: `∃Y. ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)`. -/
abbrev shiftSolveInv (A : Tm [] JetTy) (F : JExpr) :=
  let ctx : List Ty := .nat :: .nat :: JetTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let Y : Tm ctx JetTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  (Formula.ex JetTy
    (.all .nat (.all .nat
      (.imp (.eq (.add i (.succ d)) k)
        (.eq (.app (.app (shiftStep A F (Γ := ctx)) Y) i) (.app Y i))))) :
    Formula (.nat :: []) _)

/-- Renaming leaves `tmJetShift` unchanged. -/
@[derivNorm] theorem tmJetShift_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetShift (Γ := Γ)).rename ρ = tmJetShift (Γ := Δ) := rfl

/-- Substitution leaves `tmJetShift` unchanged. -/
@[derivNorm] theorem tmJetShift_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetShift (Γ := Γ)).subst s = tmJetShift (Γ := Δ) := rfl

/-- Renaming leaves `shiftStep A F` unchanged. -/
@[derivNorm] theorem shiftStep_rename (A : Tm [] JetTy) (F : JExpr) {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (shiftStep A F (Γ := Γ)).rename ρ = shiftStep A F (Γ := Δ) := by
  simp only [shiftStep, Tm.rename, tmJetAdd_rename, closedWk_rename, tmJetShift_rename,
    JExpr.toTm_rename]
  rfl

/-- Substitution leaves `shiftStep A F` unchanged. -/
@[derivNorm] theorem shiftStep_subst (A : Tm [] JetTy) (F : JExpr) {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (shiftStep A F (Γ := Γ)).subst s = shiftStep A F (Γ := Δ) := by
  simp only [shiftStep, Tm.subst, tmJetAdd_subst, closedWk_subst, tmJetShift_subst,
    JExpr.toTm_subst]
  rfl

/-- Step functional inside `tmJetShift` applied to `c`: `λ k acc. c(k)`. -/
def jetShiftStep {Γ : List Ty} (c : Tm Γ JetTy) : Tm Γ (.arrow .nat (.arrow .rat .rat)) :=
  .lam (.lam (.app ((c.wk (σ := .nat)).wk (σ := .rat)) (.var (.there .here))))

/-- Open System T shift of jet `c` at index `n`: `recNat 0 (jetShiftStep c) n`. -/
def jetShiftAt {Γ : List Ty} (c : Tm Γ JetTy) (n : Tm Γ .nat) : Tm Γ .rat :=
  .recNat (.qnat .zero) (jetShiftStep c) n

attribute [derivNorm] jetShiftStep jetShiftAt

/-- Applying `tmJetShift` to `c, i` converts to `jetShiftAt c i` inside `Deriv`. -/
def tmJetShift_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (c : Tm Γ JetTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (tmJetShift (Γ := Γ)) c) i) (jetShiftAt c i)) := by
  have h1 : Deriv Δ (.eq (.app (tmJetShift (Γ := Γ)) c) (.lam (jetShiftAt c.wk (.var .here)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (.recNat (.qnat .zero)
        (.lam (.lam (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))))
        (.var .here))) c
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq (.app (.lam (jetShiftAt c.wk (.var .here))) i) (jetShiftAt c i)) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (jetShiftAt c.wk (.var .here)) i
    deriv_norm at hb
    exact hb
  exact Deriv.transE (Deriv.congFun h1 i) h2

/-- Applying `tmJetShift` to `c, 0` converts to `0` inside `Deriv`. -/
def tmJetShift_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} (c : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app (tmJetShift (Γ := Γ)) c) .zero) (.qnat .zero)) :=
  Deriv.transE (tmJetShift_appD c .zero)
    (Deriv.convRecZero (.qnat .zero) (jetShiftStep c))

/-- Applying `tmJetShift` to `c, succ j` converts to `c(j)` inside `Deriv`. -/
def tmJetShift_succD {Γ as : List Ty} {Δ : Ctx Γ as}
    (c : Tm Γ JetTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (tmJetShift (Γ := Γ)) c) (.succ j)) (.app c j)) := by
  have hrec := Deriv.convRecSucc (Δ := Δ) (.qnat .zero) (jetShiftStep c) j
  have hb1 : Deriv Δ (.eq (.app (jetShiftStep c) j)
      (.lam (.app (c.wk (σ := .rat)) j.wk))) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.lam (.app ((c.wk (σ := .nat)).wk (σ := .rat)) (.var (.there .here)))) j
    deriv_norm at h
    exact h
  have hb2 : Deriv Δ (.eq
      (.app (.lam (.app (c.wk (σ := .rat)) j.wk)) (jetShiftAt c j))
      (.app c j)) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .rat)
      (.app (c.wk (σ := .rat)) j.wk) (jetShiftAt c j)
    deriv_norm at h
    exact h
  exact Deriv.transE (tmJetShift_appD c (.succ j))
    (Deriv.transE hrec (Deriv.transE (Deriv.congFun hb1 (jetShiftAt c j)) hb2))

/-- Applying `shiftStep A F` to `U, i` converts to `A(i) + (x · F(U))(i)` inside `Deriv`. -/
def shiftStep_appD (A : Tm [] JetTy) (F : JExpr) {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (shiftStep A F (Γ := Γ)) U) i)
                 (.qadd (.app (Tm.closedWk A) i) (.app (.app tmJetShift (F.toTm U)) i))) := by
  have h1 : Deriv Δ (.eq (.app (shiftStep A F (Γ := Γ)) U)
      (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetShift (F.toTm U)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetShift (F.toTm (.var .here)))) U
    deriv_norm at hb
    exact hb
  have h2 := tmJetAdd_appD (Δ := Δ) (Tm.closedWk A) (.app tmJetShift (F.toTm U)) i
  exact Deriv.transE (Deriv.congFun h1 i) h2

/-- `shiftStep A F` applied to `U` at `0` converts to `A(0) + 0` inside `Deriv`. -/
def shiftStep_zeroD (A : Tm [] JetTy) (F : JExpr) {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app (shiftStep A F (Γ := Γ)) U) .zero)
                 (.qadd (.app (Tm.closedWk A) .zero) (.qnat .zero))) :=
  Deriv.transE (shiftStep_appD A F U .zero)
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) .zero))
      (tmJetShift_zeroD (F.toTm U)))

/-- `shiftStep A F` applied to `U` at `succ j` converts to `A(succ j) + F(U)(j)` inside `Deriv`. -/
def shiftStep_succD (A : Tm [] JetTy) (F : JExpr) {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (shiftStep A F (Γ := Γ)) U) (.succ j))
                 (.qadd (.app (Tm.closedWk A) (.succ j)) (.app (F.toTm U) j))) :=
  Deriv.transE (shiftStep_appD A F U (.succ j))
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) (.succ j)))
      (tmJetShift_succD (F.toTm U) j))

/-- Inner step of `shiftSolveIHPrefixT` in context `e :: m :: d :: j :: Y :: k :: []`. -/
def shiftSolveIHPrefixInnerT (A : Tm [] JetTy) (F : JExpr) {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: .nat :: .nat :: JetTy :: .nat :: []) as}
    (h_ih_wk : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.eq (.app (.app (shiftStep A F) (.var (.there (.there (.there (.there (.there (.there .here))))))))
              (.var (.there .here)))
          (.app (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var (.there .here))))))))
    (h_succ_wk : Deriv Δ (.eq
      (.add (.succ (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there .here)))))
      (.succ (.var (.there (.there (.there (.there (.there .here)))))))))
    (h_me : Deriv Δ (.eq (.add (.var (.there .here)) (.var .here))
      (.var (.there (.there (.there .here)))))) :
    Deriv Δ (.eq
      (.app (.app (shiftStep A F) (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))
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
def shiftSolveIHPrefixT (A : Tm [] JetTy) (F : JExpr) {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: JetTy :: .nat :: []) as}
    (h_ih_all : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there .here)))))))
        (.eq (.app (.app (shiftStep A F) (.var (.there (.there (.there (.there .here))))))
              (.var (.there .here)))
          (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here))))))))
    (h_eq_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there (.there .here))))))) :
    Deriv Δ (prefixAgree
      (.app (shiftStep A F (Γ := .nat :: .nat :: JetTy :: .nat :: [])) (.var (.there (.there .here))))
      (.var (.there (.there .here)))
      (.var (.there .here))) := by
  refine Deriv.impE (Deriv.impE ?_ h_ih_all) h_eq_succ
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  exact shiftSolveIHPrefixInnerT A F (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax

/-- Base case (`k = 0`) of `shiftSolveD`: `Y₀ = A` vacuously solves below `0`. -/
def shiftSolveBaseD (A : Tm [] JetTy) (F : JExpr) : Deriv Ctx.nil ((shiftSolveInv A F).subst1 .zero) := by
  refine Deriv.exI (Tm.closedWk A) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let d : Tm (.nat :: .nat :: []) .nat := .var .here
  let i : Tm (.nat :: .nat :: []) .nat := .var (.there .here)
  exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.add i d))
    (Deriv.transE (Deriv.symmE (Deriv.convAddSucc i d)) Deriv.ax))

/-- Existential body of `shiftSolveInv A F`. -/
abbrev shiftSolveBody (A : Tm [] JetTy) (F : JExpr) :
    Formula (JetTy :: .nat :: []) (.arrow .nat (.arrow .nat (.arrow .unit .unit))) :=
  let ctx : List Ty := .nat :: .nat :: JetTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let Y : Tm ctx JetTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  .all .nat (.all .nat
    (.imp (.eq (.add i (.succ d)) k)
      (.eq (.app (.app (shiftStep A F (Γ := ctx)) Y) i) (.app Y i))))

/-- Inner certificate of `shiftSolveStepD`: `P(Y)` solves `Z = P(Z)` below degree `succ k`. -/
def shiftSolveStepCertD (A : Tm [] JetTy) (F : JExpr) :
    Deriv (.cons (shiftSolveBody A F) (Ctx.cons (shiftSolveInv A F) Ctx.nil).wk)
      ((((shiftSolveBody A F).subst (Sub.ext Sub.succHere)).rename (Ren.ext (Ren.wk JetTy))).subst1
        (.app (shiftStep A F) (.var .here))) := by
  deriv_norm
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let Y₀ : Tm (.nat :: JetTy :: .nat :: []) JetTy := .var (.there .here)
    let P₀ : Tm (.nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := shiftStep A F
    exact Deriv.transE (shiftStep_zeroD A F (.app P₀ Y₀))
      (Deriv.symmE (shiftStep_zeroD A F Y₀))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    let j : Tm (.nat :: .nat :: JetTy :: .nat :: []) .nat := .var (.there .here)
    let Ys : Tm (.nat :: .nat :: JetTy :: .nat :: []) JetTy := .var (.there (.there .here))
    let Ps : Tm (.nat :: .nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := shiftStep A F
    exact Deriv.transE (shiftStep_succD A F (.app Ps Ys) j)
      (Deriv.transE
        (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) (.succ j)))
          (prefixAgreeElimT
            (F.prefixT (.app Ps Ys) Ys j
              (shiftSolveIHPrefixT A F (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax))
            (Deriv.convAddZero j)))
        (Deriv.symmE (shiftStep_succD A F Ys j)))

/-- Inductive step (`k → succ k`) of `shiftSolveD`: map `Y ↦ P(Y)` and split on `i` via `Deriv.ind`. -/
def shiftSolveStepD (A : Tm [] JetTy) (F : JExpr) :
    Deriv Ctx.nil (.all .nat (.imp (shiftSolveInv A F) ((shiftSolveInv A F).subst Sub.succHere))) :=
  Deriv.allI (Deriv.impI
    (Deriv.exE (ψ := (shiftSolveInv A F).subst Sub.succHere) Deriv.ax
      (Deriv.exI (.app (shiftStep A F) (.var .here)) (shiftSolveStepCertD A F))))

/-- **The shift-guarded solver**, for every `A` and `F`, by `Deriv.ind` on `k`. -/
def shiftSolveD (A : Tm [] JetTy) (F : JExpr) :
    Deriv Ctx.nil (.all .nat (shiftSolveInv A F)) :=
  Deriv.ind (shiftSolveBaseD A F) (shiftSolveStepD A F)

/-- First projection of the extracted base case `shiftSolveBaseD A F`. -/
theorem extract_shiftSolveBaseD_fst (A : Tm [] JetTy) (F : JExpr) :
    ((extract (shiftSolveBaseD A F)).eval Env.nil).1 = A.eval Env.nil :=
  (extract_exI_fst (Tm.closedWk (Γ := []) A) _).trans (closedWk_nil_eval A)

/-- First projection of the extracted induction step `shiftSolveStepD A F`. -/
theorem extract_shiftSolveStepD_fst (A : Tm [] JetTy) (F : JExpr)
    (m : Nat) (ih : (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp) :
    (((extract (shiftSolveStepD A F)).eval Env.nil) m ih).1 =
      ((shiftStep A F (Γ := [])).eval Env.nil) ih.1 := by
  unfold shiftSolveStepD
  rw [extract_step_exI_fst (body := shiftSolveBody A F)
    (.app (shiftStep A F) (.var .here)) (shiftSolveStepCertD A F) m ih]
  dsimp [Tm.eval]
  rw [← shiftStep_rename A F (Γ := [.nat]) (Δ := [JetTy, .nat]) (Ren.wk JetTy),
      ← shiftStep_rename A F (Γ := []) (Δ := [.nat]) (Ren.wk .nat),
      Tm.eval_wk, Tm.eval_wk]
  rfl

/-- The extracted solver at `k` is the `k`-th iterate of `P` from `A`. -/
theorem extractClosed_shiftSolveD_fst (A : Tm [] JetTy) (F : JExpr) (k : Nat) :
    (((extractClosed (shiftSolveD A F)).eval Env.nil) k).1 =
      ((shiftStep A F (Γ := [])).eval Env.nil)^[k] (A.eval Env.nil) := by
  induction k with
  | zero =>
    have h0 := congrArg Prod.fst
      (extractClosed_ind_eval (shiftSolveBaseD A F) (shiftSolveStepD A F) 0)
    exact h0.trans (extract_shiftSolveBaseD_fst A F)
  | succ m ih =>
    have hm := congrArg Prod.fst
      (extractClosed_ind_eval (shiftSolveBaseD A F) (shiftSolveStepD A F) m)
    have hs := congrArg Prod.fst
      (extractClosed_ind_eval (shiftSolveBaseD A F) (shiftSolveStepD A F) (m + 1))
    have hstep := extract_shiftSolveStepD_fst A F m
      (Nat.rec (motive := fun _ ↦ (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp)
        ((extract (shiftSolveBaseD A F)).eval Env.nil)
        (fun j acc ↦ ((extract (shiftSolveStepD A F)).eval Env.nil) j acc) m)
    rw [← hm] at hstep
    rw [Function.iterate_succ_apply']
    exact hs.trans (hstep.trans (congrArg ((shiftStep A F (Γ := [])).eval Env.nil) ih))

/-- The jet `1 + x`. -/
def tmOnePlusX : Tm [] JetTy := .app (.app tmJetAdd tmConstOneJet) (.app tmJetShift tmConstOneJet)

/-- Evaluating `Tm.closedWk A` in any environment `e` yields `A.eval Env.nil`. -/
theorem closedWk_eval {Γ : List Ty} {τ : Ty} (A : Tm [] τ) (e : Env Γ) :
    (Tm.closedWk (Γ := Γ) A).eval e = A.eval Env.nil := by
  unfold Tm.closedWk
  rw [Tm.eval_rename]
  congr 1
  funext σ v
  cases v

/-- Normalizing `Int.ofNat m` over denominator `1` yields `Q.ofNat m`. -/
theorem Q.of_ofNat_one (m : Nat) : Q.of (Int.ofNat m) 1 = Q.ofNat m := by
  unfold Q.of
  have habs : (Int.ofNat m).natAbs = m := rfl
  rw [if_neg Nat.one_ne_zero, habs, Nat.gcd_one_right, if_neg Nat.one_ne_zero]
  change ⟨Int.tdiv (Int.ofNat m) 1, 0⟩ = Q.ofNat m
  rw [Int.tdiv_one]
  rfl

/-- Adding two `Q.ofNat` values yields `Q.ofNat` of their sum. -/
theorem Q.add_ofNat (a b : Nat) : Q.add (Q.ofNat a) (Q.ofNat b) = Q.ofNat (a + b) := by
  have hnum : Int.add (Int.mul (Q.ofNat a).num (Int.ofNat (Q.ofNat b).den))
      (Int.mul (Q.ofNat b).num (Int.ofNat (Q.ofNat a).den)) = Int.ofNat (a + b) := by
    show (a : Int) * 1 + (b : Int) * 1 = ((a + b : Nat) : Int)
    omega
  unfold Q.add
  rw [hnum]
  exact Q.of_ofNat_one (a + b)

/-- Multiplying two `Q.ofNat` values yields `Q.ofNat` of their product. -/
theorem Q.mul_ofNat (a b : Nat) : Q.mul (Q.ofNat a) (Q.ofNat b) = Q.ofNat (a * b) := by
  have hnum : Int.mul (Q.ofNat a).num (Q.ofNat b).num = Int.ofNat (a * b) := rfl
  unfold Q.mul
  rw [hnum]
  exact Q.of_ofNat_one (a * b)

/-- Multiplying `Q.ofNat 0` on the left by any `q : Q` yields `Q.ofNat 0`. -/
theorem Q.mul_zero_left (q : Q) : Q.mul (Q.ofNat 0) q = Q.ofNat 0 := by
  have hnum : Int.mul (Q.ofNat 0).num q.num = 0 := Int.zero_mul q.num
  have hden : (Q.ofNat 0).den * q.den = q.den := Nat.one_mul q.den
  unfold Q.mul
  rw [hnum, hden]
  unfold Q.of
  rw [if_neg q.den_ne_zero]
  have habs : (0 : Int).natAbs = 0 := rfl
  rw [habs, Nat.gcd_zero_left, if_neg q.den_ne_zero,
      Nat.div_self (Nat.pos_of_ne_zero q.den_ne_zero)]
  change ⟨Int.tdiv 0 (Int.ofNat q.den), 0⟩ = Q.ofNat 0
  have htd : Int.tdiv 0 (Int.ofNat q.den) = 0 := by simp [Int.tdiv, Nat.zero_div]
  rw [htd]
  rfl

/-- All coefficients of `tmOnePlusX` at degree `l + 2` are `Q.ofNat 0`. -/
theorem tmOnePlusX_eval_ge_two (l : Nat) :
    (tmOnePlusX.eval Env.nil) (l + 2) = Q.ofNat 0 := by
  change Q.add (Q.ofNat 0) (Q.ofNat 0) = Q.ofNat 0
  exact Q.add_ofNat 0 0

/-- Beyond index `2`, the Cauchy convolution sum with `tmOnePlusX` is constant. -/
theorem cauchyConvAux_onePlusX_ge_two (Y : Nat → Q) (n m : Nat)
    (h2 : Jet.cauchyConvAux ⟨tmOnePlusX.eval Env.nil⟩ ⟨Y⟩ n 2 = Q.ofNat m) :
    ∀ l : Nat, Jet.cauchyConvAux ⟨tmOnePlusX.eval Env.nil⟩ ⟨Y⟩ n (l + 2) = Q.ofNat m
  | 0 => h2
  | l + 1 => by
    show Q.add (Jet.cauchyConvAux ⟨tmOnePlusX.eval Env.nil⟩ ⟨Y⟩ n (l + 2))
      (Q.mul ((tmOnePlusX.eval Env.nil) (l + 2)) (Y (n - (l + 2)))) = Q.ofNat m
    rw [cauchyConvAux_onePlusX_ge_two Y n m h2 l, tmOnePlusX_eval_ge_two l,
        Q.mul_zero_left, Q.add_ofNat, Nat.add_zero]

/-- At degree `0`, the Cauchy product of `tmOnePlusX` and `Y` equals `Q.ofNat a` when `Y 0 = Q.ofNat a`. -/
theorem mul_onePlusX_zero (Y : Nat → Q) (a : Nat) (h0 : Y 0 = Q.ofNat a) :
    ((Jet.mk (tmOnePlusX.eval Env.nil)).mul (Jet.mk Y)).coeff 0 = Q.ofNat a := by
  change Q.add (Q.ofNat 0) (Q.mul (Q.add (Q.ofNat 1) (Q.ofNat 0)) (Y 0)) = Q.ofNat a
  rw [h0, Q.add_ofNat, Q.mul_ofNat, Q.add_ofNat]
  simp

/-- At degree `n + 1`, the Cauchy product of `tmOnePlusX` and `Y` equals `Q.ofNat (a + b)` when `Y (n + 1) = Q.ofNat a` and `Y n = Q.ofNat b`. -/
theorem mul_onePlusX_succ (Y : Nat → Q) (n a b : Nat)
    (h1 : Y (n + 1) = Q.ofNat a) (h0 : Y n = Q.ofNat b) :
    ((Jet.mk (tmOnePlusX.eval Env.nil)).mul (Jet.mk Y)).coeff (n + 1) = Q.ofNat (a + b) := by
  have hconv2 : Jet.cauchyConvAux ⟨tmOnePlusX.eval Env.nil⟩ ⟨Y⟩ (n + 1) 2 = Q.ofNat (a + b) := by
    change Q.add (Q.add (Q.ofNat 0) (Q.mul (Q.add (Q.ofNat 1) (Q.ofNat 0)) (Y (n + 1))))
      (Q.mul (Q.add (Q.ofNat 0) (Q.ofNat 1)) (Y n)) = Q.ofNat (a + b)
    rw [h1, h0, Q.add_ofNat, Q.add_ofNat, Q.mul_ofNat, Q.mul_ofNat, Q.add_ofNat, Q.add_ofNat]
    simp
  exact cauchyConvAux_onePlusX_ge_two Y (n + 1) (a + b) hconv2 n

/-- At index `0`, `shiftStep A (.mul (.const C) .var)` evaluates to `Q.add (A.eval Env.nil 0) (Q.ofNat 0)`. -/
theorem shiftStep_mul_const_zero (A C : Tm [] JetTy) (Y : Nat → Q) :
    (((shiftStep A (.mul (.const C) .var) (Γ := [])).eval Env.nil) Y) 0 =
      Q.add (A.eval Env.nil 0) (Q.ofNat 0) := by
  change Q.add ((Tm.closedWk A).eval (Env.cons (σ := JetTy) Y Env.nil) 0) (Q.ofNat 0) = _
  rw [closedWk_eval]

/-- At index `j + 1`, `shiftStep A (.mul (.const C) .var)` evaluates to `Q.add (A.eval Env.nil (j + 1)) (((Jet.mk (C.eval Env.nil)).mul (Jet.mk Y)).coeff j)`. -/
theorem shiftStep_mul_const_succ (A C : Tm [] JetTy) (Y : Nat → Q) (j : Nat) :
    (((shiftStep A (.mul (.const C) .var) (Γ := [])).eval Env.nil) Y) (j + 1) =
      Q.add (A.eval Env.nil (j + 1)) (((Jet.mk (C.eval Env.nil)).mul (Jet.mk Y)).coeff j) := by
  change Q.add ((Tm.closedWk A).eval (Env.cons (σ := JetTy) Y Env.nil) (j + 1))
    (((tmJetMul (Γ := [JetTy])).eval (Env.cons (σ := JetTy) Y Env.nil)
      ((Tm.closedWk C).eval (Env.cons (σ := JetTy) Y Env.nil)) Y) j) = _
  rw [closedWk_eval, tmJetMul_eval_fun, closedWk_eval]

/-- Below degree `k`, the `k`-th iterate of the Fibonacci shift operator produces `Q.ofNat (Nat.fib (i + 1))`. -/
theorem shiftStep_fib_iterate : ∀ (k i : Nat), i < k →
    (((shiftStep tmConstOneJet (.mul (.const tmOnePlusX) .var) (Γ := [])).eval Env.nil)^[k]
      ((tmConstOneJet (Γ := [])).eval Env.nil)) i = Q.ofNat (Nat.fib (i + 1))
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, 0, _ => by
    rw [Function.iterate_succ_apply', shiftStep_mul_const_zero]
    change Q.add (Q.ofNat 1) (Q.ofNat 0) = Q.ofNat 1
    exact Q.add_ofNat 1 0
  | m + 1, 1, hi => by
    have hm : 0 < m := Nat.lt_of_succ_lt_succ hi
    have ih0 := shiftStep_fib_iterate m 0 hm
    rw [Function.iterate_succ_apply', shiftStep_mul_const_succ _ _ _ 0,
        mul_onePlusX_zero _ (Nat.fib 1) ih0]
    change Q.add (Q.ofNat 0) (Q.ofNat 1) = Q.ofNat 1
    exact Q.add_ofNat 0 1
  | m + 1, n + 2, hi => by
    have hn1 : n + 1 < m := Nat.lt_of_succ_lt_succ hi
    have hn0 : n < m := Nat.lt_trans (Nat.lt_succ_self n) hn1
    have ih1 := shiftStep_fib_iterate m (n + 1) hn1
    have ih0 := shiftStep_fib_iterate m n hn0
    rw [Function.iterate_succ_apply', shiftStep_mul_const_succ _ _ _ (n + 1),
        mul_onePlusX_succ _ n (Nat.fib (n + 2)) (Nat.fib (n + 1)) ih1 ih0]
    change Q.add (Q.ofNat 0) (Q.ofNat (Nat.fib (n + 2) + Nat.fib (n + 1))) =
      Q.ofNat (Nat.fib (n + 1 + 2))
    rw [Q.add_ofNat, Nat.zero_add, Nat.add_comm, ← Nat.fib_add_two]

/-- `1/(1 − x − x²)`: below degree `k`, the `k`-th iterate has the Fibonacci
    numbers `F(i+1)` as coefficients (exactly, as `Q` values). -/
theorem shiftSolve_fib (k i : Nat) (hi : i < k) :
    (((extractClosed (shiftSolveD tmConstOneJet (.mul (.const tmOnePlusX) .var))).eval
      Env.nil) k).1 i = Q.ofNat (Nat.fib (i + 1)) := by
  rw [extractClosed_shiftSolveD_fst]
  exact shiftStep_fib_iterate k i hi

#print axioms shiftSolveD
#print axioms extractClosed_shiftSolveD_fst
#print axioms shiftSolve_fib

end HAomega
