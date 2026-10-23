/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PicardLockingDeriv

/-!
# A proof-computed jet solver for `y' = y`, `y(0) = 1`

Every analysis program in the catalog so far is witness-style or has an
explicit witness with derived correctness: the specification names the answer
(`Y = P^k(Y₀)`), or the proof writes it at `exI`. This module states the ODE
without naming any algorithm and lets the induction produce the solver.

The ODE `y' = y, y(0) = 1` is stated in integral form `Y = P(Y)`, with
`P(Y) = 1 + ∫Y` the Picard operator `tmPicardExpStep`. The specification says
only that `Y` solves it below degree `k`:

  `∀k ∃Y. ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)`

(`i + succ d = k` is `i < k` without an order primitive; `+` recurses on its
second argument, `convAddSucc`). It names the equation, not the iteration: the
coefficients below `k` are forced to be `1/i!`, but nothing says how to find
them. `picardExpSolveD` proves it by `Deriv.ind` on `k`, so the extracted
solver's recursion comes from the induction.

Out of scope: the differential form `D(Y)(i) = Y(i)` (equivalent via FTC1, not
derived here), and the nonlinear steps.
-/

namespace HAomega

/-- Invariant over `.nat :: []`: `∃Y. ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)`. -/
abbrev picardExpSolveInv :=
  let ctx : List Ty := .nat :: .nat :: JetTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let Y : Tm ctx JetTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  (Formula.ex JetTy
    (.all .nat (.all .nat
      (.imp (.eq (.add i (.succ d)) k)
        (.eq (.app (.app (tmPicardExpStep (Γ := ctx)) Y) i) (.app Y i))))) :
    Formula (.nat :: []) _)

/-- From `succ j + succ d = succ k`, derive `j + succ d = k` inside `Deriv`. -/
def succAddSuccInjT {Γ as : List Ty} {Δ : Ctx Γ as} {j d k : Tm Γ .nat}
    (h : Deriv Δ (.eq (.add (.succ j) (.succ d)) (.succ k))) :
    Deriv Δ (.eq (.add j (.succ d)) k) := by
  have h1 : Deriv Δ (.eq (.succ (.add (.succ j) d)) (.succ k)) :=
    Deriv.transE (Deriv.symmE (Deriv.convAddSucc (.succ j) d)) h
  have h2 : Deriv Δ (.eq (.add (.succ j) d) k) :=
    Deriv.impE (Deriv.succInj (.add (.succ j) d) k) h1
  have h3 : Deriv Δ (.eq (.add j (.succ d)) (.add (.succ j) d)) :=
    Deriv.transE (Deriv.convAddSucc j d) (Deriv.symmE (succPlusT j d))
  exact Deriv.transE h3 h2

/-- Instantiate the outer IH `∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)` at `j, d` and apply it to `succ j + succ d = succ k`. -/
def picardExpSolveIHStepT {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: JetTy :: .nat :: []) as}
    (h_ih_all : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there .here)))))))
        (.eq (.app (.app (tmPicardExpStep (Γ := .nat :: .nat :: .nat :: .nat :: JetTy :: .nat :: []))
                (.var (.there (.there (.there (.there .here))))))
              (.var (.there .here)))
          (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here))))))))
    (h_eq_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there (.there .here))))))) :
    Deriv Δ (.eq
      (.app (.app (tmPicardExpStep (Γ := .nat :: .nat :: JetTy :: .nat :: []))
              (.var (.there (.there .here))))
            (.var (.there .here)))
      (.app (.var (.there (.there .here))) (.var (.there .here)))) := by
  let d : Tm (.nat :: .nat :: JetTy :: .nat :: []) .nat := .var .here
  let j : Tm (.nat :: .nat :: JetTy :: .nat :: []) .nat := .var (.there .here)
  have h_ih := Deriv.allE d (Deriv.allE j h_ih_all)
  deriv_norm at h_ih
  exact Deriv.impE h_ih (succAddSuccInjT h_eq_succ)

/-- Base case (`k = 0`) of `picardExpSolveD`: `Y₀ = 1` vacuously solves below `0`. -/
def picardExpSolveBaseD : Deriv Ctx.nil (picardExpSolveInv.subst1 .zero) := by
  refine Deriv.exI (tmConstOneJet (Γ := [])) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let d : Tm (.nat :: .nat :: []) .nat := .var .here
  let i : Tm (.nat :: .nat :: []) .nat := .var (.there .here)
  exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.add i d))
    (Deriv.transE (Deriv.symmE (Deriv.convAddSucc i d)) Deriv.ax))

/-- Inductive step (`k → succ k`) of `picardExpSolveD`: map `Y ↦ P(Y)` and split on `i` via `Deriv.ind`. -/
def picardExpSolveStepD :
    Deriv Ctx.nil (.all .nat (.imp picardExpSolveInv (picardExpSolveInv.subst Sub.succHere))) := by
  refine Deriv.allI (Deriv.impI ?_)
  refine Deriv.exE (ψ := picardExpSolveInv.subst Sub.succHere) Deriv.ax ?_
  let Y : Tm (JetTy :: .nat :: []) JetTy := .var .here
  let P : Tm (JetTy :: .nat :: []) (.arrow JetTy JetTy) := tmPicardExpStep
  refine Deriv.exI (.app P Y) ?_
  deriv_norm
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let Y₀ : Tm (.nat :: JetTy :: .nat :: []) JetTy := .var (.there .here)
    let P₀ : Tm (.nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := tmPicardExpStep
    exact Deriv.transE (tmPicardExpStep_zeroD (.app P₀ Y₀))
      (Deriv.symmE (tmPicardExpStep_zeroD Y₀))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let j : Tm (.nat :: .nat :: JetTy :: .nat :: []) .nat := .var (.there .here)
    let Ys : Tm (.nat :: .nat :: JetTy :: .nat :: []) JetTy := .var (.there (.there .here))
    let Ps : Tm (.nat :: .nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := tmPicardExpStep
    exact Deriv.transE (tmPicardExpStep_succD (.app Ps Ys) j)
      (Deriv.transE
        (Deriv.congQDivNum (.qnat (.succ j))
          (picardExpSolveIHStepT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax))
        (Deriv.symmE (tmPicardExpStep_succD Ys j)))

/-- First projection of the extracted base case `picardExpSolveBaseD`. -/
theorem extract_picardExpSolveBaseD_fst :
    ((extract picardExpSolveBaseD).eval Env.nil).1 = (tmConstOneJet (Γ := [])).eval Env.nil :=
  extract_exI_fst (tmConstOneJet (Γ := [])) _

/-- First projection of the extracted induction step `picardExpSolveStepD`. -/
theorem extract_picardExpSolveStepD_fst
    (m : Nat) (ih : (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp) :
    (((extract picardExpSolveStepD).eval Env.nil) m ih).1 =
      ((tmPicardExpStep (Γ := [])).eval Env.nil) ih.1 := by
  unfold picardExpSolveStepD
  dsimp [extract, Tm.eval]
  rw [Tm.eval_rename]
  dsimp [Tm.eval]
  rw [Tm.eval_rename]
  dsimp [Tm.eval]
  rw [Tm.eval_rename]
  rfl

/-- `∀k ∃Y. Y solves Y = P(Y) below degree k`, proved by `Deriv.ind` on `k`. -/
def picardExpSolveD : Deriv Ctx.nil (.all .nat picardExpSolveInv) :=
  Deriv.ind picardExpSolveBaseD picardExpSolveStepD

/-- The extracted solver at `k` is the `k`-th Picard iterate. -/
theorem extractClosed_picardExpSolveD_fst (k : Nat) :
    (((extractClosed picardExpSolveD).eval Env.nil) k).1 = extractedPicardJet k := by
  induction k with
  | zero =>
    have h0 := congrArg Prod.fst
      (extractClosed_ind_eval picardExpSolveBaseD picardExpSolveStepD 0)
    exact h0.trans (extract_picardExpSolveBaseD_fst.trans
      (extractClosed_iterSequenceD_zero JetTy tmConstOneJet tmPicardExpStep).symm)
  | succ m ih =>
    have hm := congrArg Prod.fst
      (extractClosed_ind_eval picardExpSolveBaseD picardExpSolveStepD m)
    have hs := congrArg Prod.fst
      (extractClosed_ind_eval picardExpSolveBaseD picardExpSolveStepD (m + 1))
    have hstep := extract_picardExpSolveStepD_fst m
      (Nat.rec (motive := fun _ ↦ (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp)
        ((extract picardExpSolveBaseD).eval Env.nil)
        (fun j acc ↦ ((extract picardExpSolveStepD).eval Env.nil) j acc) m)
    rw [← hm] at hstep
    exact hs.trans (hstep.trans ((congrArg ((tmPicardExpStep (Γ := [])).eval Env.nil) ih).trans
      (extractClosed_iterSequenceD_succ JetTy tmConstOneJet tmPicardExpStep m).symm))

#print axioms picardExpSolveD
#print axioms extractClosed_picardExpSolveD_fst

end HAomega
