/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PicardLocking

/-!
# Degree locking inside `Deriv` for the linear Picard solver `y' = y`

`PicardLocking.lean` proves degree locking in the metatheory. This module
states the diagonal case inside the object logic for the linear step
`tmPicardExpStep`: for every `k`, the `k`-th iterate `Y` satisfies
`P(Y)(k) = Y(k)`, derived by `Deriv.ind` on `k`.

The linear case closes by induction on `k` alone because `P(Y)(k+1)` depends
only on `Y(k)`. The nonlinear steps (Riccati, blow-up, Duffing) are not
covered: their Cauchy-product coefficient depends on the whole prefix, which
would need prefix agreement and order on `ℕ` in the object logic.

The specification still names the iterate (`iterTm`), so catalog #22 stays
witness-style; the locking conjunct is an equation, hence contentless.
-/

namespace HAomega

/-- Congruence in the numerator of `Tm.qdiv`. -/
def Deriv.congQDivNum {Γ as : List Ty} {Δ : Ctx Γ as} {s s' : Tm Γ .rat} (d : Tm Γ .rat)
    (h : Deriv Δ (.eq s s')) : Deriv Δ (.eq (.qdiv s d) (.qdiv s' d)) := by
  have hs : ∀ u : Tm Γ .rat,
      (Formula.eq (.qdiv s.wk d.wk) (.qdiv (.var .here) d.wk)).subst1 u
        = Formula.eq (.qdiv s d) (.qdiv u d) := by
    intro u
    show Formula.eq (.qdiv (s.wk.subst1 u) (d.wk.subst1 u)) (.qdiv u (d.wk.subst1 u)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.qdiv s.wk d.wk) (.qdiv (.var .here) d.wk)) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key

/-- The inner recursor step term of `tmPicardExpStep` specialized to a jet term `U`. -/
def picardExpDivStep {Γ : List Ty} (U : Tm Γ JetTy) : Tm Γ (.arrow .nat (.arrow .rat .rat)) :=
  .lam (.lam (.qdiv (.app U.wk.wk (.var (.there .here)))
                    (.qnat (.succ (.var (.there .here))))))

/-- `tmConstOneJet` evaluated at `0` converts to `1` inside `Deriv`. -/
def tmConstOneJet_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app (tmConstOneJet (Γ := Γ)) .zero) (.qnat (.succ .zero))) :=
  Deriv.transE
    (Deriv.convBeta (.recNat (.qnat (.succ .zero)) (.lam (.lam (.qnat .zero))) (.var .here)) .zero)
    (Deriv.convRecZero (.qnat (.succ .zero)) (.lam (.lam (.qnat .zero))))

/-- Substitution of `m` into the inner `recNat` body of `tmPicardExpStep`. -/
theorem picardExpStep_inner_subst {Γ : List Ty} (U : Tm Γ JetTy) (m : Tm Γ .nat) :
    (Tm.recNat (.qnat (.succ .zero)) (picardExpDivStep (U.wk (σ := .nat))) (.var .here)).subst1 m =
      Tm.recNat (.qnat (.succ .zero)) (picardExpDivStep U) m := by
  simp only [picardExpDivStep, Tm.subst1, Tm.subst, Tm.wk_subst_ext, Tm.wk_subst_one]
  rfl

/-- Applying `tmPicardExpStep` to `U` and `m` converts to the underlying `recNat` term. -/
def tmPicardExpStep_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (tmPicardExpStep (Γ := Γ)) U) m)
                 (.recNat (.qnat (.succ .zero)) (picardExpDivStep U) m)) := by
  have h1 : Deriv Δ (.eq (.app (tmPicardExpStep (Γ := Γ)) U)
      (.lam (.recNat (.qnat (.succ .zero)) (picardExpDivStep (U.wk (σ := .nat))) (.var .here)))) :=
    Deriv.convBeta _ U
  have h2 : Deriv Δ (.eq
      (.app (.lam (.recNat (.qnat (.succ .zero)) (picardExpDivStep (U.wk (σ := .nat))) (.var .here))) m)
      (.recNat (.qnat (.succ .zero)) (picardExpDivStep U) m)) := by
    have hb := Deriv.convBeta (Δ := Δ)
      (.recNat (.qnat (.succ .zero)) (picardExpDivStep (U.wk (σ := .nat))) (.var .here)) m
    rwa [picardExpStep_inner_subst] at hb
  exact Deriv.transE (Deriv.congFun h1 m) h2

/-- `tmPicardExpStep` applied to `U` at `0` converts to `1` inside `Deriv`. -/
def tmPicardExpStep_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} (U : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app (tmPicardExpStep (Γ := Γ)) U) .zero) (.qnat (.succ .zero))) :=
  Deriv.transE (tmPicardExpStep_appD U .zero)
    (Deriv.convRecZero (.qnat (.succ .zero)) (picardExpDivStep U))

/-- Substitution of `k` into the body of `picardExpDivStep U`. -/
theorem picardExpDivStep_subst1 {Γ : List Ty} (U : Tm Γ JetTy) (k : Tm Γ .nat) :
    (Tm.lam (.qdiv (.app U.wk.wk (.var (.there .here)))
                   (.qnat (.succ (.var (.there .here)))))).subst1 k =
      Tm.lam (.qdiv (.app (U.wk (σ := .rat)) (k.wk (σ := .rat)))
                    (.qnat (.succ (k.wk (σ := .rat))))) := by
  simp only [Tm.subst1, Tm.subst, Tm.wk_subst_ext, Tm.wk_subst_one]
  rfl

/-- Substitution of `r` into the inner body of `picardExpDivStep U` after applying `k`. -/
theorem picardExpDivStep_subst2 {Γ : List Ty} (U : Tm Γ JetTy) (k : Tm Γ .nat) (r : Tm Γ .rat) :
    (Tm.qdiv (.app (U.wk (σ := .rat)) (k.wk (σ := .rat)))
             (.qnat (.succ (k.wk (σ := .rat))))).subst1 r =
      Tm.qdiv (.app U k) (.qnat (.succ k)) := by
  simp only [Tm.subst1, Tm.subst, Tm.wk_subst_one]

/-- `tmPicardExpStep` applied to `U` at `succ k` converts to `U(k) / (k + 1)` inside `Deriv`. -/
def tmPicardExpStep_succD {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (k : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (tmPicardExpStep (Γ := Γ)) U) (.succ k))
                 (.qdiv (.app U k) (.qnat (.succ k)))) := by
  let r : Tm Γ .rat := .recNat (.qnat (.succ .zero)) (picardExpDivStep U) k
  have h1 := tmPicardExpStep_appD (Δ := Δ) U (.succ k)
  have h2 := Deriv.convRecSucc (Δ := Δ) (.qnat (.succ .zero)) (picardExpDivStep U) k
  have h3 : Deriv Δ (.eq (.app (picardExpDivStep U) k)
      (.lam (.qdiv (.app (U.wk (σ := .rat)) (k.wk (σ := .rat)))
                   (.qnat (.succ (k.wk (σ := .rat))))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.lam (a := .rat) (.qdiv (.app U.wk.wk (.var (.there .here))) (.qnat (.succ (.var (.there .here)))))) k
    rwa [picardExpDivStep_subst1] at hb
  have h4 : Deriv Δ (.eq
      (.app (.lam (.qdiv (.app (U.wk (σ := .rat)) (k.wk (σ := .rat)))
                         (.qnat (.succ (k.wk (σ := .rat)))))) r)
      (.qdiv (.app U k) (.qnat (.succ k)))) := by
    have hb := Deriv.convBeta (Δ := Δ)
      (.qdiv (.app (U.wk (σ := .rat)) (k.wk (σ := .rat))) (.qnat (.succ (k.wk (σ := .rat))))) r
    rwa [picardExpDivStep_subst2] at hb
  exact Deriv.transE h1 (Deriv.transE h2 (Deriv.transE (Deriv.congFun h3 r) h4))

/-- One step of the Picard iterate `recNat Y₀ (iterStepTm P) (succ k)` converts to `P(recNat Y₀ (iterStepTm P) k)`. -/
def picardExpIter_succD {Γ as : List Ty} {Δ : Ctx Γ as} (k : Tm Γ .nat) :
    Deriv Δ (.eq (.recNat (tmConstOneJet (Γ := Γ))
                    (.lam (.lam (.app (tmPicardExpStep (Γ := JetTy :: .nat :: Γ)) (.var .here))))
                    (.succ k))
                 (.app (tmPicardExpStep (Γ := Γ))
                    (.recNat (tmConstOneJet (Γ := Γ))
                      (.lam (.lam (.app (tmPicardExpStep (Γ := JetTy :: .nat :: Γ)) (.var .here))))
                      k))) := by
  let y0 : Tm Γ JetTy := tmConstOneJet (Γ := Γ)
  let S : Tm Γ (.arrow .nat (.arrow JetTy JetTy)) :=
    .lam (.lam (.app (tmPicardExpStep (Γ := JetTy :: .nat :: Γ)) (.var .here)))
  let rk : Tm Γ JetTy := .recNat y0 S k
  have h1 := Deriv.convRecSucc (Δ := Δ) y0 S k
  have h2 : Deriv Δ (.eq (.app S k) (.lam (.app (tmPicardExpStep (Γ := JetTy :: Γ)) (.var .here)))) :=
    Deriv.convBeta (.lam (.app (tmPicardExpStep (Γ := JetTy :: .nat :: Γ)) (.var .here))) k
  have h3 : Deriv Δ (.eq (.app (.lam (.app (tmPicardExpStep (Γ := JetTy :: Γ)) (.var .here))) rk)
      (.app (tmPicardExpStep (Γ := Γ)) rk)) :=
    Deriv.convBeta (.app (tmPicardExpStep (Γ := JetTy :: Γ)) (.var .here)) rk
  exact Deriv.transE h1 (Deriv.transE (Deriv.congFun h2 rk) h3)

/-- Evaluation of `extractClosed (Deriv.ind D₁ D₂)` at `k` reduces to `Nat.rec` in `Env.nil`. -/
theorem extractClosed_ind_eval {a : Ty} {φ : Formula (.nat :: []) a}
    (D₁ : Deriv Ctx.nil (φ.subst1 .zero))
    (D₂ : Deriv Ctx.nil (.all .nat (.imp φ (φ.subst Sub.succHere)))) (k : Nat) :
    ((extractClosed (Deriv.ind D₁ D₂)).eval Env.nil) k =
      Nat.rec (motive := fun _ ↦ a.interp)
        ((extract D₁).eval Env.nil)
        (fun m ih ↦ ((extract D₂).eval Env.nil) m ih) k := by
  let ek : Env [.nat] := Env.cons (σ := .nat) k Env.nil
  have hz : ((extract D₁).wk (σ := .nat)).eval ek = (extract D₁).eval Env.nil :=
    Tm.eval_wk (σ := .nat) (extract D₁) k Env.nil
  have hs : (fun (m : Nat) (ih : a.interp) ↦ (((extract D₂).wk (σ := .nat)).eval ek) m ih) =
      (fun (m : Nat) (ih : a.interp) ↦ ((extract D₂).eval Env.nil) m ih) := by
    funext m ih
    exact congrFun (congrFun (Tm.eval_wk (σ := .nat) (extract D₂) k Env.nil) m) ih
  change Nat.rec (motive := fun _ ↦ a.interp)
    (((extract D₁).wk (σ := .nat)).eval ek)
    (fun m ih ↦ (((extract D₂).wk (σ := .nat)).eval ek) m ih) k = _
  rw [hz, hs]

/-- Evaluating the first component of `extract (.exI u D)` in `Env.nil` ignores the certificate `D`. -/
theorem extract_exI_fst {a b : Ty} {φ : Formula (a :: []) b}
    (u : Tm [] a) (D : Deriv Ctx.nil (φ.subst1 u)) :
    ((extract (Deriv.exI u D)).eval Env.nil).1 = u.eval Env.nil := by
  dsimp [extract, Tm.eval]
  rw [Tm.eval_rename]
  rfl

/-- Invariant over `.nat :: []`:
    `∃Y. Y = P^k(Y₀) ∧ P(Y)(k) = Y(k)` for `P = tmPicardExpStep`, `Y₀ = 1`. -/
abbrev picardExpLockedInv : Formula (.nat :: []) (.prod JetTy (.prod .unit .unit)) :=
  let Y : Tm (JetTy :: .nat :: []) JetTy := .var .here
  let k : Tm (JetTy :: .nat :: []) .nat := .var (.there .here)
  .ex JetTy
    (.and
      (.eq Y (iterTm JetTy (tmConstOneJet (Γ := [])) (tmPicardExpStep (Γ := []))).wk)
      (.eq (.app (.app (tmPicardExpStep (Γ := JetTy :: .nat :: [])) Y) k) (.app Y k)))

/-- Base case (`k = 0`) of `picardExpLockedD`. -/
def picardExpLockedBaseD : Deriv Ctx.nil (picardExpLockedInv.subst1 .zero) := by
  refine Deriv.exI (tmConstOneJet (Γ := [])) ?_
  deriv_norm
  refine Deriv.andI ?_ ?_
  · exact Deriv.symmE (Deriv.convRecZero (tmConstOneJet (Γ := []))
      (.lam (.lam (.app (tmPicardExpStep (Γ := JetTy :: .nat :: [])) (.var .here)))))
  · exact Deriv.transE (tmPicardExpStep_zeroD (tmConstOneJet (Γ := [])))
      (Deriv.symmE tmConstOneJet_zeroD)

/-- Inductive step (`k → k + 1`) of `picardExpLockedD`. -/
def picardExpLockedStepD :
    Deriv Ctx.nil (.all .nat (.imp picardExpLockedInv (picardExpLockedInv.subst Sub.succHere))) := by
  refine Deriv.allI (Deriv.impI ?_)
  refine Deriv.exE (ψ := picardExpLockedInv.subst Sub.succHere) Deriv.ax ?_
  let Y : Tm (JetTy :: .nat :: []) JetTy := .var .here
  let k : Tm (JetTy :: .nat :: []) .nat := .var (.there .here)
  let P : Tm (JetTy :: .nat :: []) (.arrow JetTy JetTy) := tmPicardExpStep
  refine Deriv.exI (.app P Y) ?_
  deriv_norm
  refine Deriv.andI ?_ ?_
  · exact Deriv.transE (Deriv.congArg P (Deriv.andE₁ Deriv.ax))
      (Deriv.symmE (picardExpIter_succD k))
  · exact Deriv.transE (tmPicardExpStep_succD (.app P Y) k)
      (Deriv.transE (Deriv.congQDivNum (.qnat (.succ k)) (Deriv.andE₂ Deriv.ax))
        (Deriv.symmE (tmPicardExpStep_succD Y k)))

/-- First projection of the extracted base case `picardExpLockedBaseD`. -/
theorem extract_picardExpLockedBaseD_fst :
    ((extract picardExpLockedBaseD).eval Env.nil).1 = (tmConstOneJet (Γ := [])).eval Env.nil :=
  extract_exI_fst (tmConstOneJet (Γ := [])) _

/-- First projection of the extracted induction step `picardExpLockedStepD`. -/
theorem extract_picardExpLockedStepD_fst
    (m : Nat) (ih : (Ty.prod JetTy (.prod .unit .unit)).interp) :
    (((extract picardExpLockedStepD).eval Env.nil) m ih).1 =
      ((tmPicardExpStep (Γ := [])).eval Env.nil) ih.1 := by
  unfold picardExpLockedStepD
  dsimp [extract, Tm.eval]
  rw [Tm.eval_rename]
  dsimp [Tm.eval]
  rw [Tm.eval_rename]
  dsimp [Tm.eval]
  rw [Tm.eval_rename]
  rfl

/-- `∀k ∃Y. Y = P^k(Y₀) ∧ P(Y)(k) = Y(k)`, derived by `Deriv.ind` on `k`. -/
def picardExpLockedD : Deriv Ctx.nil (.all .nat picardExpLockedInv) :=
  Deriv.ind picardExpLockedBaseD picardExpLockedStepD

/-- The extracted witness is the extracted linear Picard iterate. -/
theorem extractClosed_picardExpLockedD_fst (k : Nat) :
    (((extractClosed picardExpLockedD).eval Env.nil) k).1 = extractedPicardJet k := by
  induction k with
  | zero =>
    have h0 := congrArg Prod.fst
      (extractClosed_ind_eval picardExpLockedBaseD picardExpLockedStepD 0)
    exact h0.trans (extract_picardExpLockedBaseD_fst.trans
      (extractClosed_iterSequenceD_zero JetTy tmConstOneJet tmPicardExpStep).symm)
  | succ m ih =>
    have hm := congrArg Prod.fst
      (extractClosed_ind_eval picardExpLockedBaseD picardExpLockedStepD m)
    have hs := congrArg Prod.fst
      (extractClosed_ind_eval picardExpLockedBaseD picardExpLockedStepD (m + 1))
    have hstep := extract_picardExpLockedStepD_fst m
      (Nat.rec (motive := fun _ ↦ (Ty.prod JetTy (.prod .unit .unit)).interp)
        ((extract picardExpLockedBaseD).eval Env.nil)
        (fun j acc ↦ ((extract picardExpLockedStepD).eval Env.nil) j acc) m)
    rw [← hm] at hstep
    exact hs.trans (hstep.trans ((congrArg ((tmPicardExpStep (Γ := [])).eval Env.nil) ih).trans
      (extractClosed_iterSequenceD_succ JetTy tmConstOneJet tmPicardExpStep m).symm))

#print axioms picardExpLockedD
#print axioms extractClosed_picardExpLockedD_fst

end HAomega
