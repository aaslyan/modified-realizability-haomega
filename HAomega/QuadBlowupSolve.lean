/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PicardExpSolve

/-!
# A proof-computed jet solver for the nonlinear ODE `y' = y²`, `y(0) = 1`

`PicardExpSolve.lean` extracts the solver of the linear equation `y' = y` from
an algorithm-free specification. This module does the same for the first
nonlinear equation, `y' = y²`, stated in integral form `Y = P(Y)` with
`P(Y) = 1 + ∫(Y·Y)` the Picard operator `tmQuadBlowupStep`:

  `∀k ∃Y. ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)`

The linear proof only needed the induction hypothesis at one index. Here
`P(Y)(j+1)` involves `(Y·Y)(j) = Σ_{m ≤ j} Y(m)·Y(j−m)`, which depends on the
whole prefix `Y(0), …, Y(j)`. The load-bearing lemma is `jetMulPrefixT`,
derived inside `Deriv`: Cauchy-product coefficient `n` depends only on the
factors' coefficients at indices `≤ n` (`m ≤ n` written `∃`-free as
`m + d = n`).

`quadBlowupSolveD` proves the specification by `Deriv.ind` on `k`; the
extracted solver's recursion comes from the induction. Out of scope: the
differential form, and the Riccati and Duffing steps (which `jetMulPrefixT`
is meant to serve next).
-/

namespace HAomega

/-- Congruence for `Tm.qadd` in both arguments, derived from `Deriv.eqSubst`. -/
def Deriv.congQAdd {Γ as : List Ty} {Δ : Ctx Γ as} {u u' v v' : Tm Γ .rat}
    (hu : Deriv Δ (.eq u u')) (hv : Deriv Δ (.eq v v')) :
    Deriv Δ (.eq (.qadd u v) (.qadd u' v')) := by
  have hs1 : ∀ z : Tm Γ .rat,
      (Formula.eq (.qadd u.wk (.var .here)) (Tm.qadd u v).wk).subst1 z
        = Formula.eq (.qadd u z) (.qadd u v) := by
    intro z
    show Formula.eq (.qadd (u.wk.subst1 z) z) (.qadd (u.wk.subst1 z) (v.wk.subst1 z)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have h1 := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.qadd u.wk (.var .here)) (Tm.qadd u v).wk) hv
    (by rw [hs1]; exact Deriv.eqRefl _)
  rw [hs1] at h1
  have hs2 : ∀ z : Tm Γ .rat,
      (Formula.eq (.qadd (.var .here) v'.wk) (Tm.qadd u v').wk).subst1 z
        = Formula.eq (.qadd z v') (.qadd u v') := by
    intro z
    show Formula.eq (.qadd z (v'.wk.subst1 z)) (.qadd (u.wk.subst1 z) (v'.wk.subst1 z)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have h2 := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.qadd (.var .here) v'.wk) (Tm.qadd u v').wk) hu
    (by rw [hs2]; exact Deriv.eqRefl _)
  rw [hs2] at h2
  exact Deriv.transE h1.symmE h2.symmE

/-- Congruence for `Tm.qmul` in both arguments, derived from `Deriv.eqSubst`. -/
def Deriv.congQMul {Γ as : List Ty} {Δ : Ctx Γ as} {u u' v v' : Tm Γ .rat}
    (hu : Deriv Δ (.eq u u')) (hv : Deriv Δ (.eq v v')) :
    Deriv Δ (.eq (.qmul u v) (.qmul u' v')) := by
  have hs1 : ∀ z : Tm Γ .rat,
      (Formula.eq (.qmul u.wk (.var .here)) (Tm.qmul u v).wk).subst1 z
        = Formula.eq (.qmul u z) (.qmul u v) := by
    intro z
    show Formula.eq (.qmul (u.wk.subst1 z) z) (.qmul (u.wk.subst1 z) (v.wk.subst1 z)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have h1 := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.qmul u.wk (.var .here)) (Tm.qmul u v).wk) hv
    (by rw [hs1]; exact Deriv.eqRefl _)
  rw [hs1] at h1
  have hs2 : ∀ z : Tm Γ .rat,
      (Formula.eq (.qmul (.var .here) v'.wk) (Tm.qmul u v').wk).subst1 z
        = Formula.eq (.qmul z v') (.qmul u v') := by
    intro z
    show Formula.eq (.qmul z (v'.wk.subst1 z)) (.qmul (u.wk.subst1 z) (v'.wk.subst1 z)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have h2 := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.qmul (.var .here) v'.wk) (Tm.qmul u v').wk) hu
    (by rw [hs2]; exact Deriv.eqRefl _)
  rw [hs2] at h2
  exact Deriv.transE h1.symmE h2.symmE

attribute [derivNorm] Sub.succHere

/-- Substituting `Sub.succHere` into a weakened term leaves it unchanged. -/
@[derivNorm] theorem subst_succHere_rename {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    Tm.subst Sub.succHere (Tm.rename (Ren.wk .nat) t) = Tm.rename (Ren.wk .nat) t := by
  rw [Tm.subst_rename]
  exact (Tm.subst_rename t (Ren.wk .nat) (fun _ v ↦ Tm.var v)).symm.trans
    (Tm.subst_id (t.rename (Ren.wk .nat)))

/-- Pushing `Ren.ext` past `Ren.wk`. -/
@[derivNorm] theorem rename_ext_rename_wk {Γ Δ : List Ty} {σ τ : Ty}
    (t : Tm Γ τ) (ρ : Ren Γ Δ) :
    Tm.rename (Ren.ext (σ := σ) ρ) (Tm.rename (Ren.wk σ) t) =
      Tm.rename (Ren.wk σ) (Tm.rename ρ t) := by
  rw [Tm.rename_rename, Tm.rename_rename]
  rfl

/-- Renaming commutes with `tmNatPred`. -/
@[derivNorm] theorem tmNatPred_rename {Γ Δ : List Ty} (m : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (tmNatPred m).rename ρ = tmNatPred (m.rename ρ) := rfl

/-- Substitution commutes with `tmNatPred`. -/
@[derivNorm] theorem tmNatPred_subst {Γ Δ : List Ty} (m : Tm Γ .nat) (s : Sub Γ Δ) :
    (tmNatPred m).subst s = tmNatPred (m.subst s) := rfl

/-- Renaming commutes with `tmNatSub`. -/
@[derivNorm] theorem tmNatSub_rename {Γ Δ : List Ty} (a b : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (tmNatSub a b).rename ρ = tmNatSub (a.rename ρ) (b.rename ρ) := rfl

/-- Substitution commutes with `tmNatSub`. -/
@[derivNorm] theorem tmNatSub_subst {Γ Δ : List Ty} (a b : Tm Γ .nat) (s : Sub Γ Δ) :
    (tmNatSub a b).subst s = tmNatSub (a.subst s) (b.subst s) := rfl

/-- `tmNatPred (succ m) = m` inside `Deriv` via `convRecSucc` and `convBeta`. -/
def tmNatPred_succD {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) :
    Deriv Δ (.eq (tmNatPred (.succ m)) m) := by
  let S : Tm Γ (.arrow .nat (.arrow .nat .nat)) := .lam (.lam (.var (.there .here)))
  have h1 := Deriv.convRecSucc (Δ := Δ) .zero S m
  have h2 : Deriv Δ (.eq (.app S m) (.lam (m.wk (σ := .nat)))) :=
    Deriv.convBeta (.lam (a := .nat) (.var (.there .here))) m
  have h3 : Deriv Δ (.eq (.app (.lam (m.wk (σ := .nat))) (tmNatPred m)) m) := by
    have hb := Deriv.convBeta (Δ := Δ) (m.wk (σ := .nat)) (tmNatPred m)
    rwa [Tm.subst1_wk] at hb
  exact Deriv.transE h1 (Deriv.transE (Deriv.congFun h2 (tmNatPred m)) h3)

/-- Congruence for `tmNatPred` inside `Deriv`. -/
def Deriv.congTmNatPred {Γ as : List Ty} {Δ : Ctx Γ as} {x y : Tm Γ .nat}
    (h : Deriv Δ (.eq x y)) : Deriv Δ (.eq (tmNatPred x) (tmNatPred y)) := by
  have hs : ∀ u : Tm Γ .nat,
      (Formula.eq (tmNatPred (.var .here)) (tmNatPred x).wk).subst1 u
        = Formula.eq (tmNatPred u) (tmNatPred x) := by
    intro u
    show Formula.eq (tmNatPred u) (((tmNatPred x).wk).subst1 u) = _
    rw [Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (tmNatPred (.var .here)) (tmNatPred x).wk) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

/-- `tmNatSub a 0 = a` inside `Deriv` via `convRecZero`. -/
def tmNatSub_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} (a : Tm Γ .nat) :
    Deriv Δ (.eq (tmNatSub a .zero) a) :=
  Deriv.convRecZero a (.lam (.lam (tmNatPred (.var .here))))

/-- `tmNatSub a (succ j) = tmNatPred (tmNatSub a j)` inside `Deriv`. -/
def tmNatSub_succD {Γ as : List Ty} {Δ : Ctx Γ as} (a j : Tm Γ .nat) :
    Deriv Δ (.eq (tmNatSub a (.succ j)) (tmNatPred (tmNatSub a j))) := by
  let S : Tm Γ (.arrow .nat (.arrow .nat .nat)) := .lam (.lam (tmNatPred (.var .here)))
  have h1 := Deriv.convRecSucc (Δ := Δ) a S j
  have h2 : Deriv Δ (.eq (.app S j) (.lam (tmNatPred (.var .here)))) :=
    Deriv.convBeta (.lam (tmNatPred (.var .here))) j
  have h3 : Deriv Δ (.eq (.app (.lam (tmNatPred (.var .here))) (tmNatSub a j))
      (tmNatPred (tmNatSub a j))) :=
    Deriv.convBeta (tmNatPred (.var .here)) (tmNatSub a j)
  exact Deriv.transE h1 (Deriv.transE (Deriv.congFun h2 (tmNatSub a j)) h3)

/-- Helper step for `tmNatSubAddCancelD`: from `∀e. j + e = n → tmNatSub n j = e` and `succ j + e = n`, derive `tmNatSub n (succ j) = e`. -/
def tmNatSubAddCancelStepT {Γ as : List Ty} {Δ : Ctx (.nat :: .nat :: Γ) as}
    (n : Tm Γ .nat)
    (h_ih : Deriv Δ (.all .nat
      (.imp (.eq (.add (.var (.there (.there .here))) (.var .here)) (n.wk.wk.wk))
            (.eq (tmNatSub (n.wk.wk.wk) (.var (.there (.there .here)))) (.var .here)))))
    (h_add : Deriv Δ (.eq (.add (.succ (.var (.there .here))) (.var .here)) (n.wk.wk))) :
    Deriv Δ (.eq (tmNatSub (n.wk.wk) (.succ (.var (.there .here)))) (.var .here)) := by
  let e : Tm (.nat :: .nat :: Γ) .nat := .var .here
  let j : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  have h_ih_succ := Deriv.allE (.succ e) h_ih
  deriv_norm at h_ih_succ
  have h_j_succ_e : Deriv Δ (.eq (.add j (.succ e)) (n.wk.wk)) :=
    Deriv.transE (Deriv.convAddSucc j e)
      (Deriv.transE (Deriv.symmE (succPlusT j e)) h_add)
  have h_sub_j : Deriv Δ (.eq (tmNatSub (n.wk.wk) j) (.succ e)) :=
    Deriv.impE h_ih_succ h_j_succ_e
  exact Deriv.transE (tmNatSub_succD (n.wk.wk) j)
    (Deriv.transE (Deriv.congTmNatPred h_sub_j) (tmNatPred_succD e))

/-- `∀j ∀e. j + e = n → tmNatSub n j = e`, proved by `Deriv.ind` on `j`. -/
def tmNatSubAddCancelD {Γ as : List Ty} {Δ : Ctx Γ as} (n : Tm Γ .nat) :
    Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) (n.wk.wk))
            (.eq (tmNatSub (n.wk.wk) (.var (.there .here))) (.var .here))))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let e : Tm (.nat :: Γ) .nat := .var .here
    exact Deriv.transE (tmNatSub_zeroD n.wk)
      (Deriv.transE (Deriv.symmE Deriv.ax) (zeroPlusT e))
  · refine Deriv.allI (Deriv.impI ?_)
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact tmNatSubAddCancelStepT n (Deriv.wk Deriv.ax) Deriv.ax

/-- Term form of `tmNatSubAddCancelD`: from `j + e = n`, derive `tmNatSub n j = e`. -/
def tmNatSubAddCancelT {Γ as : List Ty} {Δ : Ctx Γ as} {n j e : Tm Γ .nat}
    (h : Deriv Δ (.eq (.add j e) n)) :
    Deriv Δ (.eq (tmNatSub n j) e) := by
  have h_all := Deriv.allE e (Deriv.allE j (tmNatSubAddCancelD (Δ := Δ) n))
  deriv_norm at h_all
  exact Deriv.impE h_all h

/-- The recursor step of `tmJetMulAt c1 c2 n`. -/
def jetMulStep {Γ : List Ty} (c1 c2 : Tm Γ JetTy) (n : Tm Γ .nat) :
    Tm Γ (.arrow .nat (.arrow .rat .rat)) :=
  .lam (.lam (
    let j : Tm (.rat :: .nat :: Γ) .nat := .var (.there .here)
    let acc : Tm (.rat :: .nat :: Γ) .rat := .var .here
    let c1_wk : Tm (.rat :: .nat :: Γ) JetTy := (c1.wk (σ := .nat)).wk (σ := .rat)
    let c2_wk : Tm (.rat :: .nat :: Γ) JetTy := (c2.wk (σ := .nat)).wk (σ := .rat)
    let n_wk : Tm (.rat :: .nat :: Γ) .nat := (n.wk (σ := .nat)).wk (σ := .rat)
    .qadd acc (.qmul (.app c1_wk j) (.app c2_wk (tmNatSub n_wk j)))
  ))

/-- Partial Cauchy convolution sum up to `t` terms (`t = succ n` is `tmJetMulAt c1 c2 n`). -/
def jetMulPartialAt {Γ : List Ty} (c1 c2 : Tm Γ JetTy) (n t : Tm Γ .nat) : Tm Γ .rat :=
  .recNat (.qnat .zero) (jetMulStep c1 c2 n) t

/-- Renaming commutes with `jetMulStep`. -/
@[derivNorm] theorem jetMulStep_rename {Γ Δ : List Ty}
    (c1 c2 : Tm Γ JetTy) (n : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (jetMulStep c1 c2 n).rename ρ = jetMulStep (c1.rename ρ) (c2.rename ρ) (n.rename ρ) := by
  simp only [jetMulStep, Tm.rename, Tm.wk, Tm.rename_rename, tmNatSub_rename]
  rfl

/-- Substitution commutes with `jetMulStep`. -/
@[derivNorm] theorem jetMulStep_subst {Γ Δ : List Ty}
    (c1 c2 : Tm Γ JetTy) (n : Tm Γ .nat) (s : Sub Γ Δ) :
    (jetMulStep c1 c2 n).subst s = jetMulStep (c1.subst s) (c2.subst s) (n.subst s) := by
  simp only [jetMulStep, Tm.subst, Tm.wk_subst_ext, tmNatSub_subst]
  rfl

/-- Renaming commutes with `jetMulPartialAt`. -/
@[derivNorm] theorem jetMulPartialAt_rename {Γ Δ : List Ty}
    (c1 c2 : Tm Γ JetTy) (n t : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (jetMulPartialAt c1 c2 n t).rename ρ =
      jetMulPartialAt (c1.rename ρ) (c2.rename ρ) (n.rename ρ) (t.rename ρ) := by
  simp only [jetMulPartialAt, Tm.rename, jetMulStep_rename]

/-- Substitution commutes with `jetMulPartialAt`. -/
@[derivNorm] theorem jetMulPartialAt_subst {Γ Δ : List Ty}
    (c1 c2 : Tm Γ JetTy) (n t : Tm Γ .nat) (s : Sub Γ Δ) :
    (jetMulPartialAt c1 c2 n t).subst s =
      jetMulPartialAt (c1.subst s) (c2.subst s) (n.subst s) (t.subst s) := by
  simp only [jetMulPartialAt, Tm.subst, jetMulStep_subst]

/-- Substitution of `j` into the outer lambda body of `jetMulStep c1 c2 n`. -/
theorem jetMulStep_subst1 {Γ : List Ty} (c1 c2 : Tm Γ JetTy) (n j : Tm Γ .nat) :
    (Tm.lam (
      let jv : Tm (.rat :: .nat :: Γ) .nat := .var (.there .here)
      let acc : Tm (.rat :: .nat :: Γ) .rat := .var .here
      let c1_wk : Tm (.rat :: .nat :: Γ) JetTy := (c1.wk (σ := .nat)).wk (σ := .rat)
      let c2_wk : Tm (.rat :: .nat :: Γ) JetTy := (c2.wk (σ := .nat)).wk (σ := .rat)
      let n_wk : Tm (.rat :: .nat :: Γ) .nat := (n.wk (σ := .nat)).wk (σ := .rat)
      .qadd acc (.qmul (.app c1_wk jv) (.app c2_wk (tmNatSub n_wk jv)))
    )).subst1 j =
    Tm.lam (.qadd (.var .here)
      (.qmul (.app (c1.wk (σ := .rat)) (j.wk (σ := .rat)))
             (.app (c2.wk (σ := .rat)) (tmNatSub (n.wk (σ := .rat)) (j.wk (σ := .rat)))))) := by
  simp only [Tm.subst1, Tm.subst, Tm.wk_subst_ext, Tm.wk_subst_one, tmNatSub_subst]
  rfl

/-- Substitution of `acc` into the inner lambda body of `jetMulStep c1 c2 n` after `j`. -/
theorem jetMulStep_subst2 {Γ : List Ty} (c1 c2 : Tm Γ JetTy) (n j : Tm Γ .nat) (acc : Tm Γ .rat) :
    (Tm.qadd (.var .here)
      (.qmul (.app (c1.wk (σ := .rat)) (j.wk (σ := .rat)))
             (.app (c2.wk (σ := .rat)) (tmNatSub (n.wk (σ := .rat)) (j.wk (σ := .rat)))))).subst1 acc =
    Tm.qadd acc (.qmul (.app c1 j) (.app c2 (tmNatSub n j))) := by
  simp only [Tm.subst1, Tm.subst, Sub.one, Tm.wk_subst_one, tmNatSub_subst]

/-- Base equation `jetMulPartialAt c1 c2 n 0 = 0` inside `Deriv`. -/
def jetMulPartial_zeroD {Γ as : List Ty} {Δ : Ctx Γ as}
    (c1 c2 : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (jetMulPartialAt c1 c2 n .zero) (.qnat .zero)) :=
  Deriv.convRecZero (.qnat .zero) (jetMulStep c1 c2 n)

/-- Step equation for `jetMulPartialAt c1 c2 n (succ j)` inside `Deriv`. -/
def jetMulPartial_succD {Γ as : List Ty} {Δ : Ctx Γ as}
    (c1 c2 : Tm Γ JetTy) (n j : Tm Γ .nat) :
    Deriv Δ (.eq (jetMulPartialAt c1 c2 n (.succ j))
      (.qadd (jetMulPartialAt c1 c2 n j)
             (.qmul (.app c1 j) (.app c2 (tmNatSub n j))))) := by
  let r : Tm Γ .rat := jetMulPartialAt c1 c2 n j
  have h1 := Deriv.convRecSucc (Δ := Δ) (.qnat .zero) (jetMulStep c1 c2 n) j
  have h2 : Deriv Δ (.eq (.app (jetMulStep c1 c2 n) j)
      (.lam (.qadd (.var .here)
        (.qmul (.app (c1.wk (σ := .rat)) (j.wk (σ := .rat)))
               (.app (c2.wk (σ := .rat)) (tmNatSub (n.wk (σ := .rat)) (j.wk (σ := .rat)))))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.lam (.qadd (.var .here)
        (.qmul (.app ((c1.wk (σ := .nat)).wk (σ := .rat)) (.var (.there .here)))
               (.app ((c2.wk (σ := .nat)).wk (σ := .rat))
                 (tmNatSub ((n.wk (σ := .nat)).wk (σ := .rat)) (.var (.there .here))))))) j
    rwa [jetMulStep_subst1] at hb
  have h3 : Deriv Δ (.eq
      (.app (.lam (.qadd (.var .here)
        (.qmul (.app (c1.wk (σ := .rat)) (j.wk (σ := .rat)))
               (.app (c2.wk (σ := .rat)) (tmNatSub (n.wk (σ := .rat)) (j.wk (σ := .rat))))))) r)
      (.qadd r (.qmul (.app c1 j) (.app c2 (tmNatSub n j))))) := by
    have hb := Deriv.convBeta (Δ := Δ)
      (.qadd (.var .here)
        (.qmul (.app (c1.wk (σ := .rat)) (j.wk (σ := .rat)))
               (.app (c2.wk (σ := .rat)) (tmNatSub (n.wk (σ := .rat)) (j.wk (σ := .rat)))))) r
    rwa [jetMulStep_subst2] at hb
  exact Deriv.transE h1 (Deriv.transE (Deriv.congFun h2 r) h3)

/-- Inductive step for `jetMulPartialPrefixD`: from agreement below `n` and `succ t + f = succ n`, derive partial-sum agreement at `succ t`. -/
def jetMulPartialPrefixStepT {Γ as : List Ty} {Δ : Ctx (.nat :: .nat :: Γ) as}
    (a a' b b' : Tm Γ JetTy) (n : Tm Γ .nat)
    (ha : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) (n.wk.wk.wk.wk))
        (.eq (.app (a.wk.wk.wk.wk) (.var (.there .here))) (.app (a'.wk.wk.wk.wk) (.var (.there .here))))))))
    (hb : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) (n.wk.wk.wk.wk))
        (.eq (.app (b.wk.wk.wk.wk) (.var (.there .here))) (.app (b'.wk.wk.wk.wk) (.var (.there .here))))))))
    (h_ih : Deriv Δ (.all .nat
      (.imp (.eq (.add (.var (.there (.there .here))) (.var .here)) (.succ (n.wk.wk.wk)))
        (.eq (jetMulPartialAt (a.wk.wk.wk) (b.wk.wk.wk) (n.wk.wk.wk) (.var (.there (.there .here))))
             (jetMulPartialAt (a'.wk.wk.wk) (b'.wk.wk.wk) (n.wk.wk.wk) (.var (.there (.there .here))))))))
    (h_succ : Deriv Δ (.eq (.add (.succ (.var (.there .here))) (.var .here)) (.succ (n.wk.wk)))) :
    Deriv Δ (.eq (jetMulPartialAt (a.wk.wk) (b.wk.wk) (n.wk.wk) (.succ (.var (.there .here))))
                 (jetMulPartialAt (a'.wk.wk) (b'.wk.wk) (n.wk.wk) (.succ (.var (.there .here))))) := by
  let f : Tm (.nat :: .nat :: Γ) .nat := .var .here
  let t : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  let n₂ : Tm (.nat :: .nat :: Γ) .nat := n.wk.wk
  let a₂ : Tm (.nat :: .nat :: Γ) JetTy := a.wk.wk
  let a'₂ : Tm (.nat :: .nat :: Γ) JetTy := a'.wk.wk
  let b₂ : Tm (.nat :: .nat :: Γ) JetTy := b.wk.wk
  let b'₂ : Tm (.nat :: .nat :: Γ) JetTy := b'.wk.wk
  have h_t_succ_f : Deriv Δ (.eq (.add t (.succ f)) (.succ n₂)) :=
    Deriv.transE (Deriv.convAddSucc t f)
      (Deriv.transE (Deriv.symmE (succPlusT t f)) h_succ)
  have h_ih_f := Deriv.allE (.succ f) h_ih
  deriv_norm at h_ih_f
  have h_part : Deriv Δ (.eq (jetMulPartialAt a₂ b₂ n₂ t) (jetMulPartialAt a'₂ b'₂ n₂ t)) :=
    Deriv.impE h_ih_f h_t_succ_f
  have h_tf : Deriv Δ (.eq (.add t f) n₂) :=
    Deriv.impE (Deriv.succInj (.add t f) n₂)
      (Deriv.transE (Deriv.symmE (succPlusT t f)) h_succ)
  have ha_inst := Deriv.allE f (Deriv.allE t ha)
  deriv_norm at ha_inst
  have h_a : Deriv Δ (.eq (.app a₂ t) (.app a'₂ t)) :=
    Deriv.impE ha_inst h_tf
  have h_sub : Deriv Δ (.eq (tmNatSub n₂ t) f) :=
    tmNatSubAddCancelT h_tf
  have h_ft : Deriv Δ (.eq (.add f t) n₂) :=
    Deriv.transE (plusCommT f t) h_tf
  have hb_inst := Deriv.allE t (Deriv.allE f hb)
  deriv_norm at hb_inst
  have h_bf : Deriv Δ (.eq (.app b₂ f) (.app b'₂ f)) :=
    Deriv.impE hb_inst h_ft
  have h_b : Deriv Δ (.eq (.app b₂ (tmNatSub n₂ t)) (.app b'₂ (tmNatSub n₂ t))) :=
    Deriv.transE (Deriv.congArg b₂ h_sub)
      (Deriv.transE h_bf (Deriv.symmE (Deriv.congArg b'₂ h_sub)))
  exact Deriv.transE (jetMulPartial_succD a₂ b₂ n₂ t)
    (Deriv.transE (Deriv.congQAdd h_part (Deriv.congQMul h_a h_b))
      (Deriv.symmE (jetMulPartial_succD a'₂ b'₂ n₂ t)))

/-- Partial-sum prefix invariance for Cauchy product, proved by `Deriv.ind` on `t`. -/
def jetMulPartialPrefixD {Γ as : List Ty} {Δ : Ctx Γ as}
    (a a' b b' : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.imp
      (.all .nat (.all .nat
        (.imp (.eq (.add (.var (.there .here)) (.var .here)) (n.wk.wk))
          (.eq (.app (a.wk.wk) (.var (.there .here))) (.app (a'.wk.wk) (.var (.there .here)))))))
      (.imp
        (.all .nat (.all .nat
          (.imp (.eq (.add (.var (.there .here)) (.var .here)) (n.wk.wk))
            (.eq (.app (b.wk.wk) (.var (.there .here))) (.app (b'.wk.wk) (.var (.there .here)))))))
        (.all .nat (.all .nat
          (.imp (.eq (.add (.var (.there .here)) (.var .here)) (.succ (n.wk.wk)))
            (.eq (jetMulPartialAt (a.wk.wk) (b.wk.wk) (n.wk.wk) (.var (.there .here)))
                 (jetMulPartialAt (a'.wk.wk) (b'.wk.wk) (n.wk.wk) (.var (.there .here))))))))) := by
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    exact Deriv.transE (jetMulPartial_zeroD a.wk b.wk n.wk)
      (Deriv.symmE (jetMulPartial_zeroD a'.wk b'.wk n.wk))
  · refine Deriv.allI (Deriv.impI ?_)
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact jetMulPartialPrefixStepT a a' b b' n
      (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax)))
      (Deriv.wk (Deriv.wk Deriv.ax))
      (Deriv.wk Deriv.ax)
      Deriv.ax

/-- **Prefix dependence of the Cauchy product, inside `Deriv`.** If `a, a'`
    agree at every `m ≤ n` and so do `b, b'`, then `(a·b)(n) = (a'·b')(n)`.
    `m ≤ n` is written `∀d. m + d = n → …`. -/
def jetMulPrefixT {Γ as : List Ty} {Δ : Ctx Γ as} (a a' b b' : Tm Γ JetTy) (n : Tm Γ .nat)
    (ha : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) (n.wk.wk))
        (.eq (.app (a.wk.wk) (.var (.there .here))) (.app (a'.wk.wk) (.var (.there .here))))))))
    (hb : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) (n.wk.wk))
        (.eq (.app (b.wk.wk) (.var (.there .here))) (.app (b'.wk.wk) (.var (.there .here))))))))
    : Deriv Δ (.eq (tmJetMulAt a b n) (tmJetMulAt a' b' n)) := by
  have h_all := Deriv.impE (Deriv.impE (jetMulPartialPrefixD a a' b b' n) ha) hb
  have h_inst := Deriv.allE .zero (Deriv.allE (.succ n) h_all)
  deriv_norm at h_inst
  exact Deriv.impE h_inst (Deriv.convAddZero (.succ n))

/-- Invariant over `.nat :: []`: `∃Y. ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)`
    for `P = tmQuadBlowupStep`. -/
abbrev quadBlowupSolveInv :=
  let ctx : List Ty := .nat :: .nat :: JetTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let Y : Tm ctx JetTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  (Formula.ex JetTy
    (.all .nat (.all .nat
      (.imp (.eq (.add i (.succ d)) k)
        (.eq (.app (.app (tmQuadBlowupStep (Γ := ctx)) Y) i) (.app Y i))))) :
    Formula (.nat :: []) _)

/-- Renaming commutes with `jetIntegStep`. -/
@[derivNorm] theorem jetIntegStep_rename {Γ Δ : List Ty} (c : Tm Γ JetTy) (ρ : Ren Γ Δ) :
    (jetIntegStep c).rename ρ = jetIntegStep (c.rename ρ) := by
  simp only [jetIntegStep, Tm.rename, Tm.wk, Tm.rename_rename]
  rfl

/-- Substitution commutes with `jetIntegStep`. -/
@[derivNorm] theorem jetIntegStep_subst {Γ Δ : List Ty} (c : Tm Γ JetTy) (s : Sub Γ Δ) :
    (jetIntegStep c).subst s = jetIntegStep (c.subst s) := by
  simp only [jetIntegStep, Tm.subst, Tm.wk_subst_ext]
  rfl

/-- Renaming commutes with `jetIntegAt`. -/
@[derivNorm] theorem jetIntegAt_rename {Γ Δ : List Ty} (c : Tm Γ JetTy) (n : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (jetIntegAt c n).rename ρ = jetIntegAt (c.rename ρ) (n.rename ρ) := by
  simp only [jetIntegAt, Tm.rename, jetIntegStep_rename]

/-- Substitution commutes with `jetIntegAt`. -/
@[derivNorm] theorem jetIntegAt_subst {Γ Δ : List Ty} (c : Tm Γ JetTy) (n : Tm Γ .nat) (s : Sub Γ Δ) :
    (jetIntegAt c n).subst s = jetIntegAt (c.subst s) (n.subst s) := by
  simp only [jetIntegAt, Tm.subst, jetIntegStep_subst]

/-- Renaming commutes with `tmJetMulAt`. -/
@[derivNorm] theorem tmJetMulAt_rename {Γ Δ : List Ty}
    (c1 c2 : Tm Γ JetTy) (n : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (tmJetMulAt c1 c2 n).rename ρ = tmJetMulAt (c1.rename ρ) (c2.rename ρ) (n.rename ρ) :=
  jetMulPartialAt_rename c1 c2 n (.succ n) ρ

/-- Substitution commutes with `tmJetMulAt`. -/
@[derivNorm] theorem tmJetMulAt_subst {Γ Δ : List Ty}
    (c1 c2 : Tm Γ JetTy) (n : Tm Γ .nat) (s : Sub Γ Δ) :
    (tmJetMulAt c1 c2 n).subst s = tmJetMulAt (c1.subst s) (c2.subst s) (n.subst s) :=
  jetMulPartialAt_subst c1 c2 n (.succ n) s

/-- Renaming leaves `tmConstOneJet` unchanged. -/
@[derivNorm] theorem tmConstOneJet_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmConstOneJet (Γ := Γ)).rename ρ = tmConstOneJet (Γ := Δ) := rfl

/-- Substitution leaves `tmConstOneJet` unchanged. -/
@[derivNorm] theorem tmConstOneJet_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmConstOneJet (Γ := Γ)).subst s = tmConstOneJet (Γ := Δ) := rfl

/-- Renaming leaves `tmJetAdd` unchanged. -/
@[derivNorm] theorem tmJetAdd_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetAdd (Γ := Γ)).rename ρ = tmJetAdd (Γ := Δ) := rfl

/-- Substitution leaves `tmJetAdd` unchanged. -/
@[derivNorm] theorem tmJetAdd_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetAdd (Γ := Γ)).subst s = tmJetAdd (Γ := Δ) := rfl

/-- Renaming leaves `tmJetInteg` unchanged. -/
@[derivNorm] theorem tmJetInteg_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetInteg (Γ := Γ)).rename ρ = tmJetInteg (Γ := Δ) := rfl

/-- Substitution leaves `tmJetInteg` unchanged. -/
@[derivNorm] theorem tmJetInteg_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetInteg (Γ := Γ)).subst s = tmJetInteg (Γ := Δ) := rfl

/-- Renaming leaves `tmJetMul` unchanged. -/
@[derivNorm] theorem tmJetMul_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetMul (Γ := Γ)).rename ρ = tmJetMul (Γ := Δ) := rfl

/-- Substitution leaves `tmJetMul` unchanged. -/
@[derivNorm] theorem tmJetMul_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetMul (Γ := Γ)).subst s = tmJetMul (Γ := Δ) := rfl

/-- Renaming leaves `tmQuadBlowupStep` unchanged. -/
@[derivNorm] theorem tmQuadBlowupStep_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmQuadBlowupStep (Γ := Γ)).rename ρ = tmQuadBlowupStep (Γ := Δ) := rfl

/-- Substitution leaves `tmQuadBlowupStep` unchanged. -/
@[derivNorm] theorem tmQuadBlowupStep_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmQuadBlowupStep (Γ := Γ)).subst s = tmQuadBlowupStep (Γ := Δ) := rfl

/-- Applying `tmJetAdd` to `A, B, i` converts to `.qadd (.app A i) (.app B i)` inside `Deriv`. -/
def tmJetAdd_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (A B : Tm Γ JetTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app (tmJetAdd (Γ := Γ)) A) B) i)
                 (.qadd (.app A i) (.app B i))) := by
  have h1 : Deriv Δ (.eq (.app (tmJetAdd (Γ := Γ)) A)
      (.lam (.lam (.qadd (.app (A.wk.wk) (.var .here)) (.app (.var (.there .here)) (.var .here)))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (.lam (.qadd (.app (.var (.there (.there .here))) (.var .here))
                         (.app (.var (.there .here)) (.var .here))))) A
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq
      (.app (.lam (.lam (.qadd (.app (A.wk.wk) (.var .here)) (.app (.var (.there .here)) (.var .here))))) B)
      (.lam (.qadd (.app A.wk (.var .here)) (.app B.wk (.var .here))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (.qadd (.app (A.wk.wk) (.var .here)) (.app (.var (.there .here)) (.var .here)))) B
    deriv_norm at hb
    exact hb
  have h3 : Deriv Δ (.eq (.app (.lam (.qadd (.app A.wk (.var .here)) (.app B.wk (.var .here)))) i)
      (.qadd (.app A i) (.app B i))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.qadd (.app A.wk (.var .here)) (.app B.wk (.var .here))) i
    deriv_norm at hb
    exact hb
  exact Deriv.transE (Deriv.congFun (Deriv.transE (Deriv.congFun h1 B) h2) i) h3

/-- Applying `tmJetInteg` to `C, i` converts to `jetIntegAt C i` inside `Deriv`. -/
def tmJetInteg_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (C : Tm Γ JetTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (tmJetInteg (Γ := Γ)) C) i) (jetIntegAt C i)) := by
  have h1 : Deriv Δ (.eq (.app (tmJetInteg (Γ := Γ)) C) (.lam (jetIntegAt C.wk (.var .here)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (jetIntegAt (.var (.there .here)) (.var .here))) C
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq (.app (.lam (jetIntegAt C.wk (.var .here))) i) (jetIntegAt C i)) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (jetIntegAt C.wk (.var .here)) i
    deriv_norm at hb
    exact hb
  exact Deriv.transE (Deriv.congFun h1 i) h2

/-- Applying `tmJetMul` to `A, B, j` converts to `tmJetMulAt A B j` inside `Deriv`. -/
def tmJetMul_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (A B : Tm Γ JetTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app (tmJetMul (Γ := Γ)) A) B) j)
                 (tmJetMulAt A B j)) := by
  have h1 : Deriv Δ (.eq (.app (tmJetMul (Γ := Γ)) A)
      (.lam (.lam (tmJetMulAt (A.wk.wk) (.var (.there .here)) (.var .here))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (.lam (tmJetMulAt (.var (.there (.there .here))) (.var (.there .here)) (.var .here)))) A
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq
      (.app (.lam (.lam (tmJetMulAt (A.wk.wk) (.var (.there .here)) (.var .here)))) B)
      (.lam (tmJetMulAt A.wk B.wk (.var .here)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (tmJetMulAt (A.wk.wk) (.var (.there .here)) (.var .here))) B
    deriv_norm at hb
    exact hb
  have h3 : Deriv Δ (.eq (.app (.lam (tmJetMulAt A.wk B.wk (.var .here))) j)
      (tmJetMulAt A B j)) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (tmJetMulAt A.wk B.wk (.var .here)) j
    deriv_norm at hb
    exact hb
  exact Deriv.transE (Deriv.congFun (Deriv.transE (Deriv.congFun h1 B) h2) j) h3

/-- Applying `tmQuadBlowupStep` to `U, i` converts to `1(i) + jetIntegAt (U·U) i` inside `Deriv`. -/
def tmQuadBlowupStep_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (tmQuadBlowupStep (Γ := Γ)) U) i)
                 (.qadd (.app tmConstOneJet i) (jetIntegAt (.app (.app tmJetMul U) U) i))) := by
  let U_sq : Tm Γ JetTy := .app (.app tmJetMul U) U
  have h1 : Deriv Δ (.eq (.app (tmQuadBlowupStep (Γ := Γ)) U)
      (.app (.app tmJetAdd tmConstOneJet) (.app tmJetInteg U_sq))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.app (.app tmJetAdd tmConstOneJet)
            (.app tmJetInteg (.app (.app tmJetMul (.var .here)) (.var .here)))) U
    deriv_norm at hb
    exact hb
  have h2 := tmJetAdd_appD (Δ := Δ) tmConstOneJet (.app tmJetInteg U_sq) i
  have h3 := Deriv.congQAdd (Δ := Δ) (Deriv.eqRefl (.app tmConstOneJet i)) (tmJetInteg_appD U_sq i)
  exact Deriv.transE (Deriv.congFun h1 i) (Deriv.transE h2 h3)

/-- `tmQuadBlowupStep` applied to `U` at `0` converts to `1(0) + 0` inside `Deriv`. -/
def tmQuadBlowupStep_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} (U : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app (tmQuadBlowupStep (Γ := Γ)) U) .zero)
                 (.qadd (.app tmConstOneJet .zero) (.qnat .zero))) :=
  Deriv.transE (tmQuadBlowupStep_appD U .zero)
    (Deriv.congQAdd (Deriv.eqRefl (.app tmConstOneJet .zero))
      (jetIntegZeroD (.app (.app tmJetMul U) U)))

/-- `tmQuadBlowupStep` applied to `U` at `succ j` converts to `1(succ j) + (U·U)(j) / (j + 1)` inside `Deriv`. -/
def tmQuadBlowupStep_succD {Γ as : List Ty} {Δ : Ctx Γ as}
    (U : Tm Γ JetTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (tmQuadBlowupStep (Γ := Γ)) U) (.succ j))
                 (.qadd (.app tmConstOneJet (.succ j))
                        (.qdiv (tmJetMulAt U U j) (.qnat (.succ j))))) := by
  let U_sq : Tm Γ JetTy := .app (.app tmJetMul U) U
  have h1 := tmQuadBlowupStep_appD (Δ := Δ) U (.succ j)
  have h2 := jetIntegSuccD (Δ := Δ) U_sq j
  have h3 := Deriv.congQDivNum (.qnat (.succ j)) (tmJetMul_appD (Δ := Δ) U U j)
  exact Deriv.transE h1
    (Deriv.congQAdd (Deriv.eqRefl (.app tmConstOneJet (.succ j))) (Deriv.transE h2 h3))

/-- From `m + e = j` and `j + succ d = k`, derive `m + succ (e + d) = k` inside `Deriv`. -/
def leLtTransAddT {Γ as : List Ty} {Δ : Ctx Γ as} {m e j d k : Tm Γ .nat}
    (h_me : Deriv Δ (.eq (.add m e) j))
    (h_jk : Deriv Δ (.eq (.add j (.succ d)) k)) :
    Deriv Δ (.eq (.add m (.succ (.add e d))) k) := by
  have h1 := Deriv.convAddSucc (Δ := Δ) m (.add e d)
  have h2 := Deriv.congSucc (Δ := Δ) (Deriv.symmE (plusAssocT (Δ := Δ) m e d))
  have h3 := Deriv.symmE (Deriv.convAddSucc (Δ := Δ) (.add m e) d)
  have h4 := Deriv.congAddL (Δ := Δ) (.succ d) h_me
  exact Deriv.transE h1 (Deriv.transE h2 (Deriv.transE h3 (Deriv.transE h4 h_jk)))

/-- Inner step of `quadBlowupIHPrefixT` in context `e :: m :: d :: j :: Y :: k :: []`. -/
def quadBlowupIHPrefixInnerT {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: .nat :: .nat :: JetTy :: .nat :: []) as}
    (h_ih_wk : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.eq (.app (.app tmQuadBlowupStep (.var (.there (.there (.there (.there (.there (.there .here))))))))
              (.var (.there .here)))
          (.app (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var (.there .here))))))))
    (h_succ_wk : Deriv Δ (.eq
      (.add (.succ (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there .here)))))
      (.succ (.var (.there (.there (.there (.there (.there .here)))))))))
    (h_me : Deriv Δ (.eq (.add (.var (.there .here)) (.var .here))
      (.var (.there (.there (.there .here)))))) :
    Deriv Δ (.eq
      (.app (.app tmQuadBlowupStep (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))
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
def quadBlowupIHPrefixT {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: JetTy :: .nat :: []) as}
    (h_ih_all : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there .here)))))))
        (.eq (.app (.app tmQuadBlowupStep (.var (.there (.there (.there (.there .here))))))
              (.var (.there .here)))
          (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here))))))))
    (h_eq_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there (.there .here))))))) :
    Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here))
              ((Tm.var (.there .here) : Tm (.nat :: .nat :: JetTy :: .nat :: []) .nat).wk.wk))
        (.eq (.app ((Tm.app tmQuadBlowupStep (.var (.there (.there .here))) :
                Tm (.nat :: .nat :: JetTy :: .nat :: []) JetTy).wk.wk) (.var (.there .here)))
          (.app ((Tm.var (.there (.there .here)) :
                Tm (.nat :: .nat :: JetTy :: .nat :: []) JetTy).wk.wk) (.var (.there .here))))))) := by
  refine Deriv.impE (Deriv.impE ?_ h_ih_all) h_eq_succ
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  exact quadBlowupIHPrefixInnerT (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax

/-- Base case (`k = 0`) of `quadBlowupSolveD`: `Y₀ = 1` vacuously solves below `0`. -/
def quadBlowupSolveBaseD : Deriv Ctx.nil (quadBlowupSolveInv.subst1 .zero) := by
  refine Deriv.exI (tmConstOneJet (Γ := [])) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let d : Tm (.nat :: .nat :: []) .nat := .var .here
  let i : Tm (.nat :: .nat :: []) .nat := .var (.there .here)
  exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.add i d))
    (Deriv.transE (Deriv.symmE (Deriv.convAddSucc i d)) Deriv.ax))

/-- Existential body of `quadBlowupSolveInv`. -/
abbrev quadBlowupSolveBody :
    Formula (JetTy :: .nat :: []) (.arrow .nat (.arrow .nat (.arrow .unit .unit))) :=
  let ctx : List Ty := .nat :: .nat :: JetTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let Y : Tm ctx JetTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  .all .nat (.all .nat
    (.imp (.eq (.add i (.succ d)) k)
      (.eq (.app (.app (tmQuadBlowupStep (Γ := ctx)) Y) i) (.app Y i))))

/-- Inner certificate of `quadBlowupSolveStepD`: `P(Y)` solves `Z = P(Z)` below degree `succ k`. -/
def quadBlowupSolveStepCertD :
    Deriv (.cons quadBlowupSolveBody (Ctx.cons quadBlowupSolveInv Ctx.nil).wk)
      (((quadBlowupSolveBody.subst (Sub.ext Sub.succHere)).rename (Ren.ext (Ren.wk JetTy))).subst1
        (.app tmQuadBlowupStep (.var .here))) := by
  deriv_norm
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let Y₀ : Tm (.nat :: JetTy :: .nat :: []) JetTy := .var (.there .here)
    let P₀ : Tm (.nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := tmQuadBlowupStep
    exact Deriv.transE (tmQuadBlowupStep_zeroD (.app P₀ Y₀))
      (Deriv.symmE (tmQuadBlowupStep_zeroD Y₀))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let j : Tm (.nat :: .nat :: JetTy :: .nat :: []) .nat := .var (.there .here)
    let Ys : Tm (.nat :: .nat :: JetTy :: .nat :: []) JetTy := .var (.there (.there .here))
    let Ps : Tm (.nat :: .nat :: JetTy :: .nat :: []) (.arrow JetTy JetTy) := tmQuadBlowupStep
    exact Deriv.transE (tmQuadBlowupStep_succD (.app Ps Ys) j)
      (Deriv.transE
        (Deriv.congQAdd (Deriv.eqRefl (.app tmConstOneJet (.succ j)))
          (Deriv.congQDivNum (.qnat (.succ j))
            (jetMulPrefixT (.app Ps Ys) Ys (.app Ps Ys) Ys j
              (quadBlowupIHPrefixT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax)
              (quadBlowupIHPrefixT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax))))
        (Deriv.symmE (tmQuadBlowupStep_succD Ys j)))

/-- Inductive step (`k → succ k`) of `quadBlowupSolveD`: map `Y ↦ P(Y)` and split on `i` via `Deriv.ind`. -/
def quadBlowupSolveStepD :
    Deriv Ctx.nil (.all .nat (.imp quadBlowupSolveInv (quadBlowupSolveInv.subst Sub.succHere))) :=
  Deriv.allI (Deriv.impI
    (Deriv.exE (ψ := quadBlowupSolveInv.subst Sub.succHere) Deriv.ax
      (Deriv.exI (.app tmQuadBlowupStep (.var .here)) quadBlowupSolveStepCertD)))

/-- First projection of the extracted base case `quadBlowupSolveBaseD`. -/
theorem extract_quadBlowupSolveBaseD_fst :
    ((extract quadBlowupSolveBaseD).eval Env.nil).1 = (tmConstOneJet (Γ := [])).eval Env.nil :=
  extract_exI_fst (tmConstOneJet (Γ := [])) _

/-- Evaluating the first projection of `extract (.allI (.impI (.exE .ax (.exI u D))))` in `Env.nil` ignores `D`. -/
theorem extract_step_exI_fst {a b : Ty}
    {body : Formula (a :: .nat :: []) b}
    (u : Tm (a :: .nat :: []) a)
    (D : Deriv (.cons body (Ctx.cons (.ex a body) Ctx.nil).wk)
      (((body.subst (Sub.ext Sub.succHere)).rename (Ren.ext (Ren.wk a))).subst1 u))
    (m : Nat) (ih : (Ty.prod a b).interp) :
    (((extract (Deriv.allI (Δ := Ctx.nil) (Deriv.impI
      (Deriv.exE (ψ := (Formula.ex a body).subst Sub.succHere) Deriv.ax
        (Deriv.exI u D))))).eval Env.nil) m ih).1 =
      u.eval (Env.cons ih.1 (Env.cons m Env.nil)) := by
  dsimp [extract, Tm.eval]
  rw [Tm.eval_rename]
  dsimp [Tm.eval]
  rw [Tm.eval_rename]
  dsimp [Tm.eval]
  rw [Tm.eval_rename]
  congr 1
  funext x v
  cases v with
  | here => rfl
  | there v =>
    cases v with
    | here => rfl
    | there v => nomatch v

/-- First projection of the extracted induction step `quadBlowupSolveStepD`. -/
theorem extract_quadBlowupSolveStepD_fst
    (m : Nat) (ih : (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp) :
    (((extract quadBlowupSolveStepD).eval Env.nil) m ih).1 =
      ((tmQuadBlowupStep (Γ := [])).eval Env.nil) ih.1 := by
  unfold quadBlowupSolveStepD
  rw [extract_step_exI_fst (body := quadBlowupSolveBody)
    (.app tmQuadBlowupStep (.var .here)) quadBlowupSolveStepCertD m ih]
  dsimp [Tm.eval]
  rw [← tmQuadBlowupStep_rename (Γ := [.nat]) (Δ := [JetTy, .nat]) (Ren.wk JetTy),
      ← tmQuadBlowupStep_rename (Γ := []) (Δ := [.nat]) (Ren.wk .nat),
      Tm.eval_wk, Tm.eval_wk]
  rfl

/-- `∀k ∃Y. Y solves Y = 1 + ∫(Y·Y) below degree k`, proved by `Deriv.ind` on `k`. -/
def quadBlowupSolveD : Deriv Ctx.nil (.all .nat quadBlowupSolveInv) :=
  Deriv.ind quadBlowupSolveBaseD quadBlowupSolveStepD

/-- The extracted solver at `k` is the `k`-th Picard iterate for `y' = y²`. -/
theorem extractClosed_quadBlowupSolveD_fst (k : Nat) :
    (((extractClosed quadBlowupSolveD).eval Env.nil) k).1 = extractedQuadBlowupJet k := by
  induction k with
  | zero =>
    have h0 := congrArg Prod.fst
      (extractClosed_ind_eval quadBlowupSolveBaseD quadBlowupSolveStepD 0)
    exact h0.trans (extract_quadBlowupSolveBaseD_fst.trans
      (extractClosed_iterSequenceD_zero JetTy tmConstOneJet tmQuadBlowupStep).symm)
  | succ m ih =>
    have hm := congrArg Prod.fst
      (extractClosed_ind_eval quadBlowupSolveBaseD quadBlowupSolveStepD m)
    have hs := congrArg Prod.fst
      (extractClosed_ind_eval quadBlowupSolveBaseD quadBlowupSolveStepD (m + 1))
    have hstep := extract_quadBlowupSolveStepD_fst m
      (Nat.rec (motive := fun _ ↦ (Ty.prod JetTy (.arrow .nat (.arrow .nat (.arrow .unit .unit)))).interp)
        ((extract quadBlowupSolveBaseD).eval Env.nil)
        (fun j acc ↦ ((extract quadBlowupSolveStepD).eval Env.nil) j acc) m)
    rw [← hm] at hstep
    exact hs.trans (hstep.trans ((congrArg ((tmQuadBlowupStep (Γ := [])).eval Env.nil) ih).trans
      (extractClosed_iterSequenceD_succ JetTy tmConstOneJet tmQuadBlowupStep m).symm))

#print axioms jetMulPrefixT
#print axioms quadBlowupSolveD
#print axioms extractClosed_quadBlowupSolveD_fst

end HAomega
