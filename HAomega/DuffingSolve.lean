/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.RiccatiSolve

/-!
# A proof-computed jet solver for the Duffing system

The system `u' = v, v' = −u − u²`, `(u, v)(0) = (1, 0)`, stated in integral
form `W = P(W)` for pairs of jets, with `P = tmDuffingStep`:
`P(u, v) = (1 + ∫v, ∫(0 − u − u·u))`. The specification says only that `W`
solves it, in both components, below degree `k`:

  `∀k ∃W. ∀i ∀d. i + succ d = k → P(W)₁(i) = W₁(i) ∧ P(W)₂(i) = W₂(i)`

Same shape as #27, #28 and Riccati, now for a system. The nonlinear term `u·u`
rests on `jetMulPrefixT` (`QuadBlowupSolve.lean`). `duffingSolveD` proves the
specification by `Deriv.ind` on `k`; the extracted solver's recursion comes
from the induction. Out of scope: the differential form.
-/

namespace HAomega

/-- Invariant over `.nat :: []`:
    `∃W. ∀i ∀d. i + succ d = k → P(W)₁(i) = W₁(i) ∧ P(W)₂(i) = W₂(i)`
    for `P = tmDuffingStep`. -/
abbrev duffingSolveInv :=
  let ctx : List Ty := .nat :: .nat :: JetPairTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let W : Tm ctx JetPairTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  let PW : Tm ctx JetPairTy := .app (tmDuffingStep (Γ := ctx)) W
  (Formula.ex JetPairTy
    (.all .nat (.all .nat
      (.imp (.eq (.add i (.succ d)) k)
        (.and (.eq (.app (.fst PW) i) (.app (.fst W) i))
              (.eq (.app (.snd PW) i) (.app (.snd W) i)))))) :
    Formula (.nat :: []) _)

/-- Congruence for `Tm.fst`, derived from `Deriv.eqSubst`. -/
def Deriv.congFst {Γ as : List Ty} {Δ : Ctx Γ as} {c d : Ty}
    {p q : Tm Γ (.prod c d)} (h : Deriv Δ (.eq p q)) :
    Deriv Δ (.eq (.fst p) (.fst q)) := by
  have hs : ∀ u : Tm Γ (.prod c d),
      (Formula.eq (.fst (.var .here)) (Tm.fst p).wk).subst1 u
        = Formula.eq (.fst u) (.fst p) := by
    intro u
    show Formula.eq (.fst u) (((Tm.fst p).wk).subst1 u) = _
    rw [Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.fst (.var .here)) (Tm.fst p).wk) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

/-- Congruence for `Tm.snd`, derived from `Deriv.eqSubst`. -/
def Deriv.congSnd {Γ as : List Ty} {Δ : Ctx Γ as} {c d : Ty}
    {p q : Tm Γ (.prod c d)} (h : Deriv Δ (.eq p q)) :
    Deriv Δ (.eq (.snd p) (.snd q)) := by
  have hs : ∀ u : Tm Γ (.prod c d),
      (Formula.eq (.snd (.var .here)) (Tm.snd p).wk).subst1 u
        = Formula.eq (.snd u) (.snd p) := by
    intro u
    show Formula.eq (.snd u) (((Tm.snd p).wk).subst1 u) = _
    rw [Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.snd (.var .here)) (Tm.snd p).wk) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

/-- Congruence for `Tm.qsub` in both arguments, derived from `Deriv.eqSubst`. -/
def Deriv.congQSub {Γ as : List Ty} {Δ : Ctx Γ as} {u u' v v' : Tm Γ .rat}
    (hu : Deriv Δ (.eq u u')) (hv : Deriv Δ (.eq v v')) :
    Deriv Δ (.eq (.qsub u v) (.qsub u' v')) := by
  have hs1 : ∀ z : Tm Γ .rat,
      (Formula.eq (.qsub u.wk (.var .here)) (Tm.qsub u v).wk).subst1 z
        = Formula.eq (.qsub u z) (.qsub u v) := by
    intro z
    show Formula.eq (.qsub (u.wk.subst1 z) z) (.qsub (u.wk.subst1 z) (v.wk.subst1 z)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have h1 := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.qsub u.wk (.var .here)) (Tm.qsub u v).wk) hv
    (by rw [hs1]; exact Deriv.eqRefl _)
  rw [hs1] at h1
  have hs2 : ∀ z : Tm Γ .rat,
      (Formula.eq (.qsub (.var .here) v'.wk) (Tm.qsub u v').wk).subst1 z
        = Formula.eq (.qsub z v') (.qsub u v') := by
    intro z
    show Formula.eq (.qsub z (v'.wk.subst1 z)) (.qsub (u.wk.subst1 z) (v'.wk.subst1 z)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have h2 := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.qsub (.var .here) v'.wk) (Tm.qsub u v').wk) hu
    (by rw [hs2]; exact Deriv.eqRefl _)
  rw [hs2] at h2
  exact Deriv.transE h1.symmE h2.symmE

/-- Renaming leaves `tmJetSub` unchanged. -/
@[derivNorm] theorem tmJetSub_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetSub (Γ := Γ)).rename ρ = tmJetSub (Γ := Δ) := rfl

/-- Substitution leaves `tmJetSub` unchanged. -/
@[derivNorm] theorem tmJetSub_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetSub (Γ := Γ)).subst s = tmJetSub (Γ := Δ) := rfl

/-- Renaming leaves `tmDuffingInit` unchanged. -/
@[derivNorm] theorem tmDuffingInit_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmDuffingInit (Γ := Γ)).rename ρ = tmDuffingInit (Γ := Δ) := rfl

/-- Substitution leaves `tmDuffingInit` unchanged. -/
@[derivNorm] theorem tmDuffingInit_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmDuffingInit (Γ := Γ)).subst s = tmDuffingInit (Γ := Δ) := rfl

/-- Renaming leaves `tmDuffingStep` unchanged. -/
@[derivNorm] theorem tmDuffingStep_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmDuffingStep (Γ := Γ)).rename ρ = tmDuffingStep (Γ := Δ) := rfl

/-- Substitution leaves `tmDuffingStep` unchanged. -/
@[derivNorm] theorem tmDuffingStep_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmDuffingStep (Γ := Γ)).subst s = tmDuffingStep (Γ := Δ) := rfl

/-- Applying `tmJetSub` to `A, B, i` converts to `.qsub (.app A i) (.app B i)` inside `Deriv`. -/
def tmJetSub_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (A B : Tm Γ JetTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app (tmJetSub (Γ := Γ)) A) B) i)
                 (.qsub (.app A i) (.app B i))) := by
  have h1 : Deriv Δ (.eq (.app (tmJetSub (Γ := Γ)) A)
      (.lam (.lam (.qsub (.app (A.wk.wk) (.var .here)) (.app (.var (.there .here)) (.var .here)))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (.lam (.qsub (.app (.var (.there (.there .here))) (.var .here))
                         (.app (.var (.there .here)) (.var .here))))) A
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq
      (.app (.lam (.lam (.qsub (.app (A.wk.wk) (.var .here)) (.app (.var (.there .here)) (.var .here))))) B)
      (.lam (.qsub (.app A.wk (.var .here)) (.app B.wk (.var .here))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (.qsub (.app (A.wk.wk) (.var .here)) (.app (.var (.there .here)) (.var .here)))) B
    deriv_norm at hb
    exact hb
  have h3 : Deriv Δ (.eq (.app (.lam (.qsub (.app A.wk (.var .here)) (.app B.wk (.var .here)))) i)
      (.qsub (.app A i) (.app B i))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.qsub (.app A.wk (.var .here)) (.app B.wk (.var .here))) i
    deriv_norm at hb
    exact hb
  exact Deriv.transE (Deriv.congFun (Deriv.transE (Deriv.congFun h1 B) h2) i) h3

/-- The forcing jet `0 - W₁ - W₁·W₁` in the second component of `tmDuffingStep`. -/
def duffingForce {Γ : List Ty} (W : Tm Γ JetPairTy) : Tm Γ JetTy :=
  .app (.app tmJetSub (.app (.app tmJetSub tmZeroJet) (.fst W)))
       (.app (.app tmJetMul (.fst W)) (.fst W))

/-- Beta-reduction of `tmDuffingStep` applied to a pair term `W` inside `Deriv`. -/
def tmDuffingStep_betaD {Γ as : List Ty} {Δ : Ctx Γ as} (W : Tm Γ JetPairTy) :
    Deriv Δ (.eq (.app (tmDuffingStep (Γ := Γ)) W)
      (.pair (.app (.app tmJetAdd tmConstOneJet) (.app tmJetInteg (.snd W)))
             (.app tmJetInteg (duffingForce W)))) := by
  have hb := Deriv.convBeta (Δ := Δ) (c := JetPairTy)
    (.pair
      (.app (.app tmJetAdd tmConstOneJet) (.app tmJetInteg (.snd (.var .here))))
      (.app tmJetInteg
        (.app (.app tmJetSub (.app (.app tmJetSub tmZeroJet) (.fst (.var .here))))
              (.app (.app tmJetMul (.fst (.var .here))) (.fst (.var .here)))))) W
  deriv_norm at hb
  exact hb

/-- First projection of `tmDuffingStep W` converts to `1 + ∫W₂` inside `Deriv`. -/
def tmDuffingStep_fstD {Γ as : List Ty} {Δ : Ctx Γ as} (W : Tm Γ JetPairTy) :
    Deriv Δ (.eq (.fst (.app (tmDuffingStep (Γ := Γ)) W))
                 (.app (.app tmJetAdd tmConstOneJet) (.app tmJetInteg (.snd W)))) :=
  Deriv.transE (Deriv.congFst (tmDuffingStep_betaD W))
    (Deriv.convFst (.app (.app tmJetAdd tmConstOneJet) (.app tmJetInteg (.snd W)))
                   (.app tmJetInteg (duffingForce W)))

/-- Second projection of `tmDuffingStep W` converts to `∫(duffingForce W)` inside `Deriv`. -/
def tmDuffingStep_sndD {Γ as : List Ty} {Δ : Ctx Γ as} (W : Tm Γ JetPairTy) :
    Deriv Δ (.eq (.snd (.app (tmDuffingStep (Γ := Γ)) W))
                 (.app tmJetInteg (duffingForce W))) :=
  Deriv.transE (Deriv.congSnd (tmDuffingStep_betaD W))
    (Deriv.convSnd (.app (.app tmJetAdd tmConstOneJet) (.app tmJetInteg (.snd W)))
                   (.app tmJetInteg (duffingForce W)))

/-- First component of `tmDuffingStep W` at `i` converts to `1(i) + jetIntegAt W₂ i` inside `Deriv`. -/
def tmDuffingStep_fst_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.fst (.app (tmDuffingStep (Γ := Γ)) W)) i)
                 (.qadd (.app tmConstOneJet i) (jetIntegAt (.snd W) i))) := by
  have h1 := Deriv.congFun (tmDuffingStep_fstD (Δ := Δ) W) i
  have h2 := tmJetAdd_appD (Δ := Δ) tmConstOneJet (.app tmJetInteg (.snd W)) i
  have h3 := Deriv.congQAdd (Δ := Δ) (Deriv.eqRefl (.app tmConstOneJet i))
    (tmJetInteg_appD (.snd W) i)
  exact Deriv.transE h1 (Deriv.transE h2 h3)

/-- First component of `tmDuffingStep W` at `0` converts to `1(0) + 0` inside `Deriv`. -/
def tmDuffingStep_fst_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} (W : Tm Γ JetPairTy) :
    Deriv Δ (.eq (.app (.fst (.app (tmDuffingStep (Γ := Γ)) W)) .zero)
                 (.qadd (.app tmConstOneJet .zero) (.qnat .zero))) :=
  Deriv.transE (tmDuffingStep_fst_appD W .zero)
    (Deriv.congQAdd (Deriv.eqRefl (.app tmConstOneJet .zero)) (jetIntegZeroD (.snd W)))

/-- First component of `tmDuffingStep W` at `succ j` converts to `1(succ j) + W₂(j) / (j + 1)` inside `Deriv`. -/
def tmDuffingStep_fst_succD {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.fst (.app (tmDuffingStep (Γ := Γ)) W)) (.succ j))
                 (.qadd (.app tmConstOneJet (.succ j))
                        (.qdiv (.app (.snd W) j) (.qnat (.succ j))))) :=
  Deriv.transE (tmDuffingStep_fst_appD W (.succ j))
    (Deriv.congQAdd (Deriv.eqRefl (.app tmConstOneJet (.succ j))) (jetIntegSuccD (.snd W) j))

/-- Second component of `tmDuffingStep W` at `i` converts to `jetIntegAt (duffingForce W) i` inside `Deriv`. -/
def tmDuffingStep_snd_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.snd (.app (tmDuffingStep (Γ := Γ)) W)) i)
                 (jetIntegAt (duffingForce W) i)) :=
  Deriv.transE (Deriv.congFun (tmDuffingStep_sndD W) i)
    (tmJetInteg_appD (duffingForce W) i)

/-- Second component of `tmDuffingStep W` at `0` converts to `0` inside `Deriv`. -/
def tmDuffingStep_snd_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} (W : Tm Γ JetPairTy) :
    Deriv Δ (.eq (.app (.snd (.app (tmDuffingStep (Γ := Γ)) W)) .zero) (.qnat .zero)) :=
  Deriv.transE (tmDuffingStep_snd_appD W .zero) (jetIntegZeroD (duffingForce W))

/-- Second component of `tmDuffingStep W` at `succ j` converts to `((0(j) - W₁(j)) - (W₁·W₁)(j)) / (j + 1)` inside `Deriv`. -/
def tmDuffingStep_snd_succD {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.snd (.app (tmDuffingStep (Γ := Γ)) W)) (.succ j))
                 (.qdiv (.qsub (.qsub (.app tmZeroJet j) (.app (.fst W) j))
                               (tmJetMulAt (.fst W) (.fst W) j))
                        (.qnat (.succ j)))) := by
  let u : Tm Γ JetTy := .fst W
  let neg_u : Tm Γ JetTy := .app (.app tmJetSub tmZeroJet) u
  let u_sq : Tm Γ JetTy := .app (.app tmJetMul u) u
  have h1 := tmDuffingStep_snd_appD (Δ := Δ) W (.succ j)
  have h2 := jetIntegSuccD (Δ := Δ) (duffingForce W) j
  have h3 := tmJetSub_appD (Δ := Δ) neg_u u_sq j
  have h4 := Deriv.congQSub (Δ := Δ)
    (tmJetSub_appD (Δ := Δ) tmZeroJet u j)
    (tmJetMul_appD (Δ := Δ) u u j)
  have h5 := Deriv.congQDivNum (.qnat (.succ j)) (Deriv.transE h3 h4)
  exact Deriv.transE h1 (Deriv.transE h2 h5)

/-- Instantiate the outer Duffing IH at `(j, d)` from `succ j + succ d = succ k` to get both component agreements at `j`. -/
def duffingIHAtJT {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: JetPairTy :: .nat :: []) as}
    (h_ih_all : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there .here)))))))
        (.and
          (.eq (.app (.fst (.app tmDuffingStep (.var (.there (.there (.there (.there .here)))))))
                (.var (.there .here)))
            (.app (.fst (.var (.there (.there (.there (.there .here)))))) (.var (.there .here))))
          (.eq (.app (.snd (.app tmDuffingStep (.var (.there (.there (.there (.there .here)))))))
                (.var (.there .here)))
            (.app (.snd (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))))))))
    (h_eq_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there (.there .here))))))) :
    Deriv Δ (.and
      (.eq (.app (.fst (.app tmDuffingStep (.var (.there (.there .here))))) (.var (.there .here)))
           (.app (.fst (.var (.there (.there .here)))) (.var (.there .here))))
      (.eq (.app (.snd (.app tmDuffingStep (.var (.there (.there .here))))) (.var (.there .here)))
           (.app (.snd (.var (.there (.there .here)))) (.var (.there .here))))) := by
  let ctx4 : List Ty := .nat :: .nat :: JetPairTy :: .nat :: []
  let d : Tm ctx4 .nat := .var .here
  let j : Tm ctx4 .nat := .var (.there .here)
  have h_inst := Deriv.allE d (Deriv.allE j h_ih_all)
  deriv_norm at h_inst
  exact Deriv.impE h_inst (succAddSuccInjT h_eq_succ)

/-- Inner step of `duffingIHPrefixFstT` in context `e :: m :: d :: j :: W :: k :: []`. -/
def duffingIHPrefixInnerFstT {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: .nat :: .nat :: JetPairTy :: .nat :: []) as}
    (h_ih_wk : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.and
          (.eq (.app (.fst (.app tmDuffingStep
                  (.var (.there (.there (.there (.there (.there (.there .here)))))))))
                (.var (.there .here)))
            (.app (.fst (.var (.there (.there (.there (.there (.there (.there .here))))))))
              (.var (.there .here))))
          (.eq (.app (.snd (.app tmDuffingStep
                  (.var (.there (.there (.there (.there (.there (.there .here)))))))))
                (.var (.there .here)))
            (.app (.snd (.var (.there (.there (.there (.there (.there (.there .here))))))))
              (.var (.there .here)))))))))
    (h_succ_wk : Deriv Δ (.eq
      (.add (.succ (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there .here)))))
      (.succ (.var (.there (.there (.there (.there (.there .here)))))))))
    (h_me : Deriv Δ (.eq (.add (.var (.there .here)) (.var .here))
      (.var (.there (.there (.there .here)))))) :
    Deriv Δ (.eq
      (.app (.fst (.app tmDuffingStep (.var (.there (.there (.there (.there .here)))))))
            (.var (.there .here)))
      (.app (.fst (.var (.there (.there (.there (.there .here))))))
            (.var (.there .here)))) := by
  let ctx6 : List Ty := .nat :: .nat :: .nat :: .nat :: JetPairTy :: .nat :: []
  let e : Tm ctx6 .nat := .var .here
  let m : Tm ctx6 .nat := .var (.there .here)
  let d : Tm ctx6 .nat := .var (.there (.there .here))
  have h_jk := succAddSuccInjT h_succ_wk
  have h_mk := leLtTransAddT h_me h_jk
  have h_inst := Deriv.allE (.add e d) (Deriv.allE m h_ih_wk)
  deriv_norm at h_inst
  exact Deriv.andE₁ (Deriv.impE h_inst h_mk)

/-- From outer Duffing IH and `succ j + succ d = succ k`, derive first-component prefix agreement `∀m ∀e. m + e = j → P(W)₁(m) = W₁(m)`. -/
def duffingIHPrefixFstT {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: JetPairTy :: .nat :: []) as}
    (h_ih_all : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there .here)))))))
        (.and
          (.eq (.app (.fst (.app tmDuffingStep (.var (.there (.there (.there (.there .here)))))))
                (.var (.there .here)))
            (.app (.fst (.var (.there (.there (.there (.there .here)))))) (.var (.there .here))))
          (.eq (.app (.snd (.app tmDuffingStep (.var (.there (.there (.there (.there .here)))))))
                (.var (.there .here)))
            (.app (.snd (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))))))))
    (h_eq_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there (.there .here))))))) :
    Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here))
              ((Tm.var (.there .here) : Tm (.nat :: .nat :: JetPairTy :: .nat :: []) .nat).wk.wk))
        (.eq (.app ((Tm.fst (.app tmDuffingStep (.var (.there (.there .here)))) :
                Tm (.nat :: .nat :: JetPairTy :: .nat :: []) JetTy).wk.wk) (.var (.there .here)))
          (.app ((Tm.fst (.var (.there (.there .here))) :
                Tm (.nat :: .nat :: JetPairTy :: .nat :: []) JetTy).wk.wk) (.var (.there .here))))))) := by
  refine Deriv.impE (Deriv.impE ?_ h_ih_all) h_eq_succ
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  exact duffingIHPrefixInnerFstT (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax

/-- Base case (`k = 0`) of `duffingSolveD`: `W₀ = (1, 0)` vacuously solves below `0`. -/
def duffingSolveBaseD : Deriv Ctx.nil (duffingSolveInv.subst1 .zero) := by
  refine Deriv.exI (tmDuffingInit (Γ := [])) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let d : Tm (.nat :: .nat :: []) .nat := .var .here
  let i : Tm (.nat :: .nat :: []) .nat := .var (.there .here)
  exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.add i d))
    (Deriv.transE (Deriv.symmE (Deriv.convAddSucc i d)) Deriv.ax))

/-- Existential body of `duffingSolveInv`. -/
abbrev duffingSolveBody :
    Formula (JetPairTy :: .nat :: []) (.arrow .nat (.arrow .nat (.arrow .unit (.prod .unit .unit)))) :=
  let ctx : List Ty := .nat :: .nat :: JetPairTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let W : Tm ctx JetPairTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  let PW : Tm ctx JetPairTy := .app (tmDuffingStep (Γ := ctx)) W
  .all .nat (.all .nat
    (.imp (.eq (.add i (.succ d)) k)
      (.and (.eq (.app (.fst PW) i) (.app (.fst W) i))
            (.eq (.app (.snd PW) i) (.app (.snd W) i)))))

/-- Inner certificate of `duffingSolveStepD`: `P(W)` solves `Z = P(Z)` in both components below degree `succ k`. -/
def duffingSolveStepCertD :
    Deriv (.cons duffingSolveBody (Ctx.cons duffingSolveInv Ctx.nil).wk)
      (((duffingSolveBody.subst (Sub.ext Sub.succHere)).rename (Ren.ext (Ren.wk JetPairTy))).subst1
        (.app tmDuffingStep (.var .here))) := by
  deriv_norm
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let W₀ : Tm (.nat :: JetPairTy :: .nat :: []) JetPairTy := .var (.there .here)
    let P₀ : Tm (.nat :: JetPairTy :: .nat :: []) (.arrow JetPairTy JetPairTy) := tmDuffingStep
    refine Deriv.andI ?_ ?_
    · exact Deriv.transE (tmDuffingStep_fst_zeroD (.app P₀ W₀))
        (Deriv.symmE (tmDuffingStep_fst_zeroD W₀))
    · exact Deriv.transE (tmDuffingStep_snd_zeroD (.app P₀ W₀))
        (Deriv.symmE (tmDuffingStep_snd_zeroD W₀))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let j : Tm (.nat :: .nat :: JetPairTy :: .nat :: []) .nat := .var (.there .here)
    let Ws : Tm (.nat :: .nat :: JetPairTy :: .nat :: []) JetPairTy := .var (.there (.there .here))
    let Ps : Tm (.nat :: .nat :: JetPairTy :: .nat :: []) (.arrow JetPairTy JetPairTy) := tmDuffingStep
    refine Deriv.andI ?_ ?_
    · exact Deriv.transE (tmDuffingStep_fst_succD (.app Ps Ws) j)
        (Deriv.transE
          (Deriv.congQAdd (Deriv.eqRefl (.app tmConstOneJet (.succ j)))
            (Deriv.congQDivNum (.qnat (.succ j))
              (Deriv.andE₂ (duffingIHAtJT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax))))
          (Deriv.symmE (tmDuffingStep_fst_succD Ws j)))
    · exact Deriv.transE (tmDuffingStep_snd_succD (.app Ps Ws) j)
        (Deriv.transE
          (Deriv.congQDivNum (.qnat (.succ j))
            (Deriv.congQSub
              (Deriv.congQSub (Deriv.eqRefl (.app tmZeroJet j))
                (Deriv.andE₁ (duffingIHAtJT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax)))
              (jetMulPrefixT (.fst (.app Ps Ws)) (.fst Ws) (.fst (.app Ps Ws)) (.fst Ws) j
                (duffingIHPrefixFstT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax)
                (duffingIHPrefixFstT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax))))
          (Deriv.symmE (tmDuffingStep_snd_succD Ws j)))

/-- Inductive step (`k → succ k`) of `duffingSolveD`: map `W ↦ P(W)` and split on `i` via `Deriv.ind`. -/
def duffingSolveStepD :
    Deriv Ctx.nil (.all .nat (.imp duffingSolveInv (duffingSolveInv.subst Sub.succHere))) :=
  Deriv.allI (Deriv.impI
    (Deriv.exE (ψ := duffingSolveInv.subst Sub.succHere) Deriv.ax
      (Deriv.exI (.app tmDuffingStep (.var .here)) duffingSolveStepCertD)))

/-- `∀k ∃W. W solves the Duffing system in integral form below degree k`,
    proved by `Deriv.ind` on `k`. -/
def duffingSolveD : Deriv Ctx.nil (.all .nat duffingSolveInv) :=
  Deriv.ind duffingSolveBaseD duffingSolveStepD

/-- First projection of the extracted base case `duffingSolveBaseD`. -/
theorem extract_duffingSolveBaseD_fst :
    ((extract duffingSolveBaseD).eval Env.nil).1 = (tmDuffingInit (Γ := [])).eval Env.nil :=
  extract_exI_fst (tmDuffingInit (Γ := [])) _

/-- First projection of the extracted induction step `duffingSolveStepD`. -/
theorem extract_duffingSolveStepD_fst
    (m : Nat) (ih : (Ty.prod JetPairTy (.arrow .nat (.arrow .nat (.arrow .unit (.prod .unit .unit))))).interp) :
    (((extract duffingSolveStepD).eval Env.nil) m ih).1 =
      ((tmDuffingStep (Γ := [])).eval Env.nil) ih.1 := by
  unfold duffingSolveStepD
  rw [extract_step_exI_fst (body := duffingSolveBody)
    (.app tmDuffingStep (.var .here)) duffingSolveStepCertD m ih]
  dsimp [Tm.eval]
  rw [← tmDuffingStep_rename (Γ := [.nat]) (Δ := [JetPairTy, .nat]) (Ren.wk JetPairTy),
      ← tmDuffingStep_rename (Γ := []) (Δ := [.nat]) (Ren.wk .nat),
      Tm.eval_wk, Tm.eval_wk]
  rfl

/-- The extracted solver at `k` is the `k`-th Picard iterate for the Duffing system. -/
theorem extractClosed_duffingSolveD_fst (k : Nat) :
    (((extractClosed duffingSolveD).eval Env.nil) k).1 = extractedDuffingJet k := by
  induction k with
  | zero =>
    have h0 := congrArg Prod.fst
      (extractClosed_ind_eval duffingSolveBaseD duffingSolveStepD 0)
    exact h0.trans (extract_duffingSolveBaseD_fst.trans
      (extractClosed_iterSequenceD_zero JetPairTy tmDuffingInit tmDuffingStep).symm)
  | succ m ih =>
    have hm := congrArg Prod.fst
      (extractClosed_ind_eval duffingSolveBaseD duffingSolveStepD m)
    have hs := congrArg Prod.fst
      (extractClosed_ind_eval duffingSolveBaseD duffingSolveStepD (m + 1))
    have hstep := extract_duffingSolveStepD_fst m
      (Nat.rec (motive := fun _ ↦ (Ty.prod JetPairTy (.arrow .nat (.arrow .nat (.arrow .unit (.prod .unit .unit))))).interp)
        ((extract duffingSolveBaseD).eval Env.nil)
        (fun j acc ↦ ((extract duffingSolveStepD).eval Env.nil) j acc) m)
    rw [← hm] at hstep
    exact hs.trans (hstep.trans ((congrArg ((tmDuffingStep (Γ := [])).eval Env.nil) ih).trans
      (extractClosed_iterSequenceD_succ JetPairTy tmDuffingInit tmDuffingStep m).symm))

#print axioms duffingSolveD
#print axioms extractClosed_duffingSolveD_fst

end HAomega
