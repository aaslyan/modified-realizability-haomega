/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PolyODEInstances

/-!
# One proof-computed jet solver for every two-variable polynomial–integral system

`PolyODESolve.lean` handles one jet variable. This module handles systems in
two, which is what brings `sin` and `cos` into the universe (as the pair
`u' = v, v' = −u`) and covers the Duffing oscillator.

`JExpr2` is `JExpr` with two jet variables `U`, `V`. For closed initial jets
`A, B` and right-hand sides `F, G : JExpr2`, the Picard operator is
`P(u, v) = (A + ∫F(u, v), B + ∫G(u, v))` (`genStep2`), and `genSolve2D` proves

  `∀k ∃W. ∀i ∀d. i + succ d = k → P(W)₁(i) = W₁(i) ∧ P(W)₂(i) = W₂(i)`

by `Deriv.ind` on `k`, resting on `JExpr2.prefixT`. The statement names the
system, never the iteration; the extract is the Picard iteration from `(A, B)`.

Instances: Duffing (`genSolve2_duffing_eq`, exact `Q`-valued equality with
`extractedDuffingJet`) and sine/cosine (`genSolve2_sinCos_val`: below degree
`k`, the `k`-th iterate has the Taylor coefficients of `sin` and `cos`, as
rational values).
-/

namespace HAomega

/-- Polynomial–integral expressions in two jet variables `U`, `V`. -/
inductive JExpr2 : Type where
  | varU : JExpr2
  | varV : JExpr2
  | const : Tm [] JetTy → JExpr2
  | add : JExpr2 → JExpr2 → JExpr2
  | sub : JExpr2 → JExpr2 → JExpr2
  | mul : JExpr2 → JExpr2 → JExpr2
  | integ : JExpr2 → JExpr2

/-- The jet term `F(u, v)`. -/
def JExpr2.toTm {Γ : List Ty} (u v : Tm Γ JetTy) : JExpr2 → Tm Γ JetTy
  | .varU => u
  | .varV => v
  | .const c => Tm.closedWk c
  | .add a b => .app (.app tmJetAdd (a.toTm u v)) (b.toTm u v)
  | .sub a b => .app (.app tmJetSub (a.toTm u v)) (b.toTm u v)
  | .mul a b => .app (.app tmJetMul (a.toTm u v)) (b.toTm u v)
  | .integ a => .app tmJetInteg (a.toTm u v)

/-- **Prefix property of every `JExpr2`, inside `Deriv`.** If `u, u'` and `v, v'`
    agree at every index `≤ n`, then so do `F(u, v)` and `F(u', v')`. -/
def JExpr2.prefixT (F : JExpr2) {Γ as : List Ty} {Δ : Ctx Γ as}
    (u u' v v' : Tm Γ JetTy) (n : Tm Γ .nat)
    (hu : Deriv Δ (prefixAgree u u' n)) (hv : Deriv Δ (prefixAgree v v' n)) :
    Deriv Δ (prefixAgree (F.toTm u v) (F.toTm u' v') n) := by
  cases F with
  | varU => exact hu
  | varV => exact hv
  | const _ => exact Deriv.allI (Deriv.allI (Deriv.impI (Deriv.eqRefl _)))
  | add a b =>
    exact prefixAgree_addT (a.toTm u v) (a.toTm u' v') (b.toTm u v) (b.toTm u' v') n
      (a.prefixT u u' v v' n hu hv) (b.prefixT u u' v v' n hu hv)
  | sub a b =>
    exact prefixAgree_subT (a.toTm u v) (a.toTm u' v') (b.toTm u v) (b.toTm u' v') n
      (a.prefixT u u' v v' n hu hv) (b.prefixT u u' v v' n hu hv)
  | mul a b =>
    exact prefixAgree_mulT (a.toTm u v) (a.toTm u' v') (b.toTm u v) (b.toTm u' v') n
      (a.prefixT u u' v v' n hu hv) (b.prefixT u u' v v' n hu hv)
  | integ a =>
    exact prefixAgree_integT (a.toTm u v) (a.toTm u' v') n (a.prefixT u u' v v' n hu hv)

/-- The Picard operator `P(u, v) = (A + ∫F(u, v), B + ∫G(u, v))`. -/
def genStep2 (A B : Tm [] JetTy) (F G : JExpr2) {Γ : List Ty} :
    Tm Γ (.arrow JetPairTy JetPairTy) :=
  .lam (.pair
    (.app (.app tmJetAdd (Tm.closedWk A))
      (.app tmJetInteg (F.toTm (.fst (.var .here)) (.snd (.var .here)))))
    (.app (.app tmJetAdd (Tm.closedWk B))
      (.app tmJetInteg (G.toTm (.fst (.var .here)) (.snd (.var .here))))))

/-- Invariant over `.nat :: []`:
    `∃W. ∀i ∀d. i + succ d = k → P(W)₁(i) = W₁(i) ∧ P(W)₂(i) = W₂(i)`. -/
abbrev genSolve2Inv (A B : Tm [] JetTy) (F G : JExpr2) :=
  let ctx : List Ty := .nat :: .nat :: JetPairTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let W : Tm ctx JetPairTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  let PW : Tm ctx JetPairTy := .app (genStep2 A B F G (Γ := ctx)) W
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

/-- Renaming commutes with `JExpr2.toTm`. -/
@[derivNorm] theorem JExpr2.toTm_rename (F : JExpr2) {Γ Δ : List Ty}
    (u v : Tm Γ JetTy) (ρ : Ren Γ Δ) :
    (F.toTm u v).rename ρ = F.toTm (u.rename ρ) (v.rename ρ) := by
  induction F with
  | varU => rfl
  | varV => rfl
  | const c => exact closedWk_rename c ρ
  | add a b iha ihb =>
    simp only [JExpr2.toTm, Tm.rename, tmJetAdd_rename, iha, ihb]
  | sub a b iha ihb =>
    simp only [JExpr2.toTm, Tm.rename, tmJetSub_rename, iha, ihb]
  | mul a b iha ihb =>
    simp only [JExpr2.toTm, Tm.rename, tmJetMul_rename, iha, ihb]
  | integ a iha =>
    simp only [JExpr2.toTm, Tm.rename, tmJetInteg_rename, iha]

/-- Substitution commutes with `JExpr2.toTm`. -/
@[derivNorm] theorem JExpr2.toTm_subst (F : JExpr2) {Γ Δ : List Ty}
    (u v : Tm Γ JetTy) (s : Sub Γ Δ) :
    (F.toTm u v).subst s = F.toTm (u.subst s) (v.subst s) := by
  induction F with
  | varU => rfl
  | varV => rfl
  | const c => exact closedWk_subst c s
  | add a b iha ihb =>
    simp only [JExpr2.toTm, Tm.subst, tmJetAdd_subst, iha, ihb]
  | sub a b iha ihb =>
    simp only [JExpr2.toTm, Tm.subst, tmJetSub_subst, iha, ihb]
  | mul a b iha ihb =>
    simp only [JExpr2.toTm, Tm.subst, tmJetMul_subst, iha, ihb]
  | integ a iha =>
    simp only [JExpr2.toTm, Tm.subst, tmJetInteg_subst, iha]

/-- Renaming leaves `genStep2 A B F G` unchanged. -/
@[derivNorm] theorem genStep2_rename (A B : Tm [] JetTy) (F G : JExpr2)
    {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (genStep2 A B F G (Γ := Γ)).rename ρ = genStep2 A B F G (Γ := Δ) := by
  simp only [genStep2, Tm.rename, tmJetAdd_rename, closedWk_rename, tmJetInteg_rename,
    JExpr2.toTm_rename]
  rfl

/-- Substitution leaves `genStep2 A B F G` unchanged. -/
@[derivNorm] theorem genStep2_subst (A B : Tm [] JetTy) (F G : JExpr2)
    {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (genStep2 A B F G (Γ := Γ)).subst s = genStep2 A B F G (Γ := Δ) := by
  simp only [genStep2, Tm.subst, tmJetAdd_subst, closedWk_subst, tmJetInteg_subst,
    JExpr2.toTm_subst]
  rfl

/-- Applying `genStep2 A B F G` to `W` converts to `(A + ∫F(W₁, W₂), B + ∫G(W₁, W₂))` inside `Deriv`. -/
def genStep2_pairD (A B : Tm [] JetTy) (F G : JExpr2) {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) :
    Deriv Δ (.eq (.app (genStep2 A B F G (Γ := Γ)) W)
                 (.pair
                   (.app (.app tmJetAdd (Tm.closedWk A))
                     (.app tmJetInteg (F.toTm (.fst W) (.snd W))))
                   (.app (.app tmJetAdd (Tm.closedWk B))
                     (.app tmJetInteg (G.toTm (.fst W) (.snd W)))))) := by
  have hb := Deriv.convBeta (Δ := Δ) (c := JetPairTy)
    (.pair
      (.app (.app tmJetAdd (Tm.closedWk A))
        (.app tmJetInteg (F.toTm (.fst (.var .here)) (.snd (.var .here)))))
      (.app (.app tmJetAdd (Tm.closedWk B))
        (.app tmJetInteg (G.toTm (.fst (.var .here)) (.snd (.var .here)))))) W
  deriv_norm at hb
  exact hb

/-- First component of `genStep2 A B F G` applied to `W` at `i` converts to `A(i) + jetIntegAt (F.toTm W₁ W₂) i`. -/
def genStep2_fst_appD (A B : Tm [] JetTy) (F G : JExpr2) {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.fst (.app (genStep2 A B F G (Γ := Γ)) W)) i)
                 (.qadd (.app (Tm.closedWk A) i) (jetIntegAt (F.toTm (.fst W) (.snd W)) i))) := by
  let FW : Tm Γ JetTy := F.toTm (.fst W) (.snd W)
  let GW : Tm Γ JetTy := G.toTm (.fst W) (.snd W)
  let u_next : Tm Γ JetTy := .app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg FW)
  let v_next : Tm Γ JetTy := .app (.app tmJetAdd (Tm.closedWk B)) (.app tmJetInteg GW)
  have h1 := Deriv.transE (Deriv.congFst (genStep2_pairD (Δ := Δ) A B F G W))
    (Deriv.convFst u_next v_next)
  have h2 := tmJetAdd_appD (Δ := Δ) (Tm.closedWk A) (.app tmJetInteg FW) i
  have h3 := Deriv.congQAdd (Δ := Δ) (Deriv.eqRefl (.app (Tm.closedWk A) i))
    (tmJetInteg_appD FW i)
  exact Deriv.transE (Deriv.congFun h1 i) (Deriv.transE h2 h3)

/-- Second component of `genStep2 A B F G` applied to `W` at `i` converts to `B(i) + jetIntegAt (G.toTm W₁ W₂) i`. -/
def genStep2_snd_appD (A B : Tm [] JetTy) (F G : JExpr2) {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) (i : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.snd (.app (genStep2 A B F G (Γ := Γ)) W)) i)
                 (.qadd (.app (Tm.closedWk B) i) (jetIntegAt (G.toTm (.fst W) (.snd W)) i))) := by
  let FW : Tm Γ JetTy := F.toTm (.fst W) (.snd W)
  let GW : Tm Γ JetTy := G.toTm (.fst W) (.snd W)
  let u_next : Tm Γ JetTy := .app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg FW)
  let v_next : Tm Γ JetTy := .app (.app tmJetAdd (Tm.closedWk B)) (.app tmJetInteg GW)
  have h1 := Deriv.transE (Deriv.congSnd (genStep2_pairD (Δ := Δ) A B F G W))
    (Deriv.convSnd u_next v_next)
  have h2 := tmJetAdd_appD (Δ := Δ) (Tm.closedWk B) (.app tmJetInteg GW) i
  have h3 := Deriv.congQAdd (Δ := Δ) (Deriv.eqRefl (.app (Tm.closedWk B) i))
    (tmJetInteg_appD GW i)
  exact Deriv.transE (Deriv.congFun h1 i) (Deriv.transE h2 h3)

/-- First component of `genStep2 A B F G` at `0` converts to `A(0) + 0`. -/
def genStep2_fst_zeroD (A B : Tm [] JetTy) (F G : JExpr2) {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) :
    Deriv Δ (.eq (.app (.fst (.app (genStep2 A B F G (Γ := Γ)) W)) .zero)
                 (.qadd (.app (Tm.closedWk A) .zero) (.qnat .zero))) :=
  Deriv.transE (genStep2_fst_appD A B F G W .zero)
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) .zero))
      (jetIntegZeroD (F.toTm (.fst W) (.snd W))))

/-- First component of `genStep2 A B F G` at `succ j` converts to `A(succ j) + F(W₁, W₂)(j) / (j + 1)`. -/
def genStep2_fst_succD (A B : Tm [] JetTy) (F G : JExpr2) {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.fst (.app (genStep2 A B F G (Γ := Γ)) W)) (.succ j))
                 (.qadd (.app (Tm.closedWk A) (.succ j))
                        (.qdiv (.app (F.toTm (.fst W) (.snd W)) j) (.qnat (.succ j))))) :=
  Deriv.transE (genStep2_fst_appD A B F G W (.succ j))
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) (.succ j)))
      (jetIntegSuccD (F.toTm (.fst W) (.snd W)) j))

/-- Second component of `genStep2 A B F G` at `0` converts to `B(0) + 0`. -/
def genStep2_snd_zeroD (A B : Tm [] JetTy) (F G : JExpr2) {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) :
    Deriv Δ (.eq (.app (.snd (.app (genStep2 A B F G (Γ := Γ)) W)) .zero)
                 (.qadd (.app (Tm.closedWk B) .zero) (.qnat .zero))) :=
  Deriv.transE (genStep2_snd_appD A B F G W .zero)
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk B) .zero))
      (jetIntegZeroD (G.toTm (.fst W) (.snd W))))

/-- Second component of `genStep2 A B F G` at `succ j` converts to `B(succ j) + G(W₁, W₂)(j) / (j + 1)`. -/
def genStep2_snd_succD (A B : Tm [] JetTy) (F G : JExpr2) {Γ as : List Ty} {Δ : Ctx Γ as}
    (W : Tm Γ JetPairTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.snd (.app (genStep2 A B F G (Γ := Γ)) W)) (.succ j))
                 (.qadd (.app (Tm.closedWk B) (.succ j))
                        (.qdiv (.app (G.toTm (.fst W) (.snd W)) j) (.qnat (.succ j))))) :=
  Deriv.transE (genStep2_snd_appD A B F G W (.succ j))
    (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk B) (.succ j)))
      (jetIntegSuccD (G.toTm (.fst W) (.snd W)) j))

/-- Inner step of `genSolve2IHPrefixFstT` and `genSolve2IHPrefixSndT` in context `e :: m :: d :: j :: W :: k :: []`. -/
def genSolve2IHPrefixInnerT (A B : Tm [] JetTy) (F G : JExpr2) {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: .nat :: .nat :: JetPairTy :: .nat :: []) as}
    (h_ih_wk : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.and
          (.eq (.app (.fst (.app (genStep2 A B F G)
                  (.var (.there (.there (.there (.there (.there (.there .here)))))))))
                (.var (.there .here)))
            (.app (.fst (.var (.there (.there (.there (.there (.there (.there .here))))))))
              (.var (.there .here))))
          (.eq (.app (.snd (.app (genStep2 A B F G)
                  (.var (.there (.there (.there (.there (.there (.there .here)))))))))
                (.var (.there .here)))
            (.app (.snd (.var (.there (.there (.there (.there (.there (.there .here))))))))
              (.var (.there .here)))))))))
    (h_succ_wk : Deriv Δ (.eq
      (.add (.succ (.var (.there (.there (.there .here))))) (.succ (.var (.there (.there .here)))))
      (.succ (.var (.there (.there (.there (.there (.there .here)))))))))
    (h_me : Deriv Δ (.eq (.add (.var (.there .here)) (.var .here))
      (.var (.there (.there (.there .here)))))) :
    Deriv Δ (.and
      (.eq (.app (.fst (.app (genStep2 A B F G) (.var (.there (.there (.there (.there .here)))))))
            (.var (.there .here)))
        (.app (.fst (.var (.there (.there (.there (.there .here)))))) (.var (.there .here))))
      (.eq (.app (.snd (.app (genStep2 A B F G) (.var (.there (.there (.there (.there .here)))))))
            (.var (.there .here)))
        (.app (.snd (.var (.there (.there (.there (.there .here)))))) (.var (.there .here))))) := by
  let ctx6 : List Ty := .nat :: .nat :: .nat :: .nat :: JetPairTy :: .nat :: []
  let e : Tm ctx6 .nat := .var .here
  let m : Tm ctx6 .nat := .var (.there .here)
  let d : Tm ctx6 .nat := .var (.there (.there .here))
  have h_jk := succAddSuccInjT h_succ_wk
  have h_mk := leLtTransAddT h_me h_jk
  have h_inst := Deriv.allE (.add e d) (Deriv.allE m h_ih_wk)
  deriv_norm at h_inst
  exact Deriv.impE h_inst h_mk

/-- From outer IH and `succ j + succ d = succ k`, derive `prefixAgree (P(W)₁) (W₁) j`. -/
def genSolve2IHPrefixFstT (A B : Tm [] JetTy) (F G : JExpr2) {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: JetPairTy :: .nat :: []) as}
    (h_ih_all : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there .here)))))))
        (.and
          (.eq (.app (.fst (.app (genStep2 A B F G) (.var (.there (.there (.there (.there .here)))))))
                (.var (.there .here)))
            (.app (.fst (.var (.there (.there (.there (.there .here)))))) (.var (.there .here))))
          (.eq (.app (.snd (.app (genStep2 A B F G) (.var (.there (.there (.there (.there .here)))))))
                (.var (.there .here)))
            (.app (.snd (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))))))))
    (h_eq_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there (.there .here))))))) :
    Deriv Δ (prefixAgree
      (.fst (.app (genStep2 A B F G (Γ := .nat :: .nat :: JetPairTy :: .nat :: []))
        (.var (.there (.there .here)))))
      (.fst (.var (.there (.there .here))))
      (.var (.there .here))) := by
  refine Deriv.impE (Deriv.impE ?_ h_ih_all) h_eq_succ
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  exact Deriv.andE₁
    (genSolve2IHPrefixInnerT A B F G (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax)

/-- From outer IH and `succ j + succ d = succ k`, derive `prefixAgree (P(W)₂) (W₂) j`. -/
def genSolve2IHPrefixSndT (A B : Tm [] JetTy) (F G : JExpr2) {as : List Ty}
    {Δ : Ctx (.nat :: .nat :: JetPairTy :: .nat :: []) as}
    (h_ih_all : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there .here)))))))
        (.and
          (.eq (.app (.fst (.app (genStep2 A B F G) (.var (.there (.there (.there (.there .here)))))))
                (.var (.there .here)))
            (.app (.fst (.var (.there (.there (.there (.there .here)))))) (.var (.there .here))))
          (.eq (.app (.snd (.app (genStep2 A B F G) (.var (.there (.there (.there (.there .here)))))))
                (.var (.there .here)))
            (.app (.snd (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))))))))
    (h_eq_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there (.there .here))))))) :
    Deriv Δ (prefixAgree
      (.snd (.app (genStep2 A B F G (Γ := .nat :: .nat :: JetPairTy :: .nat :: []))
        (.var (.there (.there .here)))))
      (.snd (.var (.there (.there .here))))
      (.var (.there .here))) := by
  refine Deriv.impE (Deriv.impE ?_ h_ih_all) h_eq_succ
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  exact Deriv.andE₂
    (genSolve2IHPrefixInnerT A B F G (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax)

/-- Base case (`k = 0`) of `genSolve2D`: `W₀ = (A, B)` vacuously solves below `0`. -/
def genSolve2BaseD (A B : Tm [] JetTy) (F G : JExpr2) :
    Deriv Ctx.nil ((genSolve2Inv A B F G).subst1 .zero) := by
  refine Deriv.exI (.pair (Tm.closedWk A) (Tm.closedWk B)) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let d : Tm (.nat :: .nat :: []) .nat := .var .here
  let i : Tm (.nat :: .nat :: []) .nat := .var (.there .here)
  exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.add i d))
    (Deriv.transE (Deriv.symmE (Deriv.convAddSucc i d)) Deriv.ax))

/-- Existential body of `genSolve2Inv A B F G`. -/
abbrev genSolve2Body (A B : Tm [] JetTy) (F G : JExpr2) :
    Formula (JetPairTy :: .nat :: []) (.arrow .nat (.arrow .nat (.arrow .unit (.prod .unit .unit)))) :=
  let ctx : List Ty := .nat :: .nat :: JetPairTy :: .nat :: []
  let d : Tm ctx .nat := .var .here
  let i : Tm ctx .nat := .var (.there .here)
  let W : Tm ctx JetPairTy := .var (.there (.there .here))
  let k : Tm ctx .nat := .var (.there (.there (.there .here)))
  let PW : Tm ctx JetPairTy := .app (genStep2 A B F G (Γ := ctx)) W
  .all .nat (.all .nat
    (.imp (.eq (.add i (.succ d)) k)
      (.and (.eq (.app (.fst PW) i) (.app (.fst W) i))
            (.eq (.app (.snd PW) i) (.app (.snd W) i)))))

/-- Inner certificate of `genSolve2StepD`: `P(W)` solves `Z = P(Z)` in both components below degree `succ k`. -/
def genSolve2StepCertD (A B : Tm [] JetTy) (F G : JExpr2) :
    Deriv (.cons (genSolve2Body A B F G) (Ctx.cons (genSolve2Inv A B F G) Ctx.nil).wk)
      ((((genSolve2Body A B F G).subst (Sub.ext Sub.succHere)).rename (Ren.ext (Ren.wk JetPairTy))).subst1
        (.app (genStep2 A B F G) (.var .here))) := by
  deriv_norm
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let W₀ : Tm (.nat :: JetPairTy :: .nat :: []) JetPairTy := .var (.there .here)
    let P₀ : Tm (.nat :: JetPairTy :: .nat :: []) (.arrow JetPairTy JetPairTy) := genStep2 A B F G
    refine Deriv.andI ?_ ?_
    · exact Deriv.transE (genStep2_fst_zeroD A B F G (.app P₀ W₀))
        (Deriv.symmE (genStep2_fst_zeroD A B F G W₀))
    · exact Deriv.transE (genStep2_snd_zeroD A B F G (.app P₀ W₀))
        (Deriv.symmE (genStep2_snd_zeroD A B F G W₀))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    let j : Tm (.nat :: .nat :: JetPairTy :: .nat :: []) .nat := .var (.there .here)
    let Ws : Tm (.nat :: .nat :: JetPairTy :: .nat :: []) JetPairTy := .var (.there (.there .here))
    let Ps : Tm (.nat :: .nat :: JetPairTy :: .nat :: []) (.arrow JetPairTy JetPairTy) := genStep2 A B F G
    refine Deriv.andI ?_ ?_
    · exact Deriv.transE (genStep2_fst_succD A B F G (.app Ps Ws) j)
        (Deriv.transE
          (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk A) (.succ j)))
            (Deriv.congQDivNum (.qnat (.succ j))
              (prefixAgreeElimT
                (F.prefixT (.fst (.app Ps Ws)) (.fst Ws) (.snd (.app Ps Ws)) (.snd Ws) j
                  (genSolve2IHPrefixFstT A B F G (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax)
                  (genSolve2IHPrefixSndT A B F G (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax))
                (Deriv.convAddZero j))))
          (Deriv.symmE (genStep2_fst_succD A B F G Ws j)))
    · exact Deriv.transE (genStep2_snd_succD A B F G (.app Ps Ws) j)
        (Deriv.transE
          (Deriv.congQAdd (Deriv.eqRefl (.app (Tm.closedWk B) (.succ j)))
            (Deriv.congQDivNum (.qnat (.succ j))
              (prefixAgreeElimT
                (G.prefixT (.fst (.app Ps Ws)) (.fst Ws) (.snd (.app Ps Ws)) (.snd Ws) j
                  (genSolve2IHPrefixFstT A B F G (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax)
                  (genSolve2IHPrefixSndT A B F G (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax))
                (Deriv.convAddZero j))))
          (Deriv.symmE (genStep2_snd_succD A B F G Ws j)))

/-- Inductive step (`k → succ k`) of `genSolve2D`: map `W ↦ P(W)` and split on `i` via `Deriv.ind`. -/
def genSolve2StepD (A B : Tm [] JetTy) (F G : JExpr2) :
    Deriv Ctx.nil (.all .nat (.imp (genSolve2Inv A B F G) ((genSolve2Inv A B F G).subst Sub.succHere))) :=
  Deriv.allI (Deriv.impI
    (Deriv.exE (ψ := (genSolve2Inv A B F G).subst Sub.succHere) Deriv.ax
      (Deriv.exI (.app (genStep2 A B F G) (.var .here)) (genSolve2StepCertD A B F G))))

/-- **The general two-variable solver**, by `Deriv.ind` on `k`. -/
def genSolve2D (A B : Tm [] JetTy) (F G : JExpr2) :
    Deriv Ctx.nil (.all .nat (genSolve2Inv A B F G)) :=
  Deriv.ind (genSolve2BaseD A B F G) (genSolve2StepD A B F G)

/-- First projection of the extracted base case `genSolve2BaseD A B F G`. -/
theorem extract_genSolve2BaseD_fst (A B : Tm [] JetTy) (F G : JExpr2) :
    ((extract (genSolve2BaseD A B F G)).eval Env.nil).1 = (A.eval Env.nil, B.eval Env.nil) :=
  (extract_exI_fst (.pair (Tm.closedWk A) (Tm.closedWk B)) _).trans
    (Prod.ext (closedWk_nil_eval A) (closedWk_nil_eval B))

/-- First projection of the extracted induction step `genSolve2StepD A B F G`. -/
theorem extract_genSolve2StepD_fst (A B : Tm [] JetTy) (F G : JExpr2)
    (m : Nat) (ih : (Ty.prod JetPairTy (.arrow .nat (.arrow .nat (.arrow .unit (.prod .unit .unit))))).interp) :
    (((extract (genSolve2StepD A B F G)).eval Env.nil) m ih).1 =
      ((genStep2 A B F G (Γ := [])).eval Env.nil) ih.1 := by
  unfold genSolve2StepD
  rw [extract_step_exI_fst (body := genSolve2Body A B F G)
    (.app (genStep2 A B F G) (.var .here)) (genSolve2StepCertD A B F G) m ih]
  dsimp [Tm.eval]
  rw [← genStep2_rename A B F G (Γ := [.nat]) (Δ := [JetPairTy, .nat]) (Ren.wk JetPairTy),
      ← genStep2_rename A B F G (Γ := []) (Δ := [.nat]) (Ren.wk .nat),
      Tm.eval_wk, Tm.eval_wk]
  rfl

/-- The extracted solver at `k` is the `k`-th Picard iterate from `(A, B)`. -/
theorem extractClosed_genSolve2D_fst (A B : Tm [] JetTy) (F G : JExpr2) (k : Nat) :
    (((extractClosed (genSolve2D A B F G)).eval Env.nil) k).1 =
      ((genStep2 A B F G (Γ := [])).eval Env.nil)^[k] (A.eval Env.nil, B.eval Env.nil) := by
  induction k with
  | zero =>
    have h0 := congrArg Prod.fst
      (extractClosed_ind_eval (genSolve2BaseD A B F G) (genSolve2StepD A B F G) 0)
    exact h0.trans (extract_genSolve2BaseD_fst A B F G)
  | succ m ih =>
    have hm := congrArg Prod.fst
      (extractClosed_ind_eval (genSolve2BaseD A B F G) (genSolve2StepD A B F G) m)
    have hs := congrArg Prod.fst
      (extractClosed_ind_eval (genSolve2BaseD A B F G) (genSolve2StepD A B F G) (m + 1))
    have hstep := extract_genSolve2StepD_fst A B F G m
      (Nat.rec (motive := fun _ ↦ (Ty.prod JetPairTy (.arrow .nat (.arrow .nat (.arrow .unit (.prod .unit .unit))))).interp)
        ((extract (genSolve2BaseD A B F G)).eval Env.nil)
        (fun j acc ↦ ((extract (genSolve2StepD A B F G)).eval Env.nil) j acc) m)
    rw [← hm] at hstep
    rw [Function.iterate_succ_apply']
    exact hs.trans (hstep.trans (congrArg ((genStep2 A B F G (Γ := [])).eval Env.nil) ih))

/-- The general 2-variable step for the Duffing system evaluates to the same function as `tmDuffingStep`. -/
theorem genStep2_duffing_eval :
    (genStep2 tmConstOneJet tmZeroJet .varV
      (.sub (.sub (.const tmZeroJet) .varU) (.mul .varU .varU)) (Γ := [])).eval Env.nil =
      (tmDuffingStep (Γ := [])).eval Env.nil := by
  funext W
  refine Prod.ext rfl ?_
  funext n
  dsimp [genStep2, tmDuffingStep, JExpr2.toTm, Tm.closedWk, tmZeroJet, tmJetAdd, tmJetInteg, jetIntegAt, Tm.eval]
  cases n with
  | zero => exact Q.zero_add_of_coprime (Q.ofNat 0) (Nat.gcd_zero_left 1)
  | succ m => exact Q.zero_add_div_ofNat_succ _ m

/-- Iterating `step.eval Env.nil` from `y0.eval Env.nil` at `JetPairTy` equals `extractClosed (iterSequenceD JetPairTy y0 step)`. -/
theorem iterate_eval_eq_iterSequenceD_pair (y0 : Tm [] JetPairTy) (step : Tm [] (.arrow JetPairTy JetPairTy)) (k : Nat) :
    ((step.eval Env.nil)^[k] (y0.eval Env.nil)) =
      (((extractClosed (iterSequenceD JetPairTy y0 step)).eval Env.nil) k).1 := by
  induction k with
  | zero =>
    exact (extractClosed_iterSequenceD_zero JetPairTy y0 step).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih,
      extractClosed_iterSequenceD_succ JetPairTy y0 step m]

/-- Duffing `u' = v, v' = −u − u²`, `(u, v)(0) = (1, 0)` is an instance. -/
theorem genSolve2_duffing_eq (k : Nat) :
    (((extractClosed (genSolve2D tmConstOneJet tmZeroJet .varV
      (.sub (.sub (.const tmZeroJet) .varU) (.mul .varU .varU)))).eval Env.nil) k).1 =
      extractedDuffingJet k := by
  rw [extractClosed_genSolve2D_fst, genStep2_duffing_eval]
  exact iterate_eval_eq_iterSequenceD_pair tmDuffingInit tmDuffingStep k

/-- Below degree `k`, the `k`-th iterate of the sine/cosine Picard operator has the rational values of `Jet.sin` and `Jet.cos`. -/
theorem sinCos_iterate_val : ∀ (k i : Nat), i < k →
    let W := ((genStep2 tmZeroJet tmConstOneJet .varV
      (.sub (.const tmZeroJet) .varU) (Γ := [])).eval Env.nil)^[k]
        ((tmZeroJet (Γ := [])).eval Env.nil, (tmConstOneJet (Γ := [])).eval Env.nil)
    (W.1 i).val = (Jet.sin.coeff i).val ∧ (W.2 i).val = (Jet.cos.coeff i).val
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, 0, _ => by
    dsimp only
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_⟩
    · change (Q.add (Q.ofNat 0) (Q.ofNat 0)).val = Q.zero.val
      rw [Q.zero_add_of_coprime (Q.ofNat 0) (Nat.gcd_zero_left 1)]
      rfl
    · change (Q.add (Q.ofNat 1) (Q.ofNat 0)).val = (Q.ofNat 1).val
      rw [Q.one_add_zero]
  | m + 1, j + 1, hi => by
    have hj : j < m := Nat.lt_of_succ_lt_succ hi
    have ih := sinCos_iterate_val m j hj
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    set Wm := ((genStep2 tmZeroJet tmConstOneJet .varV
      (.sub (.const tmZeroJet) .varU) (Γ := [])).eval Env.nil)^[m]
        ((tmZeroJet (Γ := [])).eval Env.nil, (tmConstOneJet (Γ := [])).eval Env.nil)
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    refine ⟨?_, ?_⟩
    · change (Q.add (Q.ofNat 0) (Q.div (Wm.2 j) (Q.ofNat (j + 1)))).val =
        (Q.div (Jet.cos.coeff j) (Q.ofNat (j + 1))).val
      rw [Q.zero_add_div_ofNat_succ, Q.val_div _ _ hne, Q.val_div _ _ hne, ih.2]
    · change (Q.add (Q.ofNat 0) (Q.div (Q.sub (Q.ofNat 0) (Wm.1 j)) (Q.ofNat (j + 1)))).val =
        (Q.div (Q.neg (Jet.sin.coeff j)) (Q.ofNat (j + 1))).val
      rw [Q.zero_add_div_ofNat_succ, Q.val_div _ _ hne, Q.val_div _ _ hne,
          Q.val_sub, Q.val_ofNat, Q.val_neg, ih.1]
      ring

/-- Sine and cosine: `u' = v, v' = −u`, `(u, v)(0) = (0, 1)`. Below degree `k`
    the `k`-th iterate has the Taylor coefficients of `sin` and `cos`. -/
theorem genSolve2_sinCos_val (k i : Nat) (hi : i < k) :
    let W := (((extractClosed (genSolve2D tmZeroJet tmConstOneJet .varV
      (.sub (.const tmZeroJet) .varU))).eval Env.nil) k).1
    (W.1 i).val = (Jet.sin.coeff i).val ∧ (W.2 i).val = (Jet.cos.coeff i).val := by
  dsimp only
  rw [extractClosed_genSolve2D_fst]
  exact sinCos_iterate_val k i hi

#print axioms JExpr2.prefixT
#print axioms genSolve2D
#print axioms extractClosed_genSolve2D_fst
#print axioms genSolve2_duffing_eq
#print axioms genSolve2_sinCos_val

end HAomega
