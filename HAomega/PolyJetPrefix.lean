/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.DuffingSolve

/-!
# Polynomial–integral jet expressions and their prefix property, inside `Deriv`

`JExpr` is a small syntax of operators on one jet variable `Y`: `Y` itself,
closed jet constants, `+`, `−`, Cauchy product `×`, and `∫`. Every right-hand
side of the scalar ODEs handled so far is one of these (`Y`, `Y·Y`,
`1 + Y·Y`), and so is every polynomial ODE right-hand side.

`JExpr.prefixT` is the general form of `jetMulPrefixT`, derived inside `Deriv`
by recursion on the expression: if `y, y'` agree at every index `≤ n`, so do
`F(y), F(y')`. It is the one lemma the generic Picard solver needs.
-/

namespace HAomega

/-- Weaken a closed term into any context. -/
def Tm.closedWk {Γ : List Ty} {τ : Ty} (c : Tm [] τ) : Tm Γ τ :=
  c.rename (fun _ v ↦ by cases v)

/-- Polynomial–integral expressions in one jet variable `Y`. -/
inductive JExpr : Type where
  | var : JExpr
  | const : Tm [] JetTy → JExpr
  | add : JExpr → JExpr → JExpr
  | sub : JExpr → JExpr → JExpr
  | mul : JExpr → JExpr → JExpr
  | integ : JExpr → JExpr

/-- The jet term `F(y)`. -/
def JExpr.toTm {Γ : List Ty} (y : Tm Γ JetTy) : JExpr → Tm Γ JetTy
  | .var => y
  | .const c => Tm.closedWk c
  | .add a b => .app (.app tmJetAdd (a.toTm y)) (b.toTm y)
  | .sub a b => .app (.app tmJetSub (a.toTm y)) (b.toTm y)
  | .mul a b => .app (.app tmJetMul (a.toTm y)) (b.toTm y)
  | .integ a => .app tmJetInteg (a.toTm y)

/-- `y` and `y'` agree at every index `≤ n`: `∀m ∀d. m + d = n → y(m) = y'(m)`. -/
abbrev prefixAgree {Γ : List Ty} (y y' : Tm Γ JetTy) (n : Tm Γ .nat) :=
  (Formula.all .nat (.all .nat
    (.imp (.eq (.add (.var (.there .here)) (.var .here)) (n.wk.wk))
      (.eq (.app (y.wk.wk) (.var (.there .here))) (.app (y'.wk.wk) (.var (.there .here)))))) :
    Formula Γ _)

/-- Instantiate `prefixAgree y y' n` at indices `m, d` and apply to `m + d = n`. -/
def prefixAgreeElimT {Γ as : List Ty} {Δ : Ctx Γ as}
    {y y' : Tm Γ JetTy} {n m d : Tm Γ .nat}
    (h : Deriv Δ (prefixAgree y y' n))
    (h_md : Deriv Δ (.eq (.add m d) n)) :
    Deriv Δ (.eq (.app y m) (.app y' m)) := by
  have h_inst := Deriv.allE d (Deriv.allE m h)
  deriv_norm at h_inst
  exact Deriv.impE h_inst h_md

/-- Monotonicity of `prefixAgree`: if `c, c'` agree up to `n` and `m + d = n`, then `c, c'` agree up to `m`. -/
def prefixAgreeLeT {Γ as : List Ty} {Δ : Ctx Γ as}
    {c c' : Tm Γ JetTy} {m d n : Tm Γ .nat}
    (hc : Deriv Δ (prefixAgree c c' n))
    (h_md : Deriv Δ (.eq (.add m d) n)) :
    Deriv Δ (prefixAgree c c' m) := by
  refine Deriv.impE (Deriv.impE ?_ hc) h_md
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  let d' : Tm (.nat :: .nat :: Γ) .nat := .var .here
  let m' : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  exact prefixAgreeElimT (Deriv.wk (Deriv.wk Deriv.ax))
    (Deriv.transE (Deriv.symmE (plusAssocT m' d' d.wk.wk))
      (Deriv.transE (Deriv.congAddL d.wk.wk Deriv.ax) (Deriv.wk Deriv.ax)))

/-- Prefix agreement is preserved by `tmJetAdd`. -/
def prefixAgree_addT {Γ as : List Ty} {Δ : Ctx Γ as}
    (A A' B B' : Tm Γ JetTy) (n : Tm Γ .nat)
    (ha : Deriv Δ (prefixAgree A A' n))
    (hb : Deriv Δ (prefixAgree B B' n)) :
    Deriv Δ (prefixAgree (.app (.app tmJetAdd A) B) (.app (.app tmJetAdd A') B') n) := by
  refine Deriv.impE (Deriv.impE ?_ ha) hb
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  let m : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  let A₂ : Tm (.nat :: .nat :: Γ) JetTy := A.wk.wk
  let A'₂ : Tm (.nat :: .nat :: Γ) JetTy := A'.wk.wk
  let B₂ : Tm (.nat :: .nat :: Γ) JetTy := B.wk.wk
  let B'₂ : Tm (.nat :: .nat :: Γ) JetTy := B'.wk.wk
  exact Deriv.transE (tmJetAdd_appD A₂ B₂ m)
    (Deriv.transE
      (Deriv.congQAdd
        (prefixAgreeElimT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax)
        (prefixAgreeElimT (Deriv.wk Deriv.ax) Deriv.ax))
      (Deriv.symmE (tmJetAdd_appD A'₂ B'₂ m)))

/-- Prefix agreement is preserved by `tmJetSub`. -/
def prefixAgree_subT {Γ as : List Ty} {Δ : Ctx Γ as}
    (A A' B B' : Tm Γ JetTy) (n : Tm Γ .nat)
    (ha : Deriv Δ (prefixAgree A A' n))
    (hb : Deriv Δ (prefixAgree B B' n)) :
    Deriv Δ (prefixAgree (.app (.app tmJetSub A) B) (.app (.app tmJetSub A') B') n) := by
  refine Deriv.impE (Deriv.impE ?_ ha) hb
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  let m : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  let A₂ : Tm (.nat :: .nat :: Γ) JetTy := A.wk.wk
  let A'₂ : Tm (.nat :: .nat :: Γ) JetTy := A'.wk.wk
  let B₂ : Tm (.nat :: .nat :: Γ) JetTy := B.wk.wk
  let B'₂ : Tm (.nat :: .nat :: Γ) JetTy := B'.wk.wk
  exact Deriv.transE (tmJetSub_appD A₂ B₂ m)
    (Deriv.transE
      (Deriv.congQSub
        (prefixAgreeElimT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax)
        (prefixAgreeElimT (Deriv.wk Deriv.ax) Deriv.ax))
      (Deriv.symmE (tmJetSub_appD A'₂ B'₂ m)))

/-- Prefix agreement is preserved by `tmJetMul`. -/
def prefixAgree_mulT {Γ as : List Ty} {Δ : Ctx Γ as}
    (A A' B B' : Tm Γ JetTy) (n : Tm Γ .nat)
    (ha : Deriv Δ (prefixAgree A A' n))
    (hb : Deriv Δ (prefixAgree B B' n)) :
    Deriv Δ (prefixAgree (.app (.app tmJetMul A) B) (.app (.app tmJetMul A') B') n) := by
  refine Deriv.impE (Deriv.impE ?_ ha) hb
  refine Deriv.impI (Deriv.impI ?_)
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  let m : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  let A₂ : Tm (.nat :: .nat :: Γ) JetTy := A.wk.wk
  let A'₂ : Tm (.nat :: .nat :: Γ) JetTy := A'.wk.wk
  let B₂ : Tm (.nat :: .nat :: Γ) JetTy := B.wk.wk
  let B'₂ : Tm (.nat :: .nat :: Γ) JetTy := B'.wk.wk
  exact Deriv.transE (tmJetMul_appD A₂ B₂ m)
    (Deriv.transE
      (jetMulPrefixT A₂ A'₂ B₂ B'₂ m
        (prefixAgreeLeT (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax)
        (prefixAgreeLeT (Deriv.wk Deriv.ax) Deriv.ax))
      (Deriv.symmE (tmJetMul_appD A'₂ B'₂ m)))

/-- Prefix agreement is preserved by `tmJetInteg`, proved by `Deriv.ind` on the index `m`. -/
def prefixAgree_integT {Γ as : List Ty} {Δ : Ctx Γ as}
    (A A' : Tm Γ JetTy) (n : Tm Γ .nat)
    (ha : Deriv Δ (prefixAgree A A' n)) :
    Deriv Δ (prefixAgree (.app tmJetInteg A) (.app tmJetInteg A') n) := by
  refine Deriv.impE ?_ ha
  refine Deriv.impI ?_
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    let A₁ : Tm (.nat :: Γ) JetTy := A.wk
    let A'₁ : Tm (.nat :: Γ) JetTy := A'.wk
    exact Deriv.transE (tmJetInteg_appD A₁ .zero)
      (Deriv.transE (jetIntegZeroD A₁)
        (Deriv.symmE (Deriv.transE (tmJetInteg_appD A'₁ .zero) (jetIntegZeroD A'₁))))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    let d : Tm (.nat :: .nat :: Γ) .nat := .var .here
    let j : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
    let A₂ : Tm (.nat :: .nat :: Γ) JetTy := A.wk.wk
    let A'₂ : Tm (.nat :: .nat :: Γ) JetTy := A'.wk.wk
    exact Deriv.transE (tmJetInteg_appD A₂ (.succ j))
      (Deriv.transE (jetIntegSuccD A₂ j)
        (Deriv.transE
          (Deriv.congQDivNum (.qnat (.succ j))
            (prefixAgreeElimT (Deriv.wk (Deriv.wk Deriv.ax))
              (Deriv.transE (Deriv.convAddSucc j d)
                (Deriv.transE (Deriv.symmE (succPlusT j d)) Deriv.ax))))
          (Deriv.symmE (Deriv.transE (tmJetInteg_appD A'₂ (.succ j)) (jetIntegSuccD A'₂ j)))))

/-- **Prefix property of every `JExpr`, inside `Deriv`.** If `y, y'` agree at
    every index `≤ n`, then so do `F(y)` and `F(y')`. -/
def JExpr.prefixT (F : JExpr) {Γ as : List Ty} {Δ : Ctx Γ as}
    (y y' : Tm Γ JetTy) (n : Tm Γ .nat)
    (h : Deriv Δ (prefixAgree y y' n)) :
    Deriv Δ (prefixAgree (F.toTm y) (F.toTm y') n) := by
  cases F with
  | var => exact h
  | const _ => exact Deriv.allI (Deriv.allI (Deriv.impI (Deriv.eqRefl _)))
  | add a b =>
    exact prefixAgree_addT (a.toTm y) (a.toTm y') (b.toTm y) (b.toTm y') n
      (a.prefixT y y' n h) (b.prefixT y y' n h)
  | sub a b =>
    exact prefixAgree_subT (a.toTm y) (a.toTm y') (b.toTm y) (b.toTm y') n
      (a.prefixT y y' n h) (b.prefixT y y' n h)
  | mul a b =>
    exact prefixAgree_mulT (a.toTm y) (a.toTm y') (b.toTm y) (b.toTm y') n
      (a.prefixT y y' n h) (b.prefixT y y' n h)
  | integ a =>
    exact prefixAgree_integT (a.toTm y) (a.toTm y') n (a.prefixT y y' n h)

#print axioms JExpr.prefixT

end HAomega
