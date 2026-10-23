/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.JetCauchyComputed

/-!
# Proof-computed continuity and differentiability moduli

`jetContModulusD` and `jetDiffModulusD` (`MajorantDom.lean`, catalog #20, #21)
write their moduli `k + (B + 1)` at `exI` and certify them with
`Deriv.convQLipScale`: explicit witnesses. Here the same algorithm-free
conclusions (`jetContConcl`, `jetDiffConcl`) are proved with the modulus
computed by `Deriv.ind` on the precision `k`, through the invariant

  `∃ω. ∀j ∀m. close(ω + j, x, y) → close(k + j, S_m(x), S_m(y))`

(resp. with the difference quotient): base `ω = B + 1` (from the Lipschitz
premise by `convQLipScale`), step `ω ↦ ω + 1` (the hypothesis at `j + 1`, since
`succ ω + j = ω + succ j`), and `j = 0` at the end. No `ℚ`-laws beyond the
existing premise are needed. The extracted moduli are the recursions this
induction produces; they equal `k + (B + 1)`.
-/

namespace HAomega

/-- Congruence for `qclose` in its scale argument `s`. -/
def jetModuli_qcloseCongS {Γ as : List Ty} {Δ : Ctx Γ as} {s s' : Tm Γ .nat} (u v : Tm Γ .rat)
    (hs : Deriv Δ (.eq s s'))
    (h : Deriv Δ (.eq (.app (.app (.app qclose s) u) v) (.succ .zero))) :
    Deriv Δ (.eq (.app (.app (.app qclose s') u) v) (.succ .zero)) := by
  have heq : Deriv Δ (.eq (.app (.app (.app qclose s) u) v) (.app (.app (.app qclose s') u) v)) :=
    Deriv.congFun (Deriv.congFun (Deriv.congArg qclose hs) u) v
  have hsub : ∀ z : Tm Γ .nat,
      (Formula.eq (.var .here) (.succ .zero)).subst1 z = Formula.eq z (.succ .zero) :=
    fun _ ↦ rfl
  have key := Deriv.eqSubst (Δ := Δ) (Formula.eq (.var .here) (.succ .zero))
    heq (by rw [hsub]; exact h)
  rw [hsub] at key
  exact key

/-- Existential body `∀j ∀m. close(ω + j, x, y) → close(k + j, S_m(x), S_m(y))` over `ω :: k :: y :: x :: B1 :: c :: Γ`. -/
abbrev jetContModBody (Γ : List Ty) :
    Formula (.nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ)
      (.arrow .nat (.arrow .nat (.arrow .unit .unit))) :=
  let ctx : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx .nat := .var .here
  let j  : Tm ctx .nat := .var (.there .here)
  let om : Tm ctx .nat := .var (.there (.there .here))
  let k  : Tm ctx .nat := .var (.there (.there (.there .here)))
  let y  : Tm ctx .rat := .var (.there (.there (.there (.there .here))))
  let x  : Tm ctx .rat := .var (.there (.there (.there (.there (.there .here)))))
  let c  : Tm ctx JetTy := .var (.there (.there (.there (.there (.there (.there (.there .here)))))))
  .all .nat (.all .nat
    (.imp (.eq (.app (.app (.app qclose (.add om j)) x) y) (.succ .zero))
          (.eq (.app (.app (.app qclose (.add k j)) (jetEvalAt c m x)) (jetEvalAt c m y)) (.succ .zero))))

/-- Inductive invariant `∃ω. ∀j ∀m. close(ω + j, x, y) → close(k + j, S_m(x), S_m(y))` over `k :: y :: x :: B1 :: c :: Γ`. -/
abbrev jetContModInv (Γ : List Ty) :
    Formula (.nat :: .rat :: .rat :: .nat :: JetTy :: Γ)
      (.prod .nat (.arrow .nat (.arrow .nat (.arrow .unit .unit)))) :=
  .ex .nat (jetContModBody Γ)

/-- Context over `y :: x :: B1 :: c :: Γ` containing `jetLipPremise`. -/
abbrev jetContModCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.rat :: .rat :: .nat :: JetTy :: Γ) ((.arrow .nat .unit) :: as) :=
  .cons (jetLipPremise Γ) ((((Δ.wk).wk).wk).wk)

/-- Base case (`k = 0`) of the continuity modulus induction, with witness `.succ B1`. -/
def jetContModBaseD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv (jetContModCtx Γ Δ) ((jetContModInv Γ).subst1 .zero) := by
  refine Deriv.exI (.succ (.var (.there (.there .here)))) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let ctx2 : List Ty := .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx2 .nat := .var .here
  let j  : Tm ctx2 .nat := .var (.there .here)
  let y  : Tm ctx2 .rat := .var (.there (.there .here))
  let x  : Tm ctx2 .rat := .var (.there (.there (.there .here)))
  let B1 : Tm ctx2 .nat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx2 JetTy := .var (.there (.there (.there (.there (.there .here)))))
  let baseCtx :=
    Ctx.cons (.eq (.app (.app (.app qclose (.add (.succ B1) j)) x) y) (.succ .zero))
      (((jetContModCtx Γ Δ).wk (σ := .nat)).wk (σ := .nat))
  have hClose : Deriv baseCtx
      (.eq (.app (.app (.app qclose (.add (.succ B1) j)) x) y) (.succ .zero)) := Deriv.ax
  have hPrem : Deriv baseCtx (((jetLipPremise Γ).wk (σ := .nat)).wk (σ := .nat)) :=
    Deriv.wk Deriv.ax
  have hLip := Deriv.allE (τ := .nat) m hPrem
  deriv_norm at hLip
  have h0j := Deriv.allE (τ := .nat) j (zeroPlusD (Δ := baseCtx))
  deriv_norm at h0j
  have hScale : Deriv baseCtx (.eq (.add (.succ B1) j) (.add (.add .zero j) (.succ B1))) :=
    Deriv.transE (plusCommT (.succ B1) j) (Deriv.congAddL (.succ B1) h0j.symmE)
  have hClose' := jetModuli_qcloseCongS x y hScale hClose
  exact Deriv.convQLipScale (.add .zero j) (.succ B1) x y (jetEvalAt c m x) (jetEvalAt c m y)
    hLip hClose'

/-- Inductive step (`k → succ k`) of the continuity modulus induction, advancing witness `ω` to `.succ ω`. -/
def jetContModStepD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv (jetContModCtx Γ Δ)
      (.all .nat (.imp (jetContModInv Γ) ((jetContModInv Γ).subst Sub.succHere))) := by
  refine Deriv.allI (Deriv.impI ?_)
  refine Deriv.exE (ψ := (jetContModInv Γ).subst Sub.succHere) Deriv.ax ?_
  refine Deriv.exI (.succ (.var .here)) ?_
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let ctx4 : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx4 .nat := .var .here
  let j  : Tm ctx4 .nat := .var (.there .here)
  let om : Tm ctx4 .nat := .var (.there (.there .here))
  let k  : Tm ctx4 .nat := .var (.there (.there (.there .here)))
  let y  : Tm ctx4 .rat := .var (.there (.there (.there (.there .here))))
  let x  : Tm ctx4 .rat := .var (.there (.there (.there (.there (.there .here)))))
  let c  : Tm ctx4 JetTy := .var (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let stepCtx :=
    Ctx.cons (.eq (.app (.app (.app qclose (.add (.succ om) j)) x) y) (.succ .zero))
      (Ctx.cons (((jetContModBody Γ).wk (σ := .nat)).wk (σ := .nat))
        (Ctx.cons ((((jetContModInv Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))
          (((((jetContModCtx Γ Δ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))))
  have hClose : Deriv stepCtx
      (.eq (.app (.app (.app qclose (.add (.succ om) j)) x) y) (.succ .zero)) := Deriv.ax
  have hIH : Deriv stepCtx (((jetContModBody Γ).wk (σ := .nat)).wk (σ := .nat)) :=
    Deriv.wk Deriv.ax
  have hIH1 := Deriv.allE (τ := .nat) (.succ j) hIH
  deriv_norm at hIH1
  have hIH2 := Deriv.allE (τ := .nat) m hIH1
  deriv_norm at hIH2
  have hScaleIn : Deriv stepCtx (.eq (.add (.succ om) j) (.add om (.succ j))) :=
    Deriv.transE (succPlusT om j) (Deriv.convAddSucc om j).symmE
  have hCloseIn := jetModuli_qcloseCongS x y hScaleIn hClose
  have hOut := Deriv.impE hIH2 hCloseIn
  have hScaleOut : Deriv stepCtx (.eq (.add k (.succ j)) (.add (.succ k) j)) :=
    Deriv.transE (Deriv.convAddSucc k j) (succPlusT k j).symmE
  exact jetModuli_qcloseCongS (jetEvalAt c m x) (jetEvalAt c m y) hScaleOut hOut

/-- Re-packing `jetContModInv` at `j = 0` into `jetContConcl`. -/
def jetContModRepackD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv (jetContModCtx Γ Δ) (.imp (.all .nat (jetContModInv Γ)) (jetContConcl Γ)) := by
  refine Deriv.impI (Deriv.allI ?_)
  have hIndAll : Deriv (Ctx.cons (.all .nat (jetContModInv Γ)) (jetContModCtx Γ Δ)).wk
      ((Formula.all .nat (jetContModInv Γ)).wk (σ := .nat)) := Deriv.ax
  refine Deriv.exE (Deriv.allE (.var .here) hIndAll) ?_
  refine Deriv.exI (.var .here) ?_
  refine Deriv.allI (Deriv.impI ?_)
  let ctx3 : List Ty := .nat :: .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx3 .nat := .var .here
  let om : Tm ctx3 .nat := .var (.there .here)
  let k  : Tm ctx3 .nat := .var (.there (.there .here))
  let y  : Tm ctx3 .rat := .var (.there (.there (.there .here)))
  let x  : Tm ctx3 .rat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx3 JetTy := .var (.there (.there (.there (.there (.there (.there .here))))))
  let φ_om := ((jetContModBody Γ).rename (Ren.ext (Ren.ext (Ren.wk .nat)))).subst
    (Sub.ext (Sub.one (.var .here)))
  let repackCtx :=
    Ctx.cons (.eq (.app (.app (.app qclose om) x) y) (.succ .zero))
      (Ctx.cons (φ_om.wk (σ := .nat))
        (Ctx.cons ((((Formula.all .nat (jetContModInv Γ)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))
          ((((jetContModCtx Γ Δ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))))
  have hClose : Deriv repackCtx
      (.eq (.app (.app (.app qclose om) x) y) (.succ .zero)) := Deriv.ax
  have hBody : Deriv repackCtx (φ_om.wk (σ := .nat)) := Deriv.wk Deriv.ax
  have hB1 := Deriv.allE (τ := .nat) .zero hBody
  deriv_norm at hB1
  have hB2 := Deriv.allE (τ := .nat) m hB1
  deriv_norm at hB2
  have hClose0 := jetModuli_qcloseCongS x y (Deriv.convAddZero om).symmE hClose
  have hOut0 := Deriv.impE hB2 hClose0
  exact jetModuli_qcloseCongS (jetEvalAt c m x) (jetEvalAt c m y) (Deriv.convAddZero k) hOut0

/-- **Proof-computed uniform continuity modulus**, by `Deriv.ind` on `k`. -/
def jetContModulusComputedD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all JetTy (.all .nat (.all .rat (.all .rat
      (.imp (jetLipPremise Γ) (jetContConcl Γ)))))) :=
  Deriv.allI (Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI
    (Deriv.impE jetContModRepackD (Deriv.ind jetContModBaseD jetContModStepD))))))

/-- Existential body `∀j ∀m. close(ω + j, h, 0) → close(k + j, diffQuot_m(x, h), S_m'(x))` over `ω :: k :: h :: x :: B2 :: c :: Γ`. -/
abbrev jetDiffModBody (Γ : List Ty) :
    Formula (.nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ)
      (.arrow .nat (.arrow .nat (.arrow .unit .unit))) :=
  let ctx : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx .nat := .var .here
  let j  : Tm ctx .nat := .var (.there .here)
  let om : Tm ctx .nat := .var (.there (.there .here))
  let k  : Tm ctx .nat := .var (.there (.there (.there .here)))
  let h  : Tm ctx .rat := .var (.there (.there (.there (.there .here))))
  let x  : Tm ctx .rat := .var (.there (.there (.there (.there (.there .here)))))
  let c  : Tm ctx JetTy := .var (.there (.there (.there (.there (.there (.there (.there .here)))))))
  .all .nat (.all .nat
    (.imp (.eq (.app (.app (.app qclose (.add om j)) h) (.qnat .zero)) (.succ .zero))
          (.eq (.app (.app (.app qclose (.add k j)) (jetDiffQuotAt c m x h))
                     (jetEvalAt (.app tmJetDeriv c) m x)) (.succ .zero))))

/-- Inductive invariant `∃ω. ∀j ∀m. close(ω + j, h, 0) → close(k + j, diffQuot_m(x, h), S_m'(x))` over `k :: h :: x :: B2 :: c :: Γ`. -/
abbrev jetDiffModInv (Γ : List Ty) :
    Formula (.nat :: .rat :: .rat :: .nat :: JetTy :: Γ)
      (.prod .nat (.arrow .nat (.arrow .nat (.arrow .unit .unit)))) :=
  .ex .nat (jetDiffModBody Γ)

/-- Context over `h :: x :: B2 :: c :: Γ` containing `jetDiffPremise`. -/
abbrev jetDiffModCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.rat :: .rat :: .nat :: JetTy :: Γ) ((.arrow .nat .unit) :: as) :=
  .cons (jetDiffPremise Γ) ((((Δ.wk).wk).wk).wk)

/-- Base case (`k = 0`) of the differentiability modulus induction, with witness `.succ B2`. -/
def jetDiffModBaseD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv (jetDiffModCtx Γ Δ) ((jetDiffModInv Γ).subst1 .zero) := by
  refine Deriv.exI (.succ (.var (.there (.there .here)))) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let ctx2 : List Ty := .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx2 .nat := .var .here
  let j  : Tm ctx2 .nat := .var (.there .here)
  let h  : Tm ctx2 .rat := .var (.there (.there .here))
  let x  : Tm ctx2 .rat := .var (.there (.there (.there .here)))
  let B2 : Tm ctx2 .nat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx2 JetTy := .var (.there (.there (.there (.there (.there .here)))))
  let baseCtx :=
    Ctx.cons (.eq (.app (.app (.app qclose (.add (.succ B2) j)) h) (.qnat .zero)) (.succ .zero))
      (((jetDiffModCtx Γ Δ).wk (σ := .nat)).wk (σ := .nat))
  have hClose : Deriv baseCtx
      (.eq (.app (.app (.app qclose (.add (.succ B2) j)) h) (.qnat .zero)) (.succ .zero)) := Deriv.ax
  have hPrem : Deriv baseCtx (((jetDiffPremise Γ).wk (σ := .nat)).wk (σ := .nat)) :=
    Deriv.wk Deriv.ax
  have hLip := Deriv.allE (τ := .nat) m hPrem
  deriv_norm at hLip
  have h0j := Deriv.allE (τ := .nat) j (zeroPlusD (Δ := baseCtx))
  deriv_norm at h0j
  have hScale : Deriv baseCtx (.eq (.add (.succ B2) j) (.add (.add .zero j) (.succ B2))) :=
    Deriv.transE (plusCommT (.succ B2) j) (Deriv.congAddL (.succ B2) h0j.symmE)
  have hClose' := jetModuli_qcloseCongS h (.qnat .zero) hScale hClose
  exact Deriv.convQLipScale (.add .zero j) (.succ B2) h (.qnat .zero)
    (jetDiffQuotAt c m x h) (jetEvalAt (.app tmJetDeriv c) m x) hLip hClose'

/-- Inductive step (`k → succ k`) of the differentiability modulus induction, advancing witness `ω` to `.succ ω`. -/
def jetDiffModStepD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv (jetDiffModCtx Γ Δ)
      (.all .nat (.imp (jetDiffModInv Γ) ((jetDiffModInv Γ).subst Sub.succHere))) := by
  refine Deriv.allI (Deriv.impI ?_)
  refine Deriv.exE (ψ := (jetDiffModInv Γ).subst Sub.succHere) Deriv.ax ?_
  refine Deriv.exI (.succ (.var .here)) ?_
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let ctx4 : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx4 .nat := .var .here
  let j  : Tm ctx4 .nat := .var (.there .here)
  let om : Tm ctx4 .nat := .var (.there (.there .here))
  let k  : Tm ctx4 .nat := .var (.there (.there (.there .here)))
  let h  : Tm ctx4 .rat := .var (.there (.there (.there (.there .here))))
  let x  : Tm ctx4 .rat := .var (.there (.there (.there (.there (.there .here)))))
  let c  : Tm ctx4 JetTy := .var (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let stepCtx :=
    Ctx.cons (.eq (.app (.app (.app qclose (.add (.succ om) j)) h) (.qnat .zero)) (.succ .zero))
      (Ctx.cons (((jetDiffModBody Γ).wk (σ := .nat)).wk (σ := .nat))
        (Ctx.cons ((((jetDiffModInv Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))
          (((((jetDiffModCtx Γ Δ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))))
  have hClose : Deriv stepCtx
      (.eq (.app (.app (.app qclose (.add (.succ om) j)) h) (.qnat .zero)) (.succ .zero)) := Deriv.ax
  have hIH : Deriv stepCtx (((jetDiffModBody Γ).wk (σ := .nat)).wk (σ := .nat)) :=
    Deriv.wk Deriv.ax
  have hIH1 := Deriv.allE (τ := .nat) (.succ j) hIH
  deriv_norm at hIH1
  have hIH2 := Deriv.allE (τ := .nat) m hIH1
  deriv_norm at hIH2
  have hScaleIn : Deriv stepCtx (.eq (.add (.succ om) j) (.add om (.succ j))) :=
    Deriv.transE (succPlusT om j) (Deriv.convAddSucc om j).symmE
  have hCloseIn := jetModuli_qcloseCongS h (.qnat .zero) hScaleIn hClose
  have hOut := Deriv.impE hIH2 hCloseIn
  have hScaleOut : Deriv stepCtx (.eq (.add k (.succ j)) (.add (.succ k) j)) :=
    Deriv.transE (Deriv.convAddSucc k j) (succPlusT k j).symmE
  exact jetModuli_qcloseCongS (jetDiffQuotAt c m x h) (jetEvalAt (.app tmJetDeriv c) m x)
    hScaleOut hOut

/-- Re-packing `jetDiffModInv` at `j = 0` into `jetDiffConcl`. -/
def jetDiffModRepackD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv (jetDiffModCtx Γ Δ) (.imp (.all .nat (jetDiffModInv Γ)) (jetDiffConcl Γ)) := by
  refine Deriv.impI (Deriv.allI ?_)
  have hIndAll : Deriv (Ctx.cons (.all .nat (jetDiffModInv Γ)) (jetDiffModCtx Γ Δ)).wk
      ((Formula.all .nat (jetDiffModInv Γ)).wk (σ := .nat)) := Deriv.ax
  refine Deriv.exE (Deriv.allE (.var .here) hIndAll) ?_
  refine Deriv.exI (.var .here) ?_
  refine Deriv.allI (Deriv.impI ?_)
  let ctx3 : List Ty := .nat :: .nat :: .nat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let m  : Tm ctx3 .nat := .var .here
  let om : Tm ctx3 .nat := .var (.there .here)
  let k  : Tm ctx3 .nat := .var (.there (.there .here))
  let h  : Tm ctx3 .rat := .var (.there (.there (.there .here)))
  let x  : Tm ctx3 .rat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx3 JetTy := .var (.there (.there (.there (.there (.there (.there .here))))))
  let φ_om := ((jetDiffModBody Γ).rename (Ren.ext (Ren.ext (Ren.wk .nat)))).subst
    (Sub.ext (Sub.one (.var .here)))
  let repackCtx :=
    Ctx.cons (.eq (.app (.app (.app qclose om) h) (.qnat .zero)) (.succ .zero))
      (Ctx.cons (φ_om.wk (σ := .nat))
        (Ctx.cons ((((Formula.all .nat (jetDiffModInv Γ)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))
          ((((jetDiffModCtx Γ Δ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))))
  have hClose : Deriv repackCtx
      (.eq (.app (.app (.app qclose om) h) (.qnat .zero)) (.succ .zero)) := Deriv.ax
  have hBody : Deriv repackCtx (φ_om.wk (σ := .nat)) := Deriv.wk Deriv.ax
  have hB1 := Deriv.allE (τ := .nat) .zero hBody
  deriv_norm at hB1
  have hB2 := Deriv.allE (τ := .nat) m hB1
  deriv_norm at hB2
  have hClose0 := jetModuli_qcloseCongS h (.qnat .zero) (Deriv.convAddZero om).symmE hClose
  have hOut0 := Deriv.impE hB2 hClose0
  exact jetModuli_qcloseCongS (jetDiffQuotAt c m x h) (jetEvalAt (.app tmJetDeriv c) m x)
    (Deriv.convAddZero k) hOut0

/-- **Proof-computed differentiability modulus**, by `Deriv.ind` on `k`. -/
def jetDiffModulusComputedD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all JetTy (.all .nat (.all .rat (.all .rat
      (.imp (jetDiffPremise Γ) (jetDiffConcl Γ)))))) :=
  Deriv.allI (Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI
    (Deriv.impE jetDiffModRepackD (Deriv.ind jetDiffModBaseD jetDiffModStepD))))))

def extractedJetContModulusComputed (c : Nat → Q) (B1 : Nat) (x y : Q) (k : Nat) : Nat :=
  ((((extractClosed (jetContModulusComputedD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    c B1 x y (fun _ ↦ ())) k).1

def extractedJetDiffModulusComputed (c : Nat → Q) (B2 : Nat) (x h : Q) (k : Nat) : Nat :=
  ((((extractClosed (jetDiffModulusComputedD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    c B2 x h (fun _ ↦ ())) k).1

theorem extractedJetContModulusComputed_eq (c : Nat → Q) (B1 : Nat) (x y : Q) (k : Nat) :
    extractedJetContModulusComputed c B1 x y k = k + (B1 + 1) := by
  let a1 : Ty := .arrow .nat .unit
  let p1 : a1.interp := fun _ ↦ ()
  let ec : Env [JetTy] := Env.cons (σ := JetTy) c Env.nil
  let eB : Env [.nat, JetTy] := Env.cons (σ := .nat) B1 ec
  let ex : Env [.rat, .nat, JetTy] := Env.cons (σ := .rat) x eB
  let ey : Env [.rat, .rat, .nat, JetTy] := Env.cons (σ := .rat) y ex
  let e0 : Env [a1, .rat, .rat, .nat, JetTy] := Env.cons (σ := a1) p1 ey
  let D_core : Deriv (jetContModCtx [] Ctx.nil) (jetContConcl []) :=
    Deriv.impE jetContModRepackD (Deriv.ind jetContModBaseD jetContModStepD)
  let D_y : Deriv ((Ctx.nil (Γ := [])).wk.wk.wk.wk)
      (.imp (jetLipPremise []) (jetContConcl [])) :=
    Deriv.impI D_core
  let D_x : Deriv ((Ctx.nil (Γ := [])).wk.wk.wk) (.all .rat _) := Deriv.allI D_y
  let D_B : Deriv ((Ctx.nil (Γ := [])).wk.wk) (.all .rat (.all .rat _)) := Deriv.allI D_x
  let D_c : Deriv ((Ctx.nil (Γ := [])).wk) (.all .nat (.all .rat (.all .rat _))) := Deriv.allI D_B
  have hc : ((extractClosed (jetContModulusComputedD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) c =
      (extract D_c).eval ec :=
    jetHalve_eval_exch_nil (extract D_c) ec
  have hB : ((extract D_c).eval ec) B1 = (extract D_B).eval eB :=
    jetHalve_eval_exch_nil (extract D_B) eB
  have hx : ((extract D_B).eval eB) x = (extract D_x).eval ex :=
    jetHalve_eval_exch_nil (extract D_x) ex
  have hy : ((extract D_x).eval ex) y = (extract D_y).eval ey :=
    jetHalve_eval_exch_nil (extract D_y) ey
  let D_repack := jetContModRepackD (Γ := []) (as := []) (Δ := Ctx.nil)
  let D1 := jetContModBaseD (Γ := []) (as := []) (Δ := Ctx.nil)
  let D2 := jetContModStepD (Γ := []) (as := []) (Δ := Ctx.nil)
  let R : Ty := .prod .nat (.arrow .nat (.arrow .nat (.arrow .unit .unit)))
  have h_repack : ∀ (f : Nat → R.interp), (((extract D_repack).eval e0) f k).1 = (f k).1 :=
    fun _ ↦ rfl
  have h_chain : extractedJetContModulusComputed c B1 x y k =
      (((extract D_repack).eval e0) ((extract (Deriv.ind D1 D2)).eval e0) k).1 := by
    unfold extractedJetContModulusComputed
    rw [hc, hB, hx, hy]
    rfl
  rw [h_chain, h_repack]
  change (Nat.rec (motive := fun _ ↦ R.interp)
    (((extract D1).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0))
    (fun m ih ↦ (((extract D2).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0)) m ih)
    k).1 = k + (B1 + 1)
  have hz : ((extract D1).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0) =
      (extract D1).eval e0 :=
    Tm.eval_wk (σ := .nat) (extract D1) k e0
  have hs : (fun (m : Nat) (ih : R.interp) ↦
      (((extract D2).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0)) m ih) =
      (fun (m : Nat) (ih : R.interp) ↦ ((extract D2).eval e0) m ih) := by
    funext m ih
    exact congrFun (congrFun (Tm.eval_wk (σ := .nat) (extract D2) k e0) m) ih
  rw [hz, hs]
  clear h_repack h_chain hz hs
  have h0 : (((extract D1).eval e0).1 : Nat) = B1 + 1 := rfl
  have hstep : ∀ (m : Nat) (ih : R.interp),
      ((((extract D2).eval e0) m ih).1 : Nat) = (ih.1 : Nat) + 1 :=
    fun _ _ ↦ rfl
  induction k with
  | zero =>
    exact h0.trans (Nat.zero_add (B1 + 1)).symm
  | succ m ih =>
    exact (hstep m _).trans ((congrArg (· + 1) ih).trans (Nat.add_right_comm m (B1 + 1) 1))

theorem extractedJetDiffModulusComputed_eq (c : Nat → Q) (B2 : Nat) (x h : Q) (k : Nat) :
    extractedJetDiffModulusComputed c B2 x h k = k + (B2 + 1) := by
  let a1 : Ty := .arrow .nat .unit
  let p1 : a1.interp := fun _ ↦ ()
  let ec : Env [JetTy] := Env.cons (σ := JetTy) c Env.nil
  let eB : Env [.nat, JetTy] := Env.cons (σ := .nat) B2 ec
  let ex : Env [.rat, .nat, JetTy] := Env.cons (σ := .rat) x eB
  let eh : Env [.rat, .rat, .nat, JetTy] := Env.cons (σ := .rat) h ex
  let e0 : Env [a1, .rat, .rat, .nat, JetTy] := Env.cons (σ := a1) p1 eh
  let D_core : Deriv (jetDiffModCtx [] Ctx.nil) (jetDiffConcl []) :=
    Deriv.impE jetDiffModRepackD (Deriv.ind jetDiffModBaseD jetDiffModStepD)
  let D_h : Deriv ((Ctx.nil (Γ := [])).wk.wk.wk.wk)
      (.imp (jetDiffPremise []) (jetDiffConcl [])) :=
    Deriv.impI D_core
  let D_x : Deriv ((Ctx.nil (Γ := [])).wk.wk.wk) (.all .rat _) := Deriv.allI D_h
  let D_B : Deriv ((Ctx.nil (Γ := [])).wk.wk) (.all .rat (.all .rat _)) := Deriv.allI D_x
  let D_c : Deriv ((Ctx.nil (Γ := [])).wk) (.all .nat (.all .rat (.all .rat _))) := Deriv.allI D_B
  have hc : ((extractClosed (jetDiffModulusComputedD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) c =
      (extract D_c).eval ec :=
    jetHalve_eval_exch_nil (extract D_c) ec
  have hB : ((extract D_c).eval ec) B2 = (extract D_B).eval eB :=
    jetHalve_eval_exch_nil (extract D_B) eB
  have hx : ((extract D_B).eval eB) x = (extract D_x).eval ex :=
    jetHalve_eval_exch_nil (extract D_x) ex
  have hh : ((extract D_x).eval ex) h = (extract D_h).eval eh :=
    jetHalve_eval_exch_nil (extract D_h) eh
  let D_repack := jetDiffModRepackD (Γ := []) (as := []) (Δ := Ctx.nil)
  let D1 := jetDiffModBaseD (Γ := []) (as := []) (Δ := Ctx.nil)
  let D2 := jetDiffModStepD (Γ := []) (as := []) (Δ := Ctx.nil)
  let R : Ty := .prod .nat (.arrow .nat (.arrow .nat (.arrow .unit .unit)))
  have h_repack : ∀ (f : Nat → R.interp), (((extract D_repack).eval e0) f k).1 = (f k).1 :=
    fun _ ↦ rfl
  have h_chain : extractedJetDiffModulusComputed c B2 x h k =
      (((extract D_repack).eval e0) ((extract (Deriv.ind D1 D2)).eval e0) k).1 := by
    unfold extractedJetDiffModulusComputed
    rw [hc, hB, hx, hh]
    rfl
  rw [h_chain, h_repack]
  change (Nat.rec (motive := fun _ ↦ R.interp)
    (((extract D1).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0))
    (fun m ih ↦ (((extract D2).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0)) m ih)
    k).1 = k + (B2 + 1)
  have hz : ((extract D1).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0) =
      (extract D1).eval e0 :=
    Tm.eval_wk (σ := .nat) (extract D1) k e0
  have hs : (fun (m : Nat) (ih : R.interp) ↦
      (((extract D2).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0)) m ih) =
      (fun (m : Nat) (ih : R.interp) ↦ ((extract D2).eval e0) m ih) := by
    funext m ih
    exact congrFun (congrFun (Tm.eval_wk (σ := .nat) (extract D2) k e0) m) ih
  rw [hz, hs]
  clear h_repack h_chain hz hs
  have h0 : (((extract D1).eval e0).1 : Nat) = B2 + 1 := rfl
  have hstep : ∀ (m : Nat) (ih : R.interp),
      ((((extract D2).eval e0) m ih).1 : Nat) = (ih.1 : Nat) + 1 :=
    fun _ _ ↦ rfl
  induction k with
  | zero =>
    exact h0.trans (Nat.zero_add (B2 + 1)).symm
  | succ m ih =>
    exact (hstep m _).trans ((congrArg (· + 1) ih).trans (Nat.add_right_comm m (B2 + 1) 1))

#print axioms jetContModulusComputedD
#print axioms jetDiffModulusComputedD
#print axioms extractedJetContModulusComputed_eq
#print axioms extractedJetDiffModulusComputed_eq

end HAomega
