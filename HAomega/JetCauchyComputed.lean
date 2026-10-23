/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ComposeProof

/-!
# A proof-computed Cauchy modulus for jet evaluation

`jetCauchyModulusGenuineD` (`JetCauchyDeriv.lean`, catalog #19) writes the
modulus `N(k) = k + (B + 3)` at `exI` and derives its correctness: an explicit
witness. This module computes the modulus by the proof instead. The geometric
argument is the induction itself: if the tail bound from `N + d₁` onward is
below `2^{−k}`, then advancing `N` by one halves the bound, giving precision
`k + 1`. So `∀k ∃N` is proved by `Deriv.ind` on `k`, with witness `B + 3` at
`k = 0` and `N + 1` at each step; the extracted modulus is a recursion produced
by the induction (closed-universe pillar 5, first step).

The conclusion is the same algorithm-free `jetCauchyConcl`. Besides the per-term
premise and the four `ℚ`-laws of `qGeomArithPremise`, two closed `ℚ`-laws enter
as the hypothesis `qHalvePremise`, mentioning only `B` (never `c`, `x`, `k` or
`N`), each proved unconditionally below:

* base:  `∀d₁ d₂. tail(B + 3 + d₁, d₂) < 2⁰`;
* step:  `∀m d₂ k. tail(m, d₂) < 2^{−k} → tail(m + 1, d₂) < 2^{−(k+1)}`,

with `tail(m, d₂) = jetTailBound B m d₂ = 2^{B+3}(2^{−m} − 2^{−(m+d₂+1)})`.
-/

namespace HAomega

/-- The two closed halving laws, over `.rat :: .nat :: JetTy :: Γ` (`x`, `B`, `c`). -/
abbrev qHalvePremise (Γ : List Ty) :=
  let c5 : List Ty := .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm c5 .nat := .var .here
  let d1 : Tm c5 .nat := .var (.there .here)
  let B5 : Tm c5 .nat := .var (.there (.there (.there .here)))
  let c6 : List Ty := .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let k : Tm c6 .nat := .var .here
  let e2 : Tm c6 .nat := .var (.there .here)
  let m : Tm c6 .nat := .var (.there (.there .here))
  let B6 : Tm c6 .nat := .var (.there (.there (.there (.there .here))))
  (Formula.and
    (.all .nat (.all .nat
      (.eq (.qlt (jetTailBound B5 (.add (.succ (.succ (.succ B5))) d1) d2) (.app qpow2 .zero))
           (.succ .zero))))
    (.all .nat (.all .nat (.all .nat
      (.imp (.eq (.qlt (jetTailBound B6 m e2) (.app qpow2 k)) (.succ .zero))
            (.eq (.qlt (jetTailBound B6 (.succ m) e2) (.app qpow2 (.succ k))) (.succ .zero)))))) :
    Formula (.rat :: .nat :: JetTy :: Γ) _)

/-- Existential body `∀d₁ ∀d₂. qlt (jetTailBound B (N + d₁) d₂) (qpow2 k) = 1` over `N :: k :: x :: B :: c :: Γ`. -/
abbrev jetHalveBody (Γ : List Ty) :
    Formula (.nat :: .nat :: .rat :: .nat :: JetTy :: Γ)
      (.arrow .nat (.arrow .nat .unit)) :=
  let ctx : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx .nat := .var .here
  let d1 : Tm ctx .nat := .var (.there .here)
  let N  : Tm ctx .nat := .var (.there (.there .here))
  let k  : Tm ctx .nat := .var (.there (.there (.there .here)))
  let B  : Tm ctx .nat := .var (.there (.there (.there (.there (.there .here)))))
  .all .nat (.all .nat
    (.eq (.qlt (jetTailBound B (.add N d1) d2) (.app qpow2 k)) (.succ .zero)))

/-- Inductive invariant `∃N. ∀d₁ ∀d₂. qlt (jetTailBound B (N + d₁) d₂) (qpow2 k) = 1` over `k :: x :: B :: c :: Γ`. -/
abbrev jetHalveInv (Γ : List Ty) :
    Formula (.nat :: .rat :: .nat :: JetTy :: Γ)
      (.prod .nat (.arrow .nat (.arrow .nat .unit))) :=
  .ex .nat (jetHalveBody Γ)

/-- Context over `x :: B :: c :: Γ` containing `qHalvePremise`, `qGeomArithPremise`, and `jetTermPremise`. -/
abbrev jetHalveCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.rat :: .nat :: JetTy :: Γ)
      ((.prod (.arrow .nat (.arrow .nat .unit))
              (.arrow .nat (.arrow .nat (.arrow .nat (.arrow .unit .unit))))) ::
       (.prod (.arrow .nat .unit)
         (.prod (.arrow .rat (.arrow .rat (.arrow .rat .unit)))
           (.prod (.arrow .nat (.arrow .nat .unit))
                  (.arrow .nat (.arrow .nat .unit))))) ::
       (.arrow .nat .unit) :: as) :=
  .cons (qHalvePremise Γ)
    (.cons (qGeomArithPremise Γ)
      (.cons (jetTermPremise Γ) (((Δ.wk).wk).wk)))

/-- Base case (`k = 0`) of the halving induction: witness `B + 3` from the first conjunct of `qHalvePremise`. -/
def jetHalveBaseD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv (jetHalveCtx Γ Δ) ((jetHalveInv Γ).subst1 .zero) := by
  refine Deriv.exI (.succ (.succ (.succ (.var (.there .here))))) ?_
  deriv_norm
  exact Deriv.andE₁ Deriv.ax

/-- Inductive step (`k → succ k`) of the halving induction: advance witness `N` to `succ N`. -/
def jetHalveStepD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv (jetHalveCtx Γ Δ)
      (.all .nat (.imp (jetHalveInv Γ) ((jetHalveInv Γ).subst Sub.succHere))) := by
  refine Deriv.allI (Deriv.impI ?_)
  refine Deriv.exE (ψ := (jetHalveInv Γ).subst Sub.succHere) Deriv.ax ?_
  refine Deriv.exI (.succ (.var .here)) ?_
  refine Deriv.allI (Deriv.allI ?_)
  let ctx4 : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx4 .nat := .var .here
  let d1 : Tm ctx4 .nat := .var (.there .here)
  let N  : Tm ctx4 .nat := .var (.there (.there .here))
  let k  : Tm ctx4 .nat := .var (.there (.there (.there .here)))
  let B  : Tm ctx4 .nat := .var (.there (.there (.there (.there (.there .here)))))
  let stepCtx :=
    Ctx.cons (((jetHalveBody Γ).wk (σ := .nat)).wk (σ := .nat))
      (Ctx.cons ((((jetHalveInv Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))
        (((((jetHalveCtx Γ Δ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)))
  have hIH : Deriv stepCtx (((jetHalveBody Γ).wk (σ := .nat)).wk (σ := .nat)) := Deriv.ax
  have hIH1 := Deriv.allE (τ := .nat) d1 hIH
  deriv_norm at hIH1
  have hIH2 := Deriv.allE (τ := .nat) d2 hIH1
  deriv_norm at hIH2
  have hHalveStep : Deriv stepCtx
      ((((qHalvePremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk :=
    Deriv.wk (Deriv.wk Deriv.ax)
  have hS1 := Deriv.allE (τ := .nat) (.add N d1) (Deriv.andE₂ hHalveStep)
  deriv_norm at hS1
  have hS2 := Deriv.allE (τ := .nat) d2 hS1
  deriv_norm at hS2
  have hS3 := Deriv.allE (τ := .nat) k hS2
  deriv_norm at hS3
  have hStep := Deriv.impE hS3 hIH2
  exact Deriv.qltEqLeft (jetTailBoundCongM B d2 (succPlusT N d1).symmE) hStep

/-- Inner context at the certificate of `jetCauchyModulusComputedD`. -/
abbrev jetHalveInnerCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :=
  let φ_N := ((jetHalveBody Γ).rename (Ren.ext (Ren.ext (Ren.wk .nat)))).subst
    (Sub.ext (Sub.one (.var .here)))
  Ctx.cons ((φ_N.wk (σ := .nat)).wk (σ := .nat))
    (Ctx.cons (((((Formula.all .nat (jetHalveInv Γ)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))
      (((((jetHalveCtx Γ Δ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)))

/-- Multi-step geometric tail bound `|S_{N+d₁}(x) - S_{N+d₁+d₂}(x)| < jetTailBound B (N + d₁) d₂` by `Deriv.ind` on `d₂`. -/
def jetHalveTailBoundD {Γ as : List Ty} {Δ : Ctx Γ as} :
    let ctx4 : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
    let d2 : Tm ctx4 .nat := .var .here
    let d1 : Tm ctx4 .nat := .var (.there .here)
    let N  : Tm ctx4 .nat := .var (.there (.there .here))
    let x  : Tm ctx4 .rat := .var (.there (.there (.there (.there .here))))
    let B  : Tm ctx4 .nat := .var (.there (.there (.there (.there (.there .here)))))
    let c  : Tm ctx4 JetTy := .var (.there (.there (.there (.there (.there (.there .here))))))
    let m  : Tm ctx4 .nat := .add N d1
    Deriv (jetHalveInnerCtx Γ Δ)
      (.eq (.qlt (.app qabsT (.qsub (jetEvalAt c m x) (jetEvalAt c (.add m d2) x)))
                 (jetTailBound B m d2))
           (.succ .zero)) := by
  let ctx4 : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx4 .nat := .var .here
  let d1 : Tm ctx4 .nat := .var (.there .here)
  let N  : Tm ctx4 .nat := .var (.there (.there .here))
  let x  : Tm ctx4 .rat := .var (.there (.there (.there (.there .here))))
  let B  : Tm ctx4 .nat := .var (.there (.there (.there (.there (.there .here)))))
  let c  : Tm ctx4 JetTy := .var (.there (.there (.there (.there (.there (.there .here))))))
  let m  : Tm ctx4 .nat := .add N d1
  let innerCtx := jetHalveInnerCtx Γ Δ
  let tailInv : Formula (.nat :: ctx4) .unit :=
    let d2_v : Tm (.nat :: ctx4) .nat := .var .here
    let m_v  : Tm (.nat :: ctx4) .nat := m.wk (σ := .nat)
    let x_v  : Tm (.nat :: ctx4) .rat := x.wk (σ := .nat)
    let B_v  : Tm (.nat :: ctx4) .nat := B.wk (σ := .nat)
    let c_v  : Tm (.nat :: ctx4) JetTy := c.wk (σ := .nat)
    .eq (.qlt (.app qabsT (.qsub (jetEvalAt c_v m_v x_v) (jetEvalAt c_v (.add m_v d2_v) x_v)))
              (jetTailBound B_v m_v d2_v))
        (.succ .zero)
  have hInd : Deriv innerCtx (.all .nat tailInv) := by
    refine Deriv.ind ?_ ?_
    · deriv_norm
      have hAdd0 : Deriv innerCtx (.eq (.add m .zero) m) := Deriv.convAddZero m
      have hEval0 : Deriv innerCtx (.eq (jetEvalAt c (.add m .zero) x) (jetEvalAt c m x)) :=
        Deriv.congFun (Deriv.congArg (.app tmJetEvalPoly c) hAdd0) x
      have hSub0 : Deriv innerCtx
          (.eq (.qsub (jetEvalAt c m x) (jetEvalAt c (.add m .zero) x)) (.qnat .zero)) :=
        Deriv.transE (qsubCong (Deriv.eqRefl _) hEval0) (Deriv.convQSubSelf (jetEvalAt c m x))
      have hAbs0 : Deriv innerCtx
          (.eq (.app qabsT (.qsub (jetEvalAt c m x) (jetEvalAt c (.add m .zero) x)))
               (.app qabsT (.qnat .zero))) :=
        Deriv.congArg qabsT hSub0
      have hArith : Deriv innerCtx
          ((((qGeomArithPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk :=
        Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))
      have hZeroInst := Deriv.allE (τ := .nat) m (Deriv.andE₁ hArith)
      deriv_norm at hZeroInst
      exact Deriv.qltEqLeft hAbs0.symmE hZeroInst
    · refine Deriv.allI (Deriv.impI ?_)
      let stepCtxTy : List Ty := .nat :: ctx4
      let d2_s : Tm stepCtxTy .nat := .var .here
      let m_s  : Tm stepCtxTy .nat := m.wk (σ := .nat)
      let x_s  : Tm stepCtxTy .rat := x.wk (σ := .nat)
      let B_s  : Tm stepCtxTy .nat := B.wk (σ := .nat)
      let c_st : Tm stepCtxTy JetTy := c.wk (σ := .nat)
      let stepCtx := Ctx.cons tailInv innerCtx.wk
      have hIH : Deriv stepCtx tailInv := Deriv.ax
      have hTermPrem : Deriv stepCtx
          (((((jetTermPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk :=
        Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))))
      have hTermInst := Deriv.allE (τ := .nat) (.add m_s d2_s) hTermPrem
      deriv_norm at hTermInst
      have hSum := qAddLtAddT
        (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.add m_s d2_s) x_s)))
        (.app qabsT (.qsub (jetEvalAt c_st (.add m_s d2_s) x_s) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s)))
        (jetTailBound B_s m_s d2_s)
        (jetStepBound B_s (.add m_s d2_s))
        hIH hTermInst
      have hArithS : Deriv stepCtx
          (((((qGeomArithPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk :=
        Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax)))
      have hTriPrem := Deriv.andE₁ (Deriv.andE₂ hArithS)
      have hTri1 := Deriv.allE (τ := .rat) (jetEvalAt c_st m_s x_s) hTriPrem
      deriv_norm at hTri1
      have hTri2 := Deriv.allE (τ := .rat) (jetEvalAt c_st (.add m_s d2_s) x_s) hTri1
      deriv_norm at hTri2
      have hTri3 := Deriv.allE (τ := .rat) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s) hTri2
      deriv_norm at hTri3
      have hTriStep := Deriv.convQLeLtTrans
        (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s)))
        (.qadd (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.add m_s d2_s) x_s)))
               (.app qabsT (.qsub (jetEvalAt c_st (.add m_s d2_s) x_s) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s))))
        (.qadd (jetTailBound B_s m_s d2_s) (jetStepBound B_s (.add m_s d2_s)))
        hTri3 hSum
      have hTelPrem := Deriv.andE₁ (Deriv.andE₂ (Deriv.andE₂ hArithS))
      have hTel1 := Deriv.allE (τ := .nat) m_s hTelPrem
      deriv_norm at hTel1
      have hTel2 := Deriv.allE (τ := .nat) d2_s hTel1
      deriv_norm at hTel2
      have hTelStep := Deriv.qltEqRight hTel2 hTriStep
      have hAddSucc : Deriv stepCtx (.eq (.succ (.add m_s d2_s)) (.add m_s (.succ d2_s))) :=
        (Deriv.convAddSucc m_s d2_s).symmE
      have hEvalSucc : Deriv stepCtx
          (.eq (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s)
               (jetEvalAt c_st (.add m_s (.succ d2_s)) x_s)) :=
        Deriv.congFun (Deriv.congArg (.app tmJetEvalPoly c_st) hAddSucc) x_s
      have hAbsSucc : Deriv stepCtx
          (.eq (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s)))
               (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.add m_s (.succ d2_s)) x_s)))) :=
        Deriv.congArg qabsT (qsubCong (Deriv.eqRefl _) hEvalSucc)
      exact Deriv.qltEqLeft hAbsSucc hTelStep
  have hTailD2 := Deriv.allE (τ := .nat) d2 hInd
  deriv_norm at hTailD2
  exact hTailD2

/-- Evaluating a term renamed by `Ren.exch []` is the same as evaluating the term directly. -/
theorem jetHalve_eval_exch_nil {Γ : List Ty} {σ τ : Ty} (t : Tm (σ :: Γ) τ) (e : Env (σ :: Γ)) :
    (t.rename (Ren.exch [])).eval e = t.eval e :=
  Tm.eval_rename t (Ren.exch []) e

/-- Re-packing the existential witness from `jetHalveInv` into `jetCauchyConcl`. -/
def jetHalveRepackD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv (jetHalveCtx Γ Δ) (.imp (.all .nat (jetHalveInv Γ)) (jetCauchyConcl Γ)) := by
  refine Deriv.impI (Deriv.allI ?_)
  have hIndAll : Deriv (Ctx.cons (.all .nat (jetHalveInv Γ)) (jetHalveCtx Γ Δ)).wk
      ((Formula.all .nat (jetHalveInv Γ)).wk (σ := .nat)) := Deriv.ax
  refine Deriv.exE (Deriv.allE (.var .here) hIndAll) ?_
  refine Deriv.exI (.var .here) ?_
  refine Deriv.allI (Deriv.allI ?_)
  let ctx4 : List Ty := .nat :: .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx4 .nat := .var .here
  let d1 : Tm ctx4 .nat := .var (.there .here)
  let N  : Tm ctx4 .nat := .var (.there (.there .here))
  let k  : Tm ctx4 .nat := .var (.there (.there (.there .here)))
  let x  : Tm ctx4 .rat := .var (.there (.there (.there (.there .here))))
  let B  : Tm ctx4 .nat := .var (.there (.there (.there (.there (.there .here)))))
  let c  : Tm ctx4 JetTy := .var (.there (.there (.there (.there (.there (.there .here))))))
  let m  : Tm ctx4 .nat := .add N d1
  let innerCtx := jetHalveInnerCtx Γ Δ
  have hHalve : Deriv innerCtx _ := Deriv.ax
  have hHalve1 := Deriv.allE (τ := .nat) d1 hHalve
  deriv_norm at hHalve1
  have hHalve2 := Deriv.allE (τ := .nat) d2 hHalve1
  deriv_norm at hHalve2
  have hLtPow := Deriv.convQLtTrans
    (.app qabsT (.qsub (jetEvalAt c m x) (jetEvalAt c (.add m d2) x)))
    (jetTailBound B m d2)
    (.app qpow2 k)
    jetHalveTailBoundD hHalve2
  exact qcloseIntro k (jetEvalAt c m x) (jetEvalAt c (.add m d2) x) hLtPow

/-- **The proof-computed Cauchy modulus.** Same conclusion as
    `jetCauchyModulusGenuineD`; the `∀k ∃N` is proved by `Deriv.ind` on `k`. -/
def jetCauchyModulusComputedD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all JetTy (.all .nat (.all .rat
      (.imp (jetTermPremise Γ)
        (.imp (qGeomArithPremise Γ)
          (.imp (qHalvePremise Γ)
            (jetCauchyConcl Γ))))))) :=
  Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI (Deriv.impI
    (Deriv.impE jetHalveRepackD (Deriv.ind jetHalveBaseD jetHalveStepD)))))))

/-- The extracted modulus. -/
def extractedJetCauchyModulusComputed (c : Nat → Q) (B : Nat) (x : Q) (k : Nat) : Nat :=
  ((((extractClosed (jetCauchyModulusComputedD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    c B x (fun _ ↦ ()) (⟨fun _ ↦ (), ⟨fun _ _ _ ↦ (), ⟨fun _ _ ↦ (), fun _ _ ↦ ()⟩⟩⟩)
    ⟨fun _ _ ↦ (), fun _ _ _ _ ↦ ()⟩) k).1

/-- It computes `k + (B + 3)`, now as a recursion produced by the induction. -/
theorem extractedJetCauchyModulusComputed_eq (c : Nat → Q) (B : Nat) (x : Q) (k : Nat) :
    extractedJetCauchyModulusComputed c B x k = k + (B + 3) := by
  let a1 : Ty := .arrow .nat .unit
  let a2 : Ty := .prod (.arrow .nat .unit)
    (.prod (.arrow .rat (.arrow .rat (.arrow .rat .unit)))
      (.prod (.arrow .nat (.arrow .nat .unit)) (.arrow .nat (.arrow .nat .unit))))
  let a3 : Ty := .prod (.arrow .nat (.arrow .nat .unit))
    (.arrow .nat (.arrow .nat (.arrow .nat (.arrow .unit .unit))))
  let p1 : a1.interp := fun _ ↦ ()
  let p2 : a2.interp := ⟨fun _ ↦ (), ⟨fun _ _ _ ↦ (), ⟨fun _ _ ↦ (), fun _ _ ↦ ()⟩⟩⟩
  let p3 : a3.interp := ⟨fun _ _ ↦ (), fun _ _ _ _ ↦ ()⟩
  let ec : Env [JetTy] := Env.cons (σ := JetTy) c Env.nil
  let eB : Env [.nat, JetTy] := Env.cons (σ := .nat) B ec
  let ex : Env [.rat, .nat, JetTy] := Env.cons (σ := .rat) x eB
  let e0 : Env [a3, a2, a1, .rat, .nat, JetTy] :=
    Env.cons (σ := a3) p3 (Env.cons (σ := a2) p2 (Env.cons (σ := a1) p1 ex))
  let D_core : Deriv (jetHalveCtx [] Ctx.nil) (jetCauchyConcl []) :=
    Deriv.impE jetHalveRepackD (Deriv.ind jetHalveBaseD jetHalveStepD)
  let D_x : Deriv ((Ctx.nil (Γ := [])).wk.wk.wk)
      (.imp (jetTermPremise []) (.imp (qGeomArithPremise []) (.imp (qHalvePremise []) (jetCauchyConcl [])))) :=
    Deriv.impI (Deriv.impI (Deriv.impI D_core))
  let D_B : Deriv ((Ctx.nil (Γ := [])).wk.wk) (.all .rat _) := Deriv.allI D_x
  let D_c : Deriv ((Ctx.nil (Γ := [])).wk) (.all .nat (.all .rat _)) := Deriv.allI D_B
  have hc : ((extractClosed (jetCauchyModulusComputedD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) c =
      (extract D_c).eval ec :=
    jetHalve_eval_exch_nil (extract D_c) ec
  have hB : ((extract D_c).eval ec) B = (extract D_B).eval eB :=
    jetHalve_eval_exch_nil (extract D_B) eB
  have hx : ((extract D_B).eval eB) x = (extract D_x).eval ex :=
    jetHalve_eval_exch_nil (extract D_x) ex
  let D_repack := jetHalveRepackD (Γ := []) (as := []) (Δ := Ctx.nil)
  let D1 := jetHalveBaseD (Γ := []) (as := []) (Δ := Ctx.nil)
  let D2 := jetHalveStepD (Γ := []) (as := []) (Δ := Ctx.nil)
  let R : Ty := .prod .nat (.arrow .nat (.arrow .nat .unit))
  have h_repack : ∀ (f : Nat → R.interp), (((extract D_repack).eval e0) f k).1 = (f k).1 :=
    fun _ ↦ rfl
  have h_chain : extractedJetCauchyModulusComputed c B x k =
      (((extract D_repack).eval e0) ((extract (Deriv.ind D1 D2)).eval e0) k).1 := by
    unfold extractedJetCauchyModulusComputed
    rw [hc, hB, hx]
    rfl
  rw [h_chain, h_repack]
  change (Nat.rec (motive := fun _ ↦ R.interp)
    (((extract D1).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0))
    (fun m ih ↦ (((extract D2).wk (σ := .nat)).eval (Env.cons (σ := .nat) k e0)) m ih)
    k).1 = k + (B + 3)
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
  have h0 : (((extract D1).eval e0).1 : Nat) = B + 3 := rfl
  have hstep : ∀ (m : Nat) (ih : R.interp),
      ((((extract D2).eval e0) m ih).1 : Nat) = (ih.1 : Nat) + 1 :=
    fun _ _ ↦ rfl
  induction k with
  | zero =>
    exact h0.trans (Nat.zero_add (B + 3)).symm
  | succ m ih =>
    exact (hstep m _).trans ((congrArg (· + 1) ih).trans (Nat.add_right_comm m (B + 3) 1))

/-- The base halving law holds unconditionally. -/
theorem satisfies_qHalveBase (B d1 d2 : Nat) :
    Q.ltN (Q.mul (qpow2posVal (B + 3))
        (Q.sub (D.toQ (D.pow2neg (B + 3 + d1))) (D.toQ (D.pow2neg (B + 3 + d1 + d2 + 1)))))
      (D.toQ (D.pow2neg 0)) = 1 := by
  rw [Q.ltN_eq_one_iff, Q.val_mul, qpow2posVal_val, Q.val_sub,
      toQ_pow2neg_val, toQ_pow2neg_val, toQ_pow2neg_val]
  have h_prod : (2 : Rat) ^ (B + 3) * (1 / (2 : Rat) ^ (B + 3 + d1)) = 1 / (2 : Rat) ^ d1 := by
    rw [pow_add (2 : Rat) (B + 3) d1]
    field_simp
  have h_le : (1 : Rat) / (2 : Rat) ^ d1 ≤ 1 / (2 : Rat) ^ 0 :=
    inv_pow_le (Nat.zero_le d1)
  have h_pos : (0 : Rat) < (2 : Rat) ^ (B + 3) * (1 / (2 : Rat) ^ (B + 3 + d1 + d2 + 1)) := by
    positivity
  linarith

/-- The halving step holds unconditionally. -/
theorem satisfies_qHalveStep (B m d2 k : Nat)
    (h : Q.ltN (Q.mul (qpow2posVal (B + 3))
        (Q.sub (D.toQ (D.pow2neg m)) (D.toQ (D.pow2neg (m + d2 + 1)))))
      (D.toQ (D.pow2neg k)) = 1) :
    Q.ltN (Q.mul (qpow2posVal (B + 3))
        (Q.sub (D.toQ (D.pow2neg (m + 1))) (D.toQ (D.pow2neg (m + 1 + d2 + 1)))))
      (D.toQ (D.pow2neg (k + 1))) = 1 := by
  rw [Q.ltN_eq_one_iff, Q.val_mul, qpow2posVal_val, Q.val_sub,
      toQ_pow2neg_val, toQ_pow2neg_val, toQ_pow2neg_val] at h ⊢
  have h_lhs : (2 : Rat) ^ (B + 3) * (1 / (2 : Rat) ^ (m + 1) - 1 / (2 : Rat) ^ (m + 1 + d2 + 1)) =
      (1 / 2) * ((2 : Rat) ^ (B + 3) * (1 / (2 : Rat) ^ m - 1 / (2 : Rat) ^ (m + d2 + 1))) := by
    rw [show m + 1 + d2 + 1 = (m + d2 + 1) + 1 by omega,
        pow_succ (2 : Rat) m, pow_succ (2 : Rat) (m + d2 + 1)]
    field_simp
  have h_rhs : (1 : Rat) / (2 : Rat) ^ (k + 1) = (1 / 2) * (1 / (2 : Rat) ^ k) := by
    rw [pow_succ (2 : Rat) k]
    field_simp
  linarith

#print axioms jetCauchyModulusComputedD
#print axioms extractedJetCauchyModulusComputed
#print axioms extractedJetCauchyModulusComputed_eq
#print axioms satisfies_qHalveBase
#print axioms satisfies_qHalveStep

end HAomega
