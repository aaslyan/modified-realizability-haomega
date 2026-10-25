/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ProductRuleD

/-!
# `sin² + cos² = 1` inside `Deriv`

Coefficientwise, over the closed System T jets `tmSinJet`, `tmCosJet`, the
Cauchy product `tmJetMul`, the sum `tmJetAdd` and the constant jet
`tmConstOneJet` (`1, 0, 0, …`), with value equality `≈` (`QEquiv.lean`).
-/

namespace HAomega

@[derivNorm] theorem pythSinCosJet_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmSinCosJet (Γ := Γ)).rename ρ = tmSinCosJet (Γ := Δ) := rfl

@[derivNorm] theorem pythSinCosJet_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmSinCosJet (Γ := Γ)).subst s = tmSinCosJet (Γ := Δ) := rfl

@[derivNorm] theorem pythSinJet_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmSinJet (Γ := Γ)).rename ρ = tmSinJet (Γ := Δ) := rfl

@[derivNorm] theorem pythSinJet_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmSinJet (Γ := Γ)).subst s = tmSinJet (Γ := Δ) := rfl

@[derivNorm] theorem pythCosJet_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmCosJet (Γ := Γ)).rename ρ = tmCosJet (Γ := Δ) := rfl

@[derivNorm] theorem pythCosJet_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmCosJet (Γ := Γ)).subst s = tmCosJet (Γ := Δ) := rfl

/-- `y + (0 - y) = 0` on `rat`, from `convQAddComm`, `QLaw.subAdd`, and `QLaw.normNat`. -/
def pythAddSubZero {Γ as : List Ty} {Δ : Ctx Γ as} (y : Tm Γ .rat) :
    Deriv Δ (.eq (.qadd y (.qsub (.qnat .zero) y)) (.qnat .zero)) :=
  Deriv.transE (Deriv.convQAddComm y (.qsub (.qnat .zero) y))
    (Deriv.transE (Deriv.qlaw (.subAdd (.qnat .zero) y))
      (Deriv.qlaw (.normNat .zero)))

/-- `x * y + x * (0 - y) = 0` on `rat`. -/
def pythCancelMulNegR {Γ as : List Ty} {Δ : Ctx Γ as} (x y : Tm Γ .rat) :
    Deriv Δ (.eq (.qadd (.qmul x y) (.qmul x (.qsub (.qnat .zero) y))) (.qnat .zero)) :=
  Deriv.transE (Deriv.symmE (Deriv.convQMulAdd x y (.qsub (.qnat .zero) y)))
    (Deriv.transE (Deriv.congQMul (Deriv.eqRefl x) (pythAddSubZero y))
      (Deriv.qlaw (.mulZero x)))

/-- `x * y + (0 - x) * y = 0` on `rat`. -/
def pythCancelMulNegL {Γ as : List Ty} {Δ : Ctx Γ as} (x y : Tm Γ .rat) :
    Deriv Δ (.eq (.qadd (.qmul x y) (.qmul (.qsub (.qnat .zero) x) y)) (.qnat .zero)) :=
  Deriv.transE
    (Deriv.congQAdd (Deriv.convQMulComm x y) (Deriv.convQMulComm (.qsub (.qnat .zero) x) y))
    (pythCancelMulNegR y x)

/-- `(a + b) + (c + d) = (a + c) + (b + d)` on `rat`. -/
def pythQaddFourMid {Γ as : List Ty} {Δ : Ctx Γ as} (a b c d : Tm Γ .rat) :
    Deriv Δ (.eq (.qadd (.qadd a b) (.qadd c d)) (.qadd (.qadd a c) (.qadd b d))) :=
  Deriv.transE (prdQaddSwapMid a b c d)
    (Deriv.convQAddAssoc (.qadd a c) b d)

/-- `(a + b) + (c + d) = (a + d) + (b + c)` on `rat`. -/
def pythQaddFourCross {Γ as : List Ty} {Δ : Ctx Γ as} (a b c d : Tm Γ .rat) :
    Deriv Δ (.eq (.qadd (.qadd a b) (.qadd c d)) (.qadd (.qadd a d) (.qadd b c))) :=
  Deriv.transE (Deriv.congQAdd (Deriv.eqRefl (.qadd a b)) (Deriv.convQAddComm c d))
    (pythQaddFourMid a b d c)

/-- `tmSinCosJet 0 = (0, 1)` inside `Deriv`. -/
def pythSinCosZeroD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app (tmSinCosJet (Γ := Γ)) .zero)
      (.pair (.qnat .zero) (.qnat (.succ .zero)))) :=
  Deriv.transE (qeSinCosAppD .zero)
    (Deriv.convRecZero (.pair (.qnat .zero) (.qnat (.succ .zero))) qeSinCosStep)

/-- `tmSinJet 0 = 0` inside `Deriv`. -/
def pythSinZeroD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app (tmSinJet (Γ := Γ)) .zero) (.qnat .zero)) :=
  Deriv.transE (qeSinAppD .zero)
    (Deriv.transE (Deriv.qeCongFst pythSinCosZeroD)
      (Deriv.convFst (.qnat .zero) (.qnat (.succ .zero))))

/-- `tmCosJet 0 = 1` inside `Deriv`. -/
def pythCosZeroD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app (tmCosJet (Γ := Γ)) .zero) (.qnat (.succ .zero))) :=
  Deriv.transE (qeCosAppD .zero)
    (Deriv.transE (Deriv.qeCongSnd pythSinCosZeroD)
      (Deriv.convSnd (.qnat .zero) (.qnat (.succ .zero))))

/-- `(a · b)(0) = a(0) * b(0)` inside `Deriv`. -/
def pythJetMulZeroD {Γ as : List Ty} {Δ : Ctx Γ as} (a b : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) b) .zero)
      (.qmul (.app a .zero) (.app b .zero))) :=
  Deriv.transE (tmJetMul_appD a b .zero)
    (Deriv.transE (jetMulPartial_succD a b .zero .zero)
      (Deriv.transE
        (Deriv.congQAdd (jetMulPartial_zeroD a b .zero)
          (Deriv.congQMul (Deriv.eqRefl (.app a .zero))
            (Deriv.congArg b (tmNatSub_zeroD .zero))))
        (prdQaddZeroLMul (.app a .zero) (.app b .zero))))

/-- Base case (`n = 0`) of `sin² + cos² ≈ 1`. -/
def pythZeroD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (Formula.qeqv
      (.app (.app (.app tmJetAdd (.app (.app tmJetMul tmSinJet) tmSinJet))
        (.app (.app tmJetMul tmCosJet) tmCosJet)) .zero)
      (.app tmConstOneJet .zero)) := by
  have h_sin2 : Deriv Δ (.eq (.app (.app (.app tmJetMul tmSinJet) tmSinJet) .zero) (.qnat .zero)) :=
    Deriv.transE (pythJetMulZeroD tmSinJet tmSinJet)
      (Deriv.transE (Deriv.congQMul pythSinZeroD pythSinZeroD)
        (Deriv.qlaw (.mulZero (.qnat .zero))))
  have h_cos2 : Deriv Δ (.eq (.app (.app (.app tmJetMul tmCosJet) tmCosJet) .zero)
      (.qnat (.succ .zero))) :=
    Deriv.transE (pythJetMulZeroD tmCosJet tmCosJet)
      (Deriv.transE (Deriv.congQMul pythCosZeroD pythCosZeroD)
        (Deriv.transE (Deriv.qlaw (.mulOne (.qnat (.succ .zero))))
          (Deriv.qlaw (.normNat (.succ .zero)))))
  have h_lhs : Deriv Δ (.eq
      (.app (.app (.app tmJetAdd (.app (.app tmJetMul tmSinJet) tmSinJet))
        (.app (.app tmJetMul tmCosJet) tmCosJet)) .zero)
      (.qnat (.succ .zero))) :=
    Deriv.transE (tmJetAdd_appD _ _ .zero)
      (Deriv.transE (Deriv.congQAdd h_sin2 h_cos2)
        (Deriv.transE (Deriv.convQAddComm (.qnat .zero) (.qnat (.succ .zero)))
          (Deriv.qlaw (.normNat (.succ .zero)))))
  exact Deriv.qeqvOfEq (Deriv.transE h_lhs (Deriv.symmE tmConstOneJet_zeroD))

/-- `∀ t. S_m(D sin, sin, t) + S_m(cos, D cos, t) = 0`, proved by `Deriv.ind` on `t`. -/
def pythPair1ZeroD {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) :
    Deriv Δ (.all .nat
      (.eq (.qadd (jetMulPartialAt (.app tmJetDeriv tmSinJet) tmSinJet m.wk (.var .here))
                  (jetMulPartialAt tmCosJet (.app tmJetDeriv tmCosJet) m.wk (.var .here)))
           (.qnat .zero))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    exact Deriv.transE
      (Deriv.congQAdd
        (jetMulPartial_zeroD (.app tmJetDeriv tmSinJet) tmSinJet m)
        (jetMulPartial_zeroD tmCosJet (.app tmJetDeriv tmCosJet) m))
      (Deriv.qlaw (.normNat .zero))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    let t : Tm (.nat :: Γ) .nat := .var .here
    let mw : Tm (.nat :: Γ) .nat := m.wk
    let k : Tm (.nat :: Γ) .nat := tmNatSub mw t
    let Dsin : Tm (.nat :: Γ) JetTy := .app tmJetDeriv tmSinJet
    let Dcos : Tm (.nat :: Γ) JetTy := .app tmJetDeriv tmCosJet
    exact Deriv.transE
      (Deriv.transE
        (Deriv.congQAdd
          (jetMulPartial_succD Dsin tmSinJet mw t)
          (jetMulPartial_succD tmCosJet Dcos mw t))
        (pythQaddFourMid
          (jetMulPartialAt Dsin tmSinJet mw t)
          (.qmul (.app Dsin t) (.app tmSinJet k))
          (jetMulPartialAt tmCosJet Dcos mw t)
          (.qmul (.app tmCosJet t) (.app Dcos k))))
      (Deriv.transE
        (Deriv.congQAdd Deriv.ax
          (Deriv.transE
            (Deriv.congQAdd
              (Deriv.qmulV (qeSinDerivD t) (Deriv.qeqvRefl (.app tmSinJet k)))
              (Deriv.qmulV (Deriv.qeqvRefl (.app tmCosJet t)) (qeCosDerivD k)))
            (pythCancelMulNegR (.app tmCosJet t) (.app tmSinJet k))))
        (Deriv.qlaw (.normNat .zero)))

/-- `∀ t. S_m(sin, D sin, t) + S_m(D cos, cos, t) = 0`, proved by `Deriv.ind` on `t`. -/
def pythPair2ZeroD {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) :
    Deriv Δ (.all .nat
      (.eq (.qadd (jetMulPartialAt tmSinJet (.app tmJetDeriv tmSinJet) m.wk (.var .here))
                  (jetMulPartialAt (.app tmJetDeriv tmCosJet) tmCosJet m.wk (.var .here)))
           (.qnat .zero))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    exact Deriv.transE
      (Deriv.congQAdd
        (jetMulPartial_zeroD tmSinJet (.app tmJetDeriv tmSinJet) m)
        (jetMulPartial_zeroD (.app tmJetDeriv tmCosJet) tmCosJet m))
      (Deriv.qlaw (.normNat .zero))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    let t : Tm (.nat :: Γ) .nat := .var .here
    let mw : Tm (.nat :: Γ) .nat := m.wk
    let k : Tm (.nat :: Γ) .nat := tmNatSub mw t
    let Dsin : Tm (.nat :: Γ) JetTy := .app tmJetDeriv tmSinJet
    let Dcos : Tm (.nat :: Γ) JetTy := .app tmJetDeriv tmCosJet
    exact Deriv.transE
      (Deriv.transE
        (Deriv.congQAdd
          (jetMulPartial_succD tmSinJet Dsin mw t)
          (jetMulPartial_succD Dcos tmCosJet mw t))
        (pythQaddFourMid
          (jetMulPartialAt tmSinJet Dsin mw t)
          (.qmul (.app tmSinJet t) (.app Dsin k))
          (jetMulPartialAt Dcos tmCosJet mw t)
          (.qmul (.app Dcos t) (.app tmCosJet k))))
      (Deriv.transE
        (Deriv.congQAdd Deriv.ax
          (Deriv.transE
            (Deriv.congQAdd
              (Deriv.qmulV (Deriv.qeqvRefl (.app tmSinJet t)) (qeSinDerivD k))
              (Deriv.qmulV (qeCosDerivD t) (Deriv.qeqvRefl (.app tmCosJet k))))
            (pythCancelMulNegL (.app tmSinJet t) (.app tmCosJet k))))
        (Deriv.qlaw (.normNat .zero)))

/-- `tmConstOneJet (succ m) = 0` inside `Deriv`. -/
def pythConstOneSuccD {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app (tmConstOneJet (Γ := Γ)) (.succ m)) (.qnat .zero)) := by
  let step : Tm Γ (.arrow .nat (.arrow .rat .rat)) := .lam (.lam (.qnat .zero))
  let r : Tm Γ .rat := .recNat (.qnat (.succ .zero)) step m
  have h1 : Deriv Δ (.eq (.app (tmConstOneJet (Γ := Γ)) (.succ m))
      (.recNat (.qnat (.succ .zero)) step (.succ m))) :=
    Deriv.convBeta (.recNat (.qnat (.succ .zero)) (.lam (.lam (.qnat .zero))) (.var .here)) (.succ m)
  have h2 : Deriv Δ (.eq (.recNat (.qnat (.succ .zero)) step (.succ m))
      (.app (.app step m) r)) :=
    Deriv.convRecSucc (.qnat (.succ .zero)) step m
  have h3 : Deriv Δ (.eq (.app step m) (.lam (.qnat .zero))) :=
    Deriv.convBeta (.lam (.qnat .zero)) m
  have h4 : Deriv Δ (.eq (.app (.lam (.qnat .zero)) r) (.qnat .zero)) :=
    Deriv.convBeta (.qnat .zero) r
  exact Deriv.transE h1 (Deriv.transE h2 (Deriv.transE (Deriv.congFun h3 r) h4))

/-- From `(m + 1) * u ≈ 0`, derive `u ≈ 0` via `qeqvMulDiv` and `qnatSuccNeZero`. -/
def pythCancelSuccMulZeroD {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) {u : Tm Γ .rat}
    (h : Deriv Δ (Formula.qeqv (.qmul (.qnat (.succ m)) u) (.qnat .zero))) :
    Deriv Δ (Formula.qeqv u (.qnat .zero)) := by
  let c : Tm Γ .rat := .qnat (.succ m)
  have hc0 : Deriv Δ (Formula.qeqv (.qmul c u) (.qmul c (.qnat .zero))) :=
    Deriv.qeqvTrans h (Deriv.qeqvOfEq (Deriv.symmE (Deriv.qlaw (.mulZero c))))
  have hdiv : Deriv Δ (.eq (.qdiv (.qmul c u) c) (.qdiv (.qmul c (.qnat .zero)) c)) :=
    Deriv.qdivV hc0 (Deriv.qeqvRefl c)
  exact Deriv.qeqvTrans
    (Deriv.qeqvSymm (Deriv.qeqvMulDiv u (Deriv.qnatSuccNeZero m)))
    (Deriv.qeqvTrans (Deriv.qeqvOfEq hdiv)
      (Deriv.qeqvMulDiv (.qnat .zero) (Deriv.qnatSuccNeZero m)))

/-- Successor case (`n = succ m`) of `sin² + cos² ≈ 1`. -/
def pythSuccD {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv
      (.app (.app (.app tmJetAdd (.app (.app tmJetMul tmSinJet) tmSinJet))
        (.app (.app tmJetMul tmCosJet) tmCosJet)) (.succ m))
      (.app tmConstOneJet (.succ m))) := by
  let sin2 : Tm Γ JetTy := .app (.app tmJetMul tmSinJet) tmSinJet
  let cos2 : Tm Γ JetTy := .app (.app tmJetMul tmCosJet) tmCosJet
  let E : Tm Γ JetTy := .app (.app tmJetAdd sin2) cos2
  let Dsin : Tm Γ JetTy := .app tmJetDeriv tmSinJet
  let Dcos : Tm Γ JetTy := .app tmJetDeriv tmCosJet
  have h_deriv_sum : Deriv Δ (.eq (.qmul (.qnat (.succ m)) (.app E (.succ m)))
      (.qadd (.app (.app tmJetDeriv sin2) m) (.app (.app tmJetDeriv cos2) m))) :=
    Deriv.transE
      (Deriv.congQMul (Deriv.eqRefl (.qnat (.succ m)))
        (tmJetAdd_appD sin2 cos2 (.succ m)))
      (Deriv.transE
        (Deriv.convQMulAdd (.qnat (.succ m)) (.app sin2 (.succ m)) (.app cos2 (.succ m)))
        (Deriv.congQAdd
          (Deriv.symmE (qeJetDerivAppD sin2 m))
          (Deriv.symmE (qeJetDerivAppD cos2 m))))
  have h_prd : Deriv Δ (.eq
      (.qadd (.app (.app tmJetDeriv sin2) m) (.app (.app tmJetDeriv cos2) m))
      (.qadd (.qadd (.app (.app (.app tmJetMul Dsin) tmSinJet) m)
                    (.app (.app (.app tmJetMul tmSinJet) Dsin) m))
             (.qadd (.app (.app (.app tmJetMul Dcos) tmCosJet) m)
                    (.app (.app (.app tmJetMul tmCosJet) Dcos) m)))) :=
    Deriv.qaddV (productRuleAtD tmSinJet tmSinJet m) (productRuleAtD tmCosJet tmCosJet m)
  have h_unfold : Deriv Δ (.eq
      (.qadd (.qadd (.app (.app (.app tmJetMul Dsin) tmSinJet) m)
                    (.app (.app (.app tmJetMul tmSinJet) Dsin) m))
             (.qadd (.app (.app (.app tmJetMul Dcos) tmCosJet) m)
                    (.app (.app (.app tmJetMul tmCosJet) Dcos) m)))
      (.qadd (.qadd (tmJetMulAt Dsin tmSinJet m) (tmJetMulAt tmCosJet Dcos m))
             (.qadd (tmJetMulAt tmSinJet Dsin m) (tmJetMulAt Dcos tmCosJet m)))) :=
    Deriv.transE
      (Deriv.congQAdd
        (Deriv.congQAdd (tmJetMul_appD Dsin tmSinJet m) (tmJetMul_appD tmSinJet Dsin m))
        (Deriv.congQAdd (tmJetMul_appD Dcos tmCosJet m) (tmJetMul_appD tmCosJet Dcos m)))
      (pythQaddFourCross
        (tmJetMulAt Dsin tmSinJet m)
        (tmJetMulAt tmSinJet Dsin m)
        (tmJetMulAt Dcos tmCosJet m)
        (tmJetMulAt tmCosJet Dcos m))
  have hp1 := Deriv.allE (.succ m) (pythPair1ZeroD (Δ := Δ) m)
  deriv_norm at hp1
  have hp2 := Deriv.allE (.succ m) (pythPair2ZeroD (Δ := Δ) m)
  deriv_norm at hp2
  have h_zero : Deriv Δ (.eq (.qmul (.qnat (.succ m)) (.app E (.succ m))) (.qnat .zero)) :=
    Deriv.transE h_deriv_sum
      (Deriv.transE h_prd
        (Deriv.transE h_unfold
          (Deriv.transE (Deriv.congQAdd hp1 hp2) (Deriv.qlaw (.normNat .zero)))))
  exact Deriv.qeqvTrans
    (pythCancelSuccMulZeroD m (Deriv.qeqvOfEq h_zero))
    (Deriv.qeqvOfEq (Deriv.symmE (pythConstOneSuccD m)))

/-- Universal form `∀ n. (sin·sin + cos·cos)(n) ≈ 1(n)`, by `Deriv.ind` on `n`. -/
def pythAllD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (Formula.qeqv
      (.app (.app (.app tmJetAdd (.app (.app tmJetMul tmSinJet) tmSinJet))
        (.app (.app tmJetMul tmCosJet) tmCosJet)) (.var .here))
      (.app tmConstOneJet (.var .here)))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    exact pythZeroD
  · refine Deriv.allI (Deriv.impI ?_)
    exact pythSuccD (.var .here)

/-- **`sin² + cos² ≈ 1`**, at index `n`. -/
def pythagorasAtD {Γ as : List Ty} {Δ : Ctx Γ as} (n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv
      (.app (.app (.app tmJetAdd (.app (.app tmJetMul tmSinJet) tmSinJet))
        (.app (.app tmJetMul tmCosJet) tmCosJet)) n)
      (.app tmConstOneJet n)) := by
  have h := Deriv.allE n (pythAllD (Δ := Δ))
  deriv_norm at h
  exact h

/-- The two sides, with `n` the bound variable. -/
abbrev pythagorasLhs : Tm [.nat] .rat :=
  .app (.app (.app tmJetAdd (.app (.app tmJetMul tmSinJet) tmSinJet))
    (.app (.app tmJetMul tmCosJet) tmCosJet)) (.var .here)

abbrev pythagorasRhs : Tm [.nat] .rat := .app tmConstOneJet (.var .here)

/-- `∀n. (sin·sin + cos·cos)(n) ≈ 1(n)`. -/
def pythagorasLawD : Deriv (Ctx.nil (Γ := []))
    (.all .nat (Formula.qeqv pythagorasLhs pythagorasRhs)) :=
  Deriv.allI (pythagorasAtD _)

/-- The round trip: through `soundness`, the law holds as values at every index. -/
theorem pythagorasLaw_val (n : Nat) :
    (pythagorasLhs.eval (Env.cons n Env.nil)).val = (pythagorasRhs.eval (Env.cons n Env.nil)).val :=
  (MR_qeqv_iff _ _ _ _).mp (soundness pythagorasLawD Env.nil Env.nil realizes_nil n)

-- spot check of the value statement at small indices (runs the jets)
#guard (List.range 6).all fun n ↦
  decide ((pythagorasLhs.eval (Env.cons n Env.nil)) = Q.norm (pythagorasRhs.eval (Env.cons n Env.nil)))
    || (pythagorasLhs.eval (Env.cons n Env.nil)) == (pythagorasRhs.eval (Env.cons n Env.nil))

#print axioms pythagorasLawD
#print axioms pythagorasLaw_val

end HAomega
