/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QEquiv
import HAomega.QuadBlowupSolve

/-!
# The product rule inside `Deriv`

`D(f·g) ≈ D f · g + f · D g`, coefficientwise, for arbitrary jets `f`, `g`,
over the closed System T functionals `tmJetDeriv` and `tmJetMul` (the Cauchy
product). The value-level statement is `jetMul_leibniz_val`
(`UniverseMul.lean`); this is the same law derived in the logic, with `≈`
(`QEquiv.lean`).
-/

namespace HAomega

/-- Congruence for `Tm.qnat` inside `Deriv`. -/
def prdCongQnat {Γ as : List Ty} {Δ : Ctx Γ as} {x y : Tm Γ .nat}
    (h : Deriv Δ (.eq x y)) : Deriv Δ (.eq (.qnat x) (.qnat y)) :=
  Deriv.congTm (.qnat (.var .here)) h

/-- `∀ b. qnat (a + b) = qnat a + qnat b`, proved by `Deriv.ind` on `b`. -/
def prdQnatAddD {Γ as : List Ty} {Δ : Ctx Γ as} (a : Tm Γ .nat) :
    Deriv Δ (.all .nat
      (.eq (.qnat (.add a.wk (.var .here))) (.qadd (.qnat a.wk) (.qnat (.var .here))))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    exact Deriv.transE (prdCongQnat (Deriv.convAddZero a))
      (Deriv.symmE (Deriv.qlaw (.normNat a)))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    let b : Tm (.nat :: Γ) .nat := .var .here
    let aw : Tm (.nat :: Γ) .nat := a.wk
    exact Deriv.transE (prdCongQnat (Deriv.convAddSucc aw b))
      (Deriv.transE (Deriv.qlaw (.natSucc (.add aw b)))
        (Deriv.transE (Deriv.congQAdd Deriv.ax (Deriv.eqRefl (.qnat (.succ .zero))))
          (Deriv.transE (Deriv.convQAddAssoc (.qnat aw) (.qnat b) (.qnat (.succ .zero)))
            (Deriv.congQAdd (Deriv.eqRefl (.qnat aw))
              (Deriv.symmE (Deriv.qlaw (.natSucc b)))))))

/-- Term form of `prdQnatAddD`: `qnat (a + b) = qnat a + qnat b`. -/
def prdQnatAddT {Γ as : List Ty} {Δ : Ctx Γ as} (a b : Tm Γ .nat) :
    Deriv Δ (.eq (.qnat (.add a b)) (.qadd (.qnat a) (.qnat b))) := by
  have h := Deriv.allE b (prdQnatAddD (Δ := Δ) a)
  deriv_norm at h
  exact h

/-- `0 * s = 0` on `rat`, from `convQMulComm` and `QLaw.mulZero`. -/
def prdQmulZeroL {Γ as : List Ty} {Δ : Ctx Γ as} (s : Tm Γ .rat) :
    Deriv Δ (.eq (.qmul (.qnat .zero) s) (.qnat .zero)) :=
  Deriv.transE (Deriv.convQMulComm (.qnat .zero) s) (Deriv.qlaw (.mulZero s))

/-- `0 + (x * y) = x * y` on `rat`, from `convQAddComm` and `QLaw.normMul`. -/
def prdQaddZeroLMul {Γ as : List Ty} {Δ : Ctx Γ as} (x y : Tm Γ .rat) :
    Deriv Δ (.eq (.qadd (.qnat .zero) (.qmul x y)) (.qmul x y)) :=
  Deriv.transE (Deriv.convQAddComm (.qnat .zero) (.qmul x y)) (Deriv.qlaw (.normMul x y))

/-- Right distributivity `(s + t) * u = s * u + t * u` on `rat`. -/
def prdQmulAddR {Γ as : List Ty} {Δ : Ctx Γ as} (s t u : Tm Γ .rat) :
    Deriv Δ (.eq (.qmul (.qadd s t) u) (.qadd (.qmul s u) (.qmul t u))) :=
  Deriv.transE (Deriv.convQMulComm (.qadd s t) u)
    (Deriv.transE (Deriv.convQMulAdd u s t)
      (Deriv.congQAdd (Deriv.convQMulComm u s) (Deriv.convQMulComm u t)))

/-- Left-commutativity of multiplication `x * (y * z) = y * (x * z)` on `rat`. -/
def prdQmulLeftComm {Γ as : List Ty} {Δ : Ctx Γ as} (x y z : Tm Γ .rat) :
    Deriv Δ (.eq (.qmul x (.qmul y z)) (.qmul y (.qmul x z))) :=
  Deriv.transE (Deriv.symmE (Deriv.convQMulAssoc x y z))
    (Deriv.transE (Deriv.congQMul (Deriv.convQMulComm x y) (Deriv.eqRefl z))
      (Deriv.convQMulAssoc y x z))

/-- Rearrangement `(a + b) + (c + d) = ((a + c) + b) + d` on `rat`. -/
def prdQaddSwapMid {Γ as : List Ty} {Δ : Ctx Γ as} (a b c d : Tm Γ .rat) :
    Deriv Δ (.eq (.qadd (.qadd a b) (.qadd c d)) (.qadd (.qadd (.qadd a c) b) d)) := by
  have h_inner : Deriv Δ (.eq (.qadd (.qadd a b) c) (.qadd (.qadd a c) b)) :=
    Deriv.transE (Deriv.convQAddAssoc a b c)
      (Deriv.transE (Deriv.congQAdd (Deriv.eqRefl a) (Deriv.convQAddComm b c))
        (Deriv.symmE (Deriv.convQAddAssoc a c b)))
  exact Deriv.transE (Deriv.symmE (Deriv.convQAddAssoc (.qadd a b) c d))
    (Deriv.congQAdd h_inner (Deriv.eqRefl d))

/-- Partial LHS of the product rule at step `t`: `(n + 1) * S_{n+1}(f, g, t + 1)`. -/
abbrev prdLhsAt {Γ : List Ty} (f g : Tm Γ JetTy) (n t : Tm Γ .nat) : Tm Γ .rat :=
  .qmul (.qnat (.succ n)) (jetMulPartialAt f g (.succ n) (.succ t))

/-- Partial RHS of the product rule at step `t`: `S_n(Df, g, t) + S_n(f, Dg, t)`. -/
abbrev prdRhsAt {Γ : List Ty} (f g : Tm Γ JetTy) (n t : Tm Γ .nat) : Tm Γ .rat :=
  .qadd (jetMulPartialAt (.app tmJetDeriv f) g n t)
        (jetMulPartialAt f (.app tmJetDeriv g) n t)

/-- Remainder term of the product rule invariant at `(t, d)`: `d * (f(t) * g(d))`. -/
abbrev prdRemAt {Γ : List Ty} (f g : Tm Γ JetTy) (t d : Tm Γ .nat) : Tm Γ .rat :=
  .qmul (.qnat d) (.qmul (.app f t) (.app g d))

/-- Base step (`t = 0`) of the partial Leibniz identity: from `0 + d = succ n`,
    derive `prdLhsAt f g n 0 = prdRhsAt f g n 0 + prdRemAt f g 0 d`. -/
def prdPartialLeibnizBaseT {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as}
    (f g : Tm Γ JetTy) (n : Tm Γ .nat)
    (h_zero : Deriv Δ (.eq (.add .zero (.var .here)) (.succ n.wk))) :
    Deriv Δ (.eq (prdLhsAt f.wk g.wk n.wk .zero)
                 (.qadd (prdRhsAt f.wk g.wk n.wk .zero)
                        (prdRemAt f.wk g.wk .zero (.var .here)))) := by
  let d : Tm (.nat :: Γ) .nat := .var .here
  let f₁ : Tm (.nat :: Γ) JetTy := f.wk
  let g₁ : Tm (.nat :: Γ) JetTy := g.wk
  let n₁ : Tm (.nat :: Γ) .nat := n.wk
  have h_d : Deriv Δ (.eq d (.succ n₁)) :=
    Deriv.transE (Deriv.symmE (zeroPlusT d)) h_zero
  have h_sub0 : Deriv Δ (.eq (tmNatSub (.succ n₁) .zero) d) :=
    Deriv.transE (tmNatSub_zeroD (.succ n₁)) (Deriv.symmE h_d)
  have h_part1 : Deriv Δ (.eq (jetMulPartialAt f₁ g₁ (.succ n₁) (.succ .zero))
      (.qmul (.app f₁ .zero) (.app g₁ d))) :=
    Deriv.transE (jetMulPartial_succD f₁ g₁ (.succ n₁) .zero)
      (Deriv.transE
        (Deriv.congQAdd (jetMulPartial_zeroD f₁ g₁ (.succ n₁))
          (Deriv.congQMul (Deriv.eqRefl (.app f₁ .zero)) (Deriv.congArg g₁ h_sub0)))
        (prdQaddZeroLMul (.app f₁ .zero) (.app g₁ d)))
  have h_lhs : Deriv Δ (.eq (prdLhsAt f₁ g₁ n₁ .zero) (prdRemAt f₁ g₁ .zero d)) :=
    Deriv.congQMul (prdCongQnat (Deriv.symmE h_d)) h_part1
  have h_rhs0 : Deriv Δ (.eq (prdRhsAt f₁ g₁ n₁ .zero) (.qnat .zero)) :=
    Deriv.transE
      (Deriv.congQAdd (jetMulPartial_zeroD (.app tmJetDeriv f₁) g₁ n₁)
        (jetMulPartial_zeroD f₁ (.app tmJetDeriv g₁) n₁))
      (Deriv.qlaw (.normNat .zero))
  have h_rhs : Deriv Δ (.eq (.qadd (prdRhsAt f₁ g₁ n₁ .zero) (prdRemAt f₁ g₁ .zero d))
      (prdRemAt f₁ g₁ .zero d)) :=
    Deriv.transE (Deriv.congQAdd h_rhs0 (Deriv.eqRefl (prdRemAt f₁ g₁ .zero d)))
      (prdQaddZeroLMul (.qnat d) (.qmul (.app f₁ .zero) (.app g₁ d)))
  exact Deriv.transE h_lhs (Deriv.symmE h_rhs)

/-- Inductive step (`t → succ t`) of the partial Leibniz identity:
    from IH at `t` and `succ t + d = succ n`, derive the identity at `(succ t, d)`. -/
def prdPartialLeibnizStepT {Γ as : List Ty} {Δ : Ctx (.nat :: .nat :: Γ) as}
    (f g : Tm Γ JetTy) (n : Tm Γ .nat)
    (h_ih : Deriv Δ (.all .nat
      (.imp (.eq (.add (.var (.there (.there .here))) (.var .here)) (.succ n.wk.wk.wk))
        (.eq (prdLhsAt f.wk.wk.wk g.wk.wk.wk n.wk.wk.wk (.var (.there (.there .here))))
             (.qadd (prdRhsAt f.wk.wk.wk g.wk.wk.wk n.wk.wk.wk (.var (.there (.there .here))))
                    (prdRemAt f.wk.wk.wk g.wk.wk.wk (.var (.there (.there .here))) (.var .here)))))))
    (h_succ : Deriv Δ (.eq (.add (.succ (.var (.there .here))) (.var .here)) (.succ n.wk.wk))) :
    Deriv Δ (.eq (prdLhsAt f.wk.wk g.wk.wk n.wk.wk (.succ (.var (.there .here))))
                 (.qadd (prdRhsAt f.wk.wk g.wk.wk n.wk.wk (.succ (.var (.there .here))))
                        (prdRemAt f.wk.wk g.wk.wk (.succ (.var (.there .here))) (.var .here)))) := by
  let d : Tm (.nat :: .nat :: Γ) .nat := .var .here
  let t : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  let f₂ : Tm (.nat :: .nat :: Γ) JetTy := f.wk.wk
  let g₂ : Tm (.nat :: .nat :: Γ) JetTy := g.wk.wk
  let n₂ : Tm (.nat :: .nat :: Γ) .nat := n.wk.wk
  let Df : Tm (.nat :: .nat :: Γ) JetTy := .app tmJetDeriv f₂
  let Dg : Tm (.nat :: .nat :: Γ) JetTy := .app tmJetDeriv g₂
  have h_succ_td : Deriv Δ (.eq (.succ (.add t d)) (.succ n₂)) :=
    Deriv.transE (Deriv.symmE (succPlusT t d)) h_succ
  have h_td : Deriv Δ (.eq (.add t d) n₂) :=
    Deriv.impE (Deriv.succInj (.add t d) n₂) h_succ_td
  have h_t_sd : Deriv Δ (.eq (.add t (.succ d)) (.succ n₂)) :=
    Deriv.transE (Deriv.convAddSucc t d) h_succ_td
  have h_sub_n_t : Deriv Δ (.eq (tmNatSub n₂ t) d) :=
    tmNatSubAddCancelT h_td
  have h_sub_sn_st : Deriv Δ (.eq (tmNatSub (.succ n₂) (.succ t)) d) :=
    tmNatSubAddCancelT h_succ
  have h_ih_sd := Deriv.allE (.succ d) h_ih
  deriv_norm at h_ih_sd
  have h_lt_eq : Deriv Δ (.eq (prdLhsAt f₂ g₂ n₂ t)
      (.qadd (prdRhsAt f₂ g₂ n₂ t) (prdRemAt f₂ g₂ t (.succ d)))) :=
    Deriv.impE h_ih_sd h_t_sd
  have h_b_term : Deriv Δ (.eq (.qmul (.app f₂ t) (.app Dg (tmNatSub n₂ t)))
      (prdRemAt f₂ g₂ t (.succ d))) :=
    Deriv.transE
      (Deriv.congQMul (Deriv.eqRefl (.app f₂ t))
        (Deriv.transE (Deriv.congArg Dg h_sub_n_t) (qeJetDerivAppD g₂ d)))
      (prdQmulLeftComm (.app f₂ t) (.qnat (.succ d)) (.app g₂ (.succ d)))
  have h_b_succ : Deriv Δ (.eq (.qadd (jetMulPartialAt f₂ Dg n₂ t) (prdRemAt f₂ g₂ t (.succ d)))
      (jetMulPartialAt f₂ Dg n₂ (.succ t))) :=
    Deriv.transE (Deriv.congQAdd (Deriv.eqRefl _) (Deriv.symmE h_b_term))
      (Deriv.symmE (jetMulPartial_succD f₂ Dg n₂ t))
  have h_lt_ab : Deriv Δ (.eq (prdLhsAt f₂ g₂ n₂ t)
      (.qadd (jetMulPartialAt Df g₂ n₂ t) (jetMulPartialAt f₂ Dg n₂ (.succ t)))) :=
    Deriv.transE h_lt_eq
      (Deriv.transE
        (Deriv.convQAddAssoc (jetMulPartialAt Df g₂ n₂ t) (jetMulPartialAt f₂ Dg n₂ t)
          (prdRemAt f₂ g₂ t (.succ d)))
        (Deriv.congQAdd (Deriv.eqRefl _) h_b_succ))
  have h_lhs_step : Deriv Δ (.eq (prdLhsAt f₂ g₂ n₂ (.succ t))
      (.qadd (prdLhsAt f₂ g₂ n₂ t)
             (.qmul (.qnat (.succ n₂)) (.qmul (.app f₂ (.succ t)) (.app g₂ d))))) :=
    Deriv.transE
      (Deriv.congQMul (Deriv.eqRefl (.qnat (.succ n₂)))
        (Deriv.transE (jetMulPartial_succD f₂ g₂ (.succ n₂) (.succ t))
          (Deriv.congQAdd (Deriv.eqRefl _)
            (Deriv.congQMul (Deriv.eqRefl _) (Deriv.congArg g₂ h_sub_sn_st)))))
      (Deriv.convQMulAdd (.qnat (.succ n₂))
        (jetMulPartialAt f₂ g₂ (.succ n₂) (.succ t))
        (.qmul (.app f₂ (.succ t)) (.app g₂ d)))
  have h_qnat_split : Deriv Δ (.eq (.qnat (.succ n₂)) (.qadd (.qnat (.succ t)) (.qnat d))) :=
    Deriv.transE (prdCongQnat (Deriv.symmE h_succ)) (prdQnatAddT (.succ t) d)
  have h_a_term : Deriv Δ (.eq
      (.qmul (.qnat (.succ t)) (.qmul (.app f₂ (.succ t)) (.app g₂ d)))
      (.qmul (.app Df t) (.app g₂ (tmNatSub n₂ t)))) :=
    Deriv.transE
      (Deriv.symmE (Deriv.convQMulAssoc (.qnat (.succ t)) (.app f₂ (.succ t)) (.app g₂ d)))
      (Deriv.congQMul (Deriv.symmE (qeJetDerivAppD f₂ t))
        (Deriv.symmE (Deriv.congArg g₂ h_sub_n_t)))
  have h_term_split : Deriv Δ (.eq
      (.qmul (.qnat (.succ n₂)) (.qmul (.app f₂ (.succ t)) (.app g₂ d)))
      (.qadd (.qmul (.app Df t) (.app g₂ (tmNatSub n₂ t))) (prdRemAt f₂ g₂ (.succ t) d))) :=
    Deriv.transE (Deriv.congQMul h_qnat_split (Deriv.eqRefl _))
      (Deriv.transE
        (prdQmulAddR (.qnat (.succ t)) (.qnat d) (.qmul (.app f₂ (.succ t)) (.app g₂ d)))
        (Deriv.congQAdd h_a_term (Deriv.eqRefl _)))
  exact Deriv.transE h_lhs_step
    (Deriv.transE (Deriv.congQAdd h_lt_ab h_term_split)
      (Deriv.transE
        (prdQaddSwapMid
          (jetMulPartialAt Df g₂ n₂ t)
          (jetMulPartialAt f₂ Dg n₂ (.succ t))
          (.qmul (.app Df t) (.app g₂ (tmNatSub n₂ t)))
          (prdRemAt f₂ g₂ (.succ t) d))
        (Deriv.congQAdd
          (Deriv.congQAdd (Deriv.symmE (jetMulPartial_succD Df g₂ n₂ t)) (Deriv.eqRefl _))
          (Deriv.eqRefl _))))

/-- Partial Leibniz identity proved by `Deriv.ind` on `t`:
    `∀ t ∀ d. t + d = succ n → prdLhsAt f g n t = prdRhsAt f g n t + prdRemAt f g t d`. -/
def prdPartialLeibnizD {Γ as : List Ty} {Δ : Ctx Γ as}
    (f g : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) (.succ n.wk.wk))
        (.eq (prdLhsAt f.wk.wk g.wk.wk n.wk.wk (.var (.there .here)))
             (.qadd (prdRhsAt f.wk.wk g.wk.wk n.wk.wk (.var (.there .here)))
                    (prdRemAt f.wk.wk g.wk.wk (.var (.there .here)) (.var .here))))))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    exact prdPartialLeibnizBaseT f g n Deriv.ax
  · refine Deriv.allI (Deriv.impI ?_)
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact prdPartialLeibnizStepT f g n (Deriv.wk Deriv.ax) Deriv.ax

/-- **The product rule**, at index `n`, for every pair of jets. -/
def productRuleAtD {Γ as : List Ty} {Δ : Ctx Γ as} (f g : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv (.app (.app tmJetDeriv (.app (.app tmJetMul f) g)) n)
      (.qadd (.app (.app (.app tmJetMul (.app tmJetDeriv f)) g) n)
             (.app (.app (.app tmJetMul f) (.app tmJetDeriv g)) n))) := by
  have h_inst := Deriv.allE .zero (Deriv.allE (.succ n) (prdPartialLeibnizD (Δ := Δ) f g n))
  deriv_norm at h_inst
  have h_main : Deriv Δ (.eq (prdLhsAt f g n (.succ n))
      (.qadd (prdRhsAt f g n (.succ n)) (prdRemAt f g (.succ n) .zero))) :=
    Deriv.impE h_inst (Deriv.convAddZero (.succ n))
  have h_lhs : Deriv Δ (.eq (.app (.app tmJetDeriv (.app (.app tmJetMul f) g)) n)
      (prdLhsAt f g n (.succ n))) :=
    Deriv.transE (qeJetDerivAppD (.app (.app tmJetMul f) g) n)
      (Deriv.congQMul (Deriv.eqRefl (.qnat (.succ n))) (tmJetMul_appD f g (.succ n)))
  have h_rhs : Deriv Δ (.eq (prdRhsAt f g n (.succ n))
      (.qadd (.app (.app (.app tmJetMul (.app tmJetDeriv f)) g) n)
             (.app (.app (.app tmJetMul f) (.app tmJetDeriv g)) n))) :=
    Deriv.congQAdd
      (Deriv.symmE (tmJetMul_appD (.app tmJetDeriv f) g n))
      (Deriv.symmE (tmJetMul_appD f (.app tmJetDeriv g) n))
  have h_rem : Deriv Δ (.eq (prdRemAt f g (.succ n) .zero) (.qnat .zero)) :=
    prdQmulZeroL (.qmul (.app f (.succ n)) (.app g .zero))
  exact Deriv.qeqvOfEqNorm
    (Deriv.transE h_lhs (Deriv.transE h_main (Deriv.congQAdd h_rhs h_rem)))

/-- The two sides of the product rule, with `f, g, n` the bound variables. -/
abbrev productRuleLhs : Tm [.nat, JetTy, JetTy] .rat :=
  .app (.app tmJetDeriv (.app (.app tmJetMul (.var (.there (.there .here))))
    (.var (.there .here)))) (.var .here)

abbrev productRuleRhs : Tm [.nat, JetTy, JetTy] .rat :=
  .qadd (.app (.app (.app tmJetMul (.app tmJetDeriv (.var (.there (.there .here)))))
      (.var (.there .here))) (.var .here))
    (.app (.app (.app tmJetMul (.var (.there (.there .here))))
      (.app tmJetDeriv (.var (.there .here)))) (.var .here))

/-- `∀f ∀g ∀n. D(f·g)(n) ≈ (Df·g)(n) + (f·Dg)(n)`. -/
def productRuleLawD : Deriv (Ctx.nil (Γ := []))
    (.all JetTy (.all JetTy (.all .nat (Formula.qeqv productRuleLhs productRuleRhs)))) :=
  Deriv.allI (Deriv.allI (Deriv.allI (productRuleAtD _ _ _)))

/-- The round trip: through `soundness`, the derived law holds as values at
every pair of coefficient streams and every index. -/
theorem productRuleLaw_val (a b : Nat → Q) (n : Nat) :
    (productRuleLhs.eval (Env.cons n (Env.cons b (Env.cons a Env.nil)))).val
      = (productRuleRhs.eval (Env.cons n (Env.cons b (Env.cons a Env.nil)))).val :=
  (MR_qeqv_iff _ _ _ _).mp (soundness productRuleLawD Env.nil Env.nil realizes_nil a b n)

#print axioms productRuleLawD
#print axioms productRuleLaw_val

end HAomega
