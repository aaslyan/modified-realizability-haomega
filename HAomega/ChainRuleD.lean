/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ProductRuleD
import HAomega.ChainRule

/-!
# Composition as a System T jet functional, and the chain rule inside `Deriv`

`Jet.compZero F G = F(G − G(0))` exists at the value level (`MajorantDom.lean`),
with the chain rule `compZero_deriv_val` proved as values (`ChainRule.lean`).
Here composition becomes a closed System T term, so the chain rule can be
stated in the object logic:

    (F ∘ G)(n) = Σ_{k ≤ n} F(k) · (G₊)ᵏ(n),      G₊ := G with its constant term removed

— the sum is finite because `(G₊)ᵏ` vanishes below degree `k`. Powers are an
order-1 `recNat` at the jet type, the sum an order-0 `recNat` at `rat`.
-/

namespace HAomega

/-- `G₊`: the jet `G` with its constant coefficient replaced by `0`. -/
def tmJetDrop0 {Γ : List Ty} : Tm Γ (.arrow JetTy JetTy) :=
  .lam (.lam (.recNat (.qnat .zero)
    (.lam (.lam (.app (.var (.there (.there (.there .here)))) (.succ (.var (.there .here))))))
    (.var .here)))

/-- `Gᵏ`, by recursion on `k`: `G⁰ = 1`, `Gᵏ⁺¹ = G · Gᵏ`. -/
def tmJetPow {Γ : List Ty} : Tm Γ (.arrow JetTy (.arrow .nat JetTy)) :=
  .lam (.lam (.recNat tmConstOneJet
    (.lam (.lam (.app (.app tmJetMul (.var (.there (.there (.there .here))))) (.var .here))))
    (.var .here)))

/-- **Composition** `F ∘ (G − G(0))`, at index `n`: `Σ_{k < n+1} F(k) · (G₊)ᵏ(n)`. -/
def tmJetComp {Γ : List Ty} : Tm Γ (.arrow JetTy (.arrow JetTy JetTy)) :=
  .lam (.lam (.lam (.recNat (.qnat .zero)
    (.lam (.lam (.qadd (.var .here)
      (.qmul (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here)))
        (.app (.app (.app tmJetPow (.app tmJetDrop0 (.var (.there (.there (.there .here))))))
          (.var (.there .here))) (.var (.there (.there .here))))))))
    (.succ (.var .here)))))

-- The term computes the value-level composition, checked at small degrees for
-- `exp ∘ sin` and `sin ∘ (exp − 1)`.
#guard (List.range 6).all fun n ↦
  Q.norm ((((tmJetComp (Γ := [])).eval Env.nil) ((tmExpJet (Γ := [])).eval Env.nil)
      ((tmSinJet (Γ := [])).eval Env.nil)) n)
    == Q.norm ((Jet.compZero ⟨(tmExpJet (Γ := [])).eval Env.nil⟩ ⟨(tmSinJet (Γ := [])).eval Env.nil⟩).coeff n)
#guard (List.range 6).all fun n ↦
  Q.norm ((((tmJetComp (Γ := [])).eval Env.nil) ((tmSinJet (Γ := [])).eval Env.nil)
      ((tmExpJet (Γ := [])).eval Env.nil)) n)
    == Q.norm ((Jet.compZero ⟨(tmSinJet (Γ := [])).eval Env.nil⟩ ⟨(tmExpJet (Γ := [])).eval Env.nil⟩).coeff n)

@[derivNorm] theorem chrDrop0_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetDrop0 (Γ := Γ)).rename ρ = tmJetDrop0 (Γ := Δ) := rfl

@[derivNorm] theorem chrDrop0_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetDrop0 (Γ := Γ)).subst s = tmJetDrop0 (Γ := Δ) := rfl

@[derivNorm] theorem chrPow_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetPow (Γ := Γ)).rename ρ = tmJetPow (Γ := Δ) := rfl

@[derivNorm] theorem chrPow_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetPow (Γ := Γ)).subst s = tmJetPow (Γ := Δ) := rfl

@[derivNorm] theorem chrComp_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmJetComp (Γ := Γ)).rename ρ = tmJetComp (Γ := Δ) := rfl

@[derivNorm] theorem chrComp_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmJetComp (Γ := Γ)).subst s = tmJetComp (Γ := Δ) := rfl

@[derivNorm] theorem chrQeqv_rename {Γ Δ : List Ty} (s t : Tm Γ .rat) (ρ : Ren Γ Δ) :
    (Formula.qeqv s t).rename ρ = Formula.qeqv (s.rename ρ) (t.rename ρ) := rfl

@[derivNorm] theorem chrQeqv_subst {Γ Δ : List Ty} (s t : Tm Γ .rat) (sub : Sub Γ Δ) :
    (Formula.qeqv s t).subst sub = Formula.qeqv (s.subst sub) (t.subst sub) := rfl

/-- `(a + b) + (c + d) = (a + c) + (b + d)` on `rat`. -/
def chrQaddFourMid {Γ as : List Ty} {Δ : Ctx Γ as} (a b c d : Tm Γ .rat) :
    Deriv Δ (.eq (.qadd (.qadd a b) (.qadd c d)) (.qadd (.qadd a c) (.qadd b d))) :=
  Deriv.transE (prdQaddSwapMid a b c d)
    (Deriv.convQAddAssoc (.qadd a c) b d)

/-- `(a · b)(0) = a(0) * b(0)` inside `Deriv`. -/
def chrJetMulZeroD {Γ as : List Ty} {Δ : Ctx Γ as} (a b : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) b) .zero)
      (.qmul (.app a .zero) (.app b .zero))) :=
  Deriv.transE (tmJetMul_appD a b .zero)
    (Deriv.transE (jetMulPartial_succD a b .zero .zero)
      (Deriv.transE
        (Deriv.congQAdd (jetMulPartial_zeroD a b .zero)
          (Deriv.congQMul (Deriv.eqRefl (.app a .zero))
            (Deriv.congArg b (tmNatSub_zeroD .zero))))
        (prdQaddZeroLMul (.app a .zero) (.app b .zero))))

/-- `tmConstOneJet (succ m) = 0` inside `Deriv`. -/
def chrConstOneSuccD {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) :
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

/-- `(D tmConstOneJet)(m) = 0` inside `Deriv`. -/
def chrDerivConstOneD {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app tmJetDeriv (tmConstOneJet (Γ := Γ))) m) (.qnat .zero)) :=
  Deriv.transE (qeJetDerivAppD tmConstOneJet m)
    (Deriv.transE
      (Deriv.congQMul (Deriv.eqRefl (.qnat (.succ m))) (chrConstOneSuccD m))
      (Deriv.qlaw (.mulZero (.qnat (.succ m)))))

/-- `1 * x ≈ x` on `rat`. -/
def chrQmulOneL {Γ as : List Ty} {Δ : Ctx Γ as} (x : Tm Γ .rat) :
    Deriv Δ (Formula.qeqv (.qmul (.qnat (.succ .zero)) x) x) :=
  Deriv.qeqvTrans (Deriv.qeqvOfEq (Deriv.convQMulComm (.qnat (.succ .zero)) x))
    (Deriv.qeqvMulOne x)

/-- `x + qnat m * x = qnat (succ m) * x` inside `Deriv`. -/
def chrAddMulSuccNatD {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) (x : Tm Γ .rat) :
    Deriv Δ (.eq (.qadd x (.qmul (.qnat m) x)) (.qmul (.qnat (.succ m)) x)) :=
  Deriv.transE
    (Deriv.qaddV (Deriv.qeqvSymm (chrQmulOneL x)) (Deriv.qeqvRefl (.qmul (.qnat m) x)))
    (Deriv.transE
      (Deriv.convQAddComm (.qmul (.qnat (.succ .zero)) x) (.qmul (.qnat m) x))
      (Deriv.transE
        (Deriv.symmE (prdQmulAddR (.qnat m) (.qnat (.succ .zero)) x))
        (Deriv.congQMul (Deriv.symmE (Deriv.qlaw (.natSucc m))) (Deriv.eqRefl x))))

/-- Recursor step of `tmJetDrop0 g`. -/
def chrDrop0Step {Γ : List Ty} (g : Tm Γ JetTy) : Tm Γ (.arrow .nat (.arrow .rat .rat)) :=
  .lam (.lam (.app ((g.wk (σ := .nat)).wk (σ := .rat)) (.succ (.var (.there .here)))))

@[derivNorm] theorem chrDrop0Step_rename {Γ Δ : List Ty} (g : Tm Γ JetTy) (ρ : Ren Γ Δ) :
    (chrDrop0Step g).rename ρ = chrDrop0Step (g.rename ρ) := by
  simp only [chrDrop0Step, Tm.rename, Tm.wk, Tm.rename_rename]
  rfl

@[derivNorm] theorem chrDrop0Step_subst {Γ Δ : List Ty} (g : Tm Γ JetTy) (s : Sub Γ Δ) :
    (chrDrop0Step g).subst s = chrDrop0Step (g.subst s) := by
  simp only [chrDrop0Step, Tm.subst, Tm.wk_subst_ext]
  rfl

/-- Applying `tmJetDrop0` to `g` and `n` converts to `.recNat 0 (chrDrop0Step g) n`. -/
def chrDrop0_appD {Γ as : List Ty} {Δ : Ctx Γ as} (g : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app tmJetDrop0 g) n) (.recNat (.qnat .zero) (chrDrop0Step g) n)) := by
  have h1 : Deriv Δ (.eq (.app tmJetDrop0 g)
      (.lam (.recNat (.qnat .zero) (chrDrop0Step (g.wk (σ := .nat))) (.var .here)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (.recNat (.qnat .zero)
        (.lam (.lam (.app (.var (.there (.there (.there .here)))) (.succ (.var (.there .here))))))
        (.var .here))) g
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq
      (.app (.lam (.recNat (.qnat .zero) (chrDrop0Step (g.wk (σ := .nat))) (.var .here))) n)
      (.recNat (.qnat .zero) (chrDrop0Step g) n)) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.recNat (.qnat .zero) (chrDrop0Step (g.wk (σ := .nat))) (.var .here)) n
    deriv_norm at hb
    exact hb
  exact Deriv.transE (Deriv.congFun h1 n) h2

/-- `(tmJetDrop0 g)(0) = 0` inside `Deriv`. -/
def chrDrop0_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} (g : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app tmJetDrop0 g) .zero) (.qnat .zero)) :=
  Deriv.transE (chrDrop0_appD g .zero)
    (Deriv.convRecZero (.qnat .zero) (chrDrop0Step g))

/-- `(tmJetDrop0 g)(succ m) = g(succ m)` inside `Deriv`. -/
def chrDrop0_succD {Γ as : List Ty} {Δ : Ctx Γ as} (g : Tm Γ JetTy) (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app tmJetDrop0 g) (.succ m)) (.app g (.succ m))) := by
  let r : Tm Γ .rat := .recNat (.qnat .zero) (chrDrop0Step g) m
  have h1 := chrDrop0_appD (Δ := Δ) g (.succ m)
  have h2 := Deriv.convRecSucc (Δ := Δ) (.qnat .zero) (chrDrop0Step g) m
  have h3 : Deriv Δ (.eq (.app (chrDrop0Step g) m)
      (.lam (.app (g.wk (σ := .rat)) (.succ (m.wk (σ := .rat)))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.lam (a := .rat) (.app ((g.wk (σ := .nat)).wk (σ := .rat)) (.succ (.var (.there .here))))) m
    deriv_norm at hb
    exact hb
  have h4 : Deriv Δ (.eq (.app (.lam (.app (g.wk (σ := .rat)) (.succ (m.wk (σ := .rat))))) r)
      (.app g (.succ m))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .rat)
      (.app (g.wk (σ := .rat)) (.succ (m.wk (σ := .rat)))) r
    deriv_norm at hb
    exact hb
  exact Deriv.transE h1 (Deriv.transE h2 (Deriv.transE (Deriv.congFun h3 r) h4))

/-- `(D (tmJetDrop0 g))(m) = (D g)(m)` inside `Deriv`. -/
def chrDerivDrop0D {Γ as : List Ty} {Δ : Ctx Γ as} (g : Tm Γ JetTy) (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app tmJetDeriv (.app tmJetDrop0 g)) m) (.app (.app tmJetDeriv g) m)) :=
  Deriv.transE (qeJetDerivAppD (.app tmJetDrop0 g) m)
    (Deriv.transE
      (Deriv.congQMul (Deriv.eqRefl (.qnat (.succ m))) (chrDrop0_succD g m))
      (Deriv.symmE (qeJetDerivAppD g m)))

/-- Recursor step of `tmJetPow G`. -/
def chrPowStep {Γ : List Ty} (G : Tm Γ JetTy) : Tm Γ (.arrow .nat (.arrow JetTy JetTy)) :=
  .lam (.lam (.app (.app tmJetMul ((G.wk (σ := .nat)).wk (σ := JetTy))) (.var .here)))

@[derivNorm] theorem chrPowStep_rename {Γ Δ : List Ty} (G : Tm Γ JetTy) (ρ : Ren Γ Δ) :
    (chrPowStep G).rename ρ = chrPowStep (G.rename ρ) := by
  simp only [chrPowStep, Tm.rename, Tm.wk, Tm.rename_rename, tmJetMul_rename]
  rfl

@[derivNorm] theorem chrPowStep_subst {Γ Δ : List Ty} (G : Tm Γ JetTy) (s : Sub Γ Δ) :
    (chrPowStep G).subst s = chrPowStep (G.subst s) := by
  simp only [chrPowStep, Tm.subst, Tm.wk_subst_ext, tmJetMul_subst]
  rfl

/-- Applying `tmJetPow` to `G` and `k` converts to `.recNat tmConstOneJet (chrPowStep G) k`. -/
def chrPow_appD {Γ as : List Ty} {Δ : Ctx Γ as} (G : Tm Γ JetTy) (k : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app tmJetPow G) k) (.recNat tmConstOneJet (chrPowStep G) k)) := by
  have h1 : Deriv Δ (.eq (.app tmJetPow G)
      (.lam (.recNat tmConstOneJet (chrPowStep (G.wk (σ := .nat))) (.var .here)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (.recNat tmConstOneJet
        (.lam (.lam (.app (.app tmJetMul (.var (.there (.there (.there .here))))) (.var .here))))
        (.var .here))) G
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq
      (.app (.lam (.recNat tmConstOneJet (chrPowStep (G.wk (σ := .nat))) (.var .here))) k)
      (.recNat tmConstOneJet (chrPowStep G) k)) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.recNat tmConstOneJet (chrPowStep (G.wk (σ := .nat))) (.var .here)) k
    deriv_norm at hb
    exact hb
  exact Deriv.transE (Deriv.congFun h1 k) h2

/-- `tmJetPow G 0 = tmConstOneJet` inside `Deriv`. -/
def chrPow_zeroD {Γ as : List Ty} {Δ : Ctx Γ as} (G : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app tmJetPow G) .zero) tmConstOneJet) :=
  Deriv.transE (chrPow_appD G .zero)
    (Deriv.convRecZero tmConstOneJet (chrPowStep G))

/-- `tmJetPow G (succ k) = tmJetMul G (tmJetPow G k)` inside `Deriv`. -/
def chrPow_succD {Γ as : List Ty} {Δ : Ctx Γ as} (G : Tm Γ JetTy) (k : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app tmJetPow G) (.succ k))
      (.app (.app tmJetMul G) (.app (.app tmJetPow G) k))) := by
  let r : Tm Γ JetTy := .recNat tmConstOneJet (chrPowStep G) k
  have h1 := chrPow_appD (Δ := Δ) G (.succ k)
  have h2 := Deriv.convRecSucc (Δ := Δ) tmConstOneJet (chrPowStep G) k
  have h3 : Deriv Δ (.eq (.app (chrPowStep G) k)
      (.lam (.app (.app tmJetMul (G.wk (σ := JetTy))) (.var .here)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.lam (a := JetTy) (.app (.app tmJetMul ((G.wk (σ := .nat)).wk (σ := JetTy))) (.var .here))) k
    deriv_norm at hb
    exact hb
  have h4 : Deriv Δ (.eq (.app (.lam (.app (.app tmJetMul (G.wk (σ := JetTy))) (.var .here))) r)
      (.app (.app tmJetMul G) r)) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.app (.app tmJetMul (G.wk (σ := JetTy))) (.var .here)) r
    deriv_norm at hb
    exact hb
  have h5 : Deriv Δ (.eq (.app (.app tmJetMul G) r)
      (.app (.app tmJetMul G) (.app (.app tmJetPow G) k))) :=
    Deriv.congArg (.app tmJetMul G) (Deriv.symmE (chrPow_appD G k))
  exact Deriv.transE h1 (Deriv.transE h2 (Deriv.transE (Deriv.congFun h3 r) (Deriv.transE h4 h5)))

/-- Recursor step of `tmJetComp f g n`. -/
def chrCompStep {Γ : List Ty} (f g : Tm Γ JetTy) (n : Tm Γ .nat) :
    Tm Γ (.arrow .nat (.arrow .rat .rat)) :=
  .lam (.lam (.qadd (.var .here)
    (.qmul (.app ((f.wk (σ := .nat)).wk (σ := .rat)) (.var (.there .here)))
      (.app (.app (.app tmJetPow (.app tmJetDrop0 ((g.wk (σ := .nat)).wk (σ := .rat))))
        (.var (.there .here))) ((n.wk (σ := .nat)).wk (σ := .rat))))))

/-- Partial composition sum up to `t` terms (`t = succ n` is `(f ∘ g)(n)`). -/
def chrCompPartialAt {Γ : List Ty} (f g : Tm Γ JetTy) (n t : Tm Γ .nat) : Tm Γ .rat :=
  .recNat (.qnat .zero) (chrCompStep f g n) t

@[derivNorm] theorem chrCompStep_rename {Γ Δ : List Ty}
    (f g : Tm Γ JetTy) (n : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (chrCompStep f g n).rename ρ = chrCompStep (f.rename ρ) (g.rename ρ) (n.rename ρ) := by
  simp only [chrCompStep, Tm.rename, Tm.wk, Tm.rename_rename, chrPow_rename, chrDrop0_rename]
  rfl

@[derivNorm] theorem chrCompStep_subst {Γ Δ : List Ty}
    (f g : Tm Γ JetTy) (n : Tm Γ .nat) (s : Sub Γ Δ) :
    (chrCompStep f g n).subst s = chrCompStep (f.subst s) (g.subst s) (n.subst s) := by
  simp only [chrCompStep, Tm.subst, Tm.wk_subst_ext, chrPow_subst, chrDrop0_subst]
  rfl

@[derivNorm] theorem chrCompPartialAt_rename {Γ Δ : List Ty}
    (f g : Tm Γ JetTy) (n t : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (chrCompPartialAt f g n t).rename ρ =
      chrCompPartialAt (f.rename ρ) (g.rename ρ) (n.rename ρ) (t.rename ρ) := by
  simp only [chrCompPartialAt, Tm.rename, chrCompStep_rename]

@[derivNorm] theorem chrCompPartialAt_subst {Γ Δ : List Ty}
    (f g : Tm Γ JetTy) (n t : Tm Γ .nat) (s : Sub Γ Δ) :
    (chrCompPartialAt f g n t).subst s =
      chrCompPartialAt (f.subst s) (g.subst s) (n.subst s) (t.subst s) := by
  simp only [chrCompPartialAt, Tm.subst, chrCompStep_subst]

/-- Applying `tmJetComp` to `f, g, n` converts to `chrCompPartialAt f g n (succ n)`. -/
def chrComp_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (f g : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app tmJetComp f) g) n) (chrCompPartialAt f g n (.succ n))) := by
  have h1 : Deriv Δ (.eq (.app tmJetComp f)
      (.lam (.lam (chrCompPartialAt (f.wk (σ := JetTy) |>.wk (σ := .nat))
        (.var (.there .here)) (.var .here) (.succ (.var .here)))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (.lam (.recNat (.qnat .zero)
        (.lam (.lam (.qadd (.var .here)
          (.qmul (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here)))
            (.app (.app (.app tmJetPow (.app tmJetDrop0 (.var (.there (.there (.there .here))))))
              (.var (.there .here))) (.var (.there (.there .here))))))))
        (.succ (.var .here))))) f
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq
      (.app (.lam (.lam (chrCompPartialAt (f.wk (σ := JetTy) |>.wk (σ := .nat))
        (.var (.there .here)) (.var .here) (.succ (.var .here))))) g)
      (.lam (chrCompPartialAt (f.wk (σ := .nat)) (g.wk (σ := .nat))
        (.var .here) (.succ (.var .here))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (chrCompPartialAt (f.wk (σ := JetTy) |>.wk (σ := .nat))
        (.var (.there .here)) (.var .here) (.succ (.var .here)))) g
    deriv_norm at hb
    exact hb
  have h3 : Deriv Δ (.eq
      (.app (.lam (chrCompPartialAt (f.wk (σ := .nat)) (g.wk (σ := .nat))
        (.var .here) (.succ (.var .here)))) n)
      (chrCompPartialAt f g n (.succ n))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (chrCompPartialAt (f.wk (σ := .nat)) (g.wk (σ := .nat))
        (.var .here) (.succ (.var .here))) n
    deriv_norm at hb
    exact hb
  exact Deriv.transE (Deriv.congFun (Deriv.transE (Deriv.congFun h1 g) h2) n) h3

/-- Base equation `chrCompPartialAt f g n 0 = 0` inside `Deriv`. -/
def chrCompPartial_zeroD {Γ as : List Ty} {Δ : Ctx Γ as}
    (f g : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (chrCompPartialAt f g n .zero) (.qnat .zero)) :=
  Deriv.convRecZero (.qnat .zero) (chrCompStep f g n)

/-- Step equation for `chrCompPartialAt f g n (succ k)` inside `Deriv`. -/
def chrCompPartial_succD {Γ as : List Ty} {Δ : Ctx Γ as}
    (f g : Tm Γ JetTy) (n k : Tm Γ .nat) :
    Deriv Δ (.eq (chrCompPartialAt f g n (.succ k))
      (.qadd (chrCompPartialAt f g n k)
        (.qmul (.app f k) (.app (.app (.app tmJetPow (.app tmJetDrop0 g)) k) n)))) := by
  let r : Tm Γ .rat := chrCompPartialAt f g n k
  have h1 := Deriv.convRecSucc (Δ := Δ) (.qnat .zero) (chrCompStep f g n) k
  have h2 : Deriv Δ (.eq (.app (chrCompStep f g n) k)
      (.lam (.qadd (.var .here)
        (.qmul (.app (f.wk (σ := .rat)) (k.wk (σ := .rat)))
          (.app (.app (.app tmJetPow (.app tmJetDrop0 (g.wk (σ := .rat))))
            (k.wk (σ := .rat))) (n.wk (σ := .rat))))))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.lam (a := .rat) (.qadd (.var .here)
        (.qmul (.app ((f.wk (σ := .nat)).wk (σ := .rat)) (.var (.there .here)))
          (.app (.app (.app tmJetPow (.app tmJetDrop0 ((g.wk (σ := .nat)).wk (σ := .rat))))
            (.var (.there .here))) ((n.wk (σ := .nat)).wk (σ := .rat)))))) k
    deriv_norm at hb
    exact hb
  have h3 : Deriv Δ (.eq
      (.app (.lam (.qadd (.var .here)
        (.qmul (.app (f.wk (σ := .rat)) (k.wk (σ := .rat)))
          (.app (.app (.app tmJetPow (.app tmJetDrop0 (g.wk (σ := .rat))))
            (k.wk (σ := .rat))) (n.wk (σ := .rat)))))) r)
      (.qadd r (.qmul (.app f k) (.app (.app (.app tmJetPow (.app tmJetDrop0 g)) k) n)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .rat)
      (.qadd (.var .here)
        (.qmul (.app (f.wk (σ := .rat)) (k.wk (σ := .rat)))
          (.app (.app (.app tmJetPow (.app tmJetDrop0 (g.wk (σ := .rat))))
            (k.wk (σ := .rat))) (n.wk (σ := .rat))))) r
    deriv_norm at hb
    exact hb
  exact Deriv.transE h1 (Deriv.transE (Deriv.congFun h2 r) h3)

/-- Left-shifted jet `(chrJetShift a)(j) = a(succ j)`. -/
def chrJetShift {Γ : List Ty} (a : Tm Γ JetTy) : Tm Γ JetTy :=
  .lam (.app (a.wk (σ := .nat)) (.succ (.var .here)))

@[derivNorm] theorem chrJetShift_rename {Γ Δ : List Ty} (a : Tm Γ JetTy) (ρ : Ren Γ Δ) :
    (chrJetShift a).rename ρ = chrJetShift (a.rename ρ) := by
  simp only [chrJetShift, Tm.rename, Tm.wk, Tm.rename_rename]
  rfl

@[derivNorm] theorem chrJetShift_subst {Γ Δ : List Ty} (a : Tm Γ JetTy) (s : Sub Γ Δ) :
    (chrJetShift a).subst s = chrJetShift (a.subst s) := by
  simp only [chrJetShift, Tm.subst, Tm.wk_subst_ext]
  rfl

/-- `(chrJetShift a)(j) = a(succ j)` inside `Deriv`. -/
def chrJetShift_appD {Γ as : List Ty} {Δ : Ctx Γ as} (a : Tm Γ JetTy) (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app (chrJetShift a) j) (.app a (.succ j))) := by
  have hb := Deriv.convBeta (Δ := Δ) (c := .nat) (.app (a.wk (σ := .nat)) (.succ (.var .here))) j
  deriv_norm at hb
  exact hb

/-- `∀ j. tmNatSub (succ n) (succ j) = tmNatSub n j`, proved by `Deriv.ind` on `j`. -/
def chrNatSub_succ_succD {Γ as : List Ty} {Δ : Ctx Γ as} (n : Tm Γ .nat) :
    Deriv Δ (.all .nat
      (.eq (tmNatSub (.succ n.wk) (.succ (.var .here))) (tmNatSub n.wk (.var .here)))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    exact Deriv.transE (tmNatSub_succD (.succ n) .zero)
      (Deriv.transE (Deriv.congTmNatPred (tmNatSub_zeroD (.succ n)))
        (Deriv.transE (tmNatPred_succD n) (Deriv.symmE (tmNatSub_zeroD n))))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    let j : Tm (.nat :: Γ) .nat := .var .here
    let nw : Tm (.nat :: Γ) .nat := n.wk
    exact Deriv.transE (tmNatSub_succD (.succ nw) (.succ j))
      (Deriv.transE (Deriv.congTmNatPred Deriv.ax)
        (Deriv.symmE (tmNatSub_succD nw j)))

/-- Term form of `chrNatSub_succ_succD`: `tmNatSub (succ n) (succ j) = tmNatSub n j`. -/
def chrNatSub_succ_succT {Γ as : List Ty} {Δ : Ctx Γ as} (n j : Tm Γ .nat) :
    Deriv Δ (.eq (tmNatSub (.succ n) (.succ j)) (tmNatSub n j)) := by
  have h := Deriv.allE j (chrNatSub_succ_succD (Δ := Δ) n)
  deriv_norm at h
  exact h

/-- Inductive step of `chrJetMulPartialLeftSuccD`. -/
def chrJetMulPartialLeftSuccStepT {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as}
    (a b : Tm Γ JetTy) (n : Tm Γ .nat)
    (h_ih : Deriv Δ (.eq (jetMulPartialAt a.wk b.wk (.succ n.wk) (.succ (.var .here)))
      (.qadd (.qmul (.app a.wk .zero) (.app b.wk (.succ n.wk)))
             (jetMulPartialAt (chrJetShift a.wk) b.wk n.wk (.var .here))))) :
    Deriv Δ (.eq (jetMulPartialAt a.wk b.wk (.succ n.wk) (.succ (.succ (.var .here))))
      (.qadd (.qmul (.app a.wk .zero) (.app b.wk (.succ n.wk)))
             (jetMulPartialAt (chrJetShift a.wk) b.wk n.wk (.succ (.var .here))))) := by
  let t : Tm (.nat :: Γ) .nat := .var .here
  let a₁ : Tm (.nat :: Γ) JetTy := a.wk
  let b₁ : Tm (.nat :: Γ) JetTy := b.wk
  let n₁ : Tm (.nat :: Γ) .nat := n.wk
  have h_term : Deriv Δ (.eq
      (.qmul (.app a₁ (.succ t)) (.app b₁ (tmNatSub (.succ n₁) (.succ t))))
      (.qmul (.app (chrJetShift a₁) t) (.app b₁ (tmNatSub n₁ t)))) :=
    Deriv.congQMul (Deriv.symmE (chrJetShift_appD a₁ t))
      (Deriv.congArg b₁ (chrNatSub_succ_succT n₁ t))
  exact Deriv.transE (jetMulPartial_succD a₁ b₁ (.succ n₁) (.succ t))
    (Deriv.transE (Deriv.congQAdd h_ih h_term)
      (Deriv.transE
        (Deriv.convQAddAssoc (.qmul (.app a₁ .zero) (.app b₁ (.succ n₁)))
          (jetMulPartialAt (chrJetShift a₁) b₁ n₁ t)
          (.qmul (.app (chrJetShift a₁) t) (.app b₁ (tmNatSub n₁ t))))
        (Deriv.congQAdd (Deriv.eqRefl _)
          (Deriv.symmE (jetMulPartial_succD (chrJetShift a₁) b₁ n₁ t)))))

/-- `∀ t. S_{n+1}(a, b, t+1) = a(0) * b(n+1) + S_n(chrJetShift a, b, t)`, proved by `Deriv.ind` on `t`. -/
def chrJetMulPartialLeftSuccD {Γ as : List Ty} {Δ : Ctx Γ as}
    (a b : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.all .nat
      (.eq (jetMulPartialAt a.wk b.wk (.succ n.wk) (.succ (.var .here)))
        (.qadd (.qmul (.app a.wk .zero) (.app b.wk (.succ n.wk)))
               (jetMulPartialAt (chrJetShift a.wk) b.wk n.wk (.var .here))))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    have h_lhs : Deriv Δ (.eq (jetMulPartialAt a b (.succ n) (.succ .zero))
        (.qmul (.app a .zero) (.app b (.succ n)))) :=
      Deriv.transE (jetMulPartial_succD a b (.succ n) .zero)
        (Deriv.transE
          (Deriv.congQAdd (jetMulPartial_zeroD a b (.succ n))
            (Deriv.congQMul (Deriv.eqRefl (.app a .zero))
              (Deriv.congArg b (tmNatSub_zeroD (.succ n)))))
          (prdQaddZeroLMul (.app a .zero) (.app b (.succ n))))
    have h_rhs : Deriv Δ (.eq
        (.qadd (.qmul (.app a .zero) (.app b (.succ n)))
               (jetMulPartialAt (chrJetShift a) b n .zero))
        (.qmul (.app a .zero) (.app b (.succ n)))) :=
      Deriv.transE
        (Deriv.congQAdd (Deriv.eqRefl _) (jetMulPartial_zeroD (chrJetShift a) b n))
        (Deriv.qlaw (.normMul (.app a .zero) (.app b (.succ n))))
    exact Deriv.transE h_lhs (Deriv.symmE h_rhs)
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrJetMulPartialLeftSuccStepT a b n Deriv.ax

/-- `(a · b)(succ n) = a(0) * b(succ n) + ((chrJetShift a) · b)(n)` inside `Deriv`. -/
def chrJetMulLeftSuccT {Γ as : List Ty} {Δ : Ctx Γ as}
    (a b : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) b) (.succ n))
      (.qadd (.qmul (.app a .zero) (.app b (.succ n)))
             (.app (.app (.app tmJetMul (chrJetShift a)) b) n))) := by
  have h := Deriv.allE (.succ n) (chrJetMulPartialLeftSuccD (Δ := Δ) a b n)
  deriv_norm at h
  exact Deriv.transE (tmJetMul_appD a b (.succ n))
    (Deriv.transE h
      (Deriv.congQAdd (Deriv.eqRefl _) (Deriv.symmE (tmJetMul_appD (chrJetShift a) b n))))

/-- Inductive step of `chrJetMulPartialRightShiftD`. -/
def chrJetMulPartialRightShiftStepT {Γ as : List Ty} {Δ : Ctx (.nat :: .nat :: Γ) as}
    (b a : Tm Γ JetTy) (n : Tm Γ .nat)
    (h_ih : Deriv Δ (.all .nat
      (.imp (.eq (.add (.var (.there (.there .here))) (.var .here)) (.succ n.wk.wk.wk))
        (.eq (jetMulPartialAt b.wk.wk.wk a.wk.wk.wk (.succ n.wk.wk.wk) (.var (.there (.there .here))))
             (jetMulPartialAt b.wk.wk.wk (chrJetShift a.wk.wk.wk) n.wk.wk.wk (.var (.there (.there .here))))))))
    (h_succ : Deriv Δ (.eq (.add (.succ (.var (.there .here))) (.var .here)) (.succ n.wk.wk))) :
    Deriv Δ (.eq (jetMulPartialAt b.wk.wk a.wk.wk (.succ n.wk.wk) (.succ (.var (.there .here))))
                 (jetMulPartialAt b.wk.wk (chrJetShift a.wk.wk) n.wk.wk (.succ (.var (.there .here))))) := by
  let d : Tm (.nat :: .nat :: Γ) .nat := .var .here
  let t : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  let b₂ : Tm (.nat :: .nat :: Γ) JetTy := b.wk.wk
  let a₂ : Tm (.nat :: .nat :: Γ) JetTy := a.wk.wk
  let n₂ : Tm (.nat :: .nat :: Γ) .nat := n.wk.wk
  have h_succ_td : Deriv Δ (.eq (.succ (.add t d)) (.succ n₂)) :=
    Deriv.transE (Deriv.symmE (succPlusT t d)) h_succ
  have h_td : Deriv Δ (.eq (.add t d) n₂) :=
    Deriv.impE (Deriv.succInj (.add t d) n₂) h_succ_td
  have h_t_sd : Deriv Δ (.eq (.add t (.succ d)) (.succ n₂)) :=
    Deriv.transE (Deriv.convAddSucc t d) h_succ_td
  have h_ih_sd := Deriv.allE (.succ d) h_ih
  deriv_norm at h_ih_sd
  have h_part : Deriv Δ (.eq (jetMulPartialAt b₂ a₂ (.succ n₂) t)
      (jetMulPartialAt b₂ (chrJetShift a₂) n₂ t)) :=
    Deriv.impE h_ih_sd h_t_sd
  have h_sub_sn : Deriv Δ (.eq (tmNatSub (.succ n₂) t) (.succ d)) :=
    tmNatSubAddCancelT h_t_sd
  have h_sub_n : Deriv Δ (.eq (tmNatSub n₂ t) d) :=
    tmNatSubAddCancelT h_td
  have h_a_term : Deriv Δ (.eq (.app a₂ (tmNatSub (.succ n₂) t))
      (.app (chrJetShift a₂) (tmNatSub n₂ t))) :=
    Deriv.transE (Deriv.congArg a₂ h_sub_sn)
      (Deriv.transE (Deriv.symmE (chrJetShift_appD a₂ d))
        (Deriv.symmE (Deriv.congArg (chrJetShift a₂) h_sub_n)))
  exact Deriv.transE (jetMulPartial_succD b₂ a₂ (.succ n₂) t)
    (Deriv.transE
      (Deriv.congQAdd h_part (Deriv.congQMul (Deriv.eqRefl (.app b₂ t)) h_a_term))
      (Deriv.symmE (jetMulPartial_succD b₂ (chrJetShift a₂) n₂ t)))

/-- `∀ t ∀ d. t + d = succ n → S_{n+1}(b, a, t) = S_n(b, chrJetShift a, t)`, proved by `Deriv.ind` on `t`. -/
def chrJetMulPartialRightShiftD {Γ as : List Ty} {Δ : Ctx Γ as}
    (b a : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) (.succ n.wk.wk))
        (.eq (jetMulPartialAt b.wk.wk a.wk.wk (.succ n.wk.wk) (.var (.there .here)))
             (jetMulPartialAt b.wk.wk (chrJetShift a.wk.wk) n.wk.wk (.var (.there .here))))))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    exact Deriv.transE (jetMulPartial_zeroD b.wk a.wk (.succ n.wk))
      (Deriv.symmE (jetMulPartial_zeroD b.wk (chrJetShift a.wk) n.wk))
  · refine Deriv.allI (Deriv.impI ?_)
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrJetMulPartialRightShiftStepT b a n (Deriv.wk Deriv.ax) Deriv.ax

/-- `(b · a)(succ n) = (b · (chrJetShift a))(n) + b(succ n) * a(0)` inside `Deriv`. -/
def chrJetMulRightSuccT {Γ as : List Ty} {Δ : Ctx Γ as}
    (b a : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul b) a) (.succ n))
      (.qadd (.app (.app (.app tmJetMul b) (chrJetShift a)) n)
             (.qmul (.app b (.succ n)) (.app a .zero)))) := by
  have h_inst := Deriv.allE .zero (Deriv.allE (.succ n) (chrJetMulPartialRightShiftD (Δ := Δ) b a n))
  deriv_norm at h_inst
  have h_part : Deriv Δ (.eq (jetMulPartialAt b a (.succ n) (.succ n))
      (.app (.app (.app tmJetMul b) (chrJetShift a)) n)) :=
    Deriv.transE (Deriv.impE h_inst (Deriv.convAddZero (.succ n)))
      (Deriv.symmE (tmJetMul_appD b (chrJetShift a) n))
  have h_sub_self : Deriv Δ (.eq (tmNatSub (.succ n) (.succ n)) .zero) :=
    tmNatSubAddCancelT (Deriv.convAddZero (.succ n))
  exact Deriv.transE (tmJetMul_appD b a (.succ n))
    (Deriv.transE (jetMulPartial_succD b a (.succ n) (.succ n))
      (Deriv.congQAdd h_part
        (Deriv.congQMul (Deriv.eqRefl (.app b (.succ n))) (Deriv.congArg a h_sub_self))))

/-- Inductive step of `chrJetMulCommD`. -/
def chrJetMulCommStepT {Γ as : List Ty} {Δ : Ctx (JetTy :: .nat :: Γ) as}
    (b : Tm Γ JetTy)
    (h_ih : Deriv Δ (.all JetTy
      (.eq (.app (.app (.app tmJetMul (.var .here)) b.wk.wk.wk) (.var (.there (.there .here))))
           (.app (.app (.app tmJetMul b.wk.wk.wk) (.var .here)) (.var (.there (.there .here))))))) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul (.var .here)) b.wk.wk) (.succ (.var (.there .here))))
                 (.app (.app (.app tmJetMul b.wk.wk) (.var .here)) (.succ (.var (.there .here))))) := by
  let a : Tm (JetTy :: .nat :: Γ) JetTy := .var .here
  let n : Tm (JetTy :: .nat :: Γ) .nat := .var (.there .here)
  let b₂ : Tm (JetTy :: .nat :: Γ) JetTy := b.wk.wk
  have h_ih_sa := Deriv.allE (chrJetShift a) h_ih
  deriv_norm at h_ih_sa
  exact Deriv.transE (chrJetMulLeftSuccT a b₂ n)
    (Deriv.transE (Deriv.convQAddComm
        (.qmul (.app a .zero) (.app b₂ (.succ n)))
        (.app (.app (.app tmJetMul (chrJetShift a)) b₂) n))
      (Deriv.transE
        (Deriv.congQAdd h_ih_sa (Deriv.convQMulComm (.app a .zero) (.app b₂ (.succ n))))
        (Deriv.symmE (chrJetMulRightSuccT b₂ a n))))

/-- `∀ n ∀ a. (a · b)(n) = (b · a)(n)`, proved by `Deriv.ind` on `n`. -/
def chrJetMulCommD {Γ as : List Ty} {Δ : Ctx Γ as} (b : Tm Γ JetTy) :
    Deriv Δ (.all .nat (.all JetTy
      (.eq (.app (.app (.app tmJetMul (.var .here)) b.wk.wk) (.var (.there .here)))
           (.app (.app (.app tmJetMul b.wk.wk) (.var .here)) (.var (.there .here)))))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI ?_
    let a : Tm (JetTy :: Γ) JetTy := .var .here
    let b₁ : Tm (JetTy :: Γ) JetTy := b.wk
    exact Deriv.transE (chrJetMulZeroD a b₁)
      (Deriv.transE (Deriv.convQMulComm (.app a .zero) (.app b₁ .zero))
        (Deriv.symmE (chrJetMulZeroD b₁ a)))
  · refine Deriv.allI (Deriv.impI (Deriv.allI ?_))
    deriv_norm
    exact chrJetMulCommStepT b Deriv.ax

/-- Commutativity of jet multiplication: `(a · b)(n) = (b · a)(n)`. -/
def chrJetMulCommT {Γ as : List Ty} {Δ : Ctx Γ as} (a b : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) b) n) (.app (.app (.app tmJetMul b) a) n)) := by
  have h := Deriv.allE a (Deriv.allE n (chrJetMulCommD (Δ := Δ) b))
  deriv_norm at h
  exact h

/-- Inductive step of `chrJetMulPartialZeroR`. -/
def chrJetMulPartialZeroRStepT {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as}
    (a u : Tm Γ JetTy) (n : Tm Γ .nat)
    (hu : Deriv Δ (.all .nat (Formula.qeqv (.app u.wk.wk (.var .here)) (.qnat .zero))))
    (h_ih : Deriv Δ (.eq (jetMulPartialAt a.wk u.wk n.wk (.var .here)) (.qnat .zero))) :
    Deriv Δ (.eq (jetMulPartialAt a.wk u.wk n.wk (.succ (.var .here))) (.qnat .zero)) := by
  let t : Tm (.nat :: Γ) .nat := .var .here
  let a₁ : Tm (.nat :: Γ) JetTy := a.wk
  let u₁ : Tm (.nat :: Γ) JetTy := u.wk
  let n₁ : Tm (.nat :: Γ) .nat := n.wk
  let k : Tm (.nat :: Γ) .nat := tmNatSub n₁ t
  have hu_k := Deriv.allE k hu
  deriv_norm at hu_k
  have h_term : Deriv Δ (.eq (.qmul (.app a₁ t) (.app u₁ k)) (.qnat .zero)) :=
    Deriv.transE (Deriv.qmulV (Deriv.qeqvRefl (.app a₁ t)) hu_k)
      (Deriv.qlaw (.mulZero (.app a₁ t)))
  exact Deriv.transE (jetMulPartial_succD a₁ u₁ n₁ t)
    (Deriv.transE (Deriv.congQAdd h_ih h_term)
      (Deriv.qlaw (.normNat .zero)))

/-- `(∀ j. u(j) ≈ 0) → ∀ t. S_n(a, u, t) = 0`, proved by `Deriv.ind` on `t`. -/
def chrJetMulPartialZeroR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.imp (.all .nat (Formula.qeqv (.app u.wk (.var .here)) (.qnat .zero)))
      (.all .nat (.eq (jetMulPartialAt a.wk u.wk n.wk (.var .here)) (.qnat .zero)))) := by
  refine Deriv.impI (Deriv.ind ?_ ?_)
  · deriv_norm
    exact jetMulPartial_zeroD a u n
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrJetMulPartialZeroRStepT a u n (Deriv.wk Deriv.ax) Deriv.ax

/-- `(a · u)(n) = 0` when `∀ j. u(j) ≈ 0`. -/
def chrJetMulZeroR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u : Tm Γ JetTy) (n : Tm Γ .nat)
    (hu : Deriv Δ (.all .nat (Formula.qeqv (.app u.wk (.var .here)) (.qnat .zero)))) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) u) n) (.qnat .zero)) := by
  have h := Deriv.allE (.succ n) (Deriv.impE (chrJetMulPartialZeroR a u n) hu)
  deriv_norm at h
  exact Deriv.transE (tmJetMul_appD a u n) h

/-- Inductive step of `chrJetMulPartialCongR`. -/
def chrJetMulPartialCongRStepT {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as}
    (a u v : Tm Γ JetTy) (n : Tm Γ .nat)
    (huv : Deriv Δ (.all .nat (Formula.qeqv (.app u.wk.wk (.var .here)) (.app v.wk.wk (.var .here)))))
    (h_ih : Deriv Δ (.eq (jetMulPartialAt a.wk u.wk n.wk (.var .here))
                         (jetMulPartialAt a.wk v.wk n.wk (.var .here)))) :
    Deriv Δ (.eq (jetMulPartialAt a.wk u.wk n.wk (.succ (.var .here)))
                 (jetMulPartialAt a.wk v.wk n.wk (.succ (.var .here)))) := by
  let t : Tm (.nat :: Γ) .nat := .var .here
  let a₁ : Tm (.nat :: Γ) JetTy := a.wk
  let u₁ : Tm (.nat :: Γ) JetTy := u.wk
  let v₁ : Tm (.nat :: Γ) JetTy := v.wk
  let n₁ : Tm (.nat :: Γ) .nat := n.wk
  let k : Tm (.nat :: Γ) .nat := tmNatSub n₁ t
  have huv_k := Deriv.allE k huv
  deriv_norm at huv_k
  exact Deriv.transE (jetMulPartial_succD a₁ u₁ n₁ t)
    (Deriv.transE
      (Deriv.congQAdd h_ih (Deriv.qmulV (Deriv.qeqvRefl (.app a₁ t)) huv_k))
      (Deriv.symmE (jetMulPartial_succD a₁ v₁ n₁ t)))

/-- `(∀ j. u(j) ≈ v(j)) → ∀ t. S_n(a, u, t) = S_n(a, v, t)`, proved by `Deriv.ind` on `t`. -/
def chrJetMulPartialCongR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u v : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.imp (.all .nat (Formula.qeqv (.app u.wk (.var .here)) (.app v.wk (.var .here))))
      (.all .nat
        (.eq (jetMulPartialAt a.wk u.wk n.wk (.var .here))
             (jetMulPartialAt a.wk v.wk n.wk (.var .here))))) := by
  refine Deriv.impI (Deriv.ind ?_ ?_)
  · deriv_norm
    exact Deriv.transE (jetMulPartial_zeroD a u n) (Deriv.symmE (jetMulPartial_zeroD a v n))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrJetMulPartialCongRStepT a u v n (Deriv.wk Deriv.ax) Deriv.ax

/-- `(a · u)(n) = (a · v)(n)` when `∀ j. u(j) ≈ v(j)`. -/
def chrJetMulCongR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u v : Tm Γ JetTy) (n : Tm Γ .nat)
    (huv : Deriv Δ (.all .nat (Formula.qeqv (.app u.wk (.var .here)) (.app v.wk (.var .here))))) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) u) n) (.app (.app (.app tmJetMul a) v) n)) := by
  have h := Deriv.allE (.succ n) (Deriv.impE (chrJetMulPartialCongR a u v n) huv)
  deriv_norm at h
  exact Deriv.transE (tmJetMul_appD a u n)
    (Deriv.transE h (Deriv.symmE (tmJetMul_appD a v n)))

/-- `(u · b)(n) = (v · b)(n)` when `∀ j. u(j) ≈ v(j)`. -/
def chrJetMulCongL {Γ as : List Ty} {Δ : Ctx Γ as}
    (u v b : Tm Γ JetTy) (n : Tm Γ .nat)
    (huv : Deriv Δ (.all .nat (Formula.qeqv (.app u.wk (.var .here)) (.app v.wk (.var .here))))) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul u) b) n) (.app (.app (.app tmJetMul v) b) n)) :=
  Deriv.transE (chrJetMulCommT u b n)
    (Deriv.transE (chrJetMulCongR b u v n huv) (chrJetMulCommT b v n))

/-- Inductive step of `chrJetMulPartialScaleR`. -/
def chrJetMulPartialScaleRStepT {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as}
    (a u v : Tm Γ JetTy) (s : Tm Γ .rat) (n : Tm Γ .nat)
    (huv : Deriv Δ (.all .nat
      (Formula.qeqv (.app u.wk.wk (.var .here)) (.qmul s.wk.wk (.app v.wk.wk (.var .here))))))
    (h_ih : Deriv Δ (.eq (jetMulPartialAt a.wk u.wk n.wk (.var .here))
                         (.qmul s.wk (jetMulPartialAt a.wk v.wk n.wk (.var .here))))) :
    Deriv Δ (.eq (jetMulPartialAt a.wk u.wk n.wk (.succ (.var .here)))
                 (.qmul s.wk (jetMulPartialAt a.wk v.wk n.wk (.succ (.var .here))))) := by
  let t : Tm (.nat :: Γ) .nat := .var .here
  let a₁ : Tm (.nat :: Γ) JetTy := a.wk
  let u₁ : Tm (.nat :: Γ) JetTy := u.wk
  let v₁ : Tm (.nat :: Γ) JetTy := v.wk
  let s₁ : Tm (.nat :: Γ) .rat := s.wk
  let n₁ : Tm (.nat :: Γ) .nat := n.wk
  let k : Tm (.nat :: Γ) .nat := tmNatSub n₁ t
  have huv_k := Deriv.allE k huv
  deriv_norm at huv_k
  have h_term : Deriv Δ (.eq (.qmul (.app a₁ t) (.app u₁ k))
      (.qmul s₁ (.qmul (.app a₁ t) (.app v₁ k)))) :=
    Deriv.transE (Deriv.qmulV (Deriv.qeqvRefl (.app a₁ t)) huv_k)
      (prdQmulLeftComm (.app a₁ t) s₁ (.app v₁ k))
  exact Deriv.transE (jetMulPartial_succD a₁ u₁ n₁ t)
    (Deriv.transE (Deriv.congQAdd h_ih h_term)
      (Deriv.transE
        (Deriv.symmE (Deriv.convQMulAdd s₁ (jetMulPartialAt a₁ v₁ n₁ t)
          (.qmul (.app a₁ t) (.app v₁ k))))
        (Deriv.congQMul (Deriv.eqRefl s₁) (Deriv.symmE (jetMulPartial_succD a₁ v₁ n₁ t)))))

/-- `(∀ j. u(j) ≈ s * v(j)) → ∀ t. S_n(a, u, t) = s * S_n(a, v, t)`, proved by `Deriv.ind` on `t`. -/
def chrJetMulPartialScaleR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u v : Tm Γ JetTy) (s : Tm Γ .rat) (n : Tm Γ .nat) :
    Deriv Δ (.imp (.all .nat
        (Formula.qeqv (.app u.wk (.var .here)) (.qmul s.wk (.app v.wk (.var .here)))))
      (.all .nat
        (.eq (jetMulPartialAt a.wk u.wk n.wk (.var .here))
             (.qmul s.wk (jetMulPartialAt a.wk v.wk n.wk (.var .here)))))) := by
  refine Deriv.impI (Deriv.ind ?_ ?_)
  · deriv_norm
    exact Deriv.transE (jetMulPartial_zeroD a u n)
      (Deriv.symmE
        (Deriv.transE (Deriv.congQMul (Deriv.eqRefl s) (jetMulPartial_zeroD a v n))
          (Deriv.qlaw (.mulZero s))))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrJetMulPartialScaleRStepT a u v s n (Deriv.wk Deriv.ax) Deriv.ax

/-- `(a · u)(n) = s * (a · v)(n)` when `∀ j. u(j) ≈ s * v(j)`. -/
def chrJetMulScaleR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u v : Tm Γ JetTy) (s : Tm Γ .rat) (n : Tm Γ .nat)
    (huv : Deriv Δ (.all .nat
      (Formula.qeqv (.app u.wk (.var .here)) (.qmul s.wk (.app v.wk (.var .here)))))) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) u) n)
                 (.qmul s (.app (.app (.app tmJetMul a) v) n))) := by
  have h := Deriv.allE (.succ n) (Deriv.impE (chrJetMulPartialScaleR a u v s n) huv)
  deriv_norm at h
  exact Deriv.transE (tmJetMul_appD a u n)
    (Deriv.transE h (Deriv.congQMul (Deriv.eqRefl s) (Deriv.symmE (tmJetMul_appD a v n))))

/-- Inductive step of `chrJetMulPartialLinR`. -/
def chrJetMulPartialLinRStepT {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as}
    (a u v w : Tm Γ JetTy) (s : Tm Γ .rat) (n : Tm Γ .nat)
    (h : Deriv Δ (.all .nat
      (Formula.qeqv (.app u.wk.wk (.var .here))
        (.qadd (.app v.wk.wk (.var .here)) (.qmul s.wk.wk (.app w.wk.wk (.var .here)))))))
    (h_ih : Deriv Δ (.eq (jetMulPartialAt a.wk u.wk n.wk (.var .here))
      (.qadd (jetMulPartialAt a.wk v.wk n.wk (.var .here))
             (.qmul s.wk (jetMulPartialAt a.wk w.wk n.wk (.var .here)))))) :
    Deriv Δ (.eq (jetMulPartialAt a.wk u.wk n.wk (.succ (.var .here)))
      (.qadd (jetMulPartialAt a.wk v.wk n.wk (.succ (.var .here)))
             (.qmul s.wk (jetMulPartialAt a.wk w.wk n.wk (.succ (.var .here)))))) := by
  let t : Tm (.nat :: Γ) .nat := .var .here
  let a₁ : Tm (.nat :: Γ) JetTy := a.wk
  let u₁ : Tm (.nat :: Γ) JetTy := u.wk
  let v₁ : Tm (.nat :: Γ) JetTy := v.wk
  let w₁ : Tm (.nat :: Γ) JetTy := w.wk
  let s₁ : Tm (.nat :: Γ) .rat := s.wk
  let n₁ : Tm (.nat :: Γ) .nat := n.wk
  let k : Tm (.nat :: Γ) .nat := tmNatSub n₁ t
  have h_k := Deriv.allE k h
  deriv_norm at h_k
  have h_term : Deriv Δ (.eq (.qmul (.app a₁ t) (.app u₁ k))
      (.qadd (.qmul (.app a₁ t) (.app v₁ k))
             (.qmul s₁ (.qmul (.app a₁ t) (.app w₁ k))))) :=
    Deriv.transE (Deriv.qmulV (Deriv.qeqvRefl (.app a₁ t)) h_k)
      (Deriv.transE
        (Deriv.convQMulAdd (.app a₁ t) (.app v₁ k) (.qmul s₁ (.app w₁ k)))
        (Deriv.congQAdd (Deriv.eqRefl _) (prdQmulLeftComm (.app a₁ t) s₁ (.app w₁ k))))
  exact Deriv.transE (jetMulPartial_succD a₁ u₁ n₁ t)
    (Deriv.transE (Deriv.congQAdd h_ih h_term)
      (Deriv.transE
        (chrQaddFourMid
          (jetMulPartialAt a₁ v₁ n₁ t)
          (.qmul s₁ (jetMulPartialAt a₁ w₁ n₁ t))
          (.qmul (.app a₁ t) (.app v₁ k))
          (.qmul s₁ (.qmul (.app a₁ t) (.app w₁ k))))
        (Deriv.congQAdd
          (Deriv.symmE (jetMulPartial_succD a₁ v₁ n₁ t))
          (Deriv.transE
            (Deriv.symmE (Deriv.convQMulAdd s₁ (jetMulPartialAt a₁ w₁ n₁ t)
              (.qmul (.app a₁ t) (.app w₁ k))))
            (Deriv.congQMul (Deriv.eqRefl s₁)
              (Deriv.symmE (jetMulPartial_succD a₁ w₁ n₁ t)))))))

/-- `(∀ j. u(j) ≈ v(j) + s * w(j)) → ∀ t. S_n(a, u, t) = S_n(a, v, t) + s * S_n(a, w, t)`, by `Deriv.ind` on `t`. -/
def chrJetMulPartialLinR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u v w : Tm Γ JetTy) (s : Tm Γ .rat) (n : Tm Γ .nat) :
    Deriv Δ (.imp (.all .nat
        (Formula.qeqv (.app u.wk (.var .here))
          (.qadd (.app v.wk (.var .here)) (.qmul s.wk (.app w.wk (.var .here))))))
      (.all .nat
        (.eq (jetMulPartialAt a.wk u.wk n.wk (.var .here))
             (.qadd (jetMulPartialAt a.wk v.wk n.wk (.var .here))
                    (.qmul s.wk (jetMulPartialAt a.wk w.wk n.wk (.var .here))))))) := by
  refine Deriv.impI (Deriv.ind ?_ ?_)
  · deriv_norm
    exact Deriv.transE (jetMulPartial_zeroD a u n)
      (Deriv.symmE
        (Deriv.transE
          (Deriv.congQAdd (jetMulPartial_zeroD a v n)
            (Deriv.transE (Deriv.congQMul (Deriv.eqRefl s) (jetMulPartial_zeroD a w n))
              (Deriv.qlaw (.mulZero s))))
          (Deriv.qlaw (.normNat .zero))))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrJetMulPartialLinRStepT a u v w s n (Deriv.wk Deriv.ax) Deriv.ax

/-- `(a · u)(n) = (a · v)(n) + s * (a · w)(n)` when `∀ j. u(j) ≈ v(j) + s * w(j)`. -/
def chrJetMulLinR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u v w : Tm Γ JetTy) (s : Tm Γ .rat) (n : Tm Γ .nat)
    (h : Deriv Δ (.all .nat
      (Formula.qeqv (.app u.wk (.var .here))
        (.qadd (.app v.wk (.var .here)) (.qmul s.wk (.app w.wk (.var .here))))))) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) u) n)
                 (.qadd (.app (.app (.app tmJetMul a) v) n)
                        (.qmul s (.app (.app (.app tmJetMul a) w) n)))) := by
  have h_part := Deriv.allE (.succ n) (Deriv.impE (chrJetMulPartialLinR a u v w s n) h)
  deriv_norm at h_part
  exact Deriv.transE (tmJetMul_appD a u n)
    (Deriv.transE h_part
      (Deriv.congQAdd
        (Deriv.symmE (tmJetMul_appD a v n))
        (Deriv.congQMul (Deriv.eqRefl s) (Deriv.symmE (tmJetMul_appD a w n)))))

/-- `∀ j. (chrJetShift (a · b))(j) ≈ ((chrJetShift a) · b)(j) + a(0) * (chrJetShift b)(j)`. -/
def chrShiftMulD {Γ as : List Ty} {Δ : Ctx Γ as} (a b : Tm Γ JetTy) :
    Deriv Δ (.all .nat
      (Formula.qeqv (.app (chrJetShift (.app (.app tmJetMul a) b)).wk (.var .here))
        (.qadd (.app (Tm.app (.app tmJetMul (chrJetShift a)) b).wk (.var .here))
               (.qmul (Tm.app a .zero).wk (.app (chrJetShift b).wk (.var .here)))))) := by
  refine Deriv.allI ?_
  deriv_norm
  let j : Tm (.nat :: Γ) .nat := .var .here
  let aw : Tm (.nat :: Γ) JetTy := a.wk
  let bw : Tm (.nat :: Γ) JetTy := b.wk
  exact Deriv.qeqvOfEq
    (Deriv.transE (chrJetShift_appD (.app (.app tmJetMul aw) bw) j)
      (Deriv.transE (chrJetMulLeftSuccT aw bw j)
        (Deriv.transE
          (Deriv.convQAddComm
            (.qmul (.app aw .zero) (.app bw (.succ j)))
            (.app (.app (.app tmJetMul (chrJetShift aw)) bw) j))
          (Deriv.congQAdd (Deriv.eqRefl _)
            (Deriv.congQMul (Deriv.eqRefl (.app aw .zero))
              (Deriv.symmE (chrJetShift_appD bw j)))))))

/-- Inductive step of `chrJetMulAssocD`. -/
def chrJetMulAssocStepT {Γ as : List Ty} {Δ : Ctx (JetTy :: .nat :: Γ) as}
    (b c : Tm Γ JetTy)
    (h_ih : Deriv Δ (.all JetTy
      (.eq (.app (.app (.app tmJetMul (.app (.app tmJetMul (.var .here)) b.wk.wk.wk)) c.wk.wk.wk)
             (.var (.there (.there .here))))
           (.app (.app (.app tmJetMul (.var .here)) (.app (.app tmJetMul b.wk.wk.wk) c.wk.wk.wk))
             (.var (.there (.there .here))))))) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul (.app (.app tmJetMul (.var .here)) b.wk.wk)) c.wk.wk)
                   (.succ (.var (.there .here))))
                 (.app (.app (.app tmJetMul (.var .here)) (.app (.app tmJetMul b.wk.wk) c.wk.wk))
                   (.succ (.var (.there .here))))) := by
  let a : Tm (JetTy :: .nat :: Γ) JetTy := .var .here
  let n : Tm (JetTy :: .nat :: Γ) .nat := .var (.there .here)
  let b₂ : Tm (JetTy :: .nat :: Γ) JetTy := b.wk.wk
  let c₂ : Tm (JetTy :: .nat :: Γ) JetTy := c.wk.wk
  let sa : Tm (JetTy :: .nat :: Γ) JetTy := chrJetShift a
  let sb : Tm (JetTy :: .nat :: Γ) JetTy := chrJetShift b₂
  let ab : Tm (JetTy :: .nat :: Γ) JetTy := .app (.app tmJetMul a) b₂
  let sab : Tm (JetTy :: .nat :: Γ) JetTy := .app (.app tmJetMul sa) b₂
  let bc : Tm (JetTy :: .nat :: Γ) JetTy := .app (.app tmJetMul b₂) c₂
  have h_ih_sa := Deriv.allE sa h_ih
  deriv_norm at h_ih_sa
  have h_lin : Deriv Δ (.eq
      (.app (.app (.app tmJetMul (chrJetShift ab)) c₂) n)
      (.qadd (.app (.app (.app tmJetMul sa) bc) n)
             (.qmul (.app a .zero) (.app (.app (.app tmJetMul sb) c₂) n)))) :=
    Deriv.transE (chrJetMulCommT (chrJetShift ab) c₂ n)
      (Deriv.transE (chrJetMulLinR c₂ (chrJetShift ab) sab sb (.app a .zero) n (chrShiftMulD (Δ := Δ) a b₂))
        (Deriv.congQAdd
          (Deriv.transE (chrJetMulCommT c₂ sab n) h_ih_sa)
          (Deriv.congQMul (Deriv.eqRefl (.app a .zero)) (chrJetMulCommT c₂ sb n))))
  have h_head : Deriv Δ (.eq
      (.qmul (.app ab .zero) (.app c₂ (.succ n)))
      (.qmul (.app a .zero) (.qmul (.app b₂ .zero) (.app c₂ (.succ n))))) :=
    Deriv.transE (Deriv.congQMul (chrJetMulZeroD a b₂) (Deriv.eqRefl _))
      (Deriv.convQMulAssoc (.app a .zero) (.app b₂ .zero) (.app c₂ (.succ n)))
  have h_combine : Deriv Δ (.eq
      (.qadd (.qmul (.app a .zero) (.qmul (.app b₂ .zero) (.app c₂ (.succ n))))
        (.qadd (.app (.app (.app tmJetMul sa) bc) n)
               (.qmul (.app a .zero) (.app (.app (.app tmJetMul sb) c₂) n))))
      (.qadd (.qmul (.app a .zero) (.app bc (.succ n)))
             (.app (.app (.app tmJetMul sa) bc) n))) :=
    Deriv.transE
      (Deriv.congQAdd (Deriv.eqRefl _)
        (Deriv.convQAddComm
          (.app (.app (.app tmJetMul sa) bc) n)
          (.qmul (.app a .zero) (.app (.app (.app tmJetMul sb) c₂) n))))
      (Deriv.transE
        (Deriv.symmE (Deriv.convQAddAssoc
          (.qmul (.app a .zero) (.qmul (.app b₂ .zero) (.app c₂ (.succ n))))
          (.qmul (.app a .zero) (.app (.app (.app tmJetMul sb) c₂) n))
          (.app (.app (.app tmJetMul sa) bc) n)))
        (Deriv.congQAdd
          (Deriv.transE
            (Deriv.symmE (Deriv.convQMulAdd (.app a .zero)
              (.qmul (.app b₂ .zero) (.app c₂ (.succ n)))
              (.app (.app (.app tmJetMul sb) c₂) n)))
            (Deriv.congQMul (Deriv.eqRefl (.app a .zero))
              (Deriv.symmE (chrJetMulLeftSuccT b₂ c₂ n))))
          (Deriv.eqRefl _)))
  exact Deriv.transE (chrJetMulLeftSuccT ab c₂ n)
    (Deriv.transE (Deriv.congQAdd h_head h_lin)
      (Deriv.transE h_combine (Deriv.symmE (chrJetMulLeftSuccT a bc n))))

/-- `∀ n ∀ a. ((a · b) · c)(n) = (a · (b · c))(n)`, proved by `Deriv.ind` on `n`. -/
def chrJetMulAssocD {Γ as : List Ty} {Δ : Ctx Γ as} (b c : Tm Γ JetTy) :
    Deriv Δ (.all .nat (.all JetTy
      (.eq (.app (.app (.app tmJetMul (.app (.app tmJetMul (.var .here)) b.wk.wk)) c.wk.wk)
             (.var (.there .here)))
           (.app (.app (.app tmJetMul (.var .here)) (.app (.app tmJetMul b.wk.wk) c.wk.wk))
             (.var (.there .here)))))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI ?_
    let a : Tm (JetTy :: Γ) JetTy := .var .here
    let b₁ : Tm (JetTy :: Γ) JetTy := b.wk
    let c₁ : Tm (JetTy :: Γ) JetTy := c.wk
    let ab : Tm (JetTy :: Γ) JetTy := .app (.app tmJetMul a) b₁
    let bc : Tm (JetTy :: Γ) JetTy := .app (.app tmJetMul b₁) c₁
    exact Deriv.transE (chrJetMulZeroD ab c₁)
      (Deriv.transE (Deriv.congQMul (chrJetMulZeroD a b₁) (Deriv.eqRefl (.app c₁ .zero)))
        (Deriv.transE (Deriv.convQMulAssoc (.app a .zero) (.app b₁ .zero) (.app c₁ .zero))
          (Deriv.transE
            (Deriv.congQMul (Deriv.eqRefl (.app a .zero)) (Deriv.symmE (chrJetMulZeroD b₁ c₁)))
            (Deriv.symmE (chrJetMulZeroD a bc)))))
  · refine Deriv.allI (Deriv.impI (Deriv.allI ?_))
    deriv_norm
    exact chrJetMulAssocStepT b c Deriv.ax

/-- Associativity of jet multiplication: `((a · b) · c)(n) = (a · (b · c))(n)`. -/
def chrJetMulAssocT {Γ as : List Ty} {Δ : Ctx Γ as}
    (a b c : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul (.app (.app tmJetMul a) b)) c) n)
                 (.app (.app (.app tmJetMul a) (.app (.app tmJetMul b) c)) n)) := by
  have h := Deriv.allE a (Deriv.allE n (chrJetMulAssocD (Δ := Δ) b c))
  deriv_norm at h
  exact h

/-- Left-commutativity of jet multiplication: `(a · (b · c))(n) = (b · (a · c))(n)`. -/
def chrJetMulLeftCommT {Γ as : List Ty} {Δ : Ctx Γ as}
    (a b c : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) (.app (.app tmJetMul b) c)) n)
                 (.app (.app (.app tmJetMul b) (.app (.app tmJetMul a) c)) n)) := by
  have h_comm : Deriv Δ (.all .nat
      (Formula.qeqv (.app (.app (.app tmJetMul a.wk) b.wk) (.var .here))
                    (.app (.app (.app tmJetMul b.wk) a.wk) (.var .here)))) :=
    Deriv.allI (Deriv.qeqvOfEq (chrJetMulCommT a.wk b.wk (.var .here)))
  exact Deriv.transE (Deriv.symmE (chrJetMulAssocT a b c n))
    (Deriv.transE (chrJetMulCongL (.app (.app tmJetMul a) b) (.app (.app tmJetMul b) a) c n h_comm)
      (chrJetMulAssocT b a c n))

/-- `∀ j. D((G₊)^0)(j) ≈ 0`. -/
def chrDerivPowZeroD {Γ as : List Ty} {Δ : Ctx Γ as} (g : Tm Γ JetTy) :
    Deriv Δ (.all .nat
      (Formula.qeqv
        (.app (.app tmJetDeriv (.app (.app tmJetPow (.app tmJetDrop0 g.wk)) .zero)) (.var .here))
        (.qnat .zero))) := by
  refine Deriv.allI ?_
  deriv_norm
  let j : Tm (.nat :: Γ) .nat := .var .here
  let G₁ : Tm (.nat :: Γ) JetTy := .app tmJetDrop0 g.wk
  exact Deriv.qeqvOfEq
    (Deriv.transE
      (Deriv.congFun (Deriv.congArg tmJetDeriv (chrPow_zeroD G₁)) j)
      (chrDerivConstOneD j))

/-- Base case (`k = 0`) of `chrPowDerivD`. -/
def chrPowDerivBaseT {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as} (g : Tm Γ JetTy) :
    Deriv Δ (Formula.qeqv
      (.app (.app tmJetDeriv
        (.app (.app tmJetPow (.app tmJetDrop0 g.wk)) (.succ .zero)))
        (.var .here))
      (.qmul (.qnat (.succ .zero))
        (.app (.app (.app tmJetMul (.app tmJetDeriv g.wk))
          (.app (.app tmJetPow (.app tmJetDrop0 g.wk)) .zero))
          (.var .here)))) := by
  let n : Tm (.nat :: Γ) .nat := .var .here
  let g₁ : Tm (.nat :: Γ) JetTy := g.wk
  let G : Tm (.nat :: Γ) JetTy := .app tmJetDrop0 g₁
  let Dg : Tm (.nat :: Γ) JetTy := .app tmJetDeriv g₁
  let P0 : Tm (.nat :: Γ) JetTy := .app (.app tmJetPow G) .zero
  let P1 : Tm (.nat :: Γ) JetTy := .app (.app tmJetPow G) (.succ .zero)
  have h_dg : Deriv Δ (.all .nat
      (Formula.qeqv (.app (.app tmJetDeriv (.app tmJetDrop0 g₁.wk)) (.var .here))
                    (.app (.app tmJetDeriv g₁.wk) (.var .here)))) :=
    Deriv.allI (Deriv.qeqvOfEq (chrDerivDrop0D g₁.wk (.var .here)))
  have h_unfold : Deriv Δ (.eq (.app (.app tmJetDeriv P1) n)
      (.app (.app tmJetDeriv (.app (.app tmJetMul G) P0)) n)) :=
    Deriv.congFun (Deriv.congArg tmJetDeriv (chrPow_succD G .zero)) n
  have h_term1 : Deriv Δ (.eq (.app (.app (.app tmJetMul (.app tmJetDeriv G)) P0) n)
      (.app (.app (.app tmJetMul Dg) P0) n)) :=
    chrJetMulCongL (.app tmJetDeriv G) Dg P0 n h_dg
  have h_term2 : Deriv Δ (.eq (.app (.app (.app tmJetMul G) (.app tmJetDeriv P0)) n)
      (.qnat .zero)) :=
    chrJetMulZeroR G (.app tmJetDeriv P0) n (chrDerivPowZeroD g₁)
  exact Deriv.qeqvTrans (Deriv.qeqvOfEq h_unfold)
    (Deriv.qeqvTrans (productRuleAtD G P0 n)
      (Deriv.qeqvTrans (Deriv.qeqvOfEq (Deriv.congQAdd h_term1 h_term2))
        (Deriv.qeqvTrans (Deriv.qeqvAddZero (.app (.app (.app tmJetMul Dg) P0) n))
          (Deriv.qeqvSymm (chrQmulOneL (.app (.app (.app tmJetMul Dg) P0) n))))))

/-- Inductive step (`k = r ↦ succ r`) of `chrPowDerivD`. -/
def chrPowDerivStepT {Γ as : List Ty} {Δ : Ctx (.nat :: .nat :: Γ) as}
    (g : Tm Γ JetTy)
    (h_ih : Deriv Δ (.all .nat
      (Formula.qeqv
        (.app (.app tmJetDeriv
          (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk.wk)) (.succ (.var (.there (.there .here))))))
          (.var .here))
        (.qmul (.qnat (.succ (.var (.there (.there .here)))))
          (.app (.app (.app tmJetMul (.app tmJetDeriv g.wk.wk.wk))
            (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk.wk)) (.var (.there (.there .here)))))
            (.var .here)))))) :
    Deriv Δ (Formula.qeqv
      (.app (.app tmJetDeriv
        (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk)) (.succ (.succ (.var (.there .here))))))
        (.var .here))
      (.qmul (.qnat (.succ (.succ (.var (.there .here)))))
        (.app (.app (.app tmJetMul (.app tmJetDeriv g.wk.wk))
          (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk)) (.succ (.var (.there .here)))))
          (.var .here)))) := by
  let n : Tm (.nat :: .nat :: Γ) .nat := .var .here
  let r : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  let g₂ : Tm (.nat :: .nat :: Γ) JetTy := g.wk.wk
  let G : Tm (.nat :: .nat :: Γ) JetTy := .app tmJetDrop0 g₂
  let Dg : Tm (.nat :: .nat :: Γ) JetTy := .app tmJetDeriv g₂
  let Pr : Tm (.nat :: .nat :: Γ) JetTy := .app (.app tmJetPow G) r
  let Psr : Tm (.nat :: .nat :: Γ) JetTy := .app (.app tmJetPow G) (.succ r)
  let Pssr : Tm (.nat :: .nat :: Γ) JetTy := .app (.app tmJetPow G) (.succ (.succ r))
  have h_dg : Deriv Δ (.all .nat
      (Formula.qeqv (.app (.app tmJetDeriv (.app tmJetDrop0 g₂.wk)) (.var .here))
                    (.app (.app tmJetDeriv g₂.wk) (.var .here)))) :=
    Deriv.allI (Deriv.qeqvOfEq (chrDerivDrop0D g₂.wk (.var .here)))
  have h_unfold : Deriv Δ (.eq (.app (.app tmJetDeriv Pssr) n)
      (.app (.app tmJetDeriv (.app (.app tmJetMul G) Psr)) n)) :=
    Deriv.congFun (Deriv.congArg tmJetDeriv (chrPow_succD G (.succ r))) n
  have h_term1 : Deriv Δ (.eq (.app (.app (.app tmJetMul (.app tmJetDeriv G)) Psr) n)
      (.app (.app (.app tmJetMul Dg) Psr) n)) :=
    chrJetMulCongL (.app tmJetDeriv G) Dg Psr n h_dg
  have h_ih_norm : Deriv Δ (.all .nat
      (Formula.qeqv (.app (Tm.app tmJetDeriv Psr).wk (.var .here))
        (.qmul (Tm.qnat (.succ r)).wk (.app (Tm.app (.app tmJetMul Dg) Pr).wk (.var .here))))) := by
    dsimp only [Psr, Dg, Pr, G, g₂, r]
    deriv_norm
    exact h_ih
  have h_term2 : Deriv Δ (.eq (.app (.app (.app tmJetMul G) (.app tmJetDeriv Psr)) n)
      (.qmul (.qnat (.succ r)) (.app (.app (.app tmJetMul Dg) Psr) n))) :=
    Deriv.transE
      (chrJetMulScaleR G (.app tmJetDeriv Psr) (.app (.app tmJetMul Dg) Pr)
        (.qnat (.succ r)) n h_ih_norm)
      (Deriv.congQMul (Deriv.eqRefl (.qnat (.succ r)))
        (Deriv.transE (chrJetMulLeftCommT G Dg Pr n)
          (Deriv.congFun
            (Deriv.congArg (.app tmJetMul Dg) (Deriv.symmE (chrPow_succD G r))) n)))
  exact Deriv.qeqvTrans (Deriv.qeqvOfEq h_unfold)
    (Deriv.qeqvTrans (productRuleAtD G Psr n)
      (Deriv.qeqvOfEq
        (Deriv.transE (Deriv.congQAdd h_term1 h_term2)
          (chrAddMulSuccNatD (.succ r) (.app (.app (.app tmJetMul Dg) Psr) n)))))

/-- Power rule for `(tmJetDrop0 g)^{succ k}`, proved by `Deriv.ind` on `k`:
    `∀ k ∀ n. D((G₊)^{succ k})(n) ≈ (k + 1) * (Dg · (G₊)^k)(n)`. -/
def chrPowDerivD {Γ as : List Ty} {Δ : Ctx Γ as} (g : Tm Γ JetTy) :
    Deriv Δ (.all .nat (.all .nat
      (Formula.qeqv
        (.app (.app tmJetDeriv
          (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk)) (.succ (.var (.there .here)))))
          (.var .here))
        (.qmul (.qnat (.succ (.var (.there .here))))
          (.app (.app (.app tmJetMul (.app tmJetDeriv g.wk.wk))
            (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk)) (.var (.there .here))))
            (.var .here)))))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI ?_
    exact chrPowDerivBaseT g
  · refine Deriv.allI (Deriv.impI (Deriv.allI ?_))
    deriv_norm
    exact chrPowDerivStepT g Deriv.ax

/-- Term form of `chrPowDerivD`. -/
def chrPowDerivT {Γ as : List Ty} {Δ : Ctx Γ as} (g : Tm Γ JetTy) (k n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv
      (.app (.app tmJetDeriv (.app (.app tmJetPow (.app tmJetDrop0 g)) (.succ k))) n)
      (.qmul (.qnat (.succ k))
        (.app (.app (.app tmJetMul (.app tmJetDeriv g))
          (.app (.app tmJetPow (.app tmJetDrop0 g)) k)) n))) := by
  have h := Deriv.allE n (Deriv.allE k (chrPowDerivD (Δ := Δ) g))
  deriv_norm at h
  exact h

/-- Inductive step of `chrJetMulPartialPrefixZeroR`. -/
def chrJetMulPartialPrefixZeroStepT {Γ as : List Ty} {Δ : Ctx (.nat :: .nat :: Γ) as}
    (a u : Tm Γ JetTy) (n : Tm Γ .nat)
    (hu : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) n.wk.wk.wk.wk)
        (Formula.qeqv (.app u.wk.wk.wk.wk (.var (.there .here))) (.qnat .zero))))))
    (h_ih : Deriv Δ (.all .nat
      (.imp (.eq (.add (.var (.there (.there .here))) (.var .here)) (.succ n.wk.wk.wk))
        (.eq (jetMulPartialAt a.wk.wk.wk u.wk.wk.wk n.wk.wk.wk (.var (.there (.there .here))))
             (.qnat .zero)))))
    (h_succ : Deriv Δ (.eq (.add (.succ (.var (.there .here))) (.var .here)) (.succ n.wk.wk))) :
    Deriv Δ (.eq (jetMulPartialAt a.wk.wk u.wk.wk n.wk.wk (.succ (.var (.there .here))))
                 (.qnat .zero)) := by
  let f : Tm (.nat :: .nat :: Γ) .nat := .var .here
  let t : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  let a₂ : Tm (.nat :: .nat :: Γ) JetTy := a.wk.wk
  let u₂ : Tm (.nat :: .nat :: Γ) JetTy := u.wk.wk
  let n₂ : Tm (.nat :: .nat :: Γ) .nat := n.wk.wk
  have h_succ_tf : Deriv Δ (.eq (.succ (.add t f)) (.succ n₂)) :=
    Deriv.transE (Deriv.symmE (succPlusT t f)) h_succ
  have h_tf : Deriv Δ (.eq (.add t f) n₂) :=
    Deriv.impE (Deriv.succInj (.add t f) n₂) h_succ_tf
  have h_t_sf : Deriv Δ (.eq (.add t (.succ f)) (.succ n₂)) :=
    Deriv.transE (Deriv.convAddSucc t f) h_succ_tf
  have h_ih_f := Deriv.allE (.succ f) h_ih
  deriv_norm at h_ih_f
  have h_part : Deriv Δ (.eq (jetMulPartialAt a₂ u₂ n₂ t) (.qnat .zero)) :=
    Deriv.impE h_ih_f h_t_sf
  have h_sub : Deriv Δ (.eq (tmNatSub n₂ t) f) :=
    tmNatSubAddCancelT h_tf
  have h_ft : Deriv Δ (.eq (.add f t) n₂) :=
    Deriv.transE (plusCommT f t) h_tf
  have hu_inst := Deriv.allE t (Deriv.allE f hu)
  deriv_norm at hu_inst
  have hu_f : Deriv Δ (Formula.qeqv (.app u₂ f) (.qnat .zero)) :=
    Deriv.impE hu_inst h_ft
  have hu_sub : Deriv Δ (Formula.qeqv (.app u₂ (tmNatSub n₂ t)) (.qnat .zero)) :=
    Deriv.qeqvTrans (Deriv.qeqvOfEq (Deriv.congArg u₂ h_sub)) hu_f
  have h_term : Deriv Δ (.eq (.qmul (.app a₂ t) (.app u₂ (tmNatSub n₂ t))) (.qnat .zero)) :=
    Deriv.transE (Deriv.qmulV (Deriv.qeqvRefl (.app a₂ t)) hu_sub)
      (Deriv.qlaw (.mulZero (.app a₂ t)))
  exact Deriv.transE (jetMulPartial_succD a₂ u₂ n₂ t)
    (Deriv.transE (Deriv.congQAdd h_part h_term) (Deriv.qlaw (.normNat .zero)))

/-- Partial-sum prefix vanishing for Cauchy product, proved by `Deriv.ind` on `t`. -/
def chrJetMulPartialPrefixZeroR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.imp
      (.all .nat (.all .nat
        (.imp (.eq (.add (.var (.there .here)) (.var .here)) n.wk.wk)
          (Formula.qeqv (.app u.wk.wk (.var (.there .here))) (.qnat .zero)))))
      (.all .nat (.all .nat
        (.imp (.eq (.add (.var (.there .here)) (.var .here)) (.succ n.wk.wk))
          (.eq (jetMulPartialAt a.wk.wk u.wk.wk n.wk.wk (.var (.there .here))) (.qnat .zero)))))) := by
  refine Deriv.impI (Deriv.ind ?_ ?_)
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    exact jetMulPartial_zeroD a.wk u.wk n.wk
  · refine Deriv.allI (Deriv.impI ?_)
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrJetMulPartialPrefixZeroStepT a u n
      (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax

/-- `(a · u)(n) = 0` when `u(j) ≈ 0` for all `j ≤ n`. -/
def chrJetMulPrefixZeroR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u : Tm Γ JetTy) (n : Tm Γ .nat)
    (hu : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) n.wk.wk)
        (Formula.qeqv (.app u.wk.wk (.var (.there .here))) (.qnat .zero)))))) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) u) n) (.qnat .zero)) := by
  have h_all := Deriv.impE (chrJetMulPartialPrefixZeroR a u n) hu
  have h_inst := Deriv.allE .zero (Deriv.allE (.succ n) h_all)
  deriv_norm at h_inst
  exact Deriv.transE (tmJetMul_appD a u n) (Deriv.impE h_inst (Deriv.convAddZero (.succ n)))

/-- Inductive step of `chrJetMulPartialPrefixCongR`. -/
def chrJetMulPartialPrefixCongStepT {Γ as : List Ty} {Δ : Ctx (.nat :: .nat :: Γ) as}
    (a u v : Tm Γ JetTy) (n : Tm Γ .nat)
    (huv : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) n.wk.wk.wk.wk)
        (Formula.qeqv (.app u.wk.wk.wk.wk (.var (.there .here)))
                      (.app v.wk.wk.wk.wk (.var (.there .here))))))))
    (h_ih : Deriv Δ (.all .nat
      (.imp (.eq (.add (.var (.there (.there .here))) (.var .here)) (.succ n.wk.wk.wk))
        (.eq (jetMulPartialAt a.wk.wk.wk u.wk.wk.wk n.wk.wk.wk (.var (.there (.there .here))))
             (jetMulPartialAt a.wk.wk.wk v.wk.wk.wk n.wk.wk.wk (.var (.there (.there .here))))))))
    (h_succ : Deriv Δ (.eq (.add (.succ (.var (.there .here))) (.var .here)) (.succ n.wk.wk))) :
    Deriv Δ (.eq (jetMulPartialAt a.wk.wk u.wk.wk n.wk.wk (.succ (.var (.there .here))))
                 (jetMulPartialAt a.wk.wk v.wk.wk n.wk.wk (.succ (.var (.there .here))))) := by
  let f : Tm (.nat :: .nat :: Γ) .nat := .var .here
  let t : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
  let a₂ : Tm (.nat :: .nat :: Γ) JetTy := a.wk.wk
  let u₂ : Tm (.nat :: .nat :: Γ) JetTy := u.wk.wk
  let v₂ : Tm (.nat :: .nat :: Γ) JetTy := v.wk.wk
  let n₂ : Tm (.nat :: .nat :: Γ) .nat := n.wk.wk
  have h_succ_tf : Deriv Δ (.eq (.succ (.add t f)) (.succ n₂)) :=
    Deriv.transE (Deriv.symmE (succPlusT t f)) h_succ
  have h_tf : Deriv Δ (.eq (.add t f) n₂) :=
    Deriv.impE (Deriv.succInj (.add t f) n₂) h_succ_tf
  have h_t_sf : Deriv Δ (.eq (.add t (.succ f)) (.succ n₂)) :=
    Deriv.transE (Deriv.convAddSucc t f) h_succ_tf
  have h_ih_f := Deriv.allE (.succ f) h_ih
  deriv_norm at h_ih_f
  have h_part : Deriv Δ (.eq (jetMulPartialAt a₂ u₂ n₂ t) (jetMulPartialAt a₂ v₂ n₂ t)) :=
    Deriv.impE h_ih_f h_t_sf
  have h_sub : Deriv Δ (.eq (tmNatSub n₂ t) f) :=
    tmNatSubAddCancelT h_tf
  have h_ft : Deriv Δ (.eq (.add f t) n₂) :=
    Deriv.transE (plusCommT f t) h_tf
  have huv_inst := Deriv.allE t (Deriv.allE f huv)
  deriv_norm at huv_inst
  have huv_f : Deriv Δ (Formula.qeqv (.app u₂ f) (.app v₂ f)) :=
    Deriv.impE huv_inst h_ft
  have huv_sub : Deriv Δ (Formula.qeqv (.app u₂ (tmNatSub n₂ t)) (.app v₂ (tmNatSub n₂ t))) :=
    Deriv.qeqvTrans (Deriv.qeqvOfEq (Deriv.congArg u₂ h_sub))
      (Deriv.qeqvTrans huv_f (Deriv.qeqvOfEq (Deriv.symmE (Deriv.congArg v₂ h_sub))))
  exact Deriv.transE (jetMulPartial_succD a₂ u₂ n₂ t)
    (Deriv.transE
      (Deriv.congQAdd h_part (Deriv.qmulV (Deriv.qeqvRefl (.app a₂ t)) huv_sub))
      (Deriv.symmE (jetMulPartial_succD a₂ v₂ n₂ t)))

/-- Partial-sum prefix congruence (`≈` in right argument) for Cauchy product, by `Deriv.ind` on `t`. -/
def chrJetMulPartialPrefixCongR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u v : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.imp
      (.all .nat (.all .nat
        (.imp (.eq (.add (.var (.there .here)) (.var .here)) n.wk.wk)
          (Formula.qeqv (.app u.wk.wk (.var (.there .here)))
                        (.app v.wk.wk (.var (.there .here)))))))
      (.all .nat (.all .nat
        (.imp (.eq (.add (.var (.there .here)) (.var .here)) (.succ n.wk.wk))
          (.eq (jetMulPartialAt a.wk.wk u.wk.wk n.wk.wk (.var (.there .here)))
               (jetMulPartialAt a.wk.wk v.wk.wk n.wk.wk (.var (.there .here)))))))) := by
  refine Deriv.impI (Deriv.ind ?_ ?_)
  · deriv_norm
    refine Deriv.allI (Deriv.impI ?_)
    exact Deriv.transE (jetMulPartial_zeroD a.wk u.wk n.wk)
      (Deriv.symmE (jetMulPartial_zeroD a.wk v.wk n.wk))
  · refine Deriv.allI (Deriv.impI ?_)
    refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrJetMulPartialPrefixCongStepT a u v n
      (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax

/-- `(a · u)(n) = (a · v)(n)` when `u(j) ≈ v(j)` for all `j ≤ n`. -/
def chrJetMulPrefixCongR {Γ as : List Ty} {Δ : Ctx Γ as}
    (a u v : Tm Γ JetTy) (n : Tm Γ .nat)
    (huv : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) n.wk.wk)
        (Formula.qeqv (.app u.wk.wk (.var (.there .here)))
                      (.app v.wk.wk (.var (.there .here)))))))) :
    Deriv Δ (.eq (.app (.app (.app tmJetMul a) u) n) (.app (.app (.app tmJetMul a) v) n)) := by
  have h_all := Deriv.impE (chrJetMulPartialPrefixCongR a u v n) huv
  have h_inst := Deriv.allE .zero (Deriv.allE (.succ n) h_all)
  deriv_norm at h_inst
  exact Deriv.transE (tmJetMul_appD a u n)
    (Deriv.transE (Deriv.impE h_inst (Deriv.convAddZero (.succ n)))
      (Deriv.symmE (tmJetMul_appD a v n)))

/-- Inner step of `chrPowVanishSuccStepT` in context `e :: j :: d :: m :: k :: Γ`. -/
def chrPowVanishPrefixInnerT {Γ as : List Ty}
    {Δ : Ctx (.nat :: .nat :: .nat :: .nat :: .nat :: Γ) as}
    (g : Tm Γ JetTy)
    (h_ih_wk : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there (.there (.there .here))))))))
        (.eq (.app (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk.wk.wk.wk.wk.wk))
                (.var (.there (.there (.there (.there (.there (.there .here)))))))) (.var (.there .here)))
             (.qnat .zero))))))
    (h_mk_wk : Deriv Δ (.eq
      (.add (.var (.there (.there (.there .here)))) (.succ (.var (.there (.there .here)))))
      (.var (.there (.there (.there (.there .here)))))))
    (h_je : Deriv Δ (.eq (.add (.var (.there .here)) (.var .here))
      (.var (.there (.there (.there .here)))))) :
    Deriv Δ (Formula.qeqv
      (.app (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk.wk.wk.wk))
        (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))
      (.qnat .zero)) := by
  let e : Tm (.nat :: .nat :: .nat :: .nat :: .nat :: Γ) .nat := .var .here
  let j : Tm (.nat :: .nat :: .nat :: .nat :: .nat :: Γ) .nat := .var (.there .here)
  let dw : Tm (.nat :: .nat :: .nat :: .nat :: .nat :: Γ) .nat := .var (.there (.there .here))
  have h_jk := leLtTransAddT h_je h_mk_wk
  have h_inst := Deriv.allE (.add e dw) (Deriv.allE j h_ih_wk)
  deriv_norm at h_inst
  exact Deriv.qeqvOfEq (Deriv.impE h_inst h_jk)

/-- Inner step of `chrPowVanishD`: from `∀ m ∀ d. m + succ d = k → P_k(m) = 0` and
    `succ m + succ d = succ k`, derive `P_{succ k}(succ m) = 0`. -/
def chrPowVanishSuccStepT {Γ as : List Ty} {Δ : Ctx (.nat :: .nat :: .nat :: Γ) as}
    (g : Tm Γ JetTy)
    (h_ih_k : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here)))
              (.var (.there (.there (.there (.there .here))))))
        (.eq (.app (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk.wk.wk.wk))
                (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))
             (.qnat .zero))))))
    (h_succ : Deriv Δ (.eq
      (.add (.succ (.var (.there .here))) (.succ (.var .here)))
      (.succ (.var (.there (.there .here)))))) :
    Deriv Δ (.eq
      (.app (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk.wk))
              (.succ (.var (.there (.there .here)))))
            (.succ (.var (.there .here))))
      (.qnat .zero)) := by
  let d : Tm (.nat :: .nat :: .nat :: Γ) .nat := .var .here
  let m : Tm (.nat :: .nat :: .nat :: Γ) .nat := .var (.there .here)
  let k : Tm (.nat :: .nat :: .nat :: Γ) .nat := .var (.there (.there .here))
  let g₃ : Tm (.nat :: .nat :: .nat :: Γ) JetTy := g.wk.wk.wk
  let G : Tm (.nat :: .nat :: .nat :: Γ) JetTy := .app tmJetDrop0 g₃
  let Pk : Tm (.nat :: .nat :: .nat :: Γ) JetTy := .app (.app tmJetPow G) k
  have h_mk : Deriv Δ (.eq (.add m (.succ d)) k) :=
    succAddSuccInjT h_succ
  have h_prefix : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) (.var (.there (.there (.there .here)))))
        (Formula.qeqv
          (.app (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk.wk.wk.wk))
            (.var (.there (.there (.there (.there .here)))))) (.var (.there .here)))
          (.qnat .zero))))) := by
    refine Deriv.impE (Deriv.impE ?_ h_ih_k) h_mk
    refine Deriv.impI (Deriv.impI ?_)
    refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
    deriv_norm
    exact chrPowVanishPrefixInnerT g (Deriv.wk (Deriv.wk Deriv.ax)) (Deriv.wk Deriv.ax) Deriv.ax
  have h_head : Deriv Δ (.eq (.qmul (.app G .zero) (.app Pk (.succ m))) (.qnat .zero)) :=
    Deriv.transE
      (Deriv.congQMul (chrDrop0_zeroD g₃) (Deriv.eqRefl (.app Pk (.succ m))))
      (prdQmulZeroL (.app Pk (.succ m)))
  have h_tail : Deriv Δ (.eq (.app (.app (.app tmJetMul (chrJetShift G)) Pk) m) (.qnat .zero)) :=
    chrJetMulPrefixZeroR (chrJetShift G) Pk m h_prefix
  exact Deriv.transE (Deriv.congFun (chrPow_succD G k) (.succ m))
    (Deriv.transE (chrJetMulLeftSuccT G Pk m)
      (Deriv.transE (Deriv.congQAdd h_head h_tail) (Deriv.qlaw (.normNat .zero))))

/-- Vanishing of `(G₊)^k` below degree `k`, proved by `Deriv.ind` on `k`:
    `∀ k ∀ m ∀ d. m + succ d = k → ((G₊)^k)(m) = 0`. -/
def chrPowVanishD {Γ as : List Ty} {Δ : Ctx Γ as} (g : Tm Γ JetTy) :
    Deriv Δ (.all .nat (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here))) (.var (.there (.there .here))))
        (.eq (.app (.app (.app tmJetPow (.app tmJetDrop0 g.wk.wk.wk))
                (.var (.there (.there .here)))) (.var (.there .here)))
             (.qnat .zero)))))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
    let d : Tm (.nat :: .nat :: Γ) .nat := .var .here
    let m : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
    exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.add m d))
      (Deriv.transE (Deriv.symmE (Deriv.convAddSucc m d)) Deriv.ax))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    refine Deriv.ind ?_ ?_
    · deriv_norm
      refine Deriv.allI (Deriv.impI ?_)
      let k : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
      let g₂ : Tm (.nat :: .nat :: Γ) JetTy := g.wk.wk
      let G : Tm (.nat :: .nat :: Γ) JetTy := .app tmJetDrop0 g₂
      let Pk : Tm (.nat :: .nat :: Γ) JetTy := .app (.app tmJetPow G) k
      exact Deriv.transE (Deriv.congFun (chrPow_succD G k) .zero)
        (Deriv.transE (chrJetMulZeroD G Pk)
          (Deriv.transE
            (Deriv.congQMul (chrDrop0_zeroD g₂) (Deriv.eqRefl (.app Pk .zero)))
            (prdQmulZeroL (.app Pk .zero))))
    · refine Deriv.allI (Deriv.impI ?_)
      refine Deriv.allI (Deriv.impI ?_)
      deriv_norm
      exact chrPowVanishSuccStepT g (Deriv.wk (Deriv.wk Deriv.ax)) Deriv.ax

/-- Term form of `chrPowVanishD`: from `m + succ d = k`, derive `((G₊)^k)(m) = 0`. -/
def chrPowVanishT {Γ as : List Ty} {Δ : Ctx Γ as} (g : Tm Γ JetTy) {k m d : Tm Γ .nat}
    (h : Deriv Δ (.eq (.add m (.succ d)) k)) :
    Deriv Δ (.eq (.app (.app (.app tmJetPow (.app tmJetDrop0 g)) k) m) (.qnat .zero)) := by
  have h_all := Deriv.allE d (Deriv.allE m (Deriv.allE k (chrPowVanishD (Δ := Δ) g)))
  deriv_norm at h_all
  exact Deriv.impE h_all h

/-- Congruence in the upper-limit argument `K` of `chrCompPartialAt F g m K`. -/
def chrCongCompPartialT {Γ as : List Ty} {Δ : Ctx Γ as}
    (F g : Tm Γ JetTy) (m : Tm Γ .nat) {K₁ K₂ : Tm Γ .nat}
    (h : Deriv Δ (.eq K₁ K₂)) :
    Deriv Δ (.eq (chrCompPartialAt F g m K₁) (chrCompPartialAt F g m K₂)) := by
  have hc := Deriv.congTm (chrCompPartialAt F.wk g.wk m.wk (.var .here)) h
  deriv_norm at hc
  exact hc

/-- Inductive step of `chrCompPartialExtendD`. -/
def chrCompPartialExtendStepT {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as}
    (F g : Tm Γ JetTy) (m : Tm Γ .nat)
    (h_ih : Deriv Δ (Formula.qeqv
      (chrCompPartialAt F.wk g.wk m.wk (.add (.succ m.wk) (.var .here)))
      (chrCompPartialAt F.wk g.wk m.wk (.succ m.wk)))) :
    Deriv Δ (Formula.qeqv
      (chrCompPartialAt F.wk g.wk m.wk (.add (.succ m.wk) (.succ (.var .here))))
      (chrCompPartialAt F.wk g.wk m.wk (.succ m.wk))) := by
  let e : Tm (.nat :: Γ) .nat := .var .here
  let F₁ : Tm (.nat :: Γ) JetTy := F.wk
  let g₁ : Tm (.nat :: Γ) JetTy := g.wk
  let m₁ : Tm (.nat :: Γ) .nat := m.wk
  let K : Tm (.nat :: Γ) .nat := .add (.succ m₁) e
  have h_step : Deriv Δ (.eq (chrCompPartialAt F₁ g₁ m₁ (.add (.succ m₁) (.succ e)))
      (.qadd (chrCompPartialAt F₁ g₁ m₁ K)
        (.qmul (.app F₁ K) (.app (.app (.app tmJetPow (.app tmJetDrop0 g₁)) K) m₁)))) :=
    Deriv.transE
      (chrCongCompPartialT F₁ g₁ m₁ (Deriv.convAddSucc (.succ m₁) e))
      (chrCompPartial_succD F₁ g₁ m₁ K)
  have h_lt : Deriv Δ (.eq (.add m₁ (.succ e)) K) :=
    Deriv.transE (Deriv.convAddSucc m₁ e) (Deriv.symmE (succPlusT m₁ e))
  have h_van : Deriv Δ (.eq (.qmul (.app F₁ K)
      (.app (.app (.app tmJetPow (.app tmJetDrop0 g₁)) K) m₁)) (.qnat .zero)) :=
    Deriv.transE
      (Deriv.congQMul (Deriv.eqRefl (.app F₁ K)) (chrPowVanishT g₁ h_lt))
      (Deriv.qlaw (.mulZero (.app F₁ K)))
  exact Deriv.qeqvTrans
    (Deriv.qeqvOfEqNorm (Deriv.transE h_step (Deriv.congQAdd (Deriv.eqRefl _) h_van)))
    h_ih

/-- Extending the upper limit of `chrCompPartialAt F g m` past `succ m` leaves its value `≈` unchanged. -/
def chrCompPartialExtendD {Γ as : List Ty} {Δ : Ctx Γ as}
    (F g : Tm Γ JetTy) (m : Tm Γ .nat) :
    Deriv Δ (.all .nat
      (Formula.qeqv
        (chrCompPartialAt F.wk g.wk m.wk (.add (.succ m.wk) (.var .here)))
        (chrCompPartialAt F.wk g.wk m.wk (.succ m.wk)))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    exact Deriv.qeqvOfEq (chrCongCompPartialT F g m (Deriv.convAddZero (.succ m)))
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrCompPartialExtendStepT F g m Deriv.ax

/-- From `m + e = n`, derive `chrCompPartialAt F g m (succ n) ≈ (F ∘ g)(m)`. -/
def chrCompPartialPrefixT {Γ as : List Ty} {Δ : Ctx Γ as}
    (F g : Tm Γ JetTy) {n m e : Tm Γ .nat}
    (h_me : Deriv Δ (.eq (.add m e) n)) :
    Deriv Δ (Formula.qeqv (chrCompPartialAt F g m (.succ n))
      (.app (.app (.app tmJetComp F) g) m)) := by
  have h_add : Deriv Δ (.eq (.succ n) (.add (.succ m) e)) :=
    Deriv.transE (Deriv.congSucc (Deriv.symmE h_me)) (Deriv.symmE (succPlusT m e))
  have h_cong : Deriv Δ (.eq (chrCompPartialAt F g m (.succ n))
      (chrCompPartialAt F g m (.add (.succ m) e))) :=
    chrCongCompPartialT F g m h_add
  have h_ext := Deriv.allE e (chrCompPartialExtendD (Δ := Δ) F g m)
  deriv_norm at h_ext
  exact Deriv.qeqvTrans (Deriv.qeqvOfEq h_cong)
    (Deriv.qeqvTrans h_ext (Deriv.qeqvOfEq (Deriv.symmE (chrComp_appD F g m))))

/-- The partial composition `m ↦ chrCompPartialAt F g m K` as a jet term. -/
def chrCompPartialJet {Γ : List Ty} (F g : Tm Γ JetTy) (K : Tm Γ .nat) : Tm Γ JetTy :=
  .lam (chrCompPartialAt (F.wk (σ := .nat)) (g.wk (σ := .nat)) (.var .here) (K.wk (σ := .nat)))

@[derivNorm] theorem chrCompPartialJet_rename {Γ Δ : List Ty}
    (F g : Tm Γ JetTy) (K : Tm Γ .nat) (ρ : Ren Γ Δ) :
    (chrCompPartialJet F g K).rename ρ = chrCompPartialJet (F.rename ρ) (g.rename ρ) (K.rename ρ) := by
  simp only [chrCompPartialJet, Tm.rename, Tm.wk, Tm.rename_rename, chrCompPartialAt_rename]
  rfl

@[derivNorm] theorem chrCompPartialJet_subst {Γ Δ : List Ty}
    (F g : Tm Γ JetTy) (K : Tm Γ .nat) (s : Sub Γ Δ) :
    (chrCompPartialJet F g K).subst s = chrCompPartialJet (F.subst s) (g.subst s) (K.subst s) := by
  simp only [chrCompPartialJet, Tm.subst, Tm.wk_subst_ext, chrCompPartialAt_subst]
  rfl

/-- `(chrCompPartialJet F g K)(m) = chrCompPartialAt F g m K` inside `Deriv`. -/
def chrCompPartialJet_appD {Γ as : List Ty} {Δ : Ctx Γ as}
    (F g : Tm Γ JetTy) (K m : Tm Γ .nat) :
    Deriv Δ (.eq (.app (chrCompPartialJet F g K) m) (chrCompPartialAt F g m K)) := by
  have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
    (chrCompPartialAt (F.wk (σ := .nat)) (g.wk (σ := .nat)) (.var .here) (K.wk (σ := .nat))) m
  deriv_norm at hb
  exact hb

/-- `∀ j. (chrCompPartialJet Df g (succ K))(j) ≈ (chrCompPartialJet Df g K)(j) + Df(K) * ((G₊)^K)(j)`. -/
def chrCompPartialJetSuccLinD {Γ as : List Ty} {Δ : Ctx Γ as}
    (f g : Tm Γ JetTy) (K : Tm Γ .nat) :
    Deriv Δ (.all .nat
      (Formula.qeqv
        (.app (chrCompPartialJet (.app tmJetDeriv f) g (.succ K)).wk (.var .here))
        (.qadd (.app (chrCompPartialJet (.app tmJetDeriv f) g K).wk (.var .here))
               (.qmul (Tm.app (.app tmJetDeriv f) K).wk
                 (.app (Tm.app (.app tmJetPow (.app tmJetDrop0 g)) K).wk (.var .here)))))) := by
  refine Deriv.allI ?_
  deriv_norm
  let j : Tm (.nat :: Γ) .nat := .var .here
  let Dfw : Tm (.nat :: Γ) JetTy := .app tmJetDeriv f.wk
  let gw : Tm (.nat :: Γ) JetTy := g.wk
  let Kw : Tm (.nat :: Γ) .nat := K.wk
  exact Deriv.qeqvOfEq
    (Deriv.transE (chrCompPartialJet_appD Dfw gw (.succ Kw) j)
      (Deriv.transE (chrCompPartial_succD Dfw gw j Kw)
        (Deriv.congQAdd
          (Deriv.symmE (chrCompPartialJet_appD Dfw gw Kw j))
          (Deriv.eqRefl _))))

/-- Inductive step of `chrChainPartialD`. -/
def chrChainPartialStepT {Γ as : List Ty} {Δ : Ctx (.nat :: Γ) as}
    (f g : Tm Γ JetTy) (n : Tm Γ .nat)
    (h_ih : Deriv Δ (.eq
      (.qmul (.qnat (.succ n.wk))
             (chrCompPartialAt f.wk g.wk (.succ n.wk) (.succ (.var .here))))
      (.app (.app (.app tmJetMul (.app tmJetDeriv g.wk))
        (chrCompPartialJet (.app tmJetDeriv f.wk) g.wk (.var .here))) n.wk))) :
    Deriv Δ (.eq
      (.qmul (.qnat (.succ n.wk))
             (chrCompPartialAt f.wk g.wk (.succ n.wk) (.succ (.succ (.var .here)))))
      (.app (.app (.app tmJetMul (.app tmJetDeriv g.wk))
        (chrCompPartialJet (.app tmJetDeriv f.wk) g.wk (.succ (.var .here)))) n.wk)) := by
  let K : Tm (.nat :: Γ) .nat := .var .here
  let f₁ : Tm (.nat :: Γ) JetTy := f.wk
  let g₁ : Tm (.nat :: Γ) JetTy := g.wk
  let n₁ : Tm (.nat :: Γ) .nat := n.wk
  let G : Tm (.nat :: Γ) JetTy := .app tmJetDrop0 g₁
  let Df : Tm (.nat :: Γ) JetTy := .app tmJetDeriv f₁
  let Dg : Tm (.nat :: Γ) JetTy := .app tmJetDeriv g₁
  let PK : Tm (.nat :: Γ) JetTy := .app (.app tmJetPow G) K
  let PS : Tm (.nat :: Γ) JetTy := .app (.app tmJetPow G) (.succ K)
  let CK : Tm (.nat :: Γ) JetTy := chrCompPartialJet Df g₁ K
  let CS : Tm (.nat :: Γ) JetTy := chrCompPartialJet Df g₁ (.succ K)
  have h_lhs_split : Deriv Δ (.eq
      (.qmul (.qnat (.succ n₁)) (chrCompPartialAt f₁ g₁ (.succ n₁) (.succ (.succ K))))
      (.qadd (.qmul (.qnat (.succ n₁)) (chrCompPartialAt f₁ g₁ (.succ n₁) (.succ K)))
             (.qmul (.qnat (.succ n₁)) (.qmul (.app f₁ (.succ K)) (.app PS (.succ n₁)))))) :=
    Deriv.transE
      (Deriv.congQMul (Deriv.eqRefl (.qnat (.succ n₁)))
        (chrCompPartial_succD f₁ g₁ (.succ n₁) (.succ K)))
      (Deriv.convQMulAdd (.qnat (.succ n₁))
        (chrCompPartialAt f₁ g₁ (.succ n₁) (.succ K))
        (.qmul (.app f₁ (.succ K)) (.app PS (.succ n₁))))
  have h_top : Deriv Δ (.eq
      (.qmul (.qnat (.succ n₁)) (.qmul (.app f₁ (.succ K)) (.app PS (.succ n₁))))
      (.qmul (.app Df K) (.app (.app (.app tmJetMul Dg) PK) n₁))) :=
    Deriv.transE
      (prdQmulLeftComm (.qnat (.succ n₁)) (.app f₁ (.succ K)) (.app PS (.succ n₁)))
      (Deriv.transE
        (Deriv.congQMul (Deriv.eqRefl (.app f₁ (.succ K))) (Deriv.symmE (qeJetDerivAppD PS n₁)))
        (Deriv.transE
          (Deriv.qmulV (Deriv.qeqvRefl (.app f₁ (.succ K))) (chrPowDerivT g₁ K n₁))
          (Deriv.transE
            (Deriv.symmE (Deriv.convQMulAssoc (.app f₁ (.succ K)) (.qnat (.succ K))
              (.app (.app (.app tmJetMul Dg) PK) n₁)))
            (Deriv.congQMul
              (Deriv.transE (Deriv.convQMulComm (.app f₁ (.succ K)) (.qnat (.succ K)))
                (Deriv.symmE (qeJetDerivAppD f₁ K)))
              (Deriv.eqRefl _)))))
  have h_lhs : Deriv Δ (.eq
      (.qmul (.qnat (.succ n₁)) (chrCompPartialAt f₁ g₁ (.succ n₁) (.succ (.succ K))))
      (.qadd (.app (.app (.app tmJetMul Dg) CK) n₁)
             (.qmul (.app Df K) (.app (.app (.app tmJetMul Dg) PK) n₁)))) :=
    Deriv.transE h_lhs_split (Deriv.congQAdd h_ih h_top)
  have h_rhs : Deriv Δ (.eq
      (.app (.app (.app tmJetMul Dg) CS) n₁)
      (.qadd (.app (.app (.app tmJetMul Dg) CK) n₁)
             (.qmul (.app Df K) (.app (.app (.app tmJetMul Dg) PK) n₁)))) :=
    chrJetMulLinR Dg CS CK PK (.app Df K) n₁ (chrCompPartialJetSuccLinD (Δ := Δ) f₁ g₁ K)
  exact Deriv.transE h_lhs (Deriv.symmE h_rhs)

/-- Partial chain rule identity, proved by `Deriv.ind` on `K`:
    `∀ K. (n + 1) * chrCompPartialAt f g (n + 1) (K + 1) = (Dg · chrCompPartialJet Df g K)(n)`. -/
def chrChainPartialD {Γ as : List Ty} {Δ : Ctx Γ as}
    (f g : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.all .nat
      (.eq (.qmul (.qnat (.succ n.wk))
             (chrCompPartialAt f.wk g.wk (.succ n.wk) (.succ (.var .here))))
           (.app (.app (.app tmJetMul (.app tmJetDeriv g.wk))
             (chrCompPartialJet (.app tmJetDeriv f.wk) g.wk (.var .here))) n.wk))) := by
  refine Deriv.ind ?_ ?_
  · deriv_norm
    let G : Tm Γ JetTy := .app tmJetDrop0 g
    let Df : Tm Γ JetTy := .app tmJetDeriv f
    let Dg : Tm Γ JetTy := .app tmJetDeriv g
    have h_p0_sn : Deriv Δ (.eq (.app (.app (.app tmJetPow G) .zero) (.succ n)) (.qnat .zero)) :=
      Deriv.transE (Deriv.congFun (chrPow_zeroD G) (.succ n)) (chrConstOneSuccD n)
    have h_comp1 : Deriv Δ (.eq (chrCompPartialAt f g (.succ n) (.succ .zero)) (.qnat .zero)) :=
      Deriv.transE (chrCompPartial_succD f g (.succ n) .zero)
        (Deriv.transE
          (Deriv.congQAdd (chrCompPartial_zeroD f g (.succ n))
            (Deriv.transE
              (Deriv.congQMul (Deriv.eqRefl (.app f .zero)) h_p0_sn)
              (Deriv.qlaw (.mulZero (.app f .zero)))))
          (Deriv.qlaw (.normNat .zero)))
    have h_lhs : Deriv Δ (.eq
        (.qmul (.qnat (.succ n)) (chrCompPartialAt f g (.succ n) (.succ .zero)))
        (.qnat .zero)) :=
      Deriv.transE (Deriv.congQMul (Deriv.eqRefl (.qnat (.succ n))) h_comp1)
        (Deriv.qlaw (.mulZero (.qnat (.succ n))))
    have h_jet0 : Deriv Δ (.all .nat
        (Formula.qeqv
          (.app (chrCompPartialJet Df g .zero).wk (.var .here))
          (.qnat .zero))) := by
      dsimp only [Df]
      refine Deriv.allI ?_
      deriv_norm
      let j : Tm (.nat :: Γ) .nat := .var .here
      exact Deriv.qeqvOfEq
        (Deriv.transE (chrCompPartialJet_appD (.app tmJetDeriv f.wk) g.wk .zero j)
          (chrCompPartial_zeroD (.app tmJetDeriv f.wk) g.wk j))
    have h_rhs : Deriv Δ (.eq
        (.app (.app (.app tmJetMul Dg) (chrCompPartialJet Df g .zero)) n)
        (.qnat .zero)) :=
      chrJetMulZeroR Dg (chrCompPartialJet Df g .zero) n h_jet0
    exact Deriv.transE h_lhs (Deriv.symmE h_rhs)
  · refine Deriv.allI (Deriv.impI ?_)
    deriv_norm
    exact chrChainPartialStepT f g n Deriv.ax

/-- **The chain rule**, at index `n`, for every pair of jets:
`D(F ∘ G)(n) ≈ (DG · ((DF) ∘ G))(n)`. -/
def chainRuleAtD {Γ as : List Ty} {Δ : Ctx Γ as} (f g : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv (.app (.app tmJetDeriv (.app (.app tmJetComp f) g)) n)
      (.app (.app (.app tmJetMul (.app tmJetDeriv g)) (.app (.app tmJetComp (.app tmJetDeriv f)) g)) n)) := by
  let Df : Tm Γ JetTy := .app tmJetDeriv f
  let Dg : Tm Γ JetTy := .app tmJetDeriv g
  let Csn : Tm Γ JetTy := chrCompPartialJet Df g (.succ n)
  have h_lhs : Deriv Δ (.eq (.app (.app tmJetDeriv (.app (.app tmJetComp f) g)) n)
      (.qmul (.qnat (.succ n)) (chrCompPartialAt f g (.succ n) (.succ (.succ n))))) :=
    Deriv.transE (qeJetDerivAppD (.app (.app tmJetComp f) g) n)
      (Deriv.congQMul (Deriv.eqRefl (.qnat (.succ n))) (chrComp_appD f g (.succ n)))
  have h_chain := Deriv.allE (.succ n) (chrChainPartialD (Δ := Δ) f g n)
  deriv_norm at h_chain
  have h_prefix : Deriv Δ (.all .nat (.all .nat
      (.imp (.eq (.add (.var (.there .here)) (.var .here)) n.wk.wk)
        (Formula.qeqv
          (.app Csn.wk.wk (.var (.there .here)))
          (.app (Tm.app (.app tmJetComp Df) g).wk.wk (.var (.there .here))))))) := by
    dsimp only [Csn, Df]
    refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
    deriv_norm
    let e : Tm (.nat :: .nat :: Γ) .nat := .var .here
    let m : Tm (.nat :: .nat :: Γ) .nat := .var (.there .here)
    let Df₂ : Tm (.nat :: .nat :: Γ) JetTy := .app tmJetDeriv f.wk.wk
    let g₂ : Tm (.nat :: .nat :: Γ) JetTy := g.wk.wk
    let n₂ : Tm (.nat :: .nat :: Γ) .nat := n.wk.wk
    exact Deriv.qeqvTrans
      (Deriv.qeqvOfEq (chrCompPartialJet_appD Df₂ g₂ (.succ n₂) m))
      (chrCompPartialPrefixT Df₂ g₂ (n := n₂) (m := m) (e := e) Deriv.ax)
  have h_rhs : Deriv Δ (.eq
      (.app (.app (.app tmJetMul Dg) Csn) n)
      (.app (.app (.app tmJetMul Dg) (.app (.app tmJetComp Df) g)) n)) :=
    chrJetMulPrefixCongR Dg Csn (.app (.app tmJetComp Df) g) n h_prefix
  exact Deriv.qeqvOfEq (Deriv.transE h_lhs (Deriv.transE h_chain h_rhs))

/-- The two sides, with `f, g, n` the bound variables. -/
abbrev chainRuleLhs : Tm [.nat, JetTy, JetTy] .rat :=
  .app (.app tmJetDeriv (.app (.app tmJetComp (.var (.there (.there .here)))) (.var (.there .here))))
    (.var .here)

abbrev chainRuleRhs : Tm [.nat, JetTy, JetTy] .rat :=
  .app (.app (.app tmJetMul (.app tmJetDeriv (.var (.there .here))))
    (.app (.app tmJetComp (.app tmJetDeriv (.var (.there (.there .here))))) (.var (.there .here))))
    (.var .here)

/-- `∀f ∀g ∀n. D(f ∘ g)(n) ≈ (Dg · ((Df) ∘ g))(n)`. -/
def chainRuleLawD : Deriv (Ctx.nil (Γ := []))
    (.all JetTy (.all JetTy (.all .nat (Formula.qeqv chainRuleLhs chainRuleRhs)))) :=
  Deriv.allI (Deriv.allI (Deriv.allI (chainRuleAtD _ _ _)))

/-- The round trip: through `soundness`, the law holds as values. -/
theorem chainRuleLaw_val (a b : Nat → Q) (n : Nat) :
    (chainRuleLhs.eval (Env.cons n (Env.cons b (Env.cons a Env.nil)))).val
      = (chainRuleRhs.eval (Env.cons n (Env.cons b (Env.cons a Env.nil)))).val :=
  (MR_qeqv_iff _ _ _ _).mp (soundness chainRuleLawD Env.nil Env.nil realizes_nil a b n)

-- spot check of the statement's value truth at `f = exp, g = sin` and `f = sin, g = exp`
#guard (List.range 5).all fun n ↦
  Q.norm (chainRuleLhs.eval (Env.cons n (Env.cons ((tmSinJet (Γ := [])).eval Env.nil)
      (Env.cons ((tmExpJet (Γ := [])).eval Env.nil) Env.nil))))
    == Q.norm (chainRuleRhs.eval (Env.cons n (Env.cons ((tmSinJet (Γ := [])).eval Env.nil)
      (Env.cons ((tmExpJet (Γ := [])).eval Env.nil) Env.nil))))
#guard (List.range 5).all fun n ↦
  Q.norm (chainRuleLhs.eval (Env.cons n (Env.cons ((tmExpJet (Γ := [])).eval Env.nil)
      (Env.cons ((tmSinJet (Γ := [])).eval Env.nil) Env.nil))))
    == Q.norm (chainRuleRhs.eval (Env.cons n (Env.cons ((tmExpJet (Γ := [])).eval Env.nil)
      (Env.cons ((tmSinJet (Γ := [])).eval Env.nil) Env.nil))))

#print axioms tmJetComp
#print axioms chainRuleLawD
#print axioms chainRuleLaw_val

end HAomega
