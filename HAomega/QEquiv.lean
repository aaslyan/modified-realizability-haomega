/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ClosedCalculus

/-!
# Value equality `≈` on `rat`, and the first calculus laws inside `Deriv`

`docs/internal/QUESTIONS.md` item 18, option (b).  Structural `=` on the
unnormalized `Q` cannot state `x + 0 = x` (`Q.add_zero_not_id`), so the field
and calculus laws are stated with `s ≈ t` (`Formula.qeqv`): equality of normal
forms, `s + 0 = t + 0`.  It is a *defined* formula, so

* reflexivity, symmetry and transitivity are those of `=` (`qeqvRefl`, …);
* congruence comes from the law schema `QLaw`, entered by the one rule
  `Deriv.qlaw`: an operation applied to `≈` arguments gives a *structurally*
  equal result (`qaddV`, …), after which `=`'s Leibniz rule does the rest;
* its realizer is `unit`: `≈` facts are erased by extraction, like equations.

The laws themselves (exp′ ≈ exp, sin′ ≈ cos, cos′ ≈ −sin, FTC1, FTC2) are
derivations in this file, over the closed System T jet functionals of
`ClosedCalculus.lean`.
-/

namespace HAomega

/-! ## Congruence for `=` under an arbitrary term context -/

/-- `s = t` gives `C[s] = C[t]` for any one-hole term context `C`. -/
def Deriv.congTm {Γ as : List Ty} {Δ : Ctx Γ as} {τ σ : Ty} (C : Tm (τ :: Γ) σ)
    {s t : Tm Γ τ} (h : Deriv Δ (.eq s t)) : Deriv Δ (.eq (C.subst1 s) (C.subst1 t)) := by
  have hs : ∀ u : Tm Γ τ, (Formula.eq ((C.subst1 s).wk) C).subst1 u
      = Formula.eq (C.subst1 s) (C.subst1 u) := by
    intro u
    show Formula.eq (((C.subst1 s).wk).subst1 u) (C.subst1 u) = _
    rw [Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ) (Formula.eq ((C.subst1 s).wk) C) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key

/-! ## The `≈` kit -/

section Kit

variable {Γ as : List Ty} {Δ : Ctx Γ as}

/-- Normal forms of equal terms are equal. -/
def Deriv.qnormCong {s t : Tm Γ .rat} (h : Deriv Δ (.eq s t)) :
    Deriv Δ (.eq s.qnorm t.qnorm) :=
  Deriv.congTm (.qadd (.var .here) (.qnat .zero)) h

def Deriv.qeqvRefl (t : Tm Γ .rat) : Deriv Δ (Formula.qeqv t t) := Deriv.eqRefl _

def Deriv.qeqvSymm {s t : Tm Γ .rat} (h : Deriv Δ (Formula.qeqv s t)) :
    Deriv Δ (Formula.qeqv t s) := Deriv.symmE h

def Deriv.qeqvTrans {s t u : Tm Γ .rat} (h₁ : Deriv Δ (Formula.qeqv s t))
    (h₂ : Deriv Δ (Formula.qeqv t u)) : Deriv Δ (Formula.qeqv s u) := Deriv.transE h₁ h₂

/-- Structural equality implies value equality. -/
def Deriv.qeqvOfEq {s t : Tm Γ .rat} (h : Deriv Δ (.eq s t)) : Deriv Δ (Formula.qeqv s t) :=
  Deriv.qnormCong h

/-- A term is `≈` its normal form; equivalently `t + 0 ≈ t`. -/
def Deriv.qeqvNorm (t : Tm Γ .rat) : Deriv Δ (Formula.qeqv t.qnorm t) :=
  Deriv.qlaw (.normAdd t (.qnat .zero))

/-- `u = v + 0` gives `u ≈ v` — the shape every cancellation law arrives in. -/
def Deriv.qeqvOfEqNorm {u v : Tm Γ .rat} (h : Deriv Δ (.eq u v.qnorm)) :
    Deriv Δ (Formula.qeqv u v) :=
  Deriv.qeqvTrans (Deriv.qeqvOfEq h) (Deriv.qeqvNorm v)

/-- Two normal forms that are `≈` are structurally equal. -/
def Deriv.eqOfQeqv {s t : Tm Γ .rat} (hs : Deriv Δ (.eq s.qnorm s))
    (ht : Deriv Δ (.eq t.qnorm t)) (h : Deriv Δ (Formula.qeqv s t)) : Deriv Δ (.eq s t) :=
  Deriv.transE (Deriv.symmE hs) (Deriv.transE h ht)

/-! ### Operations read only values -/

def Deriv.qaddV {s s' t t' : Tm Γ .rat} (h₁ : Deriv Δ (Formula.qeqv s s'))
    (h₂ : Deriv Δ (Formula.qeqv t t')) : Deriv Δ (.eq (.qadd s t) (.qadd s' t')) :=
  Deriv.impE (Deriv.impE (Deriv.qlaw (.addV s s' t t')) h₁) h₂

def Deriv.qsubV {s s' t t' : Tm Γ .rat} (h₁ : Deriv Δ (Formula.qeqv s s'))
    (h₂ : Deriv Δ (Formula.qeqv t t')) : Deriv Δ (.eq (.qsub s t) (.qsub s' t')) :=
  Deriv.impE (Deriv.impE (Deriv.qlaw (.subV s s' t t')) h₁) h₂

def Deriv.qmulV {s s' t t' : Tm Γ .rat} (h₁ : Deriv Δ (Formula.qeqv s s'))
    (h₂ : Deriv Δ (Formula.qeqv t t')) : Deriv Δ (.eq (.qmul s t) (.qmul s' t')) :=
  Deriv.impE (Deriv.impE (Deriv.qlaw (.mulV s s' t t')) h₁) h₂

def Deriv.qdivV {s s' t t' : Tm Γ .rat} (h₁ : Deriv Δ (Formula.qeqv s s'))
    (h₂ : Deriv Δ (Formula.qeqv t t')) : Deriv Δ (.eq (.qdiv s t) (.qdiv s' t')) :=
  Deriv.impE (Deriv.impE (Deriv.qlaw (.divV s s' t t')) h₁) h₂

def Deriv.qltV {s s' t t' : Tm Γ .rat} (h₁ : Deriv Δ (Formula.qeqv s s'))
    (h₂ : Deriv Δ (Formula.qeqv t t')) : Deriv Δ (.eq (.qlt s t) (.qlt s' t')) :=
  Deriv.impE (Deriv.impE (Deriv.qlaw (.ltV s s' t t')) h₁) h₂

/-! ### The field laws, as `≈` -/

def Deriv.qeqvAddZero (t : Tm Γ .rat) :
    Deriv Δ (Formula.qeqv (.qadd t (.qnat .zero)) t) := Deriv.qeqvNorm t

def Deriv.qeqvMulOne (t : Tm Γ .rat) :
    Deriv Δ (Formula.qeqv (.qmul t (.qnat (.succ .zero))) t) :=
  Deriv.qeqvOfEqNorm (Deriv.qlaw (.mulOne t))

def Deriv.qeqvSubAdd (s t : Tm Γ .rat) :
    Deriv Δ (Formula.qeqv (.qadd (.qsub s t) t) s) :=
  Deriv.qeqvOfEqNorm (Deriv.qlaw (.subAdd s t))

def Deriv.qeqvAddSub (s t : Tm Γ .rat) :
    Deriv Δ (Formula.qeqv (.qsub (.qadd s t) t) s) :=
  Deriv.qeqvOfEqNorm (Deriv.qlaw (.addSub s t))

def Deriv.qeqvDivMul (s : Tm Γ .rat) {c : Tm Γ .rat}
    (hc : Deriv Δ (Formula.qeqv c (.qnat .zero)).neg) :
    Deriv Δ (Formula.qeqv (.qmul (.qdiv s c) c) s) :=
  Deriv.qeqvOfEqNorm (Deriv.impE (Deriv.qlaw (.divMul s c)) hc)

def Deriv.qeqvMulDiv (s : Tm Γ .rat) {c : Tm Γ .rat}
    (hc : Deriv Δ (Formula.qeqv c (.qnat .zero)).neg) :
    Deriv Δ (Formula.qeqv (.qdiv (.qmul c s) c) s) :=
  Deriv.qeqvOfEqNorm (Deriv.impE (Deriv.qlaw (.mulDiv s c)) hc)

/-- `n + 1 ≠ 0` in `rat`. -/
def Deriv.qnatSuccNeZero (n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv (.qnat (.succ n)) (.qnat .zero)).neg :=
  Deriv.qlaw (.natSuccNeZero n)

end Kit

/-! ## Term plumbing: one-argument congruences and the jet reductions -/

/-- `subst1_wk` in the rename-unfolded form `deriv_norm` produces. -/
@[derivNorm] theorem qeSubstOneRenameWk {Γ : List Ty} {σ τ : Ty} (t : Tm Γ τ) (u : Tm Γ σ) :
    Tm.subst (Sub.one u) (Tm.rename (Ren.wk σ) t) = t := Tm.subst1_wk t u

/-- `wk_subst_ext` in the rename-unfolded form. -/
@[derivNorm] theorem qeSubstExtRenameWk {Γ Δ : List Ty} {σ τ : Ty} (t : Tm Γ τ) (s : Sub Γ Δ) :
    Tm.subst (Sub.ext (σ := σ) s) (Tm.rename (Ren.wk σ) t)
      = Tm.rename (Ren.wk σ) (Tm.subst s t) := Tm.wk_subst_ext t s

section Plumbing

variable {Γ as : List Ty} {Δ : Ctx Γ as}

def Deriv.qeCongQDivL {x y : Tm Γ .rat} (d : Tm Γ .rat) (h : Deriv Δ (.eq x y)) :
    Deriv Δ (.eq (.qdiv x d) (.qdiv y d)) := by
  have hs : ∀ u : Tm Γ .rat, (Tm.qdiv (.var .here) d.wk).subst1 u = .qdiv u d := by
    intro u; show Tm.qdiv u (d.wk.subst1 u) = _; rw [Tm.subst1_wk]
  have := Deriv.congTm (Tm.qdiv (.var .here) d.wk) h
  rwa [hs, hs] at this

def Deriv.qeCongFst {c d : Ty} {x y : Tm Γ (.prod c d)} (h : Deriv Δ (.eq x y)) :
    Deriv Δ (.eq (.fst x) (.fst y)) :=
  Deriv.congTm (.fst (.var .here)) h

def Deriv.qeCongSnd {c d : Ty} {x y : Tm Γ (.prod c d)} (h : Deriv Δ (.eq x y)) :
    Deriv Δ (.eq (.snd x) (.snd y)) :=
  Deriv.congTm (.snd (.var .here)) h

/-- `(D c)(n) = (n+1)·c(n+1)`. -/
def qeJetDerivAppD (c : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app tmJetDeriv c) n) (jetDerivAt c n)) := by
  have h1 : Deriv Δ (.eq (.app tmJetDeriv c) (.lam (jetDerivAt c.wk (.var .here)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (jetDerivAt (.var (.there .here)) (.var .here))) c
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq (.app (.lam (jetDerivAt c.wk (.var .here))) n) (jetDerivAt c n)) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat) (jetDerivAt c.wk (.var .here)) n
    simp only [jetDerivAt] at hb ⊢
    deriv_norm at hb
    exact hb
  exact Deriv.transE (Deriv.congFun h1 n) h2

/-- `(∫ c)(n) = jetIntegAt c n`. -/
def qeJetIntegAppD (c : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app tmJetInteg c) n) (jetIntegAt c n)) := by
  have h1 : Deriv Δ (.eq (.app tmJetInteg c) (.lam (jetIntegAt c.wk (.var .here)))) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := JetTy)
      (.lam (jetIntegAt (.var (.there .here)) (.var .here))) c
    deriv_norm at hb
    exact hb
  have h2 : Deriv Δ (.eq (.app (.lam (jetIntegAt c.wk (.var .here))) n) (jetIntegAt c n)) := by
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat) (jetIntegAt c.wk (.var .here)) n
    simp only [jetIntegAt, jetIntegStep] at hb ⊢
    deriv_norm at hb
    deriv_norm
    exact hb
  exact Deriv.transE (Deriv.congFun h1 n) h2

/-- The exponential's step functional, `λ k acc. acc / (k+1)`. -/
def qeExpStep : Tm Γ (.arrow .nat (.arrow .rat .rat)) :=
  .lam (.lam (.qdiv (.var .here) (.qnat (.succ (.var (.there .here))))))

def qeExpAppD (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app tmExpJet m) (.recNat (.qnat (.succ .zero)) qeExpStep m)) := by
  have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
    (.recNat (.qnat (.succ .zero)) qeExpStep (.var .here)) m
  deriv_norm at hb
  exact hb

/-- `exp(n+1) = exp(n)/(n+1)`, by β and ι. -/
def qeExpSuccD (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app tmExpJet (.succ n)) (.qdiv (.app tmExpJet n) (.qnat (.succ n)))) := by
  have b1 := Deriv.convBeta (Δ := Δ) (c := .nat)
    (.lam (.qdiv (.var .here) (.qnat (.succ (.var (.there .here))))) : Tm (.nat :: Γ) _) n
  deriv_norm at b1
  have b2 := Deriv.convBeta (Δ := Δ) (c := .rat)
    (.qdiv (.var .here) (.qnat (.succ n.wk))) (.recNat (.qnat (.succ .zero)) qeExpStep n)
  deriv_norm at b2
  exact Deriv.transE (qeExpAppD _) (Deriv.transE (Deriv.convRecSucc _ qeExpStep n)
    (Deriv.transE (Deriv.transE (Deriv.congFun b1 _) b2)
      (Deriv.qeCongQDivL _ (Deriv.symmE (qeExpAppD n)))))

/-- The sine–cosine step functional. -/
def qeSinCosStep : Tm Γ (.arrow .nat (.arrow (.prod .rat .rat) (.prod .rat .rat))) :=
  .lam (.lam (.pair (.qdiv (.snd (.var .here)) (.qnat (.succ (.var (.there .here)))))
    (.qdiv (.qsub (.qnat .zero) (.fst (.var .here))) (.qnat (.succ (.var (.there .here)))))))

def qeSinCosAppD (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app tmSinCosJet m)
      (.recNat (.pair (.qnat .zero) (.qnat (.succ .zero))) qeSinCosStep m)) := by
  have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
    (.recNat (.pair (.qnat .zero) (.qnat (.succ .zero))) qeSinCosStep (.var .here)) m
  deriv_norm at hb
  exact hb

/-- `(s,c)(n+1) = (c(n)/(n+1), (0 − s(n))/(n+1))`. -/
def qeSinCosSuccD (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app tmSinCosJet (.succ n))
      (.pair (.qdiv (.snd (.app tmSinCosJet n)) (.qnat (.succ n)))
        (.qdiv (.qsub (.qnat .zero) (.fst (.app tmSinCosJet n))) (.qnat (.succ n))))) := by
  let acc := Tm.recNat (.pair (.qnat .zero) (.qnat (.succ .zero))) (qeSinCosStep (Γ := Γ)) n
  have b1 := Deriv.convBeta (Δ := Δ) (c := .nat)
    (.lam (.pair (.qdiv (.snd (.var .here)) (.qnat (.succ (.var (.there .here)))))
      (.qdiv (.qsub (.qnat .zero) (.fst (.var .here))) (.qnat (.succ (.var (.there .here))))))
      : Tm (.nat :: Γ) (.arrow (.prod .rat .rat) (.prod .rat .rat))) n
  deriv_norm at b1
  have b2 := Deriv.convBeta (Δ := Δ) (c := .prod .rat .rat)
    (.pair (.qdiv (.snd (.var .here)) (.qnat (.succ n.wk)))
      (.qdiv (.qsub (.qnat .zero) (.fst (.var .here))) (.qnat (.succ n.wk)))) acc
  deriv_norm at b2
  have hP : ∀ u : Tm Γ (.prod .rat .rat),
      (Tm.pair (.qdiv (.snd (.var .here)) (.qnat (.succ n.wk)))
        (.qdiv (.qsub (.qnat .zero) (.fst (.var .here))) (.qnat (.succ n.wk)))).subst1 u
      = .pair (.qdiv (.snd u) (.qnat (.succ n))) (.qdiv (.qsub (.qnat .zero) (.fst u)) (.qnat (.succ n))) := by
    intro u
    show Tm.pair (.qdiv (.snd u) (.qnat (.succ (n.wk.subst1 u))))
      (.qdiv (.qsub (.qnat .zero) (.fst u)) (.qnat (.succ (n.wk.subst1 u)))) = _
    rw [Tm.subst1_wk]
  have hc := Deriv.congTm (Δ := Δ)
    (Tm.pair (.qdiv (.snd (.var .here)) (.qnat (.succ n.wk)))
      (.qdiv (.qsub (.qnat .zero) (.fst (.var .here))) (.qnat (.succ n.wk))))
    (Deriv.symmE (qeSinCosAppD (Δ := Δ) n))
  rw [hP, hP] at hc
  exact Deriv.transE (qeSinCosAppD _) (Deriv.transE (Deriv.convRecSucc _ qeSinCosStep n)
    (Deriv.transE (Deriv.transE (Deriv.congFun b1 _) b2) hc))

def qeSinAppD (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app tmSinJet m) (.fst (.app tmSinCosJet m))) := by
  have hb := Deriv.convBeta (Δ := Δ) (c := .nat) (.fst (.app tmSinCosJet.wk (.var .here))) m
  deriv_norm at hb
  exact hb

def qeCosAppD (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app tmCosJet m) (.snd (.app tmSinCosJet m))) := by
  have hb := Deriv.convBeta (Δ := Δ) (c := .nat) (.snd (.app tmSinCosJet.wk (.var .here))) m
  deriv_norm at hb
  exact hb

/-- The shape every derivative law closes with: `(n+1)·(a/(n+1)) ≈ a`. -/
def qeCancelD (n : Tm Γ .nat) {u a : Tm Γ .rat}
    (h : Deriv Δ (.eq u (.qdiv a (.qnat (.succ n))))) :
    Deriv Δ (Formula.qeqv (.qmul (.qnat (.succ n)) u) a) :=
  Deriv.qeqvOfEqNorm (Deriv.transE (qmulCongRight _ h) (Deriv.convQMulDivCancel n a))

end Plumbing

/-! ## The calculus laws, inside `Deriv`

Stated over the closed System T functionals `tmJetDeriv`/`tmJetInteg` and the
generators `tmExpJet`/`tmSinJet`/`tmCosJet` of `ClosedCalculus.lean`, at a
symbolic index `n` (and, for FTC, a symbolic jet `c`).  Each is β/ι-reduction
followed by one `≈` cancellation — no induction: the laws are *uniform*. -/

section Laws

variable {Γ as : List Ty} {Δ : Ctx Γ as}

/-- **exp′ ≈ exp**, at index `n`. -/
def qeExpDerivD (n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv (.app (.app tmJetDeriv tmExpJet) n) (.app tmExpJet n)) :=
  Deriv.qeqvTrans (Deriv.qeqvOfEq (qeJetDerivAppD _ n)) (qeCancelD n (qeExpSuccD n))

/-- **sin′ ≈ cos**, at index `n`. -/
def qeSinDerivD (n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv (.app (.app tmJetDeriv tmSinJet) n) (.app tmCosJet n)) := by
  have h : Deriv Δ (.eq (.app tmSinJet (.succ n)) (.qdiv (.app tmCosJet n) (.qnat (.succ n)))) :=
    Deriv.transE (qeSinAppD _) (Deriv.transE (Deriv.qeCongFst (qeSinCosSuccD n))
      (Deriv.transE (Deriv.convFst _ _) (Deriv.qeCongQDivL _ (Deriv.symmE (qeCosAppD n)))))
  exact Deriv.qeqvTrans (Deriv.qeqvOfEq (qeJetDerivAppD _ n)) (qeCancelD n h)

/-- **cos′ ≈ −sin**, at index `n` (`−s` is `0 − s`). -/
def qeCosDerivD (n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv (.app (.app tmJetDeriv tmCosJet) n)
      (.qsub (.qnat .zero) (.app tmSinJet n))) := by
  have hs : ∀ u : Tm Γ .rat,
      (Tm.qdiv (.qsub (.qnat .zero) (.var .here)) (.qnat (.succ n.wk))).subst1 u
        = .qdiv (.qsub (.qnat .zero) u) (.qnat (.succ n)) := by
    intro u
    show Tm.qdiv (.qsub (.qnat .zero) u) (.qnat (.succ (n.wk.subst1 u))) = _
    rw [Tm.subst1_wk]
  have hsin := Deriv.congTm (Δ := Δ) (Tm.qdiv (.qsub (.qnat .zero) (.var .here)) (.qnat (.succ n.wk)))
    (Deriv.symmE (qeSinAppD (Δ := Δ) n))
  rw [hs, hs] at hsin
  have h : Deriv Δ (.eq (.app tmCosJet (.succ n))
      (.qdiv (.qsub (.qnat .zero) (.app tmSinJet n)) (.qnat (.succ n)))) :=
    Deriv.transE (qeCosAppD _) (Deriv.transE (Deriv.qeCongSnd (qeSinCosSuccD n))
      (Deriv.transE (Deriv.convSnd _ _) hsin))
  exact Deriv.qeqvTrans (Deriv.qeqvOfEq (qeJetDerivAppD _ n)) (qeCancelD n h)

/-- **FTC1**: `D(∫ c) ≈ c`, at index `n`, for every jet `c`. -/
def qeFTC1D (c : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv (.app (.app tmJetDeriv (.app tmJetInteg c)) n) (.app c n)) := by
  have h : Deriv Δ (.eq (.app (.app tmJetInteg c) (.succ n)) (.qdiv (.app c n) (.qnat (.succ n)))) :=
    Deriv.transE (qeJetIntegAppD c _) (jetIntegSuccD c n)
  exact Deriv.qeqvTrans (Deriv.qeqvOfEq (qeJetDerivAppD _ n)) (qeCancelD n h)

/-- **FTC2, constant term**: `∫(D c)(0) = 0`. -/
def qeFTC2ZeroD (c : Tm Γ JetTy) :
    Deriv Δ (.eq (.app (.app tmJetInteg (.app tmJetDeriv c)) .zero) (.qnat .zero)) :=
  Deriv.transE (qeJetIntegAppD _ _) (jetIntegZeroD _)

/-- **FTC2**: `∫(D c)(n+1) ≈ c(n+1)`, for every jet `c`. -/
def qeFTC2SuccD (c : Tm Γ JetTy) (n : Tm Γ .nat) :
    Deriv Δ (Formula.qeqv (.app (.app tmJetInteg (.app tmJetDeriv c)) (.succ n))
      (.app c (.succ n))) := by
  have h1 : Deriv Δ (.eq (.app (.app tmJetInteg (.app tmJetDeriv c)) (.succ n))
      (.qdiv (.qmul (.qnat (.succ n)) (.app c (.succ n))) (.qnat (.succ n)))) :=
    Deriv.transE (qeJetIntegAppD _ _) (Deriv.transE (jetIntegSuccD _ n)
      (Deriv.qeCongQDivL _ (qeJetDerivAppD c n)))
  exact Deriv.qeqvTrans (Deriv.qeqvOfEq h1)
    (Deriv.qeqvMulDiv _ (Deriv.qnatSuccNeZero n))

end Laws

/-! ## The closed statements -/

/-- `∀n. exp′(n) ≈ exp(n)`. -/
def expDerivLawD : Deriv (Ctx.nil (Γ := []))
    (.all .nat (Formula.qeqv (.app (.app tmJetDeriv tmExpJet) (.var .here))
      (.app tmExpJet (.var .here)))) :=
  Deriv.allI (qeExpDerivD _)

/-- `∀n. sin′(n) ≈ cos(n)`. -/
def sinDerivLawD : Deriv (Ctx.nil (Γ := []))
    (.all .nat (Formula.qeqv (.app (.app tmJetDeriv tmSinJet) (.var .here))
      (.app tmCosJet (.var .here)))) :=
  Deriv.allI (qeSinDerivD _)

/-- `∀n. cos′(n) ≈ −sin(n)`. -/
def cosDerivLawD : Deriv (Ctx.nil (Γ := []))
    (.all .nat (Formula.qeqv (.app (.app tmJetDeriv tmCosJet) (.var .here))
      (.qsub (.qnat .zero) (.app tmSinJet (.var .here))))) :=
  Deriv.allI (qeCosDerivD _)

/-- **FTC1**: `∀c ∀n. D(∫c)(n) ≈ c(n)`. -/
def ftc1LawD : Deriv (Ctx.nil (Γ := []))
    (.all JetTy (.all .nat (Formula.qeqv
      (.app (.app tmJetDeriv (.app tmJetInteg (.var (.there .here)))) (.var .here))
      (.app (.var (.there .here)) (.var .here))))) :=
  Deriv.allI (Deriv.allI (qeFTC1D _ _))

/-- **FTC2**: `∀c. ∫(Dc)(0) = 0 ∧ ∀n. ∫(Dc)(n+1) ≈ c(n+1)`. -/
def ftc2LawD : Deriv (Ctx.nil (Γ := []))
    (.all JetTy (.and
      (.eq (.app (.app tmJetInteg (.app tmJetDeriv (.var .here))) .zero) (.qnat .zero))
      (.all .nat (Formula.qeqv
        (.app (.app tmJetInteg (.app tmJetDeriv (.var (.there .here)))) (.succ (.var .here)))
        (.app (.var (.there .here)) (.succ (.var .here))))))) :=
  Deriv.allI (Deriv.andI (qeFTC2ZeroD _) (Deriv.allI (qeFTC2SuccD _ _)))

/-! ## What `≈` means, and a round trip -/

/-- **`≈` is equality of values**: realizing `s ≈ t` is `s` and `t` denoting
the same rational. -/
theorem MR_qeqv_iff {Γ : List Ty} (s t : Tm Γ .rat) (e : Env Γ) (x : Ty.unit.interp) :
    MR (Formula.qeqv s t) e x ↔ (s.eval e).val = (t.eval e).val :=
  Q.norm_eq_iff _ _

/-- The round trip: `soundness` applied to `expDerivLawD` gives the value law
`exp′(n) = exp(n)` at every `n`. -/
theorem expDerivLaw_val (n : Nat) :
    (((tmJetDeriv (Γ := [])).eval Env.nil) ((tmExpJet (Γ := [])).eval Env.nil) n).val
      = (((tmExpJet (Γ := [])).eval Env.nil) n).val :=
  (MR_qeqv_iff _ _ _ _).mp (soundness expDerivLawD Env.nil Env.nil realizes_nil n)

/-- The round trip for FTC1, at every jet `c` and index `n`. -/
theorem ftc1Law_val (c : Nat → Q) (n : Nat) :
    (((tmJetDeriv (Γ := [])).eval Env.nil) (((tmJetInteg (Γ := [])).eval Env.nil) c) n).val
      = (c n).val :=
  (MR_qeqv_iff _ _ _ _).mp (soundness ftc1LawD Env.nil Env.nil realizes_nil c n)

#print axioms expDerivLawD
#print axioms sinDerivLawD
#print axioms cosDerivLawD
#print axioms ftc1LawD
#print axioms ftc2LawD
#print axioms expDerivLaw_val
#print axioms ftc1Law_val

end HAomega
