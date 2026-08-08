/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Pascal

/-!
# Pascal mod 2, proved inside HA^ω

`flipTotal`, `parityTotal`, and the unfolding equations of `pasT`, assembled
below into `pasTotal` — with the disjunction **tag** a decision the proofs
compute, not a witness handed to `exI`.

## The two lessons this file encodes

**Conversion must be statable at every type** (the `Formula.eq`-at-`τ`
revision): `pasT` recurses on the *row*, an object of type `ℕ → ℕ`, and
`rowZero`/`rowSucc` are equations between rows.

**The elaborator must never be asked to reduce a substitution.**  A conversion
chain written with holes (`convBeta _ _`) forces Lean to symbolically execute
`Tm.subst` over ~100-node dependently-indexed terms at every link — minutes per
declaration.  Written explicitly — every intermediate term named
(`rowStep2T`, `rowAppT`, `innerAt`, `innerApp`), every reduction a lemma
(`linkRow1` … `linkXor2`, each `rfl` or a small `simp only`) — the same chains
elaborate in milliseconds.  The rename/substitution composition kit
(`Tm.rename_rename`, `Tm.rename_subst`, `Tm.wk_subst_ext`) is what lets the
`simp only` sets fire where a weakened symbolic subterm blocks the walk.
-/

namespace HAomega

/-- Congruence in the function position — from Leibniz, now at every type. -/
def Deriv.congFun {Γ as : List Ty} {Δ : Ctx Γ as} {c d : Ty}
    {f g : Tm Γ (.arrow c d)} (h : Deriv Δ (.eq f g)) (x : Tm Γ c) :
    Deriv Δ (.eq (.app f x) (.app g x)) := by
  have hs : ∀ u : Tm Γ (.arrow c d),
      (Formula.eq (.app (Tm.var .here) (x.wk)) ((Tm.app f x).wk)).subst1 u
        = Formula.eq (.app u x) (.app f x) := by
    intro u
    show Formula.eq (.app u ((x.wk).subst1 u)) (((Tm.app f x).wk).subst1 u) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.app (Tm.var .here) (x.wk)) ((Tm.app f x).wk)) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

/-- Congruence in the argument position. -/
def Deriv.congArg {Γ as : List Ty} {Δ : Ctx Γ as} {c d : Ty}
    (f : Tm Γ (.arrow c d)) {x y : Tm Γ c} (h : Deriv Δ (.eq x y)) :
    Deriv Δ (.eq (.app f x) (.app f y)) := by
  have hs : ∀ u : Tm Γ c,
      (Formula.eq (.app (f.wk) (Tm.var .here)) ((Tm.app f x).wk)).subst1 u
        = Formula.eq (.app f u) (.app f x) := by
    intro u
    show Formula.eq (.app ((f.wk).subst1 u) u) (((Tm.app f x).wk).subst1 u) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.app (f.wk) (Tm.var .here)) ((Tm.app f x).wk)) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key; exact key.symmE

/-- Row 0 of Pascal **is** `flip`. -/
def rowZero {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app pasT .zero) (flipT (Γ := Γ))) :=
  Deriv.transE (Deriv.convBeta _ _) (Deriv.convRecZero _ _)


/-- `pas 0 k = flip k` — one congruence step from `rowZero`. -/
def pasZeroK {Γ as : List Ty} {Δ : Ctx Γ as} (k : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app pasT .zero) k) (.app flipT k)) :=
  Deriv.congFun rowZero k



def flipZero {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app flipT .zero) (.succ .zero)) :=
  Deriv.transE (Deriv.convBeta _ _) (Deriv.convRecZero _ _)

def flipSucc {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app flipT (.succ m)) .zero) :=
  Deriv.transE (Deriv.convBeta _ _)
    (Deriv.transE (Deriv.convRecSucc _ _ _)
      (Deriv.transE (Deriv.congFun (Deriv.convBeta _ _) _) (Deriv.convBeta _ _)))

def parityZero {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app parityT .zero) .zero) :=
  Deriv.transE (Deriv.convBeta _ _) (Deriv.convRecZero _ _)

def paritySucc {Γ as : List Ty} {Δ : Ctx Γ as} (m : Tm Γ .nat) :
    Deriv Δ (.eq (.app parityT (.succ m)) (.app flipT (.app parityT m))) :=
  Deriv.transE
    (Deriv.transE (Deriv.convBeta _ _)
      (Deriv.transE (Deriv.convRecSucc _ _ _)
        (Deriv.transE (Deriv.congFun (Deriv.convBeta _ _) _) (Deriv.convBeta _ _))))
    (Deriv.congArg flipT (Deriv.symmE (Deriv.convBeta _ _)))

abbrev flipPhi {Γ : List Ty} :
    Formula (.nat :: Γ) (.prod .nat (.prod .unit .unit)) :=
  .or (.eq (.app flipT (.var .here)) (.succ .zero))
      (.eq (.app flipT (.var .here)) .zero)

def flipTotal {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (flipPhi (Γ := Γ))) := by
  refine Deriv.ind (Deriv.orI₁ flipZero) ?_
  exact Deriv.allI (Deriv.impI (Deriv.orI₂ (flipSucc _)))

abbrev parityPhi {Γ : List Ty} :
    Formula (.nat :: Γ) (.prod .nat (.prod .unit .unit)) :=
  .or (.eq (.app parityT (.var .here)) (.succ .zero))
      (.eq (.app parityT (.var .here)) .zero)

def parityTotal {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (parityPhi (Γ := Γ))) := by
  refine Deriv.ind (Deriv.orI₂ parityZero) ?_
  refine Deriv.allI (Deriv.impI ?_)
  refine Deriv.orE Deriv.ax ?_ ?_
  · exact Deriv.orI₂ (Deriv.transE (Deriv.transE (paritySucc _)
      (Deriv.congArg flipT Deriv.ax)) (flipSucc _))
  · exact Deriv.orI₁ (Deriv.transE (Deriv.transE (paritySucc _)
      (Deriv.congArg flipT Deriv.ax)) flipZero)



/-- `pasT`'s body is closed apart from its scrutinee, so beta just points the
recursor at the argument.  `rfl`: kernel evaluation, no unification. -/
theorem pasT_body_subst {Γ : List Ty} (u : Tm Γ .nat) :
    Tm.subst1 ((Tm.recNat flipT rowStepT (Tm.var .here)) :
      Tm (.nat :: Γ) (.arrow .nat .nat)) u
      = Tm.recNat flipT rowStepT u := rfl

/-- One row-recursion step, every link explicit. -/
def rowSucc {Γ as : List Ty} {Δ : Ctx Γ as} (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app pasT (.succ n)) (.app (.app rowStepT n) (.app pasT n))) := by
  have hb : Deriv Δ (.eq (.app pasT (.succ n))
      (.recNat flipT rowStepT (.succ n))) := by
    have h := Deriv.convBeta (Δ := Δ)
      (Tm.recNat flipT rowStepT (Tm.var .here)) (Tm.succ n)
    rwa [pasT_body_subst] at h
  have hn : Deriv Δ (.eq (.app pasT n) (.recNat flipT rowStepT n)) := by
    have h := Deriv.convBeta (Δ := Δ)
      (Tm.recNat flipT rowStepT (Tm.var .here)) n
    rwa [pasT_body_subst] at h
  exact Deriv.transE hb (Deriv.transE (Deriv.convRecSucc _ _ _)
    (Deriv.congArg (.app rowStepT n) hn.symmE))





theorem Ren.ext_comp {Γ Δ Θ : List Ty} {σ : Ty} (ρ : Ren Γ Δ) (ρ' : Ren Δ Θ) :
    (fun τ v ↦ Ren.ext (σ := σ) ρ' τ (Ren.ext ρ τ v))
      = Ren.ext (σ := σ) (fun τ v ↦ ρ' τ (ρ τ v)) := by
  funext τ v; cases v <;> rfl

/-- Renamings compose. -/
theorem Tm.rename_rename {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ Θ : List Ty} (ρ : Ren Γ Δ) (ρ' : Ren Δ Θ),
      (t.rename ρ).rename ρ' = t.rename (fun σ v ↦ ρ' σ (ρ σ v)) := by
  induction t with
  | var v => intros; rfl
  | lam b ih =>
      intro Δ Θ ρ ρ'
      simp only [Tm.rename]
      rw [ih ρ.ext ρ'.ext, Ren.ext_comp]
  | app f a ihf iha => intro Δ Θ ρ ρ'; simp only [Tm.rename, ihf, iha]
  | star => intros; rfl
  | pair a b iha ihb => intro Δ Θ ρ ρ'; simp only [Tm.rename, iha, ihb]
  | fst t ih => intro Δ Θ ρ ρ'; simp only [Tm.rename, ih]
  | snd t ih => intro Δ Θ ρ ρ'; simp only [Tm.rename, ih]
  | zero => intros; rfl
  | succ t ih => intro Δ Θ ρ ρ'; simp only [Tm.rename, ih]
  | add a b iha ihb => intro Δ Θ ρ ρ'; simp only [Tm.rename, iha, ihb]
  | prec a b iha ihb => intro Δ Θ ρ ρ'; simp only [Tm.rename, iha, ihb]
  | pred a ih => intro Δ Θ ρ ρ'; simp only [Tm.rename, ih]
  | bump a b iha ihb => intro Δ Θ ρ ρ'; simp only [Tm.rename, iha, ihb]
  | good a b iha ihb => intro Δ Θ ρ ρ'; simp only [Tm.rename, iha, ihb]
  | ord a b iha ihb => intro Δ Θ ρ ρ'; simp only [Tm.rename, iha, ihb]
  | hcut a b iha ihb => intro Δ Θ ρ ρ'; simp only [Tm.rename, iha, ihb]
  | hydra a b iha ihb => intro Δ Θ ρ ρ'; simp only [Tm.rename, iha, ihb]
  | hord a ih => intro Δ Θ ρ ρ'; simp only [Tm.rename, ih]
  | tiRec sc n ihs ihn => intro Δ Θ ρ ρ'; simp only [Tm.rename, ihs, ihn]
  | recNat z sc n ihz ihs ihn =>
      intro Δ Θ ρ ρ'; simp only [Tm.rename, ihz, ihs, ihn]

theorem Sub.ren_ext {Γ Δ Θ : List Ty} {σ : Ty} (s : Sub Γ Δ) (ρ : Ren Δ Θ) :
    (fun τ v ↦ (Sub.ext (σ := σ) s τ v).rename ρ.ext)
      = Sub.ext (σ := σ) (fun τ v ↦ (s τ v).rename ρ) := by
  funext τ v
  cases v with
  | here => rfl
  | there v =>
      show ((s τ v).rename (Ren.wk σ)).rename ρ.ext
        = ((s τ v).rename ρ).rename (Ren.wk σ)
      rw [Tm.rename_rename, Tm.rename_rename]
      rfl

/-- Substitution then renaming, as one substitution. -/
theorem Tm.rename_subst {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ Θ : List Ty} (s : Sub Γ Δ) (ρ : Ren Δ Θ),
      (t.subst s).rename ρ = t.subst (fun σ v ↦ (s σ v).rename ρ) := by
  induction t with
  | var v => intros; rfl
  | lam b ih =>
      intro Δ Θ s ρ
      simp only [Tm.subst, Tm.rename]
      rw [ih s.ext ρ.ext, Sub.ren_ext]
  | app f a ihf iha => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, ihf, iha]
  | star => intros; rfl
  | pair a b iha ihb => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, iha, ihb]
  | fst t ih => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, ih]
  | snd t ih => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, ih]
  | zero => intros; rfl
  | succ t ih => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, ih]
  | add a b iha ihb => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, iha, ihb]
  | prec a b iha ihb => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, iha, ihb]
  | pred a ih => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, ih]
  | bump a b iha ihb => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, iha, ihb]
  | good a b iha ihb => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, iha, ihb]
  | ord a b iha ihb => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, iha, ihb]
  | hcut a b iha ihb => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, iha, ihb]
  | hydra a b iha ihb => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, iha, ihb]
  | hord a ih => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, ih]
  | tiRec sc n ihs ihn => intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, ihs, ihn]
  | recNat z sc n ihz ihs ihn =>
      intro Δ Θ s ρ; simp only [Tm.subst, Tm.rename, ihz, ihs, ihn]

/-- **The commutation the chains need**: substituting under a binder a term
that was weakened past that binder just pushes the substitution inside. -/
theorem Tm.wk_subst_ext {Γ Δ : List Ty} {σ τ : Ty} (t : Tm Γ τ) (s : Sub Γ Δ) :
    (t.wk (σ := σ)).subst s.ext = (t.subst s).wk (σ := σ) := by
  rw [Tm.wk, Tm.subst_rename, Tm.wk, Tm.rename_subst]
  rfl

/-- Weakened terms ignore a single substitution entirely. -/
@[simp] theorem Tm.wk_subst1 {Γ : List Ty} {σ τ : Ty} (t : Tm Γ τ)
    (u : Tm Γ σ) : (t.wk (σ := σ)).subst1 u = t :=
  Tm.subst1_wk t u


/-- Weakened terms ignore the substitution, `Sub.one` form. -/
theorem Tm.wk_subst_one {Γ : List Ty} {σ τ : Ty} (t : Tm Γ τ) (u : Tm Γ σ) :
    Tm.subst (Sub.one u) (t.wk (σ := σ)) = t := Tm.subst1_wk t u

-- closed-term substitution lemmas: the walk never inspects `s`
theorem flipT_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (flipT (Γ := Γ)).subst s = flipT := rfl
theorem parityT_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (parityT (Γ := Γ)).subst s = parityT := rfl
theorem xorT_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (xorT (Γ := Γ)).subst s = xorT := rfl

/-- `rowStepT` with its (unused) row-index binder consumed: the two remaining
lambdas verbatim. -/
def rowStep2T {Γ : List Ty} :
    Tm Γ (.arrow (.arrow .nat .nat) (.arrow .nat .nat)) :=
  .lam (.lam (.recNat (.succ .zero)
    (.lam (.lam (.app (.app xorT
        (.app (.var (.there (.there (.there .here)))) (.var (.there .here))))
      (.app (.var (.there (.there (.there .here))))
        (.succ (.var (.there .here)))))))
    (.var .here)))

/-- The row builder at a concrete previous row `R`. -/
def rowAppT {Γ : List Ty} (R : Tm Γ (.arrow .nat .nat)) :
    Tm Γ (.arrow .nat .nat) :=
  .lam (.recNat (.succ .zero)
    (.lam (.lam (.app (.app xorT
        (.app (R.wk.wk.wk) (.var (.there .here))))
      (.app (R.wk.wk.wk) (.succ (.var (.there .here)))))))
    (.var .here))

/-- The inner step at row `R`, column binder gone. -/
def innerAt {Γ : List Ty} (R : Tm Γ (.arrow .nat .nat)) :
    Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.lam (.app (.app xorT
      (.app (R.wk.wk) (.var (.there .here))))
    (.app (R.wk.wk) (.succ (.var (.there .here))))))

/-- One application step of `innerAt`. -/
def innerApp {Γ : List Ty} (R : Tm Γ (.arrow .nat .nat)) (k : Tm Γ .nat) :
    Tm Γ (.arrow .nat .nat) :=
  .lam (.app (.app xorT (.app (R.wk) (k.wk)))
    (.app (R.wk) (.succ (k.wk))))

-- ===== reduction lemmas, one per beta link =====
theorem linkRow1 {Γ : List Ty} (n : Tm Γ .nat) :
    Tm.subst1 (.lam (.lam (.recNat (.succ .zero)
      (.lam (.lam (.app (.app xorT
          (.app (.var (.there (.there (.there .here)))) (.var (.there .here))))
        (.app (.var (.there (.there (.there .here))))
          (.succ (.var (.there .here)))))))
      (.var .here)))) n = rowStep2T (Γ := Γ) := rfl

theorem linkRow2 {Γ : List Ty} (R : Tm Γ (.arrow .nat .nat)) :
    Tm.subst1 (.lam (.recNat (.succ .zero)
      (.lam (.lam (.app (.app xorT
          (.app (.var (.there (.there (.there .here)))) (.var (.there .here))))
        (.app (.var (.there (.there (.there .here))))
          (.succ (.var (.there .here)))))))
      (.var .here))) R = rowAppT R := rfl

theorem linkRow3 {Γ : List Ty} (R : Tm Γ (.arrow .nat .nat)) (u : Tm Γ .nat) :
    Tm.subst1 (.recNat (.succ .zero)
      (.lam (.lam (.app (.app xorT
          (.app ((R.wk).wk.wk) (.var (.there .here))))
        (.app ((R.wk).wk.wk) (.succ (.var (.there .here)))))))
      (.var .here)) u = .recNat (.succ .zero) (innerAt R) u := by
  simp only [Tm.subst1, Tm.subst, Sub.ext, Sub.one, Tm.rename, innerAt,
    xorT_subst, parityT_subst, Tm.wk_subst_ext, Tm.wk_subst_one]
  rfl

theorem linkInner1 {Γ : List Ty} (R : Tm Γ (.arrow .nat .nat)) (k : Tm Γ .nat) :
    Tm.subst1 ((.lam (.app (.app xorT
        (.app ((R.wk (σ := .nat)).wk) (.var (.there .here))))
      (.app ((R.wk (σ := .nat)).wk) (.succ (.var (.there .here)))))
      : Tm (.nat :: Γ) (.arrow .nat .nat))) k
      = innerApp R k := by
  simp only [Tm.subst1, Tm.subst, Sub.ext, Sub.one, Tm.rename, innerApp,
    xorT_subst, parityT_subst, Tm.wk_subst_ext, Tm.wk_subst_one]
  rfl

theorem linkInner2 {Γ : List Ty} (R : Tm Γ (.arrow .nat .nat)) (k : Tm Γ .nat)
    (I : Tm Γ .nat) :
    Tm.subst1 (.app (.app xorT (.app ((R.wk)) ((k.wk))))
      (.app ((R.wk)) (.succ ((k.wk))))) I
      = .app (.app xorT (.app R k)) (.app R (.succ k)) := by
  simp only [Tm.subst1, Tm.subst, Sub.ext, Sub.one, Tm.rename,
    xorT_subst, parityT_subst, Tm.wk_subst_ext, Tm.wk_subst_one]

theorem linkXor1 {Γ : List Ty} (a : Tm Γ .nat) :
    Tm.subst1 (.lam (.app parityT
      (.add (.var (.there .here)) (.var .here)))) a
      = .lam (.app parityT (.add (a.wk) (.var .here))) := rfl

theorem linkXor2 {Γ : List Ty} (a b : Tm Γ .nat) :
    Tm.subst1 (.app parityT (.add ((a.wk)) (.var .here))) b
      = .app parityT (.add a b) := by
  simp only [Tm.subst1, Tm.subst, Sub.ext, Sub.one, Tm.rename,
    xorT_subst, parityT_subst, Tm.wk_subst_ext, Tm.wk_subst_one]


-- ===== the explicit chains =====
section
variable {Γ as : List Ty} {Δ : Ctx Γ as}

/-- `pas (n+1) 0 = 1`, every link explicit. -/
def pasSuccZero (n : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app pasT (.succ n)) .zero) (.succ .zero)) := by
  set R := Tm.app pasT n with hR
  have h1 : Deriv Δ (.eq (.app rowStepT n) rowStep2T) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat) (.lam (.lam (.recNat (.succ .zero)
      (.lam (.lam (.app (.app xorT
          (.app (.var (.there (.there (.there .here)))) (.var (.there .here))))
        (.app (.var (.there (.there (.there .here))))
          (.succ (.var (.there .here)))))))
      (.var .here)))) n
    rwa [linkRow1] at h
  have h2 : Deriv Δ (.eq (.app rowStep2T R) (rowAppT R)) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .arrow .nat .nat)
      (.lam (.recNat (.succ .zero)
      (.lam (.lam (.app (.app xorT
          (.app (.var (.there (.there (.there .here)))) (.var (.there .here))))
        (.app (.var (.there (.there (.there .here))))
          (.succ (.var (.there .here)))))))
      (.var .here))) R
    rwa [linkRow2] at h
  have h3 : Deriv Δ (.eq (.app (rowAppT R) .zero)
      (.recNat (.succ .zero) (innerAt R) .zero)) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat) (.recNat (.succ .zero)
      (.lam (.lam (.app (.app xorT
          (.app (((R.wk (σ := .nat)).wk).wk) (.var (.there .here))))
        (.app (((R.wk (σ := .nat)).wk).wk) (.succ (.var (.there .here)))))))
      (.var .here)) .zero
    rwa [linkRow3] at h
  exact Deriv.transE (Deriv.congFun (rowSucc n) .zero)
    (Deriv.transE (Deriv.congFun (Deriv.congFun h1 R) .zero)
      (Deriv.transE (Deriv.congFun h2 .zero)
        (Deriv.transE h3 (Deriv.convRecZero _ _))))

/-- `pas (n+1) (k+1) = parity (pas n k + pas n (k+1))`, every link explicit. -/
def pasSuccSucc (n k : Tm Γ .nat) :
    Deriv Δ (.eq (.app (.app pasT (.succ n)) (.succ k))
      (.app parityT (.add (.app (.app pasT n) k)
        (.app (.app pasT n) (.succ k))))) := by
  set R := Tm.app pasT n with hR
  have h1 : Deriv Δ (.eq (.app rowStepT n) rowStep2T) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat) (.lam (.lam (.recNat (.succ .zero)
      (.lam (.lam (.app (.app xorT
          (.app (.var (.there (.there (.there .here)))) (.var (.there .here))))
        (.app (.var (.there (.there (.there .here))))
          (.succ (.var (.there .here)))))))
      (.var .here)))) n
    rwa [linkRow1] at h
  have h2 : Deriv Δ (.eq (.app rowStep2T R) (rowAppT R)) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .arrow .nat .nat)
      (.lam (.recNat (.succ .zero)
      (.lam (.lam (.app (.app xorT
          (.app (.var (.there (.there (.there .here)))) (.var (.there .here))))
        (.app (.var (.there (.there (.there .here))))
          (.succ (.var (.there .here)))))))
      (.var .here))) R
    rwa [linkRow2] at h
  have h3 : Deriv Δ (.eq (.app (rowAppT R) (.succ k))
      (.recNat (.succ .zero) (innerAt R) (.succ k))) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat) (.recNat (.succ .zero)
      (.lam (.lam (.app (.app xorT
          (.app (((R.wk (σ := .nat)).wk).wk) (.var (.there .here))))
        (.app (((R.wk (σ := .nat)).wk).wk) (.succ (.var (.there .here)))))))
      (.var .here)) (.succ k)
    rwa [linkRow3] at h
  set I := Tm.recNat (.succ .zero) (innerAt R) k with hI
  have h5 : Deriv Δ (.eq (.app (innerAt R) k) (innerApp R k)) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat) ((.lam (.app (.app xorT
        (.app ((R.wk (σ := .nat)).wk) (.var (.there .here))))
      (.app ((R.wk (σ := .nat)).wk) (.succ (.var (.there .here)))))
      : Tm (.nat :: Γ) (.arrow .nat .nat))) k
    rwa [linkInner1] at h
  have h6 : Deriv Δ (.eq (.app (innerApp R k) I)
      (.app (.app xorT (.app R k)) (.app R (.succ k)))) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat) ((.app (.app xorT (.app (R.wk (σ := .nat)) (k.wk)))
      (.app (R.wk (σ := .nat)) (.succ (k.wk)))) : Tm (.nat :: Γ) .nat) I
    rwa [linkInner2] at h
  have h7a : Deriv Δ (.eq (.app xorT (.app R k))
      (.lam (.app parityT (.add ((Tm.app R k).wk) (.var .here))))) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat) ((.lam (.app parityT
      (.add (.var (.there .here)) (.var .here))))
      : Tm (.nat :: Γ) (.arrow .nat .nat)) (.app R k)
    rwa [linkXor1] at h
  have h7b : Deriv Δ (.eq
      (.app (.lam (.app parityT (.add ((Tm.app R k).wk) (.var .here))))
        (.app R (.succ k)))
      (.app parityT (.add (.app R k) (.app R (.succ k))))) := by
    have h := Deriv.convBeta (Δ := Δ) (c := .nat)
      ((.app parityT (.add ((Tm.app R k).wk (σ := .nat)) (.var .here)))
        : Tm (.nat :: Γ) .nat)
      (.app R (.succ k))
    rwa [linkXor2] at h
  exact Deriv.transE (Deriv.congFun (rowSucc n) (.succ k))
    (Deriv.transE (Deriv.congFun (Deriv.congFun h1 R) (.succ k))
      (Deriv.transE (Deriv.congFun h2 (.succ k))
        (Deriv.transE h3
          (Deriv.transE (Deriv.convRecSucc _ _ _)
            (Deriv.transE (Deriv.congFun h5 I)
              (Deriv.transE h6
                (Deriv.transE (Deriv.congFun h7a (.app R (.succ k))) h7b)))))))

end


/-- Transport `s = 1 ∨ s = 0` along `t = s`. -/
def Deriv.orEqTransport {Γ as : List Ty} {Δ : Ctx Γ as} {s t : Tm Γ .nat}
    (heq : Deriv Δ (.eq t s))
    (h : Deriv Δ (.or (Formula.eq s (.succ .zero)) (.eq s .zero))) :
    Deriv Δ (.or (Formula.eq t (.succ .zero)) (.eq t .zero)) := by
  refine Deriv.orE h ?_ ?_
  · exact Deriv.orI₁ (Deriv.transE (Deriv.wk heq) Deriv.ax)
  · exact Deriv.orI₂ (Deriv.transE (Deriv.wk heq) Deriv.ax)

/-- The totality formula, over `n` (outer) and `k` (inner). -/
abbrev pasPhi {Γ : List Ty} :
    Formula (.nat :: Γ) (.arrow .nat (.prod .nat (.prod .unit .unit))) :=
  .all .nat
    (.or (.eq (.app (.app pasT (.var (.there .here))) (.var .here)) (.succ .zero))
         (.eq (.app (.app pasT (.var (.there .here))) (.var .here)) .zero))

/-- **`∀n ∀k. pas n k = 1 ∨ pas n k = 0`** — the decision computed by the
proof.  Outer `ind` on `n`; base row via `flipTotal`, successor rows via the
unfolding chains plus `parityTotal`; the inner `ind` on `k` discards its
hypothesis — the case-split device. -/
def pasTotal {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (pasPhi (Γ := Γ))) := by
  refine Deriv.ind (φ := pasPhi) ?base ?step
  case base =>
    show Deriv Δ (.all .nat
      (.or (.eq (.app (.app pasT .zero) (.var .here)) (.succ .zero))
           (.eq (.app (.app pasT .zero) (.var .here)) .zero)))
    refine Deriv.allI ?_
    refine Deriv.orEqTransport (pasZeroK (.var .here)) ?_
    have hf := Deriv.allE (Δ := Ctx.wk Δ) (.var .here)
      (flipTotal (Γ := .nat :: Γ))
    exact hf
  case step =>
    refine Deriv.allI (Deriv.impI ?_)
    show Deriv _ (.all .nat
      (.or (.eq (.app (.app pasT (.succ (.var (.there .here)))) (.var .here))
             (.succ .zero))
           (.eq (.app (.app pasT (.succ (.var (.there .here)))) (.var .here))
             .zero)))
    refine Deriv.ind
      (φ := .or (.eq (.app (.app pasT (.succ (.var (.there .here)))) (.var .here))
               (.succ .zero))
            (.eq (.app (.app pasT (.succ (.var (.there .here)))) (.var .here))
               .zero)) ?_ ?_
    · exact Deriv.orI₁ (pasSuccZero (.var .here))
    · refine Deriv.allI (Deriv.impI ?_)
      show Deriv _ (.or
        (.eq (.app (.app pasT (.succ (.var (.there .here)))) (.succ (.var .here)))
          (.succ .zero))
        (.eq (.app (.app pasT (.succ (.var (.there .here)))) (.succ (.var .here)))
          .zero))
      refine Deriv.orEqTransport
        (pasSuccSucc (.var (.there .here)) (.var .here)) ?_
      exact Deriv.allE _ parityTotal


/-! ## The extracted decider — the point of the exercise

`pasTotal`'s realizer at `(n, k)` is a tagged pair; the **tag** is the
decision, and it was computed by the proof — by `eqDec` inside `flipTotal`
and `parityTotal`, threaded through the inductions — never handed to an
introduction rule as a witness.  This is the first case study in the HA^ω
branch whose extracted program the specification does not already contain. -/

/-- The extracted decision: `0` means the left disjunct, `pas n k = 1`. -/
def pasTag (n k : Nat) : Nat :=
  (((extractClosed (pasTotal (Γ := []) (Δ := Ctx.nil))).eval Env.nil) n k).1

/-- The decider as a bit, matching `pas` itself. -/
def pasDecide (n k : Nat) : Nat := if pasTag n k = 0 then 1 else 0

-- **The extracted decider draws the Sierpinski gasket** — and agrees with the
-- value-level `pas` everywhere in rows 0–7.  Soundness is what guarantees the
-- agreement at *every* input; this guard checks the corner the build can run.
#guard (List.range 8).map (fun n ↦ (List.range 8).map (fun k ↦ pasDecide n k))
  == (List.range 8).map (fun n ↦ (List.range 8).map (fun k ↦ pas n k))

#print axioms pasTotal
#print axioms pasTag

end HAomega
