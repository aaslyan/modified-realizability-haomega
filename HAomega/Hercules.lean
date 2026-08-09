/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Hydra

/-!
# Hercules wins against every replication strategy

    herculesD : ∀f^(ℕ→ℕ). ∀h. ∃t. play(f, h, t) = 0

where `play(f, h, t)` iterates the Kirby–Paris move with **replication factor
`f s` at step `s`** — a genuine quantification over strategies, which the
first-order fragment cannot state (no function variables).  `hydraD` is the
special case `f = (· + 1)`, and the `#guard`s below check the extracted
program agrees with `hydraX` at exactly that strategy.

Two design facts make this nearly free:

* **`play` is a term, not a primitive**: `recNat h (λs ih. hcut (f s) ih) t` —
  the recursor plus the existing `hcut`.  No new syntax, no new eval or
  tracking cases.
* **No new import**: `hordCutLt` is already term-general in its replication
  argument, so `hordCutLt (f t) (play f h t)` gives the descent for *any*
  strategy.

## Scope

This quantifies the **replication** strategy; the head choice stays the
value layer's (leftmost), as in the fragment battle.  The fully general
Kirby–Paris theorem — any head, any replication — is derived in
`HerculesAny.lean` on top of the surgery move `hcutAt`
(`HydraSurgery.lean`); this file remains as the single-strategy stepping
stone whose derivation `HerculesAny` transcribes.
-/

namespace HAomega

/-- The strategy-driven battle, as a term: `rec h (λs ih. hcut (f s) ih) t`. -/
def playT {Γ : List Ty} (F : Tm Γ (.arrow .nat .nat)) (H T : Tm Γ .nat) :
    Tm Γ .nat :=
  .recNat H
    (.lam (.lam (.hcut (.app ((F.wk).wk) (.var (.there .here))) (.var .here))))
    T

/-- The `tiEps0` invariant, with the strategy `f` free in the context. -/
abbrev hercAux (Γ : List Ty) : Formula (.nat :: .arrow .nat .nat :: Γ)
    (.arrow .nat (.arrow .nat (.arrow .unit (.prod .nat .unit)))) :=
  .all .nat (.all .nat (.imp
    (.eq (.hord (playT (.var (.there (.there (.there .here))))
      (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.ex .nat (.eq (playT (.var (.there (.there (.there (.there .here)))))
      (.var (.there (.there .here))) (.var .here)) .zero))))

theorem linkP1 {Γ : List Ty} (F : Tm Γ (.arrow .nat .nat)) (T : Tm Γ .nat) :
    Tm.subst1 ((.lam (.hcut (.app ((F.wk).wk) (.var (.there .here))) (.var .here))
      : Tm (.nat :: Γ) (.arrow .nat .nat))) T
      = .lam (.hcut (.app (F.wk) (T.wk)) (.var .here)) := by
  simp only [Tm.subst1, Tm.subst, Sub.one, Sub.ext, 
    Tm.wk_subst_ext, Tm.wk_subst_one]
  rfl

theorem linkP2 {Γ : List Ty} (F : Tm Γ (.arrow .nat .nat)) (T u : Tm Γ .nat) :
    Tm.subst1 ((.hcut (.app (F.wk) (T.wk)) (.var .here) : Tm (.nat :: Γ) .nat)) u
      = .hcut (.app F T) u := by
  simp only [Tm.subst1, Tm.subst, Sub.one, 
    Tm.wk_subst_one]

/-- One unfolding of the battle: `play f h (t+1) = hcut (f t) (play f h t)`. -/
def playSucc {Γ as : List Ty} {Δ : Ctx Γ as}
    (F : Tm Γ (.arrow .nat .nat)) (H T : Tm Γ .nat) :
    Deriv Δ (.eq (playT F H (.succ T)) (.hcut (.app F T) (playT F H T))) := by
  have hb1 := Deriv.convBeta (Δ := Δ) (c := .nat)
    ((.lam (.hcut (.app ((F.wk).wk) (.var (.there .here))) (.var .here))
      : Tm (.nat :: Γ) (.arrow .nat .nat))) T
  rw [linkP1] at hb1
  have hb2 := Deriv.convBeta (Δ := Δ) (c := .nat)
    ((.hcut (.app (F.wk) (T.wk)) (.var .here) : Tm (.nat :: Γ) .nat))
    (playT F H T)
  rw [linkP2] at hb2
  exact Deriv.transE (Deriv.convRecSucc _ _ _)
    (Deriv.transE (Deriv.congFun hb1 (playT F H T))
      (Deriv.transE hb2 (Deriv.eqRefl _)))

/-- **`∀x. AUX(x)`**, by transfinite induction along `≺`. -/
def hercAuxD {Γ as : List Ty} {Δ : Ctx (.arrow .nat .nat :: Γ) as} :
    Deriv Δ (.all .nat (hercAux Γ)) := by
  refine Deriv.tiEps0 ?_
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_))))
  deriv_norm
  refine Deriv.orE (Deriv.eqDec
    (playT (.var (.there (.there (.there .here)))) (.var (.there .here))
      (.var .here)) .zero) ?_ ?_
  · refine Deriv.exI (.var .here) ?_
    deriv_norm
    deriv_assumption
  ·
    have hneg : Deriv (.cons ((Formula.eq
        (playT (.var (.there (.there (.there .here)))) (.var (.there .here))
          (.var .here)) .zero).neg)
        (.cons (.eq (.hord (playT (.var (.there (.there (.there .here))))
            (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here))))
        (.cons (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (.all .nat (.all .nat (.imp
          (.eq (.hord (playT
            (.var (.there (.there (.there (.there (.there (.there .here)))))))
            (.var (.there .here)) (.var .here)))
            (.var (.there (.there .here))))
          (.ex .nat (.eq (playT
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there (.there .here))) (.var .here)) .zero)))))))
        (((Δ.wk).wk).wk))))
        ((Formula.eq (playT (.var (.there (.there (.there .here))))
          (.var (.there .here)) (.var .here)) .zero).neg) := Deriv.ax
    have hx1 : Deriv (.cons ((Formula.eq
        (playT (.var (.there (.there (.there .here)))) (.var (.there .here))
          (.var .here)) .zero).neg)
        (.cons (.eq (.hord (playT (.var (.there (.there (.there .here))))
            (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here))))
        (.cons (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (.all .nat (.all .nat (.imp
          (.eq (.hord (playT
            (.var (.there (.there (.there (.there (.there (.there .here)))))))
            (.var (.there .here)) (.var .here)))
            (.var (.there (.there .here))))
          (.ex .nat (.eq (playT
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there (.there .here))) (.var .here)) .zero)))))))
        (((Δ.wk).wk).wk))))
        (.eq (.hord (playT (.var (.there (.there (.there .here))))
          (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here)))) := Deriv.wk Deriv.ax
    have hIHacc : Deriv (.cons ((Formula.eq
        (playT (.var (.there (.there (.there .here)))) (.var (.there .here))
          (.var .here)) .zero).neg)
        (.cons (.eq (.hord (playT (.var (.there (.there (.there .here))))
            (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here))))
        (.cons (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (.all .nat (.all .nat (.imp
          (.eq (.hord (playT
            (.var (.there (.there (.there (.there (.there (.there .here)))))))
            (.var (.there .here)) (.var .here)))
            (.var (.there (.there .here))))
          (.ex .nat (.eq (playT
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there (.there .here))) (.var .here)) .zero)))))))
        (((Δ.wk).wk).wk))))
        (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (.all .nat (.all .nat (.imp
          (.eq (.hord (playT
            (.var (.there (.there (.there (.there (.there (.there .here)))))))
            (.var (.there .here)) (.var .here)))
            (.var (.there (.there .here))))
          (.ex .nat (.eq (playT
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there (.there .here))) (.var .here)) .zero))))))) := Deriv.wk (Deriv.wk Deriv.ax)
    -- descent: hordCutLt at replication (f t)
    have h2 := Deriv.impE
      (Deriv.hordCutLt
        (.app (.var (.there (.there (.there .here)))) (.var .here))
        (playT (.var (.there (.there (.there .here)))) (.var (.there .here))
          (.var .here))) hneg
    -- rewrite hcut (f t) (play f h t) → play f h (t+1)
    have h3 := Deriv.eqSubst
      (φ := .eq (.prec (.hord (.var .here))
        (.hord (playT (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there .here))) (.var (.there .here)))))
        (.succ .zero))
      (Deriv.symmE (playSucc (.var (.there (.there (.there .here))))
        (.var (.there .here)) (.var .here))) h2
    -- rewrite hord (play f h t) → x
    have h4 := Deriv.eqSubst
      (φ := .eq (.prec (.hord (playT (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there .here))) (.succ (.var (.there .here)))))
        (.var .here)) (.succ .zero))
      hx1 h3
    have hIH1 := Deriv.allE (τ := .nat)
      (.hord (playT (.var (.there (.there (.there .here)))) (.var (.there .here))
        (.succ (.var .here)))) hIHacc
    deriv_norm at hIH1
    have hIH2 := Deriv.impE hIH1 h4
    have hIH3 := Deriv.allE (τ := .nat) (.var (.there .here)) hIH2
    deriv_norm at hIH3
    have hIH4 := Deriv.allE (τ := .nat) (.succ (.var .here)) hIH3
    deriv_norm at hIH4
    exact Deriv.impE hIH4 (Deriv.eqRefl _)

/-- **Hercules wins against every replication strategy** (`∀h ∀f`). -/
def herculesD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all (.arrow .nat .nat) (.ex .nat
      (.eq (playT (.var (.there .here)) (.var (.there (.there .here)))
        (.var .here)) .zero)))) := by
  refine Deriv.allI (Deriv.allI ?_)
  have h0 := Deriv.allE (τ := .nat)
    (.hord (.var (.there .here)))
    (hercAuxD (Γ := .nat :: Γ) (Δ := Ctx.wk (Ctx.wk Δ)))
  deriv_norm at h0
  have h1 := Deriv.allE (τ := .nat) (.var (.there .here)) h0
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .nat) .zero h1
  deriv_norm at h2
  refine Deriv.impE h2 ?_
  refine Deriv.eqSubst
    (φ := .eq (.hord (.var .here)) (.hord (.var (.there (.there .here)))))
    (Deriv.symmE (Deriv.convRecZero (.var (.there .here))
      (.lam (.lam (.hcut
        (.app (.var (.there (.there .here))) (.var (.there .here)))
        (.var .here)))))) ?_
  deriv_norm
  exact Deriv.eqRefl _

/-- **The extracted program**: battle length under an arbitrary strategy. -/
def herculesX (f : Nat → Nat) (h : Nat) : Nat :=
  ((((extractClosed (herculesD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) h) f).1

/-- Reference battle at strategy `f`. -/
def playRef (f : Nat → Nat) (h : Nat) : Nat → Nat
  | 0 => h
  | t + 1 => Realizability.hydraStepN (f t) (playRef f h t)

-- At the fragment's own strategy `f = (·+1)`, the extract agrees with
-- `hydraX`; at other strategies the battles still end, certified by the
-- reference check.
-- At the fragment battle's own strategy the extract agrees with `hydraX` …
#guard [herculesX (· + 1) 0, herculesX (· + 1) 1, herculesX (· + 1) 2]
  == [0, 1, 3]
-- … and certified terminal at other strategies where evaluation is feasible
-- (the coded trees grow doubly-exponentially, so most strategies overflow
-- the interpreter beyond trivial codes — a cost of the coding, not the proof).
#guard [herculesX (fun _ ↦ 1) 0, herculesX (fun _ ↦ 1) 1,
        herculesX (fun _ ↦ 9) 1] == [0, 1, 1]
#guard playRef (· + 1) 2 (herculesX (· + 1) 2) == 0
#guard playRef (fun _ ↦ 9) 1 (herculesX (fun _ ↦ 9) 1) == 0

#print axioms hercAuxD
#print axioms herculesD
#print axioms herculesX

end HAomega
