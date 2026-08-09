/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GoodsteinTyped
import HAomega.Hydra

/-!
# Kirby–Paris on trees: the battle with nothing encoded

    hydraHD : ∀h^hyd. ∃t. deadᴴ?(play(h, t)) = 0

`Hydra.lean` proves this statement over ℕ **codes**: the state is
`encodeH`-of-a-tree and the measure is a code too, and those codes grow
doubly exponentially — which is why the coded extract `hydraX` overflows the
interpreter at hydra codes 4 and 7 (measured, `HAOMEGA_DOSSIER.md` §5).

Here the state is a `Hydra` and the measure is an `Eps0`.  Nothing is encoded
anywhere in the derivation or in the program it extracts to, and the wall
moves: `hydraHX` runs at exactly the inputs that kill `hydraX`, guarded below.

## What it cost

* **One rule**, `hordCutLtH` — the descent, discharged in `soundness` by
  `oltE_ordEOfHydra_step`, which is H7's `play_descends` on trees with no
  coding round trip.  `Hydra.lean`'s coded version needs three (`hordCutLt`
  plus two `hydra` conversions); the battle is a *term* here, as in
  `Hercules.lean`, so the recursor's own conversion rules replace them.
* **No new mathematics.**  Everything transfers along `toCode_ordEOfHydra`.

The death test is `ℕ`-valued (`deadᴴ?`), so the case split reuses the numeric
`eqDec` rather than needing decidable equality at type `.hyd` — the same
device as the coded version's `hydra(h,t) = 0`, which is a numeric test for
exactly the same reason.
-/

namespace HAomega

/-- The battle, as a term: `rec h (λs ih. cutᴴ (S s) ih) t` — replication
factor `s+1` at step `s`, the Kirby–Paris convention `hydraSeqN` uses. -/
def hplayT {Γ : List Ty} (H : Tm Γ .hyd) (T : Tm Γ .nat) : Tm Γ .hyd :=
  .recNat H (.lam (.lam (.hcutH (.succ (.var (.there .here))) (.var .here)))) T

theorem linkH1 {Γ : List Ty} (T : Tm Γ .nat) :
    Tm.subst1 ((.lam (.hcutH (.succ (.var (.there .here))) (.var .here))
      : Tm (.nat :: Γ) (.arrow .hyd .hyd))) T
      = .lam (.hcutH (.succ T.wk) (.var .here)) := by
  simp only [Tm.subst1, Tm.subst, Sub.one, Sub.ext]
  rfl

theorem linkH2 {Γ : List Ty} (T : Tm Γ .nat) (u : Tm Γ .hyd) :
    Tm.subst1 ((.hcutH (.succ T.wk) (.var .here) : Tm (.hyd :: Γ) .hyd)) u
      = .hcutH (.succ T) u := by
  simp only [Tm.subst1, Tm.subst, Sub.one, Tm.wk_subst_one]

/-- One unfolding: `play h (t+1) = cutᴴ(t+1, play h t)`. -/
def hplaySucc {Γ as : List Ty} {Δ : Ctx Γ as} (H : Tm Γ .hyd) (T : Tm Γ .nat) :
    Deriv Δ (.eq (hplayT H (.succ T)) (.hcutH (.succ T) (hplayT H T))) := by
  have hb1 := Deriv.convBeta (Δ := Δ) (c := .nat)
    ((.lam (.hcutH (.succ (.var (.there .here))) (.var .here))
      : Tm (.nat :: Γ) (.arrow .hyd .hyd))) T
  rw [linkH1] at hb1
  have hb2 := Deriv.convBeta (Δ := Δ) (c := .hyd)
    ((.hcutH (.succ T.wk) (.var .here) : Tm (.hyd :: Γ) .hyd)) (hplayT H T)
  rw [linkH2] at hb2
  exact Deriv.transE (Deriv.convRecSucc _ _ _)
    (Deriv.transE (Deriv.congFun hb1 (hplayT H T))
      (Deriv.transE hb2 (Deriv.eqRefl _)))

/-- The `tiEps0O` invariant, with the state a tree and the measure a
notation. -/
abbrev hydAuxH (Γ : List Ty) : Formula (.ord :: Γ)
    (.arrow .hyd (.arrow .nat (.arrow .unit (.prod .nat .unit)))) :=
  .all .hyd (.all .nat (.imp
    (.eq (.hordH (hplayT (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.ex .nat (.eq (.hleafQ (hplayT (.var (.there (.there .here))) (.var .here)))
      .zero))))

/-- The descent branch's context: `hneg :: hx :: IH` over `t::h::x::Γ`. -/
abbrev hydCtxH (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .hyd :: .ord :: Γ)
      ((.arrow .unit .unit) :: .unit ::
       (.arrow .ord (.arrow .unit
         (.arrow .hyd (.arrow .nat (.arrow .unit (.prod .nat .unit)))))) :: as) :=
  .cons ((Formula.eq (.hleafQ (hplayT (.var (.there .here)) (.var .here)))
    .zero).neg)
    (.cons (.eq (.hordH (hplayT (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.cons (.all .ord (.imp
      (.eq (.olte (.var .here) (.var (.there (.there (.there .here)))))
        (.succ .zero))
      (hydAuxH (.nat :: .hyd :: .ord :: Γ))))
    (((Δ.wk).wk).wk)))

/-- **`∀x^ord. AUX(x)`**, by transfinite induction on notations. -/
def hydAuxHD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .ord (hydAuxH Γ)) := by
  refine Deriv.tiEps0O ?_
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_))))
  deriv_norm
  refine Deriv.orE (Deriv.eqDec
    (.hleafQ (hplayT (.var (.there .here)) (.var .here))) .zero) ?_ ?_
  · -- the hydra is dead: the current step is the witness
    refine Deriv.exI (.var .here) ?_
    deriv_norm
    deriv_assumption
  · -- still alive: chop, descend, apply the induction hypothesis
    have hneg : Deriv (hydCtxH Γ Δ)
        ((Formula.eq (.hleafQ (hplayT (.var (.there .here)) (.var .here)))
          .zero).neg) := Deriv.ax
    have hx1 : Deriv (hydCtxH Γ Δ)
        (.eq (.hordH (hplayT (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here)))) := Deriv.wk Deriv.ax
    have hIHacc : Deriv (hydCtxH Γ Δ)
        (.all .ord (.imp
          (.eq (.olte (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (hydAuxH (.nat :: .hyd :: .ord :: Γ)))) := Deriv.wk (Deriv.wk Deriv.ax)
    -- descent: one move strictly lowers the notation
    have h2 := Deriv.impE
      (Deriv.hordCutLtH (.succ (.var .here))
        (hplayT (.var (.there .here)) (.var .here))) hneg
    -- rewrite cutᴴ(t+1, play(h,t)) to play(h,t+1) — a `.hyd`-typed rewrite
    have h3 := Deriv.eqSubst
      (φ := .eq (.olte (.hordH (.var .here))
        (.hordH (hplayT (.var (.there (.there .here))) (.var (.there .here)))))
        (.succ .zero))
      (Deriv.symmE (hplaySucc (.var (.there .here)) (.var .here))) h2
    -- rewrite hordᴴ(play(h,t)) to x — an `.ord`-typed rewrite
    have h4 := Deriv.eqSubst
      (φ := .eq (.olte (.hordH (hplayT (.var (.there (.there .here)))
          (.succ (.var (.there .here))))) (.var .here)) (.succ .zero))
      hx1 h3
    have hIH1 := Deriv.allE (τ := .ord)
      (.hordH (hplayT (.var (.there .here)) (.succ (.var .here)))) hIHacc
    deriv_norm at hIH1
    have hIH2 := Deriv.impE hIH1 h4
    have hIH3 := Deriv.allE (τ := .hyd) (.var (.there .here)) hIH2
    deriv_norm at hIH3
    have hIH4 := Deriv.allE (τ := .nat) (.succ (.var .here)) hIH3
    deriv_norm at hIH4
    exact Deriv.impE hIH4 (Deriv.eqRefl _)

/-- **The Kirby–Paris theorem on trees**: every hydra dies, with the battle
state and its ordinal both structural. -/
def hydraHD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .hyd (.ex .nat
      (.eq (.hleafQ (hplayT (.var (.there .here)) (.var .here))) .zero))) := by
  refine Deriv.allI ?_
  have h0 := Deriv.allE (τ := .ord) (.hordH (.var .here))
    (hydAuxHD (Γ := .hyd :: Γ) (Δ := Ctx.wk Δ))
  deriv_norm at h0
  have h1 := Deriv.allE (τ := .hyd) (.var .here) h0
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .nat) .zero h1
  deriv_norm at h2
  refine Deriv.impE h2 ?_
  refine Deriv.eqSubst
    (φ := .eq (.hordH (.var .here)) (.hordH (.var (.there .here))))
    (Deriv.symmE (Deriv.convRecZero (.var .here)
      (.lam (.lam (.hcutH (.succ (.var (.there .here))) (.var .here)))))) ?_
  deriv_norm
  exact Deriv.eqRefl _

/-- **The extracted battle-length program, on trees.** -/
def hydraHX (h : Realizability.Hydra) : Nat :=
  (((extractClosed (hydraHD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) h).1

/-- The battle itself, for checking the witness really ends it. -/
def hplayRef (h : Realizability.Hydra) : Nat → Realizability.Hydra
  | 0 => h
  | t + 1 => Realizability.hydraStep (t + 1) (hplayRef h t)

open Realizability

-- The published Kirby–Paris lengths, from trees rather than codes.
#guard [hydraHX (hydraOf 0), hydraHX (hydraOf 1), hydraHX (hydraOf 2)]
  == [0, 1, 3]
-- Agrees with the coded extract wherever *that* one can be evaluated.
#guard (List.range 3).all fun c ↦ hydraHX (hydraOf c) == hydraX c
-- **The wall moves.**  `hydraX 4` and `hydraX 7` overflow the interpreter
-- (the doubly-exponential coding, `HAOMEGA_DOSSIER.md` §5); on trees the same
-- battles run, and the witness is certified to end each one.
-- **The wall moves.**  `hydraX 4` and `hydraX 7` overflow the interpreter —
-- the doubly-exponential coding (`HAOMEGA_DOSSIER.md` §5).  On trees the same
-- battles run, and code 4 is the hydra whose **published Kirby–Paris length
-- is 37**: the extracted program computes it, where the coded extract cannot
-- take a single step.
#guard [hydraHX (hydraOf 4), hydraHX (hydraOf 7)] == [37, 13]
-- The witnesses really end those battles.
#guard [isLeafN (hplayRef (hydraOf 4) (hydraHX (hydraOf 4))),
        isLeafN (hplayRef (hydraOf 7) (hydraHX (hydraOf 7)))] == [0, 0]
-- And on a tree written directly, with no code anywhere in sight:
#guard hydraHX (.node (.cons (.node (.cons Hydra.leaf .nil)) .nil)) == 3

#print axioms hydAuxHD
#print axioms hydraHD
#print axioms hydraHX

end HAomega
