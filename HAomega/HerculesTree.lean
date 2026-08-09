/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.HydraTree
import HAomega.HerculesAny

/-!
# Hercules wins the general game, on trees — the last coded case study

    herculesTD : ∀h^hyd ∀f^(ℕ→ℕ) ∀g^(ℕ→ℕ). ∃t. deadᴴ?(playAt(g, f, h, t)) = 0

`HerculesAny.lean` proves this over ℕ codes; this is the same theorem with the
battle state a **tree** and its measure a **notation**, so nothing in the
statement, the derivation, or the extracted program is encoded.  With it, every
case study in the development that *can* be de-coded is de-coded: `Goodstein`,
`Hydra` and the two `Hercules` theorems all have typed twins, and Hanoi's move
sequences were functions from the start.

## What it cost

Nothing at the value level.  `playAt` — the any-head surgery move — was already
a function on trees (`HydraSurgery.lean`), and its descent on trees,
`oltE_ordEOfHydra_playAt`, was already proved when the typed hydra layer
landed.  So this file needed one term former (`hcutAtH`), one schema
(`hordCutAtLtH`, discharged by that theorem), and the derivation below, which
is `HerculesAny.lean`'s with `.nat → .hyd` for the state and `.nat → .ord` for
the measure.

## Scope

Fully general: both the head choice `g` and the replication factor `f` are
quantified function variables.  Independence from PA remains unformalized and
unclaimed, as everywhere in this development.
-/

namespace HAomega

/-- The two-strategy battle on trees, as a term:
`rec h (λs ih. cutAtᴴ (g s) (f s) ih) t`. -/
def playAtHT {Γ : List Ty} (G F : Tm Γ (.arrow .nat .nat))
    (H : Tm Γ .hyd) (T : Tm Γ .nat) : Tm Γ .hyd :=
  .recNat H
    (.lam (.lam (.hcutAtH
      (.app ((G.wk).wk) (.var (.there .here)))
      (.app ((F.wk).wk) (.var (.there .here)))
      (.var .here))))
    T

theorem linkR1 {Γ : List Ty} (G F : Tm Γ (.arrow .nat .nat)) (T : Tm Γ .nat) :
    Tm.subst1 ((.lam (.hcutAtH (.app ((G.wk).wk) (.var (.there .here)))
        (.app ((F.wk).wk) (.var (.there .here))) (.var .here))
      : Tm (.nat :: Γ) (.arrow .hyd .hyd))) T
      = .lam (.hcutAtH (.app (G.wk) (T.wk)) (.app (F.wk) (T.wk))
          (.var .here)) := by
  simp only [Tm.subst1, Tm.subst, Sub.one, Sub.ext,
    Tm.wk_subst_ext, Tm.wk_subst_one]
  rfl

theorem linkR2 {Γ : List Ty} (G F : Tm Γ (.arrow .nat .nat))
    (T : Tm Γ .nat) (u : Tm Γ .hyd) :
    Tm.subst1 ((.hcutAtH (.app (G.wk) (T.wk)) (.app (F.wk) (T.wk)) (.var .here)
      : Tm (.hyd :: Γ) .hyd)) u
      = .hcutAtH (.app G T) (.app F T) u := by
  simp only [Tm.subst1, Tm.subst, Sub.one, Tm.wk_subst_one]

/-- One unfolding: `playAt g f h (t+1) = cutAtᴴ(g t, f t, playAt g f h t)`. -/
def playAtHSucc {Γ as : List Ty} {Δ : Ctx Γ as}
    (G F : Tm Γ (.arrow .nat .nat)) (H : Tm Γ .hyd) (T : Tm Γ .nat) :
    Deriv Δ (.eq (playAtHT G F H (.succ T))
      (.hcutAtH (.app G T) (.app F T) (playAtHT G F H T))) := by
  have hb1 := Deriv.convBeta (Δ := Δ) (c := .nat)
    ((.lam (.hcutAtH (.app ((G.wk).wk) (.var (.there .here)))
        (.app ((F.wk).wk) (.var (.there .here))) (.var .here))
      : Tm (.nat :: Γ) (.arrow .hyd .hyd))) T
  rw [linkR1] at hb1
  have hb2 := Deriv.convBeta (Δ := Δ) (c := .hyd)
    ((.hcutAtH (.app (G.wk) (T.wk)) (.app (F.wk) (T.wk)) (.var .here)
      : Tm (.hyd :: Γ) .hyd)) (playAtHT G F H T)
  rw [linkR2] at hb2
  exact Deriv.transE (Deriv.convRecSucc _ _ _)
    (Deriv.transE (Deriv.congFun hb1 (playAtHT G F H T))
      (Deriv.transE hb2 (Deriv.eqRefl _)))

/-- The `tiEps0O` invariant, with both strategies free in the context. -/
abbrev hercAuxT (Γ : List Ty) :
    Formula (.ord :: .arrow .nat .nat :: .arrow .nat .nat :: Γ)
      (.arrow .hyd (.arrow .nat (.arrow .unit (.prod .nat .unit)))) :=
  .all .hyd (.all .nat (.imp
    (.eq (.hordH (playAtHT (.var (.there (.there (.there .here))))
      (.var (.there (.there (.there (.there .here)))))
      (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.ex .nat (.eq (.hleafQ (playAtHT
      (.var (.there (.there (.there (.there .here)))))
      (.var (.there (.there (.there (.there (.there .here))))))
      (.var (.there (.there .here))) (.var .here))) .zero))))

/-- The induction hypothesis, spelled out.  It cannot be an `hercAuxT`
application: with two strategy variables free, the accumulated hypothesis sits
under `atInnerO` *and* two weakenings, so `g` and `f` land at different depths
than the abbrev's shape — the same obstruction `HerculesAny.lean` records. -/
abbrev hercIHT (Γ : List Ty) :
    Formula (.nat :: .hyd :: .ord :: .arrow .nat .nat :: .arrow .nat .nat :: Γ)
      (.arrow .ord (.arrow .unit
        (.arrow .hyd (.arrow .nat (.arrow .unit (.prod .nat .unit)))))) :=
  .all .ord (.imp
    (.eq (.olte (.var .here) (.var (.there (.there (.there .here))))) (.succ .zero))
    (.all .hyd (.all .nat (.imp
      (.eq (.hordH (playAtHT (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.var (.there .here)) (.var .here))) (.var (.there (.there .here))))
      (.ex .nat (.eq (.hleafQ (playAtHT (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.var (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.var (.there (.there .here))) (.var .here))) .zero))))))

/-- The descent branch's context: `hneg :: hx :: IH` over `t::h::x::g::f::Γ`. -/
abbrev hercCtxT (Γ : List Ty) {as : List Ty}
    (Δ : Ctx (.arrow .nat .nat :: .arrow .nat .nat :: Γ) as) :
    Ctx (.nat :: .hyd :: .ord :: .arrow .nat .nat :: .arrow .nat .nat :: Γ)
      ((.arrow .unit .unit) :: .unit ::
       (.arrow .ord (.arrow .unit
         (.arrow .hyd (.arrow .nat (.arrow .unit (.prod .nat .unit)))))) :: as) :=
  .cons ((Formula.eq (.hleafQ (playAtHT (.var (.there (.there (.there .here))))
      (.var (.there (.there (.there (.there .here)))))
      (.var (.there .here)) (.var .here))) .zero).neg)
    (.cons (.eq (.hordH (playAtHT (.var (.there (.there (.there .here))))
        (.var (.there (.there (.there (.there .here)))))
        (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.cons (hercIHT Γ)
    (((Δ.wk).wk).wk)))

/-- **`∀x^ord. AUX(x)`**, by transfinite induction on notations. -/
def hercAuxTD {Γ as : List Ty}
    {Δ : Ctx (.arrow .nat .nat :: .arrow .nat .nat :: Γ) as} :
    Deriv Δ (.all .ord (hercAuxT Γ)) := by
  refine Deriv.tiEps0O ?_
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_))))
  deriv_norm
  refine Deriv.orE (Deriv.eqDec
    (.hleafQ (playAtHT (.var (.there (.there (.there .here))))
      (.var (.there (.there (.there (.there .here)))))
      (.var (.there .here)) (.var .here))) .zero) ?_ ?_
  · refine Deriv.exI (.var .here) ?_
    deriv_norm
    deriv_assumption
  · have hneg : Deriv (hercCtxT Γ Δ)
        ((Formula.eq (.hleafQ (playAtHT (.var (.there (.there (.there .here))))
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there .here)) (.var .here))) .zero).neg) := Deriv.ax
    have hx1 : Deriv (hercCtxT Γ Δ)
        (.eq (.hordH (playAtHT (.var (.there (.there (.there .here))))
            (.var (.there (.there (.there (.there .here)))))
            (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here)))) := Deriv.wk Deriv.ax
    have hIHacc : Deriv (hercCtxT Γ Δ) (hercIHT Γ) := Deriv.wk (Deriv.wk Deriv.ax)
    -- descent: any head, any replication, on trees
    have h2 := Deriv.impE
      (Deriv.hordCutAtLtH
        (.app (.var (.there (.there (.there .here)))) (.var .here))
        (.app (.var (.there (.there (.there (.there .here))))) (.var .here))
        (playAtHT (.var (.there (.there (.there .here))))
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there .here)) (.var .here))) hneg
    -- rewrite the move into the next battle state (a `.hyd`-typed rewrite)
    have h3 := Deriv.eqSubst
      (φ := .eq (.olte (.hordH (.var .here))
        (.hordH (playAtHT (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there (.there (.there .here))))))
          (.var (.there (.there .here))) (.var (.there .here)))))
        (.succ .zero))
      (Deriv.symmE (playAtHSucc (.var (.there (.there (.there .here))))
        (.var (.there (.there (.there (.there .here)))))
        (.var (.there .here)) (.var .here))) h2
    -- rewrite the measure to `x` (an `.ord`-typed rewrite)
    have h4 := Deriv.eqSubst
      (φ := .eq (.olte (.hordH (playAtHT
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there (.there (.there .here))))))
          (.var (.there (.there .here))) (.succ (.var (.there .here)))))
        (.var .here)) (.succ .zero))
      hx1 h3
    have hIH1 := Deriv.allE (τ := .ord)
      (.hordH (playAtHT (.var (.there (.there (.there .here))))
        (.var (.there (.there (.there (.there .here)))))
        (.var (.there .here)) (.succ (.var .here)))) hIHacc
    deriv_norm at hIH1
    have hIH2 := Deriv.impE hIH1 h4
    have hIH3 := Deriv.allE (τ := .hyd) (.var (.there .here)) hIH2
    deriv_norm at hIH3
    have hIH4 := Deriv.allE (τ := .nat) (.succ (.var .here)) hIH3
    deriv_norm at hIH4
    exact Deriv.impE hIH4 (Deriv.eqRefl _)

/-- **Hercules wins the fully general game, with nothing encoded.** -/
def herculesTD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .hyd (.all (.arrow .nat .nat) (.all (.arrow .nat .nat)
      (.ex .nat (.eq (.hleafQ (playAtHT (.var (.there .here))
        (.var (.there (.there .here)))
        (.var (.there (.there (.there .here)))) (.var .here))) .zero))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI ?_))
  have h0 := Deriv.allE (τ := .ord)
    (.hordH (.var (.there (.there .here))))
    (hercAuxTD (Γ := .hyd :: Γ) (Δ := Ctx.wk (Ctx.wk (Ctx.wk Δ))))
  deriv_norm at h0
  have h1 := Deriv.allE (τ := .hyd) (.var (.there (.there .here))) h0
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .nat) .zero h1
  deriv_norm at h2
  refine Deriv.impE h2 ?_
  refine Deriv.eqSubst
    (φ := .eq (.hordH (.var .here))
      (.hordH (.var (.there (.there (.there .here))))))
    (Deriv.symmE (Deriv.convRecZero (.var (.there (.there .here)))
      (.lam (.lam (.hcutAtH
        (.app (.var (.there (.there .here))) (.var (.there .here)))
        (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
        (.var .here)))))) ?_
  deriv_norm
  exact Deriv.eqRefl _

/-- **The extracted program**: battle length on trees, under arbitrary head
and replication strategies. -/
def herculesTX (h : Realizability.Hydra) (f g : Nat → Nat) : Nat :=
  (((((extractClosed (herculesTD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    h) f) g).1

/-- Reference battle on trees: head `g t`, replication `f t` at step `t`. -/
def playAtHRef (g f : Nat → Nat) (h : Realizability.Hydra) :
    Nat → Realizability.Hydra
  | 0 => h
  | t + 1 => playAt (g t) (f t) (playAtHRef g f h t)

open Realizability

-- At the leftmost head and the Kirby–Paris replication schedule this is the
-- ordinary battle, so it must agree with the tree extract of `HydraTree.lean`.
#guard (List.range 4).all fun c ↦
  herculesTX (hydraOf c) (· + 1) (fun _ ↦ 0) == hydraHX (hydraOf c)
-- **Including where the coded extracts cannot go**: code 4 is the published
-- 37-step battle, which `herculesAnyX` (coded) overflows on.
#guard herculesTX (hydraOf 4) (· + 1) (fun _ ↦ 0) == 37
-- Genuinely different head strategies terminate too, and the witness ends the
-- battle in each case.
#guard [isLeafN (playAtHRef (fun _ ↦ 0) (· + 1) (hydraOf 4)
          (herculesTX (hydraOf 4) (· + 1) (fun _ ↦ 0))),
        isLeafN (playAtHRef (· + 1) (fun _ ↦ 2) (hydraOf 3)
          (herculesTX (hydraOf 3) (fun _ ↦ 2) (· + 1))),
        isLeafN (playAtHRef (fun _ ↦ 1) (fun _ ↦ 9) (hydraOf 2)
          (herculesTX (hydraOf 2) (fun _ ↦ 9) (fun _ ↦ 1)))] == [0, 0, 0]

#print axioms hercAuxTD
#print axioms herculesTD
#print axioms herculesTX

end HAomega
