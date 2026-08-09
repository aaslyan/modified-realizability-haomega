/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Hercules

/-!
# Hercules wins the fully general game: any head, any replication

    herculesAnyD : ∀h. ∀f^(ℕ→ℕ). ∀g^(ℕ→ℕ). ∃t. playAt(g, f, h, t) = 0

where `playAt(g, f, h, t)` iterates the **any-head** surgery move `hcutAt`
with head position `g s` and replication factor `f s` at step `s`.  Both
players' strategies are quantified: this is the object-theory counterpart of
the first-order H7 `hercules_wins`, which had to remain metatheory there
(no function variables) and which `Hercules.lean` only reached for the
replication half (head choice fixed to the value layer's leftmost).

The derivation is `Hercules.lean`'s line for line — the invariant, the
`tiEps0` descent, the recursor unfolding — with one extra function variable
threaded through: `g` takes `f`'s de Bruijn slot and `f` moves one deeper.
The descent comes from the one new schema `hordCutAtLt`, discharged in
soundness by `olt_ordOfHydraN_playAt` = H7's `play_descends` on codes.

Every position is a legal head (`playAt` takes the position mod the head
count), so the theorem needs no side condition on `g`.
-/

namespace HAomega

/-- The two-strategy battle, as a term:
`rec h (λs ih. hcutAt (g s) (f s) ih) t`. -/
def playAtT {Γ : List Ty} (G F : Tm Γ (.arrow .nat .nat)) (H T : Tm Γ .nat) :
    Tm Γ .nat :=
  .recNat H
    (.lam (.lam (.hcutAt
      (.app ((G.wk).wk) (.var (.there .here)))
      (.app ((F.wk).wk) (.var (.there .here)))
      (.var .here))))
    T

/-- The `tiEps0` invariant, with both strategies `g`, `f` free in the
context. -/
abbrev hercAuxA (Γ : List Ty) :
    Formula (.nat :: .arrow .nat .nat :: .arrow .nat .nat :: Γ)
      (.arrow .nat (.arrow .nat (.arrow .unit (.prod .nat .unit)))) :=
  .all .nat (.all .nat (.imp
    (.eq (.hord (playAtT (.var (.there (.there (.there .here))))
      (.var (.there (.there (.there (.there .here)))))
      (.var (.there .here)) (.var .here)))
      (.var (.there (.there .here))))
    (.ex .nat (.eq (playAtT (.var (.there (.there (.there (.there .here)))))
      (.var (.there (.there (.there (.there (.there .here))))))
      (.var (.there (.there .here))) (.var .here)) .zero))))

theorem linkQ1 {Γ : List Ty} (G F : Tm Γ (.arrow .nat .nat)) (T : Tm Γ .nat) :
    Tm.subst1 ((.lam (.hcutAt (.app ((G.wk).wk) (.var (.there .here)))
        (.app ((F.wk).wk) (.var (.there .here))) (.var .here))
      : Tm (.nat :: Γ) (.arrow .nat .nat))) T
      = .lam (.hcutAt (.app (G.wk) (T.wk)) (.app (F.wk) (T.wk))
          (.var .here)) := by
  simp only [Tm.subst1, Tm.subst, Sub.one, Sub.ext,
    Tm.wk_subst_ext, Tm.wk_subst_one]
  rfl

theorem linkQ2 {Γ : List Ty} (G F : Tm Γ (.arrow .nat .nat)) (T u : Tm Γ .nat) :
    Tm.subst1 ((.hcutAt (.app (G.wk) (T.wk)) (.app (F.wk) (T.wk)) (.var .here)
      : Tm (.nat :: Γ) .nat)) u
      = .hcutAt (.app G T) (.app F T) u := by
  simp only [Tm.subst1, Tm.subst, Sub.one,
    Tm.wk_subst_one]

/-- One unfolding of the battle:
`playAt g f h (t+1) = hcutAt (g t) (f t) (playAt g f h t)`. -/
def playAtSucc {Γ as : List Ty} {Δ : Ctx Γ as}
    (G F : Tm Γ (.arrow .nat .nat)) (H T : Tm Γ .nat) :
    Deriv Δ (.eq (playAtT G F H (.succ T))
      (.hcutAt (.app G T) (.app F T) (playAtT G F H T))) := by
  have hb1 := Deriv.convBeta (Δ := Δ) (c := .nat)
    ((.lam (.hcutAt (.app ((G.wk).wk) (.var (.there .here)))
        (.app ((F.wk).wk) (.var (.there .here))) (.var .here))
      : Tm (.nat :: Γ) (.arrow .nat .nat))) T
  rw [linkQ1] at hb1
  have hb2 := Deriv.convBeta (Δ := Δ) (c := .nat)
    ((.hcutAt (.app (G.wk) (T.wk)) (.app (F.wk) (T.wk)) (.var .here)
      : Tm (.nat :: Γ) .nat))
    (playAtT G F H T)
  rw [linkQ2] at hb2
  exact Deriv.transE (Deriv.convRecSucc _ _ _)
    (Deriv.transE (Deriv.congFun hb1 (playAtT G F H T))
      (Deriv.transE hb2 (Deriv.eqRefl _)))

/-- **`∀x. AUX(x)`**, by transfinite induction along `≺`. -/
def hercAuxAD {Γ as : List Ty}
    {Δ : Ctx (.arrow .nat .nat :: .arrow .nat .nat :: Γ) as} :
    Deriv Δ (.all .nat (hercAuxA Γ)) := by
  refine Deriv.tiEps0 ?_
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_))))
  deriv_norm
  refine Deriv.orE (Deriv.eqDec
    (playAtT (.var (.there (.there (.there .here))))
      (.var (.there (.there (.there (.there .here)))))
      (.var (.there .here)) (.var .here)) .zero) ?_ ?_
  · refine Deriv.exI (.var .here) ?_
    deriv_norm
    deriv_assumption
  ·
    have hneg : Deriv (.cons ((Formula.eq
        (playAtT (.var (.there (.there (.there .here))))
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there .here)) (.var .here)) .zero).neg)
        (.cons (.eq (.hord (playAtT (.var (.there (.there (.there .here))))
            (.var (.there (.there (.there (.there .here)))))
            (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here))))
        (.cons (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (.all .nat (.all .nat (.imp
          (.eq (.hord (playAtT
            (.var (.there (.there (.there (.there (.there (.there .here)))))))
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there .here)) (.var .here)))
            (.var (.there (.there .here))))
          (.ex .nat (.eq (playAtT
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
            (.var (.there (.there .here))) (.var .here)) .zero)))))))
        (((Δ.wk).wk).wk))))
        ((Formula.eq (playAtT (.var (.there (.there (.there .here))))
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there .here)) (.var .here)) .zero).neg) := Deriv.ax
    have hx1 : Deriv (.cons ((Formula.eq
        (playAtT (.var (.there (.there (.there .here))))
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there .here)) (.var .here)) .zero).neg)
        (.cons (.eq (.hord (playAtT (.var (.there (.there (.there .here))))
            (.var (.there (.there (.there (.there .here)))))
            (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here))))
        (.cons (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (.all .nat (.all .nat (.imp
          (.eq (.hord (playAtT
            (.var (.there (.there (.there (.there (.there (.there .here)))))))
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there .here)) (.var .here)))
            (.var (.there (.there .here))))
          (.ex .nat (.eq (playAtT
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
            (.var (.there (.there .here))) (.var .here)) .zero)))))))
        (((Δ.wk).wk).wk))))
        (.eq (.hord (playAtT (.var (.there (.there (.there .here))))
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here)))) := Deriv.wk Deriv.ax
    have hIHacc : Deriv (.cons ((Formula.eq
        (playAtT (.var (.there (.there (.there .here))))
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there .here)) (.var .here)) .zero).neg)
        (.cons (.eq (.hord (playAtT (.var (.there (.there (.there .here))))
            (.var (.there (.there (.there (.there .here)))))
            (.var (.there .here)) (.var .here)))
          (.var (.there (.there .here))))
        (.cons (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (.all .nat (.all .nat (.imp
          (.eq (.hord (playAtT
            (.var (.there (.there (.there (.there (.there (.there .here)))))))
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there .here)) (.var .here)))
            (.var (.there (.there .here))))
          (.ex .nat (.eq (playAtT
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
            (.var (.there (.there .here))) (.var .here)) .zero)))))))
        (((Δ.wk).wk).wk))))
        (.all .nat (.imp
          (.eq (.prec (.var .here) (.var (.there (.there (.there .here)))))
            (.succ .zero))
          (.all .nat (.all .nat (.imp
          (.eq (.hord (playAtT
            (.var (.there (.there (.there (.there (.there (.there .here)))))))
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there .here)) (.var .here)))
            (.var (.there (.there .here))))
          (.ex .nat (.eq (playAtT
            (.var (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.var (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
            (.var (.there (.there .here))) (.var .here)) .zero))))))) :=
      Deriv.wk (Deriv.wk Deriv.ax)
    -- descent: hordCutAtLt at position (g t), replication (f t)
    have h2 := Deriv.impE
      (Deriv.hordCutAtLt
        (.app (.var (.there (.there (.there .here)))) (.var .here))
        (.app (.var (.there (.there (.there (.there .here))))) (.var .here))
        (playAtT (.var (.there (.there (.there .here))))
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there .here)) (.var .here))) hneg
    -- rewrite hcutAt (g t) (f t) (playAt g f h t) → playAt g f h (t+1)
    have h3 := Deriv.eqSubst
      (φ := .eq (.prec (.hord (.var .here))
        (.hord (playAtT (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there (.there (.there .here))))))
          (.var (.there (.there .here))) (.var (.there .here)))))
        (.succ .zero))
      (Deriv.symmE (playAtSucc (.var (.there (.there (.there .here))))
        (.var (.there (.there (.there (.there .here)))))
        (.var (.there .here)) (.var .here))) h2
    -- rewrite hord (playAt g f h t) → x
    have h4 := Deriv.eqSubst
      (φ := .eq (.prec (.hord (playAtT
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there (.there (.there .here))))))
          (.var (.there (.there .here))) (.succ (.var (.there .here)))))
        (.var .here)) (.succ .zero))
      hx1 h3
    have hIH1 := Deriv.allE (τ := .nat)
      (.hord (playAtT (.var (.there (.there (.there .here))))
        (.var (.there (.there (.there (.there .here)))))
        (.var (.there .here)) (.succ (.var .here)))) hIHacc
    deriv_norm at hIH1
    have hIH2 := Deriv.impE hIH1 h4
    have hIH3 := Deriv.allE (τ := .nat) (.var (.there .here)) hIH2
    deriv_norm at hIH3
    have hIH4 := Deriv.allE (τ := .nat) (.succ (.var .here)) hIH3
    deriv_norm at hIH4
    exact Deriv.impE hIH4 (Deriv.eqRefl _)

/-- **Hercules wins the general game** (`∀h ∀f ∀g`): any starting hydra,
any replication strategy, any head strategy. -/
def herculesAnyD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all (.arrow .nat .nat) (.all (.arrow .nat .nat)
      (.ex .nat (.eq (playAtT (.var (.there .here))
        (.var (.there (.there .here)))
        (.var (.there (.there (.there .here)))) (.var .here)) .zero))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI ?_))
  have h0 := Deriv.allE (τ := .nat)
    (.hord (.var (.there (.there .here))))
    (hercAuxAD (Γ := .nat :: Γ) (Δ := Ctx.wk (Ctx.wk (Ctx.wk Δ))))
  deriv_norm at h0
  have h1 := Deriv.allE (τ := .nat) (.var (.there (.there .here))) h0
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .nat) .zero h1
  deriv_norm at h2
  refine Deriv.impE h2 ?_
  refine Deriv.eqSubst
    (φ := .eq (.hord (.var .here))
      (.hord (.var (.there (.there (.there .here))))))
    (Deriv.symmE (Deriv.convRecZero (.var (.there (.there .here)))
      (.lam (.lam (.hcutAt
        (.app (.var (.there (.there .here))) (.var (.there .here)))
        (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
        (.var .here)))))) ?_
  deriv_norm
  exact Deriv.eqRefl _

/-- **The extracted program**: battle length under arbitrary head and
replication strategies. -/
def herculesAnyX (h : Nat) (f g : Nat → Nat) : Nat :=
  (((((extractClosed (herculesAnyD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    h) f) g).1

/-- Reference battle: head `g t`, replication `f t` at step `t`. -/
def playAtRef (g f : Nat → Nat) (h : Nat) : Nat → Nat
  | 0 => h
  | t + 1 => playAtN (g t) (f t) (playAtRef g f h t)

-- At the leftmost head strategy `g = 0` the general extract agrees with the
-- replication-only `herculesX`, hence with `hydraX`.
#guard [herculesAnyX 0 (· + 1) (fun _ ↦ 0),
        herculesAnyX 1 (· + 1) (fun _ ↦ 0),
        herculesAnyX 2 (· + 1) (fun _ ↦ 0)]
  == [herculesX (· + 1) 0, herculesX (· + 1) 1, herculesX (· + 1) 2]
-- Genuinely different head strategies still end, certified terminal by the
-- reference battle (evaluation feasible only at small codes — the coded
-- trees grow doubly exponentially, the same wall as everywhere).
#guard playAtRef (fun _ ↦ 0) (· + 1) 2 (herculesAnyX 2 (· + 1) (fun _ ↦ 0)) == 0
#guard playAtRef (· + 1) (fun _ ↦ 2) 2 (herculesAnyX 2 (fun _ ↦ 2) (· + 1)) == 0
#guard playAtRef (fun _ ↦ 1) (fun _ ↦ 9) 1 (herculesAnyX 1 (fun _ ↦ 9) (fun _ ↦ 1)) == 0

#print axioms hercAuxAD
#print axioms herculesAnyD
#print axioms herculesAnyX

end HAomega
