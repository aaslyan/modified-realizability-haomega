/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Continuity

/-!
# Pascal's triangle mod 2 in HA^ω — the terms, and a design consequence

## What is here

`pasT` computes Pascal mod 2 as a **System T term**, by recursion on the row
carrying the whole row as an object of type `ℕ → ℕ`.  The recursor at a
*function* type is what makes that possible, and it is exactly what the
first-order fragment cannot do — there, `pas` and `xor` are primitive symbols
with four axiom schemas plus a numeral graph.  Here they are definitions.

The `#guard`s below reproduce the Sierpiński gasket.

Also here: the **equality kit**.  `Deriv` has one Leibniz rule (`eqSubst`) and
no symmetry or transitivity; both are *derived* below, which substantiates the
claim that one Leibniz rule replaces the first-order development's ~20
congruence schemas.  Deriving them needs `Tm.subst1_wk` — weakening then
substituting is the identity — which in turn needs the standard
rename/substitution commutation lemmas, all proved here.

## The design consequence, recorded rather than worked around

**Equality at type `0` only means there is no beta-equation at higher type.**

`Formula.eq` takes two terms of type `nat`, so `convBeta` can only reduce a
redex whose *result* is a number.  But `recNat`'s step has type
`ℕ → τ → τ`, so unfolding `s n ih` passes through the intermediate application
`s n`, which lives at `τ → τ`.  For `τ = nat` that is `ℕ → ℕ` — a higher type —
and the object theory cannot state the equation that reduces it.

Consequence: conversion chains reduce fine while they stay at base type
(`parity 0 = 0` and `flip 0 = 1` are derived below, each in one line), but a
chain that must pass through a `recNat` *successor* step stalls.

This is a genuine consequence of the equality decision, not a gap in the
machinery — `soundness` and continuity are unaffected, and the *semantics* of
higher-type equality is available via `eqAt`/`interp_eqAt`.  What is missing is
a **rule**.  Two candidate fixes, both small:

1. a two-argument beta rule
   `(λx.λy. b) u v = b[u,v]` at `nat` result — precisely the shape every
   `recNat` step reduction needs;
2. or a congruence rule connecting `eqAt` at arrow types to application.

Until one is added, `pasTotal` (`∀n∀k. pas n k = 1 ∨ pas n k = 0`) is **not
derivable here**, and it is therefore not claimed.
-/

namespace HAomega


theorem Sub.ext_ren {Γ Δ Θ : List Ty} {σ : Ty} (ρ : Ren Γ Δ) (s : Sub Δ Θ) :
    (fun τ v ↦ Sub.ext (σ := σ) s τ (Ren.ext ρ τ v))
      = Sub.ext (σ := σ) (fun τ v ↦ s τ (ρ τ v)) := by
  funext τ v; cases v <;> rfl

theorem Tm.subst_rename {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ Θ : List Ty} (ρ : Ren Γ Δ) (s : Sub Δ Θ),
      (t.rename ρ).subst s = t.subst (fun σ v ↦ s σ (ρ σ v)) := by
  induction t with
  | var v => intros; rfl
  | lam b ih =>
      intro Δ Θ ρ s
      simp only [Tm.rename, Tm.subst]
      rw [ih ρ.ext s.ext, Sub.ext_ren]
  | app f a ihf iha => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihf, iha]
  | star => intros; rfl
  | pair a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | fst t ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | snd t ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | zero => intros; rfl
  | succ t ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | add a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | prec a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | pred a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | bump a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | good a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | ord a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | hcut a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | hcutAt p a b ihp iha ihb =>
      intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihp, iha, ihb]
  | ezero => intros; rfl
  | orde a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | olte a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | tiRecE sc n ihs ihn =>
      intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihs, ihn]
  | hleaf => intros; rfl
  | hcutH a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | hleafQ a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | hordH a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | hcutAtH p a b ihp iha ihb =>
      intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihp, iha, ihb]
  | hydra a b iha ihb => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, iha, ihb]
  | hord a ih => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ih]
  | tiRec sc n ihs ihn => intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihs, ihn]
  | recNat z sc n ihz ihs ihn =>
      intro Δ Θ ρ s; simp only [Tm.rename, Tm.subst, ihz, ihs, ihn]

theorem Tm.subst_id {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    t.subst (fun _ v ↦ Tm.var v) = t := by
  induction t with
  | var v => rfl
  | lam b ih =>
      simp only [Tm.subst]
      rw [show (Sub.ext (fun σ (v : Var _ σ) ↦ Tm.var v))
          = (fun σ (v : Var _ σ) ↦ Tm.var v) from by funext σ v; cases v <;> rfl, ih]
  | app f a ihf iha => simp only [Tm.subst, ihf, iha]
  | star => rfl
  | pair a b iha ihb => simp only [Tm.subst, iha, ihb]
  | fst t ih => simp only [Tm.subst, ih]
  | snd t ih => simp only [Tm.subst, ih]
  | zero => rfl
  | succ t ih => simp only [Tm.subst, ih]
  | add a b iha ihb => simp only [Tm.subst, iha, ihb]
  | prec a b iha ihb => simp only [Tm.subst, iha, ihb]
  | pred a ih => simp only [Tm.subst, ih]
  | bump a b iha ihb => simp only [Tm.subst, iha, ihb]
  | good a b iha ihb => simp only [Tm.subst, iha, ihb]
  | ord a b iha ihb => simp only [Tm.subst, iha, ihb]
  | hcut a b iha ihb => simp only [Tm.subst, iha, ihb]
  | hcutAt p a b ihp iha ihb => simp only [Tm.subst, ihp, iha, ihb]
  | ezero => rfl
  | orde a b iha ihb => simp only [Tm.subst, iha, ihb]
  | olte a b iha ihb => simp only [Tm.subst, iha, ihb]
  | tiRecE sc n ihs ihn => simp only [Tm.subst, ihs, ihn]
  | hleaf => rfl
  | hcutH a b iha ihb => simp only [Tm.subst, iha, ihb]
  | hleafQ a ih => simp only [Tm.subst, ih]
  | hordH a ih => simp only [Tm.subst, ih]
  | hcutAtH p a b ihp iha ihb => simp only [Tm.subst, ihp, iha, ihb]
  | hydra a b iha ihb => simp only [Tm.subst, iha, ihb]
  | hord a ih => simp only [Tm.subst, ih]
  | tiRec sc n ihs ihn => simp only [Tm.subst, ihs, ihn]
  | recNat z sc n ihz ihs ihn => simp only [Tm.subst, ihz, ihs, ihn]

theorem Tm.subst1_wk {Γ : List Ty} {σ τ : Ty} (t : Tm Γ τ) (u : Tm Γ σ) :
    (t.wk (σ := σ)).subst1 u = t := by
  rw [Tm.wk, Tm.subst1, Tm.subst_rename]
  rw [show (fun τ' (v : Var Γ τ') ↦ Sub.one u τ' (Ren.wk σ τ' v))
      = (fun τ' (v : Var Γ τ') ↦ Tm.var v) from rfl, Tm.subst_id]

#print axioms Tm.subst1_wk
theorem Formula.subst1_eq_var_wk {Γ : List Ty} {τ : Ty} (s u : Tm Γ τ) :
    (Formula.eq (Tm.var .here) (s.wk)).subst1 u = Formula.eq u s := by
  show Formula.eq u ((s.wk).subst1 u) = _
  rw [Tm.subst1_wk]

theorem Formula.subst1_eq_wk_var {Γ : List Ty} {τ : Ty} (s u : Tm Γ τ) :
    (Formula.eq (s.wk) (Tm.var .here)).subst1 u = Formula.eq s u := by
  show Formula.eq ((s.wk).subst1 u) u = _
  rw [Tm.subst1_wk]

def Deriv.symmE {Γ as} {Δ : Ctx Γ as} {τ : Ty} {s t : Tm Γ τ}
    (h : Deriv Δ (.eq s t)) : Deriv Δ (.eq t s) := by
  have key := Deriv.eqSubst (Δ := Δ) (Formula.eq (Tm.var .here) (s.wk)) h
    (by rw [Formula.subst1_eq_var_wk]; exact Deriv.eqRefl s)
  rw [Formula.subst1_eq_var_wk] at key; exact key

def Deriv.transE {Γ as} {Δ : Ctx Γ as} {τ : Ty} {s t u : Tm Γ τ}
    (h1 : Deriv Δ (.eq s t)) (h2 : Deriv Δ (.eq t u)) : Deriv Δ (.eq s u) := by
  have key := Deriv.eqSubst (Δ := Δ) (Formula.eq (s.wk) (Tm.var .here)) h2
    (by rw [Formula.subst1_eq_wk_var]; exact h1)
  rw [Formula.subst1_eq_wk_var] at key; exact key

-- the terms
def flipT {Γ : List Ty} : Tm Γ (.arrow .nat .nat) :=
  .lam (.recNat (.succ .zero) (.lam (.lam .zero)) (.var .here))
def parityT {Γ : List Ty} : Tm Γ (.arrow .nat .nat) :=
  .lam (.recNat .zero (.lam (.lam (.app flipT (.var .here)))) (.var .here))

-- the first conversion chain: parity 0 = 0
example {Γ as} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app parityT .zero) .zero) :=
  Deriv.transE (Deriv.convBeta _ _) (Deriv.convRecZero _ _)

-- and: flip 0 = 1, flip 1 = 0
example {Γ as} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app flipT .zero) (.succ .zero)) :=
  Deriv.transE (Deriv.convBeta _ _) (Deriv.convRecZero _ _)

/-! ## Pascal, and the gasket -/

/-- Exclusive or, as parity of a sum — the first-order development's `xorN`. -/
def xorT {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.lam (.app parityT (.add (.var (.there .here)) (.var .here))))

/-- The step of Pascal's row recursion: given the previous row, build the next.
Named so the unfolding chains below stay readable. -/
def rowStepT {Γ : List Ty} :
    Tm Γ (.arrow .nat (.arrow (.arrow .nat .nat) (.arrow .nat .nat))) :=
  .lam (.lam (.lam (.recNat (.succ .zero)
    (.lam (.lam (.app (.app xorT
        (.app (.var (.there (.there (.there .here)))) (.var (.there .here))))
      (.app (.var (.there (.there (.there .here))))
        (.succ (.var (.there .here)))))))
    (.var .here))))

/-- **Pascal's triangle mod 2**, by recursion on the row at type `ℕ → ℕ`. -/
def pasT {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.recNat flipT rowStepT (.var .here))

/-- The value-level reader. -/
def pas (n k : Nat) : Nat := (pasT (Γ := [])).eval Env.nil n k

-- Rows 0-7 of Pascal mod 2: the Sierpinski gasket.
#guard (List.range 8).map (fun n ↦ (List.range 8).map (fun k ↦ pas n k)) ==
  [[1,0,0,0,0,0,0,0], [1,1,0,0,0,0,0,0], [1,0,1,0,0,0,0,0], [1,1,1,1,0,0,0,0],
   [1,0,0,0,1,0,0,0], [1,1,0,0,1,1,0,0], [1,0,1,0,1,0,1,0], [1,1,1,1,1,1,1,1]]

-- Row 7 is all ones (7 = 0b111, so every C(7,k) is odd); row 6 alternates.
#guard (List.range 8).map (pas 7) == [1,1,1,1,1,1,1,1]
#guard (List.range 8).map (pas 6) == [1,0,1,0,1,0,1,0]

#print axioms Tm.subst1_wk
#print axioms pas

end HAomega
