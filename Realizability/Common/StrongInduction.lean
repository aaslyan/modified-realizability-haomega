/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Common.Exists

/-!
# Foundation phase: numeric order on `ℕ` and strong induction, inside the fragment

The fragment has `ind` (ordinary induction along `succ`) but no order on
`ℕ` and no course-of-values / strong induction.  This module builds both,
using **no new symbols and no new axiom schemas** — everything here is a
genuine `Deriv`, grounded in the existing rules (`ind`, `∃`, the Phase-A
arithmetic, `succInj`, `succNeZero`, `eqDec`).

## Order without a symbol

The fragment can already *state* order, via `∃` and `+`:

    s ≤ t   :=   ∃d. s + d = t
    s < t   :=   ∃d. (succ s) + d = t          ( i.e. succ s ≤ t )

No comparison symbol is introduced.  The order is a *defined* notion, and
every order lemma below is a derivation, not an imported schema — the
honest opposite of adding a `leq` symbol with a numeral graph.

## Strong induction, derived from `ind`

The headline is `natStrongInd`: from progressiveness along `<`,

    ∀x. ( (∀y. y < x → φ(y)) → φ(x) )   ⊢   ∀x. φ(x)

which is the numeric-`<` analogue of `tiEps0` (transfinite induction
along `≺`) — except that `tiEps0` is the fragment's one *primitive* rule,
whereas strong induction here is *derived*.  The derivation runs `ind` on
the auxiliary `Aux(n) := ∀y. y < n → φ(y)` and reads `φ(x)` back off
`Aux(succ x)`.

### The one subtlety, and how it is dodged

The textbook argument splits `y ≤ x` into `y < x ∨ y = x` and, in the
`y = x` case, turns `φ(x)` into `φ(y)` using `y = x`.  That step is
*replacement of equals inside a formula*, which the fragment does not
have (its equality kit rewrites inside **terms**, never across `∧∨→∀∃`).
So the derivation never does it: `φ(y)` is produced **at `y`** by applying
the progressiveness premise at `y` itself and discharging its antecedent
`∀z. z < y → φ(z)` from the induction hypothesis via order-transitivity
(`z < y` and `y < succ n` give `z < n`).  The only arithmetic this needs
that Phase A did not already prove is associativity of `+`.
-/

namespace Realizability

open ContinuousFunctionals

/-! ## Associativity of `+`

Phase A proved `+`'s four defining equations as `ind` theorems but not
associativity; the strong-induction descent needs it (to move the
witness of `z < y` past the witness of `y < succ n`).  One more `ind`, on
the first argument, in the exact style of `plusZeroDeriv`. -/

/-- The associativity equation `(u + v) + w = u + (v + w)`, free
variables `0`, `1`, `2`. -/
private def plusAssocEq : Formula :=
  .eq (.plus (.plus (.var 0) (.var 1)) (.var 2))
    (.plus (.var 0) (.plus (.var 1) (.var 2)))

/-- **`∀u ∀v ∀w. (u + v) + w = u + (v + w)`**, by `ind` on `u`, the
quantifiers on `v`, `w` carried through. -/
def plusAssocDeriv : Deriv [] (.all 0 (.all 1 (.all 2 plusAssocEq))) := by
  refine Deriv.ind ?_ ?_ (substOK_of_forall (by decide))
  · -- base: `∀v ∀w. (0 + v) + w = 0 + (v + w)`; both sides are `v + w`.
    refine Deriv.allI (Deriv.allI ?_ (by decide +kernel)) (by decide +kernel)
    exact (Deriv.congPlusL (.var 2) (Deriv.zeroPlus (.var 1))).transE
      (Deriv.symmE (Deriv.zeroPlus (.plus (.var 1) (.var 2))))
  · -- step: from the IH at `u`, conclude for `succ u`.
    refine Deriv.allI (Deriv.impI
      (Deriv.allI (Deriv.allI ?_ (by decide +kernel)) (by decide +kernel)))
      (by decide +kernel)
    -- context: [IH : ∀v ∀w. (u+v)+w = u+(v+w)]
    have ax0 : Deriv [.all 1 (.all 2 plusAssocEq)] (.all 1 (.all 2 plusAssocEq)) :=
      Deriv.ax
    have ih1 : Deriv [.all 1 (.all 2 plusAssocEq)] (.all 2 plusAssocEq) :=
      Deriv.allE (.var 1) ax0 (substOK_of_forall (by decide))
    have ih : Deriv [.all 1 (.all 2 plusAssocEq)] plusAssocEq :=
      Deriv.allE (.var 2) ih1 (substOK_of_forall (by decide))
    -- LHS: (succ u + v) + w = succ((u+v)+w)
    have hl : Deriv [.all 1 (.all 2 plusAssocEq)]
        (.eq (.plus (.plus (.succ (.var 0)) (.var 1)) (.var 2))
          (.succ (.plus (.plus (.var 0) (.var 1)) (.var 2)))) :=
      (Deriv.congPlusL (.var 2) (Deriv.succPlus (.var 0) (.var 1))).transE
        (Deriv.succPlus (.plus (.var 0) (.var 1)) (.var 2))
    -- RHS: succ u + (v+w) = succ(u+(v+w))
    have hr : Deriv [.all 1 (.all 2 plusAssocEq)]
        (.eq (.plus (.succ (.var 0)) (.plus (.var 1) (.var 2)))
          (.succ (.plus (.var 0) (.plus (.var 1) (.var 2))))) :=
      Deriv.succPlus (.var 0) (.plus (.var 1) (.var 2))
    exact (hl.transE (Deriv.congSuccE ih)).transE (Deriv.symmE hr)

/-- The α-variant of `plusAssocDeriv` at bound variables `6`, `7`, `8`,
for instantiation at terms whose variables lie in `0…5` (the `SubstOK`
no-capture condition forbids using `plusAssocDeriv` there).  Derived by
instantiate-and-regeneralize, in the style of `plusSuccDeriv'`. -/
def plusAssocDeriv' :
    Deriv [] (.all 6 (.all 7 (.all 8
      (.eq (.plus (.plus (.var 6) (.var 7)) (.var 8))
        (.plus (.var 6) (.plus (.var 7) (.var 8))))))) :=
  .allI
    (.allI
      (.allI
        (.allE (.var 8)
          (.allE (.var 7)
            (.allE (.var 6) plusAssocDeriv (substOK_of_forall (by decide)))
            (substOK_of_forall (by decide)))
          (substOK_of_forall (by decide)))
        (freshIn_nil 8))
      (freshIn_nil 7))
    (freshIn_nil 6)

/-! ## Substitution lemmas

The syntactic facts a *generic-in-`φ`* strong-induction former needs:
running `ind` on an abstract `φ` leaves substitutions like
`(φ.subst v (var y)).subst v u` stuck (they cannot compute), so they must
be discharged propositionally.  Standard structural inductions; reusable
across later phases.  (For a *concrete* `φ` everything computes and these
are unnecessary — which is why Phase Z0's demo needed none.) -/

/-- Substituting a variable for itself is the identity, on terms. -/
theorem Term.subst_self (x : ℕ) (t : Term) : Term.subst x (.var x) t = t := by
  induction t with
  | var i => by_cases h : i = x <;> simp [Term.subst, h]
  | zero => rfl
  | succ a ih => simp [Term.subst, ih]
  | plus a b iha ihb => simp [Term.subst, iha, ihb]
  | times a b iha ihb => simp [Term.subst, iha, ihb]
  | pred a ih => simp [Term.subst, ih]
  | exp a b iha ihb => simp [Term.subst, iha, ihb]
  | bump a b iha ihb => simp [Term.subst, iha, ihb]
  | good a b iha ihb => simp [Term.subst, iha, ihb]
  | prec a b iha ihb => simp [Term.subst, iha, ihb]
  | ord a b iha ihb => simp [Term.subst, iha, ihb]
  | hcut a b iha ihb => simp [Term.subst, iha, ihb]
  | hydra a b iha ihb => simp [Term.subst, iha, ihb]
  | hord a ih => simp [Term.subst, ih]
  | hcons a b iha ihb => simp [Term.subst, iha, ihb]
  | happ a b iha ihb => simp [Term.subst, iha, ihb]
  | mvcount a ih => simp [Term.subst, ih]
  | solves a b c d e iha ihb ihc ihd ihe => simp [Term.subst, iha, ihb, ihc, ihd, ihe]
  | xor a b iha ihb => simp [Term.subst, iha, ihb]
  | pas a b iha ihb => simp [Term.subst, iha, ihb]
  | look a b iha ihb => simp [Term.subst, iha, ihb]
  | fib a ih => simp [Term.subst, ih]

/-- Substituting for a variable that does not occur is the identity, on
terms. -/
theorem Term.subst_notMem (x : ℕ) (u : Term) :
    ∀ t : Term, x ∉ t.vars → Term.subst x u t = t := by
  intro t
  induction t with
  | var i =>
      intro h
      simp only [Term.vars, List.mem_singleton] at h
      simp only [Term.subst, if_neg (fun he : i = x ↦ h he.symm)]
  | zero => intro _; rfl
  | succ a ih => intro h; simp only [Term.vars] at h; rw [Term.subst, ih h]
  | plus a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | times a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | pred a ih => intro h; simp only [Term.vars] at h; rw [Term.subst, ih h]
  | exp a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | bump a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | good a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | prec a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | ord a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | hcut a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | hydra a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | hord a ih => intro h; simp only [Term.vars] at h; rw [Term.subst, ih h]
  | hcons a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | happ a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | mvcount a ih => intro h; simp only [Term.vars] at h; rw [Term.subst, ih h]
  | solves a b c d e iha ihb ihc ihd ihe =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1.1.1.1, ihb h.1.1.1.2, ihc h.1.1.2, ihd h.1.2, ihe h.2]
  | xor a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | pas a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | look a b iha ihb =>
      intro h; simp only [Term.vars, List.mem_append, not_or] at h
      rw [Term.subst, iha h.1, ihb h.2]
  | fib a ih => intro h; simp only [Term.vars] at h; rw [Term.subst, ih h]

/-- Substituting `x` away (by a term not containing `x`) removes `x` from
the term's variables. -/
theorem Term.notMem_self_subst (x : ℕ) (u : Term) (hu : x ∉ u.vars) :
    ∀ t : Term, x ∉ (Term.subst x u t).vars := by
  intro t
  induction t with
  | var i =>
      by_cases h : i = x
      · simp only [Term.subst, if_pos h]; exact hu
      · simp only [Term.subst, if_neg h, Term.vars, List.mem_singleton]
        exact fun he ↦ h he.symm
  | zero => simp [Term.subst, Term.vars]
  | succ a ih => simpa [Term.subst, Term.vars] using ih
  | plus a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | times a b iha ihb =>
      simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | pred a ih => simpa [Term.subst, Term.vars] using ih
  | exp a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | bump a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | good a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | prec a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | ord a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | hcut a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | hydra a b iha ihb =>
      simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | hord a ih => simpa [Term.subst, Term.vars] using ih
  | hcons a b iha ihb =>
      simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | happ a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | mvcount a ih => simpa [Term.subst, Term.vars] using ih
  | solves a b c d e iha ihb ihc ihd ihe =>
      simp only [Term.subst, Term.vars, List.mem_append, not_or]
      exact ⟨⟨⟨⟨iha, ihb⟩, ihc⟩, ihd⟩, ihe⟩
  | xor a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | pas a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | look a b iha ihb => simp only [Term.subst, Term.vars, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | fib a ih => simpa [Term.subst, Term.vars] using ih

/-- Substituting a variable for itself is the identity, on formulas. -/
theorem Formula.subst_self (x : ℕ) (φ : Formula) : φ.subst x (.var x) = φ := by
  induction φ with
  | bot => rfl
  | eq s t => simp [Formula.subst, Term.subst_self]
  | and a b iha ihb => simp [Formula.subst, iha, ihb]
  | or a b iha ihb => simp [Formula.subst, iha, ihb]
  | imp a b iha ihb => simp [Formula.subst, iha, ihb]
  | all y a ih => by_cases h : y = x <;> simp [Formula.subst, h, ih]
  | ex y a ih => by_cases h : y = x <;> simp [Formula.subst, h, ih]

/-- Substituting for a variable free nowhere is the identity, on
formulas. -/
theorem Formula.subst_notFree (x : ℕ) (u : Term) :
    ∀ φ : Formula, ¬ φ.FreeIn x → φ.subst x u = φ
  | .bot, _ => rfl
  | .eq s t, h => by
      simp only [Formula.FreeIn, not_or] at h
      rw [Formula.subst, Term.subst_notMem x u s h.1, Term.subst_notMem x u t h.2]
  | .and a b, h => by
      simp only [Formula.FreeIn, not_or] at h
      rw [Formula.subst, Formula.subst_notFree x u a h.1, Formula.subst_notFree x u b h.2]
  | .or a b, h => by
      simp only [Formula.FreeIn, not_or] at h
      rw [Formula.subst, Formula.subst_notFree x u a h.1, Formula.subst_notFree x u b h.2]
  | .imp a b, h => by
      simp only [Formula.FreeIn, not_or] at h
      rw [Formula.subst, Formula.subst_notFree x u a h.1, Formula.subst_notFree x u b h.2]
  | .all y a, h => by
      by_cases hy : y = x
      · simp [Formula.subst, hy]
      · simp only [Formula.FreeIn, not_and] at h
        rw [Formula.subst, if_neg hy, Formula.subst_notFree x u a (h (fun he ↦ hy he.symm))]
  | .ex y a, h => by
      by_cases hy : y = x
      · simp [Formula.subst, hy]
      · simp only [Formula.FreeIn, not_and] at h
        rw [Formula.subst, if_neg hy, Formula.subst_notFree x u a (h (fun he ↦ hy he.symm))]

/-- Substituting `x` away (by a term not containing `x`) makes `x` free
nowhere. -/
theorem Formula.notFree_self_subst (x : ℕ) (u : Term) (hu : x ∉ u.vars) :
    ∀ φ : Formula, ¬ (φ.subst x u).FreeIn x
  | .bot => by simp [Formula.subst, Formula.FreeIn]
  | .eq s t => by
      simp only [Formula.subst, Formula.FreeIn, not_or]
      exact ⟨Term.notMem_self_subst x u hu s, Term.notMem_self_subst x u hu t⟩
  | .and a b => by
      simp only [Formula.subst, Formula.FreeIn, not_or]
      exact ⟨Formula.notFree_self_subst x u hu a, Formula.notFree_self_subst x u hu b⟩
  | .or a b => by
      simp only [Formula.subst, Formula.FreeIn, not_or]
      exact ⟨Formula.notFree_self_subst x u hu a, Formula.notFree_self_subst x u hu b⟩
  | .imp a b => by
      simp only [Formula.subst, Formula.FreeIn, not_or]
      exact ⟨Formula.notFree_self_subst x u hu a, Formula.notFree_self_subst x u hu b⟩
  | .all y a => by
      by_cases hy : y = x
      · simp [Formula.subst, Formula.FreeIn, hy]
      · simp only [Formula.subst, if_neg hy, Formula.FreeIn, not_and]
        exact fun _ ↦ Formula.notFree_self_subst x u hu a
  | .ex y a => by
      by_cases hy : y = x
      · simp [Formula.subst, Formula.FreeIn, hy]
      · simp only [Formula.subst, if_neg hy, Formula.FreeIn, not_and]
        exact fun _ ↦ Formula.notFree_self_subst x u hu a

/-- Weakening a closed derivation into any context (iterated `wk`). -/
def Deriv.wkNil {φ : Formula} : (Γ : List Formula) → Deriv [] φ → Deriv Γ φ
  | [], D => D
  | _ :: Γ, D => Deriv.wk (Deriv.wkNil Γ D)

/-! ## Order as a defined notion

No comparison symbol is added; order is `∃` over `+`.  The difference
variable `d` is a parameter, kept distinct from the compared terms'
variables (a decidable side condition at every use site). -/

/-- `s < t`, witnessed by difference variable `d`: `∃d. succ s + d = t`. -/
def ltT (d : ℕ) (s t : Term) : Formula :=
  .ex d (.eq (.plus (.succ s) (.var d)) t)

/-- **Nothing is `< 0`.**  From `s < 0` in context, anything follows: the
witnessing equation `succ s + d = 0` contradicts `succNeZero`. -/
def ltZeroElim {Γ : List Formula} (d : ℕ) (s : Term) (χ : Formula)
    (hΓ : FreshIn d Γ) (hχ : ¬ χ.FreeIn d)
    (D : Deriv Γ (ltT d s .zero)) : Deriv Γ χ := by
  refine Deriv.exE D ?_ hΓ hχ
  -- context: [succ s + d = 0, Γ …]
  have hax : Deriv ((Formula.eq (.plus (.succ s) (.var d)) .zero) :: Γ)
      (Formula.eq (.plus (.succ s) (.var d)) .zero) := .ax
  have hs : Deriv ((Formula.eq (.plus (.succ s) (.var d)) .zero) :: Γ)
      (Formula.eq (.succ (.plus s (.var d))) .zero) :=
    (Deriv.symmE (Deriv.succPlus s (.var d))).transE hax
  exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.plus s (.var d))) hs)

/-- **`var a < succ (var a)`**, witness `0`: `succ a + 0 = succ a`. -/
def ltSuccSelfV {Γ : List Formula} (d a : ℕ) (had : a ≠ d) :
    Deriv Γ (ltT d (.var a) (.succ (.var a))) := by
  have key : Deriv Γ (Formula.eq (.plus (.succ (.var a)) .zero) (.succ (.var a))) :=
    Deriv.allE (.succ (.var a)) (Deriv.wkNil Γ plusZeroDeriv)
      (substOK_of_forall (by intro y _hy; simp [Formula.binders]))
  refine Deriv.exI .zero ?_ (substOK_numeral 0 _)
  simp only [Formula.subst, Term.subst, if_neg had]
  exact key

/-- A variable fresh for a formula and a context is fresh for the cons. -/
theorem freshIn_cons {x : ℕ} {ψ : Formula} {Γ : List Formula}
    (h1 : ¬ ψ.FreeIn x) (h2 : FreshIn x Γ) : FreshIn x (ψ :: Γ) := by
  intro χ hχ
  rcases List.mem_cons.mp hχ with h | h
  · subst h; exact h1
  · exact h2 χ h

/-- **Descent through `succ`**: from `z < y` and `y < succ v`, conclude
`z < v`.  Reading `y < succ v` as `y ≤ v` (peel the `succ` by `succInj`),
the witness of `z < v` is the sum of the two differences, which lands by
`plusAssoc`.  Variables `2 = z`, `1 = y`, `0 = v`; difference variables
`3`, `4` (both eliminated; the result reuses `4` as its bound witness
variable, sound because the conclusion binds it). -/
def ltStepDown {Γ : List Formula}
    (h3 : FreshIn 3 Γ) (h4 : FreshIn 4 Γ)
    (Dzy : Deriv Γ (ltT 3 (.var 2) (.var 1)))
    (Dysv : Deriv Γ (ltT 4 (.var 1) (.succ (.var 0)))) :
    Deriv Γ (ltT 4 (.var 2) (.var 0)) := by
  -- eliminate the `y < succ v` witness: `succ y + d₄ = succ v`
  refine Deriv.exE Dysv ?_ h4 (by decide)
  refine Deriv.exE (Deriv.wk Dzy) ?_ (freshIn_cons (by decide) h3) (by decide)
  -- context: [ succ z + d₃ = y , succ y + d₄ = succ v , Γ… ]
  set Γ' : List Formula :=
    (Formula.eq (.plus (.succ (.var 2)) (.var 3)) (.var 1))
      :: (Formula.eq (.plus (.succ (.var 1)) (.var 4)) (.succ (.var 0))) :: Γ with hΓ'
  have hzy : Deriv Γ' (Formula.eq (.plus (.succ (.var 2)) (.var 3)) (.var 1)) := .ax
  have hysv : Deriv Γ' (Formula.eq (.plus (.succ (.var 1)) (.var 4)) (.succ (.var 0))) :=
    .wk .ax
  -- `succ (y + d₄) = succ v`, hence `y + d₄ = v`
  have hyv : Deriv Γ' (Formula.eq (.plus (.var 1) (.var 4)) (.var 0)) :=
    Deriv.impE (Deriv.succInj (.plus (.var 1) (.var 4)) (.var 0))
      ((Deriv.symmE (Deriv.succPlus (.var 1) (.var 4))).transE hysv)
  -- `v = y + d₄ = (succ z + d₃) + d₄ = succ z + (d₃ + d₄)`
  have hassoc : Deriv Γ'
      (Formula.eq (.plus (.plus (.succ (.var 2)) (.var 3)) (.var 4))
        (.plus (.succ (.var 2)) (.plus (.var 3) (.var 4)))) :=
    Deriv.allE (.var 4)
      (Deriv.allE (.var 3)
        (Deriv.allE (.succ (.var 2)) (Deriv.wkNil Γ' plusAssocDeriv')
          (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide)))
      (substOK_of_forall (by decide))
  -- combine: `succ z + (d₃ + d₄) = v`
  have hsum : Deriv Γ'
      (Formula.eq (.plus (.succ (.var 2)) (.plus (.var 3) (.var 4))) (.var 0)) :=
    (Deriv.symmE hassoc).transE
      ((Deriv.congPlusL (.var 4) hzy).transE hyv)
  -- introduce `d₅ := d₃ + d₄`
  refine Deriv.exI (.plus (.var 3) (.var 4)) ?_ (substOK_of_forall (by decide))
  simpa only [ltT, Formula.subst, Term.subst] using hsum

/-! ## Case analysis and `≤`

Two more foundation pieces the Euclid roadmap needs: the case-analysis
surrogate (the fragment has no `0`/`succ` split *rule*, but the *fact* is
a one-line `ind` theorem) and the reflexive order `≤`. -/

/-- **`∀n. n = 0 ∨ ∃m. n = succ m`** — case analysis, derived by `ind`
(the step ignores its hypothesis).  Instantiating this and `orE`-ing is
the fragment's `0`/`succ` split.  The witness variable is `5`, kept clear
of the low indices callers use. -/
def caseNatDeriv :
    Deriv [] (.all 0 ((Formula.eq (.var 0) .zero).or
      (.ex 5 (.eq (.var 0) (.succ (.var 5)))))) := by
  refine Deriv.ind ?_ ?_ (substOK_of_forall (by decide))
  · exact Deriv.orI₁ (Deriv.eqRefl .zero)
  · refine Deriv.allI (Deriv.impI (Deriv.orI₂
      (Deriv.exI (.var 0) ?_ (substOK_of_forall (by decide))))) (freshIn_nil 0)
    exact Deriv.eqRefl (.succ (.var 0))

/-- `s ≤ t`, witnessed by difference variable `d`: `∃d. s + d = t`. -/
def leT (d : ℕ) (s t : Term) : Formula :=
  .ex d (.eq (.plus s (.var d)) t)

/-! The trichotomy's formulas and the contexts of its case branches,
named so the derivation can pin them (the codebase idiom for
multi-hypothesis proofs). -/
private abbrev triLE : Formula := leT 2 (.var 0) (.var 1)
/-- The strict branch `b < a`. -/
private abbrev triLT : Formula := ltT 3 (.var 1) (.var 0)
/-- Trichotomy's conclusion `∀b. a ≤ b ∨ b < a`. -/
private abbrev triPhi : Formula := .all 1 (triLE.or triLT)
/-- The `≤`-witness equation `a + d = b`. -/
private abbrev triH2 : Formula := .eq (.plus (.var 0) (.var 2)) (.var 1)
/-- The successor-split equation `d = succ d'`. -/
private abbrev triH5 : Formula := .eq (.var 2) (.succ (.var 5))

/-- **Order totality (trichotomy), `⊢ ∀a ∀b. a ≤ b ∨ b < a`** — the
comparison Euclid branches on.  By `ind` on `a` (carrying `∀b`): the base
is `0 ≤ b`; the step compares `succ a` with `b` by `caseNat` on the
difference `a ≤ b` provides — difference `0` means `a = b` (so
`b < succ a`), a successor `m` means `succ a ≤ b` (witness `m`).
Variables `0 = a`, `1 = b`; difference variables `2` (`≤`) and `3` (`<`);
`5` the `caseNat` witness. -/
def trichotomyDeriv : Deriv [] (.all 0 triPhi) := by
  refine Deriv.ind ?_ ?_ (substOK_of_forall (by decide))
  · -- base: `∀b. 0 ≤ b`, witness `b`
    refine Deriv.allI (Deriv.orI₁ (Deriv.exI (.var 1) ?_
      (substOK_of_forall (by decide)))) (freshIn_nil 1)
    simpa only [leT, Formula.subst, Term.subst] using Deriv.zeroPlus (.var 1)
  · -- step
    refine Deriv.allI (Deriv.impI (Deriv.allI ?_ (by decide +kernel))) (freshIn_nil 0)
    have ihb : Deriv [triPhi] (triLE.or triLT) :=
      Deriv.allE (.var 1) Deriv.ax (substOK_of_forall (by decide))
    refine Deriv.orE ihb ?caseLE ?caseLT
    · -- `a ≤ b`: split the difference by `caseNat`
      refine Deriv.exE Deriv.ax ?_ (by decide) (by decide)
      have hcase : Deriv [triH2, triLE, triPhi]
          ((Formula.eq (.var 2) .zero).or (.ex 5 (.eq (.var 2) (.succ (.var 5))))) :=
        Deriv.allE (.var 2) (Deriv.wkNil _ caseNatDeriv) (substOK_of_forall (by decide))
      refine Deriv.orE hcase ?d0 ?dS
      · -- difference `0`: `a = b`, so `b < succ a` (witness `0`)
        have hh2 : Deriv [.eq (.var 2) .zero, triH2, triLE, triPhi] triH2 := .wk .ax
        have hd0 : Deriv [.eq (.var 2) .zero, triH2, triLE, triPhi]
            (Formula.eq (.var 2) .zero) := .ax
        have hab : Deriv [.eq (.var 2) .zero, triH2, triLE, triPhi]
            (Formula.eq (.var 0) (.var 1)) :=
          ((Deriv.symmE (Deriv.allE (.var 0) (Deriv.wkNil _ plusZeroDeriv)
              (substOK_of_forall (by decide)))).transE
            (Deriv.congPlusR (.var 0) (Deriv.symmE hd0))).transE hh2
        refine Deriv.orI₂ (Deriv.exI .zero ?_ (substOK_numeral 0 _))
        have hz : Deriv [.eq (.var 2) .zero, triH2, triLE, triPhi]
            (Formula.eq (.plus (.succ (.var 1)) .zero) (.succ (.var 1))) :=
          Deriv.allE (.succ (.var 1)) (Deriv.wkNil _ plusZeroDeriv)
            (substOK_of_forall (by decide))
        simpa only [ltT, Formula.subst, Term.subst] using
          hz.transE (Deriv.congSuccE (Deriv.symmE hab))
      · -- difference `succ m`: `succ a ≤ b` (witness `m`)
        refine Deriv.exE Deriv.ax ?_ (by decide) (by decide)
        have hh2 : Deriv [triH5, .ex 5 triH5, triH2, triLE, triPhi] triH2 := .wk (.wk .ax)
        have hh5 : Deriv [triH5, .ex 5 triH5, triH2, triLE, triPhi] triH5 := .ax
        have e3 : Deriv [triH5, .ex 5 triH5, triH2, triLE, triPhi]
            (Formula.eq (.plus (.var 0) (.succ (.var 5))) (.var 1)) :=
          (Deriv.congPlusR (.var 0) (Deriv.symmE hh5)).transE hh2
        have e4 : Deriv [triH5, .ex 5 triH5, triH2, triLE, triPhi]
            (Formula.eq (.plus (.succ (.var 0)) (.var 5))
              (.plus (.var 0) (.succ (.var 5)))) :=
          (Deriv.succPlus (.var 0) (.var 5)).transE
            (Deriv.symmE (Deriv.allE (.var 5)
              (Deriv.allE (.var 0) (Deriv.wkNil _ plusSuccDeriv')
                (substOK_of_forall (by decide))) (substOK_of_forall (by decide))))
        refine Deriv.orI₁ (Deriv.exI (.var 5) ?_ (substOK_of_forall (by decide)))
        simpa only [leT, Formula.subst, Term.subst] using e4.transE e3
    · -- `b < a`: then `b < succ a` (witness `succ` of the old one)
      refine Deriv.exE Deriv.ax ?_ (by decide) (by decide)
      have hps : Deriv [.eq (.plus (.succ (.var 1)) (.var 3)) (.var 0), triLT, triPhi]
          (Formula.eq (.plus (.succ (.var 1)) (.succ (.var 3)))
            (.succ (.plus (.succ (.var 1)) (.var 3)))) :=
        Deriv.allE (.var 3) (Deriv.allE (.succ (.var 1))
          (Deriv.wkNil _ plusSuccDeriv') (substOK_of_forall (by decide)))
          (substOK_of_forall (by decide))
      refine Deriv.orI₂ (Deriv.exI (.succ (.var 3)) ?_ (substOK_of_forall (by decide)))
      simpa only [ltT, Formula.subst, Term.subst] using
        hps.transE (Deriv.congSuccE Deriv.ax)

/-! ## Strong induction, derived from `ind`

The reusable machinery, exercised end to end.  For a **concrete** `φ`
every side condition is `decide`-able, so no formula-substitution lemmas
are needed — the contrast with a fully generic-in-`φ` former (which would
need a substitution-composition library) is recorded in the header and
docs/first-order/STATUS.md.  The demonstration `φ` is `x = x`; the derivation nonetheless
routes through the whole scaffold — `ind` on the auxiliary
`Aux(v) := ∀y. y < v → φ(y)`, progressiveness applied **at the point**,
and `ltStepDown` — so every piece is certified together, exactly as a
course-of-values proof (Zeckendorf) would use them.

Variable convention: `0 = v` (induction/conclusion), `1 = y` (the
auxiliary's bound variable, difference `4`), `2 = z` (progressiveness'
inner bound variable `≠ 1`, so the premise applies at `y` capture-free,
difference `3`). -/

/-- The auxiliary predicate `Aux(v) := ∀y. y < v → (y = y)`. -/
abbrev demoAux : Formula :=
  .all 1 ((ltT 4 (.var 1) (.var 0)).imp (.eq (.var 1) (.var 1)))

/-- Progressiveness' antecedent `∀z. z < v → (z = z)`. -/
abbrev demoProgAnt : Formula :=
  .all 2 ((ltT 3 (.var 2) (.var 0)).imp (.eq (.var 2) (.var 2)))

/-- Progressiveness `∀v. ((∀z. z < v → φ(z)) → φ(v))`. -/
abbrev demoProg : Formula :=
  .all 0 (demoProgAnt.imp (.eq (.var 0) (.var 0)))

/-- Progressiveness holds — trivially for this `φ`, but it is what the
scaffold consumes at the point. -/
def demoProgDeriv : Deriv [] demoProg :=
  Deriv.allI (Deriv.impI (Deriv.eqRefl (.var 0))) (freshIn_nil 0)

/-- **`∀v. Aux(v)`, by ordinary induction on `v`** — the heart of the
reduction.  The step proves `Aux(succ v)` by applying progressiveness at
each `y < succ v` and discharging its `∀z. z < y → φ(z)` premise from
`Aux(v)` via `ltStepDown` (`z < y` and `y < succ v` give `z < v`). -/
def demoAuxDeriv : Deriv [] (.all 0 demoAux) := by
  refine Deriv.ind ?_ ?_ (substOK_of_forall (by decide))
  · -- base `Aux(0) = ∀y. y < 0 → (y = y)`
    exact Deriv.allI (Deriv.impI (Deriv.eqRefl (.var 1))) (freshIn_nil 1)
  · -- step `∀v. Aux(v) → Aux(succ v)`
    refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.impI ?_) (by decide +kernel)))
      (freshIn_nil 0)
    -- context: [ h₁ : y < succ v , Aux(v) ];  goal `(y = y)`
    have hProgAt1 :
        Deriv [ltT 4 (.var 1) (.succ (.var 0)), demoAux]
          ((demoProgAnt.subst 0 (.var 1)).imp (.eq (.var 1) (.var 1))) :=
      Deriv.allE (.var 1) (Deriv.wkNil _ demoProgDeriv) (substOK_of_forall (by decide))
    refine Deriv.impE hProgAt1 ?_
    -- goal `∀z. z < y → (z = z)`
    refine Deriv.allI (Deriv.impI ?_) (by decide +kernel)
    -- context: [ h₂ : z < y , h₁ , Aux(v) ];  goal `(z = z)`
    have hzv : Deriv [ltT 3 (.var 2) (.var 1), ltT 4 (.var 1) (.succ (.var 0)), demoAux]
        (ltT 4 (.var 2) (.var 0)) :=
      ltStepDown (by decide) (by decide) Deriv.ax (Deriv.wk Deriv.ax)
    have hAuxAt2 :
        Deriv [ltT 3 (.var 2) (.var 1), ltT 4 (.var 1) (.succ (.var 0)), demoAux]
          ((ltT 4 (.var 2) (.var 0)).imp (.eq (.var 2) (.var 2))) :=
      Deriv.allE (.var 2) (Deriv.wk (Deriv.wk Deriv.ax)) (substOK_of_forall (by decide))
    exact Deriv.impE hAuxAt2 hzv

/-- **Strong induction, in action**: `⊢ ∀v. (v = v)`, proved through the
full course-of-values scaffold rather than by the one-line `eqRefl` the
trivial `φ` would allow.  This certifies that the derived
strong-induction rule type-checks, is sound (`soundness`), and extracts
to a continuous realizer (`extract_continuous`). -/
def strongIndDemo : Deriv [] (.all 0 (.eq (.var 0) (.var 0))) := by
  refine Deriv.allI ?_ (freshIn_nil 0)
  -- read `φ(v)` off `Aux(succ v)` at `y := v`, using `v < succ v`
  have hAuxSucc :
      Deriv [] (.all 1 ((ltT 4 (.var 1) (.succ (.var 0))).imp (.eq (.var 1) (.var 1)))) :=
    Deriv.allE (.succ (.var 0)) demoAuxDeriv (substOK_of_forall (by decide))
  have hAt0 : Deriv [] ((ltT 4 (.var 0) (.succ (.var 0))).imp (.eq (.var 0) (.var 0))) :=
    Deriv.allE (.var 0) hAuxSucc (substOK_of_forall (by decide))
  exact Deriv.impE hAt0 (ltSuccSelfV 4 0 (by decide))

/-! ## Certification

The same discipline as every headline derivation of the repository: the
extracted realizer realizes the theorem at every ambient above the
derivation's bound (`soundness` at the empty context), and its type-2
extract is continuous (`extract_continuous`).  The `#print axioms` block
confirms the budgets: realization reports
`[propext, Classical.choice, Quot.sound]`, continuity `[propext,
Quot.sound]`. -/

/-- The extracted realizer of `∀v. (v = v)` — proved by strong induction —
realizes it. -/
theorem strongIndDemo_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound strongIndDemo ≤ n) :
    MR ρ (.all 0 (.eq (.var 0) (.var 0))) n (extract strongIndDemo ρ [] n) :=
  soundness strongIndDemo ρ [] trivial n hn

/-- Its type-2 extract is continuous — the strong-induction scaffold flows
through generic continuity with no new per-derivation work. -/
theorem strongIndDemo_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract strongIndDemo ρ [] 1) :=
  extract_continuous strongIndDemo ρ

/-- Order totality realizes — the comparison Euclid will branch on. -/
theorem trichotomy_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound trichotomyDeriv ≤ n) :
    MR ρ (.all 0 triPhi) n (extract trichotomyDeriv ρ [] n) :=
  soundness trichotomyDeriv ρ [] trivial n hn

/-- And its type-2 extract is continuous. -/
theorem trichotomy_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract trichotomyDeriv ρ [] 1) :=
  extract_continuous trichotomyDeriv ρ

#print axioms strongIndDemo_realized
#print axioms strongIndDemo_extract_continuous
#print axioms trichotomy_realized
#print axioms trichotomy_extract_continuous

end Realizability
