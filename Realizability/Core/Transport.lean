/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Core.ModifiedRealizes

/-!
# Formula-indexed level transports

The infrastructure identified in docs/first-order/STATUS.md as the sole blocker for
extraction: transports `liftR φ` / `dropR φ` moving realizers one
ambient level up or down, defined by **mutual recursion on the
formula** — the generic `up`/`down` maps do *not* preserve `MR` at
implications, so the transport must follow the formula's structure
(atoms: generic; `∧`/`∨`: componentwise with a tag split; `→`/`∀`: the
contravariant sandwich `lift (F) = abs₁ (lift ∘ app₁ F ∘ drop)`).

This is the pure-type incarnation of "every finite type is a retract of
a pure type": the price of drawing realizers from the pure hierarchy
only, and reusable infrastructure for the parent project's deferred
arbitrary-finite-types chapter.

Preservation (`MR_liftR_dropR`) is one mutual induction on the formula,
both directions at once (implication's contravariance needs them
simultaneously), under the side condition `lvl φ ≤ m` — the drop
direction is genuinely false below the formula's level, where the
implication clause degenerates.

`liftToAmb` iterates the lift along `m ≤ n`, and `famOf` packages a
single realizer into the bounded family (`FR`) that extraction's
binder-cases need: this closes exactly the "binders provide one
ambient, bodies consume several" gap.
-/

namespace Realizability

open ContinuousFunctionals

@[simp] theorem natPT_apply {n : ℕ} (k : ℕ) (z : PureType n) :
    natPT (n + 1) k z = k := rfl

mutual

/-- Transport a realizer one ambient level up, following the formula. -/
def liftR : (φ : Formula) → {m : ℕ} →
    PureType (m + 1) → PureType (m + 2)
  | .bot, m, x => up (m + 1) x
  | .eq _ _, m, x => up (m + 1) x
  | .and φ ψ, _, x =>
      pairPT (liftR φ (fstPT x)) (liftR ψ (sndPT x))
  | .or φ ψ, m, x =>
      if fstPT x (defaultPT m) = 0 then
        pairPT (fun _ ↦ (0 : ℕ)) (liftR φ (sndPT x))
      else
        pairPT (fun _ ↦ (1 : ℕ)) (liftR ψ (sndPT x))
  | .imp φ ψ, 0, _ => defaultPT 2
  | .imp φ ψ, m' + 1, F =>
      abs₁ (fun x ↦ liftR ψ (app₁ F (dropR φ x)))
  | .all _ φ, 0, _ => defaultPT 2
  | .all _ φ, m' + 1, F =>
      abs₁ (fun x ↦ liftR φ (app₁ F (natPT (m' + 1) (x (defaultPT (m' + 1))))))
  | .ex _ φ, m, x =>
      pairPT (natPT (m + 2) (fstPT x (defaultPT m))) (liftR φ (sndPT x))

/-- Transport a realizer one ambient level down, following the formula. -/
def dropR : (φ : Formula) → {m : ℕ} →
    PureType (m + 2) → PureType (m + 1)
  | .bot, m, y => down (m + 1) y
  | .eq _ _, m, y => down (m + 1) y
  | .and φ ψ, _, y =>
      pairPT (dropR φ (fstPT y)) (dropR ψ (sndPT y))
  | .or φ ψ, m, y =>
      if fstPT y (defaultPT (m + 1)) = 0 then
        pairPT (fun _ ↦ (0 : ℕ)) (dropR φ (sndPT y))
      else
        pairPT (fun _ ↦ (1 : ℕ)) (dropR ψ (sndPT y))
  | .imp φ ψ, 0, _ => defaultPT 1
  | .imp φ ψ, m' + 1, H =>
      abs₁ (fun x ↦ dropR ψ (app₁ H (liftR φ x)))
  | .all _ φ, 0, _ => defaultPT 1
  | .all _ φ, m' + 1, H =>
      abs₁ (fun x ↦ dropR φ (app₁ H (natPT (m' + 2) (x (defaultPT m')))))
  | .ex _ φ, m, y =>
      pairPT (natPT (m + 1) (fstPT y (defaultPT (m + 1)))) (dropR φ (sndPT y))

end

/-- The transports at an existential, as a rewriting rule: package the
witness (read at the canonical point) with the transported payload. -/
theorem liftR_ex (y : ℕ) (φ : Formula) {m : ℕ} (x : PureType (m + 1)) :
    liftR (.ex y φ) x
      = pairPT (natPT (m + 2) (fstPT x (defaultPT m))) (liftR φ (sndPT x)) :=
  rfl

theorem dropR_ex (y : ℕ) (φ : Formula) {m : ℕ} (z : PureType (m + 2)) :
    dropR (.ex y φ) z
      = pairPT (natPT (m + 1) (fstPT z (defaultPT (m + 1))))
          (dropR φ (sndPT z)) :=
  rfl

/-- **Preservation of realizability under the transports**, both
directions in one mutual induction, above the formula's level. -/
theorem MR_liftR_dropR :
    ∀ (φ : Formula) (ρ : ℕ → ℕ) (m : ℕ), lvl φ ≤ m →
      (∀ x : PureType (m + 1), MR ρ φ m x → MR ρ φ (m + 1) (liftR φ x)) ∧
      (∀ y : PureType (m + 2), MR ρ φ (m + 1) y → MR ρ φ m (dropR φ y)) := by
  intro φ
  induction φ with
  | bot =>
    intro ρ m _
    exact ⟨fun x hx ↦ hx.elim, fun y hy ↦ hy.elim⟩
  | eq s t =>
    intro ρ m _
    exact ⟨fun x hx ↦ hx, fun y hy ↦ hy⟩
  | and φ ψ ihφ ihψ =>
    intro ρ m hm
    have hφ : lvl φ ≤ m := le_trans (le_max_left _ _) hm
    have hψ : lvl ψ ≤ m := le_trans (le_max_right _ _) hm
    constructor
    · rintro x ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show MR ρ φ (m + 1) (fstPT (pairPT _ _))
        rw [fstPT_pairPT]
        exact (ihφ ρ m hφ).1 _ h1
      · show MR ρ ψ (m + 1) (sndPT (pairPT _ _))
        rw [sndPT_pairPT]
        exact (ihψ ρ m hψ).1 _ h2
    · rintro y ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show MR ρ φ m (fstPT (pairPT _ _))
        rw [fstPT_pairPT]
        exact (ihφ ρ m hφ).2 _ h1
      · show MR ρ ψ m (sndPT (pairPT _ _))
        rw [sndPT_pairPT]
        exact (ihψ ρ m hψ).2 _ h2
  | or φ ψ ihφ ihψ =>
    intro ρ m hm
    have hφ : lvl φ ≤ m := le_trans (le_max_left _ _) hm
    have hψ : lvl ψ ≤ m := le_trans (le_max_right _ _) hm
    constructor
    · rintro x (⟨htag, hp⟩ | ⟨htag, hp⟩)
      · show MR ρ (φ.or ψ) (m + 1) (liftR (φ.or ψ) x)
        show MR ρ (φ.or ψ) (m + 1)
          (if fstPT x (defaultPT m) = 0 then _ else _)
        rw [if_pos htag]
        left
        refine ⟨?_, ?_⟩
        · rw [fstPT_pairPT]
        · rw [sndPT_pairPT]
          exact (ihφ ρ m hφ).1 _ hp
      · show MR ρ (φ.or ψ) (m + 1)
          (if fstPT x (defaultPT m) = 0 then _ else _)
        rw [if_neg htag]
        right
        refine ⟨?_, ?_⟩
        · rw [fstPT_pairPT]
          exact one_ne_zero
        · rw [sndPT_pairPT]
          exact (ihψ ρ m hψ).1 _ hp
    · rintro y (⟨htag, hp⟩ | ⟨htag, hp⟩)
      · show MR ρ (φ.or ψ) m
          (if fstPT y (defaultPT (m + 1)) = 0 then _ else _)
        rw [if_pos htag]
        left
        refine ⟨?_, ?_⟩
        · rw [fstPT_pairPT]
        · rw [sndPT_pairPT]
          exact (ihφ ρ m hφ).2 _ hp
      · show MR ρ (φ.or ψ) m
          (if fstPT y (defaultPT (m + 1)) = 0 then _ else _)
        rw [if_neg htag]
        right
        refine ⟨?_, ?_⟩
        · rw [fstPT_pairPT]
          exact one_ne_zero
        · rw [sndPT_pairPT]
          exact (ihψ ρ m hψ).2 _ hp
  | imp φ ψ ihφ ihψ =>
    intro ρ m hm
    cases m with
    | zero =>
      exact absurd hm (by simp only [lvl]; omega)
    | succ m' =>
      have hmax : max (lvl φ) (lvl ψ) ≤ m' := by
        have h1 : max (lvl φ) (lvl ψ) + 1 ≤ m' + 1 := hm
        omega
      have hφ : lvl φ ≤ m' := le_trans (le_max_left _ _) hmax
      have hψ : lvl ψ ≤ m' := le_trans (le_max_right _ _) hmax
      constructor
      · intro F hF x hx
        show MR ρ ψ (m' + 1)
          (app₁ (abs₁ fun z ↦ liftR ψ (app₁ F (dropR φ z))) x)
        rw [app₁_abs₁]
        exact (ihψ ρ m' hψ).1 _ (hF _ ((ihφ ρ m' hφ).2 _ hx))
      · intro H hH x hx
        show MR ρ ψ m'
          (app₁ (abs₁ fun z ↦ dropR ψ (app₁ H (liftR φ z))) x)
        rw [app₁_abs₁]
        exact (ihψ ρ m' hψ).2 _ (hH _ ((ihφ ρ m' hφ).1 _ hx))
  | ex y φ ih =>
    intro ρ m hm
    have hφ : lvl φ ≤ m := hm
    constructor
    · intro x hx
      show MR (Function.update ρ y
        (fstPT (liftR (.ex y φ) x) (defaultPT (m + 1)))) φ (m + 1)
        (sndPT (liftR (.ex y φ) x))
      rw [liftR_ex, fstPT_pairPT, sndPT_pairPT]
      exact (ih (Function.update ρ y (fstPT x (defaultPT m))) m hφ).1 _ hx
    · intro z hz
      show MR (Function.update ρ y
        (fstPT (dropR (.ex y φ) z) (defaultPT m))) φ m
        (sndPT (dropR (.ex y φ) z))
      rw [dropR_ex, fstPT_pairPT, sndPT_pairPT]
      exact (ih (Function.update ρ y (fstPT z (defaultPT (m + 1)))) m hφ).2 _ hz
  | all y φ ih =>
    intro ρ m hm
    cases m with
    | zero =>
      exact absurd hm (by simp only [lvl]; omega)
    | succ m' =>
      have hφ : lvl φ ≤ m' := by
        have h1 : lvl φ + 1 ≤ m' + 1 := hm
        omega
      constructor
      · intro F hF k
        show MR (Function.update ρ y k) φ (m' + 1)
          (app₁ (abs₁ fun z ↦ liftR φ
            (app₁ F (natPT (m' + 1) (z (defaultPT (m' + 1))))))
            (natPT (m' + 2) k))
        rw [app₁_abs₁]
        show MR (Function.update ρ y k) φ (m' + 1)
          (liftR φ (app₁ F (natPT (m' + 1)
            (natPT (m' + 2) k (defaultPT (m' + 1))))))
        rw [show natPT (m' + 2) k (defaultPT (m' + 1)) = k from rfl]
        exact (ih (Function.update ρ y k) m' hφ).1 _ (hF k)
      · intro H hH k
        show MR (Function.update ρ y k) φ m'
          (app₁ (abs₁ fun z ↦ dropR φ
            (app₁ H (natPT (m' + 2) (z (defaultPT m')))))
            (natPT (m' + 1) k))
        rw [app₁_abs₁]
        show MR (Function.update ρ y k) φ m'
          (dropR φ (app₁ H (natPT (m' + 2)
            (natPT (m' + 1) k (defaultPT m')))))
        rw [show natPT (m' + 1) k (defaultPT m') = k from rfl]
        exact (ih (Function.update ρ y k) m' hφ).2 _ (hH k)

/-- Iterated lift: `k` ambient levels up. -/
def liftIter (φ : Formula) : (k : ℕ) → {m : ℕ} →
    PureType (m + 1) → PureType (m + k + 1)
  | 0, _, x => x
  | k + 1, _, x => liftR φ (liftIter φ k x)

/-- Iterated lifting preserves realizability above the formula's level. -/
theorem MR_liftIter (φ : Formula) (ρ : ℕ → ℕ) {m : ℕ}
    (hlvl : lvl φ ≤ m) (k : ℕ) (x : PureType (m + 1))
    (hx : MR ρ φ m x) : MR ρ φ (m + k) (liftIter φ k x) := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    show MR ρ φ (m + k + 1) (liftR φ (liftIter φ k x))
    exact (MR_liftR_dropR φ ρ (m + k) (le_trans hlvl (Nat.le_add_right m k))).1
      _ ih

/-- Iterated drop: `k` ambient levels down. -/
def dropIter (φ : Formula) : (k : ℕ) → {m : ℕ} →
    PureType (m + k + 1) → PureType (m + 1)
  | 0, _, x => x
  | k + 1, m, x => dropIter φ k (dropR φ (m := m + k) x)

/-- Iterated dropping preserves realizability above the formula's
level. -/
theorem MR_dropIter (φ : Formula) (ρ : ℕ → ℕ) {m : ℕ}
    (hlvl : lvl φ ≤ m) (k : ℕ) (x : PureType (m + k + 1))
    (hx : MR ρ φ (m + k) x) : MR ρ φ m (dropIter φ k x) := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    show MR ρ φ m (dropIter φ k (dropR φ x))
    exact ih _ ((MR_liftR_dropR φ ρ (m + k)
      (le_trans hlvl (Nat.le_add_right m k))).2 _ hx)

/-- Realizability transports along equalities of the ambient level. -/
theorem MR_cast {ρ : ℕ → ℕ} {φ : Formula} {a b : ℕ} (e : a = b)
    {x : PureType (a + 1)} (hx : MR ρ φ a x) :
    MR ρ φ b (e ▸ x) := by
  cases e
  exact hx

/-- The family generated by a single realizer: iterated lifts above the
base ambient, iterated drops between the formula's level and the base,
junk below the formula's level (never consulted). -/
def famOf (φ : Formula) {m : ℕ} (x : PureType (m + 1)) :
    (n : ℕ) → PureType (n + 1) :=
  fun n ↦
    if h : m ≤ n then
      (Nat.add_sub_cancel' h) ▸ liftIter φ (n - m) x
    else
      dropIter φ (m - n)
        ((Nat.add_sub_cancel' (le_of_not_ge h)).symm ▸ x)

/-- Family-realization above the formula's level: the shape in which
extraction carries hypotheses. -/
def FR (ρ : ℕ → ℕ) (φ : Formula)
    (f : (n : ℕ) → PureType (n + 1)) : Prop :=
  ∀ n, lvl φ ≤ n → MR ρ φ n (f n)

/-- A single realizer above the formula's level generates a realizing
family — the device that lets a binder's one-ambient realizer serve a
body using it at many ambients, in both directions. -/
theorem FR_famOf (φ : Formula) (ρ : ℕ → ℕ) {m : ℕ} (hlvl : lvl φ ≤ m)
    (x : PureType (m + 1)) (hx : MR ρ φ m x) :
    FR ρ φ (famOf φ x) := by
  intro n hn
  show MR ρ φ n (if h : m ≤ n then
      (Nat.add_sub_cancel' h) ▸ liftIter φ (n - m) x
    else
      dropIter φ (m - n)
        ((Nat.add_sub_cancel' (le_of_not_ge h)).symm ▸ x))
  by_cases h : m ≤ n
  · rw [dif_pos h]
    exact MR_cast (Nat.add_sub_cancel' h)
      (MR_liftIter φ ρ hlvl (n - m) x hx)
  · rw [dif_neg h]
    exact MR_dropIter φ ρ hn (m - n) _
      (MR_cast (Nat.add_sub_cancel' (le_of_not_ge h)).symm hx)

end Realizability
