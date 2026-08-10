/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Collapse

/-!
# Moduli of continuity, computed rather than asserted

`Continuity.lean` proves every extracted realizer continuous, which at type 2
says: the program consults only finitely much of its functional input. The
statement is an existential,
\[
  \forall \alpha,\ \exists n,\ \forall \beta,\ (\forall i < n,\ \alpha i =
  \beta i) \to F\,\alpha = F\,\beta ,
\]
and an existential is not a program. This file replaces it, for the programs
that admit it, by a *computed* bound.

## The predicate

`HasMod F m` is that existential with the witness supplied: `m` is a function,
so the bound may depend on the oracle, and `hasMod_contAt` recovers the
original statement. Everything else here is an algebra for building `m`
compositionally — constants, post-composition, binary operations, and the one
case that actually consults the oracle, `hasMod_query`.

## Why the bound must be a function, not a number

One might hope to Skolemize the existential to a single number. `no_constant_modulus`
below proves that impossible for a program already in the development: for
every candidate `n` there are oracles agreeing below `n` on which the extracted
type-2 Fibonacci returns different answers. The modulus is necessarily
oracle-dependent, which is why `m : (ℕ → ℕ) → ℕ` and why the existential cannot
be discharged by choice without losing computability.

## Scope: what this does not do

This automates the *construction* of moduli, not a metatheorem. Extraction is
not proved to yield a modulus for every derivation, and two obstructions
explain why that is a research problem rather than an oversight.

* **At arrow types a single number is not enough.** A modulus for a family of
  *functions* would have to bound the oracle information needed uniformly in
  the argument, and the identity family `α ↦ α` has no such bound. The general
  statement therefore needs a modulus whose *type* is computed from the finite
  type — in effect a Kleene associate — and constructing associates is exactly
  what `Continuity.lean`'s logical relation was designed to avoid.
* **`tiRec` has no compositional modulus.** For `recNat` a bound follows from
  the step's bounds and the (finite) recursion depth. For transfinite
  recursion the value at `x` may consult the values at *every* `y ≺ x`, and a
  notation can have infinitely many `≺`-predecessors, so there is no finite
  maximum to take. Continuity still holds there — for each fixed oracle the
  descending chain is finite — but the bound is not given by a formula in the
  subterms' bounds. This is the same boundary the certified Haskell emission
  meets, reached from a different direction.
-/

namespace HAomega

open ContinuousFunctionals

/-! ## The predicate, and the bridge to `Continuous2` -/

/-- **`m` is a modulus for `F`**: oracles agreeing below `m f` give the same
answer. The witness for the existential in `ContAt`/`Continuous2`. -/
def HasMod {X : Type} (F : (ℕ → ℕ) → X) (m : (ℕ → ℕ) → ℕ) : Prop :=
  ∀ f g : ℕ → ℕ, (∀ i < m f, f i = g i) → F f = F g

/-- A computed modulus gives continuity in the sense `Continuity.lean` uses. -/
theorem HasMod.contAt {X : Type} {F : (ℕ → ℕ) → X} {m : (ℕ → ℕ) → ℕ}
    (h : HasMod F m) : ContAt X F :=
  fun α ↦ ⟨m α, fun β hβ ↦ h α β hβ⟩

/-- At `ℕ` that is exactly the vendored notion. -/
theorem HasMod.continuous2 {F : (ℕ → ℕ) → ℕ} {m : (ℕ → ℕ) → ℕ}
    (h : HasMod F m) : Continuous2 F :=
  h.contAt

/-! ## The algebra -/

theorem hasMod_const {X : Type} (c : X) : HasMod (fun _ ↦ c) (fun _ ↦ 0) :=
  fun _ _ _ ↦ rfl

/-- Any weaker bound is still a bound. -/
theorem HasMod.mono {X : Type} {F : (ℕ → ℕ) → X} {m m' : (ℕ → ℕ) → ℕ}
    (h : HasMod F m) (hle : ∀ f, m f ≤ m' f) : HasMod F m' :=
  fun f g hfg ↦ h f g fun i hi ↦ hfg i (Nat.lt_of_lt_of_le hi (hle f))

/-- Post-composition costs nothing: the outer operation does not consult the
oracle. -/
theorem HasMod.comp {X Y : Type} {F : (ℕ → ℕ) → X} {m : (ℕ → ℕ) → ℕ}
    (op : X → Y) (h : HasMod F m) : HasMod (fun f ↦ op (F f)) m :=
  fun f g hfg ↦ congrArg op (h f g hfg)

/-- Two subcomputations: take the larger bound. -/
theorem HasMod.binop {X Y Z : Type} {F : (ℕ → ℕ) → X} {G : (ℕ → ℕ) → Y}
    {mF mG : (ℕ → ℕ) → ℕ} (op : X → Y → Z)
    (hF : HasMod F mF) (hG : HasMod G mG) :
    HasMod (fun f ↦ op (F f) (G f)) (fun f ↦ max (mF f) (mG f)) := by
  intro f g hfg
  have h1 := hF f g fun i hi ↦ hfg i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
  have h2 := hG f g fun i hi ↦ hfg i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))
  show op (F f) (G f) = op (F g) (G g)
  rw [h1, h2]

/-- **The only clause that touches the oracle.** To know `f (Z f)` you need
enough of `f` to compute the query point, and then `f` at that point. -/
theorem hasMod_query {Z : (ℕ → ℕ) → ℕ} {mZ : (ℕ → ℕ) → ℕ} (hZ : HasMod Z mZ) :
    HasMod (fun f ↦ f (Z f)) (fun f ↦ max (mZ f) (Z f + 1)) := by
  intro f g hfg
  have hq : Z f = Z g :=
    hZ f g fun i hi ↦ hfg i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
  have hv : f (Z f) = g (Z f) :=
    hfg (Z f) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
  show f (Z f) = g (Z g)
  rw [hv, hq]

/-! ## Worked automatically: the type-2 Fibonacci

`hiProgram f = \fib(f(f\,0))` queries the oracle at `0` and at `f 0`, and the
toolkit derives that from the term's shape rather than from an argument about
this particular program. -/

/-- The modulus the algebra computes. -/
def hiModulusAuto (f : Nat → Nat) : Nat := max 1 (f 0 + 1)

theorem hiProgram_hasMod : HasMod hiProgram hiModulusAuto := by
  have h0 : HasMod (fun _ : ℕ → ℕ ↦ (0 : ℕ)) (fun _ ↦ 0) := hasMod_const 0
  have h1 : HasMod (fun f : ℕ → ℕ ↦ f 0) (fun _ ↦ 1) :=
    (hasMod_query h0).mono (fun _ ↦ Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  have h2 : HasMod (fun f : ℕ → ℕ ↦ f (f 0)) (fun f ↦ max 1 (f 0 + 1)) :=
    hasMod_query h1
  exact HasMod.comp (fun n ↦ (fibT (Γ := [])).eval Env.nil n) h2

/-- **The computed bound is correct, and tighter than the hand-written one.**
`hiModulus` was derived by inspecting this program; the algebra beats it
without looking at it. -/
theorem hiModulusAuto_le (f : Nat → Nat) : hiModulusAuto f ≤ hiModulus f := by
  show max 1 (f 0 + 1) ≤ max (f 0) (f (f 0)) + 1
  omega

/-- Continuity of the type-2 program, now with a computed witness rather than
an existential. -/
theorem hiProgram_continuous_auto : Continuous2 hiProgram :=
  hiProgram_hasMod.continuous2

/-! ## Why the bound has to depend on the oracle -/

/-- **No constant modulus exists**, even for this one program. For every
candidate `n` there are oracles agreeing below `n` that the program separates,
so the existential in `Continuous2` cannot be Skolemized to a number --- which
is why `HasMod` takes a *function*, and why discharging the existential by
choice would give something that no longer computes. -/
theorem no_constant_modulus :
    ¬ ∃ n : Nat, ∀ f g : Nat → Nat,
        (∀ i < n, f i = g i) → hiProgram f = hiProgram g := by
  rintro ⟨n, h⟩
  -- a bound of `n` is also a bound of `n+1`, so we may assume it is positive
  have h' : ∀ f g : Nat → Nat, (∀ i < n + 1, f i = g i) → hiProgram f = hiProgram g :=
    fun f g hfg ↦ h f g fun i hi ↦ hfg i (Nat.lt_succ_of_lt hi)
  -- two oracles agreeing everywhere below `n+1`, differing only at `n+1`
  have hagree : ∀ i < n + 1,
      (if i = n + 1 then 0 else n + 1) = (if i = n + 1 then 1 else n + 1) := by
    intro i hi
    have : i ≠ n + 1 := by omega
    simp [this]
  have key := h' (fun i ↦ if i = n + 1 then 0 else n + 1)
                 (fun i ↦ if i = n + 1 then 1 else n + 1) hagree
  -- each program queries at 0, gets n+1, then queries at n+1 and gets 0 / 1
  have unfold : ∀ k : Nat → Nat,
      hiProgram k = (fibT (Γ := [])).eval Env.nil (k (k 0)) := fun _ ↦ rfl
  have hne : (0 : Nat) ≠ n + 1 := by omega
  have e0 : (fibT (Γ := [])).eval Env.nil 0 = 0 := rfl
  have e1 : (fibT (Γ := [])).eval Env.nil 1 = 1 := rfl
  rw [unfold, unfold] at key
  simp only [if_neg hne, if_true] at key
  rw [e0, e1] at key
  exact absurd key (by omega)

-- The computed modulus really is one, at concrete oracles.
#guard hiModulusAuto (· + 5) == 6
#guard hiModulusAuto (fun _ ↦ 30) == 31
#guard (hiModulus (· + 5), hiModulusAuto (· + 5)) == (11, 6)

#print axioms hiProgram_hasMod
#print axioms no_constant_modulus

end HAomega
