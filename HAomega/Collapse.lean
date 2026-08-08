/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.HigherType

/-!
# The collapse: what continuity excludes, and what it buys

Two halves, and they are the point of the whole Kleene–Kreisel apparatus.

**What it excludes.**  `∀f. …` ranges over *all* functions `ℕ → ℕ`, and the
Lean function space `(ℕ → ℕ) → ℕ` contains type-2 functionals that inspect
infinitely much of their argument.  `notAllZero` below is one.  It is a
perfectly good element of `PureType 2` — and `extract_continuous2` says **no
derivation extracts to it**.  Without a discontinuous witness the continuity
theorem could be vacuous; this is the proof that it is not.

**What it buys.**  A *continuous* type-2 functional collapses to a **type-1**
object: an associate `a : ℕ → ℕ` that represents it by reading finite prefixes.
That is the sense in which continuity makes higher-type objects countable, and
it is what `Ct 2 = {x | ∃ a, Assoc 1 a x}` says.  For `hiProgram` we get the
associate abstractly from the continuity theorem, and — because the program is
concrete — an explicit computable **modulus** as well.
-/

namespace HAomega

open ContinuousFunctionals

/-! ## A discontinuous type-2 functional -/

open Classical in
/-- `notAllZero α` is `0` when `α` is identically zero and `1` otherwise.

Deciding it requires inspecting *all* of `α`, so it is noncomputable — and, as
proved next, discontinuous. -/
noncomputable def notAllZero (α : ℕ → ℕ) : ℕ := if ∀ n, α n = 0 then 0 else 1

/-- **It is discontinuous.**  At the identically-zero oracle no finite prefix
determines the value: whatever modulus `m` is proposed, the oracle that is `1`
at `m` and `0` elsewhere agrees below `m` yet gives a different answer. -/
theorem not_continuous2_notAllZero : ¬ Continuous2 notAllZero := by
  intro h
  obtain ⟨m, hm⟩ := h (fun _ ↦ 0)
  have hagree : ∀ i < m, (fun _ : ℕ ↦ (0 : ℕ)) i = (fun i ↦ if i = m then 1 else 0) i := by
    intro i hi
    have : i ≠ m := Nat.ne_of_lt hi
    simp [this]
  have hEq := hm (fun i ↦ if i = m then 1 else 0) hagree
  have hzero : notAllZero (fun _ ↦ 0) = 0 := by
    simp [notAllZero]
  have hone : notAllZero (fun i ↦ if i = m then 1 else 0) = 1 := by
    have : ¬ ∀ n, (if n = m then 1 else 0) = 0 := by
      intro hall
      have := hall m
      simp at this
    simp [notAllZero]
  rw [hzero, hone] at hEq
  exact Nat.zero_ne_one hEq

/-- **No derivation extracts to it.**  The content of `extract_continuous2`,
stated as an exclusion. -/
theorem notAllZero_not_extractable
    {φ : Formula [] (.arrow (.arrow .nat .nat) .nat)}
    (D : Deriv Ctx.nil φ) :
    (extract D).eval Env.nil ≠ notAllZero := by
  intro hEq
  exact not_continuous2_notAllZero (hEq ▸ extract_continuous2 D)

/-! ## The collapse of a continuous functional to type 1 -/

/-- **`hiProgram` is a countable (Kleene–Kreisel) functional.** -/
theorem hiProgram_mem_ct2 : hiProgram ∈ Ct 2 :=
  mem_ct_two_iff_continuous2.mpr hiProgram_continuous

/-- **The collapse.**  The type-2 functional is represented by a **type-1**
function — its associate.  This is `Ct 2`'s definition unfolded, and it is what
continuity buys: a higher-type object presented by an `ℕ → ℕ`. -/
theorem hiProgram_has_associate : ∃ a : ℕ → ℕ, Assoc 1 a hiProgram :=
  hiProgram_mem_ct2

/-! ## The modulus, explicitly

The associate above comes from an existential.  For this particular program the
finite information needed is visible: `hiProgram f = fib (f (f 0))` consults `f`
at `0` and at `f 0`, and nowhere else. -/

/-- How much of `f` `hiProgram` reads. -/
def hiModulus (f : Nat → Nat) : Nat := max (f 0) (f (f 0)) + 1

/-- **The explicit modulus is correct**: agreement below it forces agreement of
the answers.  A computable witness for the `∃ n` in `Continuous2`. -/
theorem hiProgram_modulus (f g : Nat → Nat)
    (h : ∀ i < hiModulus f, f i = g i) : hiProgram f = hiProgram g := by
  have h0 : f 0 = g 0 := h 0 (Nat.succ_pos _)
  have h1 : f (f 0) = g (f 0) :=
    h (f 0) (Nat.lt_succ_of_le (Nat.le_max_left _ _))
  have key : f (f 0) = g (g 0) := by rw [h1, h0]
  have unfold : ∀ k : Nat → Nat,
      hiProgram k = (fibT (Γ := [])).eval Env.nil (k (k 0)) := fun _ ↦ rfl
  rw [unfold f, unfold g, key]

#print axioms not_continuous2_notAllZero
#print axioms notAllZero_not_extractable
#print axioms hiProgram_has_associate
#print axioms hiProgram_modulus

end HAomega
