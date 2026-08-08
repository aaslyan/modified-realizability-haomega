/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Continuity
import HAomega.Fib

/-!
# A higher-type theorem, its extracted program, and its continuity

`Fib.lean`'s theorem is `∀n^ℕ. ∃y. y = fib n` — type 1: the realizer takes a
*number*.  Continuity has nothing to say about it.

Here the quantifier ranges over a **function**:

    ∀f^(ℕ→ℕ). ∃y^ℕ. y = fib (f (f 0))

The realizer therefore takes a function argument, so it is a **type-2
functional**, and the continuity theorem applies to it: the answer depends on
only finitely much of `f`.  This is the shape the whole Kleene–Kreisel apparatus
exists for, and the first-order fragment cannot even state it — it has no
function variables.
-/

namespace HAomega

/-- `∀f^(ℕ→ℕ). ∃y. y = fib (f (f 0))`. -/
def hiSpec : Formula [] (.arrow (.arrow .nat .nat) (.prod .nat .unit)) :=
  .all (.arrow .nat .nat) (.ex .nat
    (.eq (.var .here)
      (.app fibT (.app (.var (.there .here))
        (.app (.var (.there .here)) .zero)))))

/-- The derivation. -/
def hiDeriv : Deriv Ctx.nil hiSpec := by
  refine Deriv.allI ?_
  exact Deriv.exI (.app fibT (.app (.var .here) (.app (.var .here) .zero)))
    (Deriv.eqRefl _)

/-- The extracted realizer: a closed System T term of **type 2**. -/
def hiRealizer : Tm [] (.arrow (.arrow .nat .nat) (.prod .nat .unit)) :=
  extractClosed hiDeriv

/-- The extracted **program**: a genuine type-2 functional `(ℕ→ℕ) → ℕ`. -/
def hiProgram (f : Nat → Nat) : Nat := (hiRealizer.eval Env.nil f).1

/-! ## It runs, on function arguments -/

#guard hiProgram (fun n ↦ n + 1) == 1        -- f (f 0) = 2, fib 2 = 1
#guard hiProgram (fun n ↦ n + 5) == 55       -- f (f 0) = 10, fib 10 = 55
#guard hiProgram (fun _ ↦ 30) == 832040      -- fib 30
#guard hiProgram (fun n ↦ 2 * n + 7) == 10946 -- f 0 = 7, f 7 = 21, fib 21 = 10946

/-! ## It is a continuous functional

`extract_tracked` gives tracking at the realizer's type; instantiating the
oracle at the identity and projecting the witness gives continuity in the
vendored `Continuous2` sense — the result depends on a finite prefix of `f`. -/

/-- **The extracted higher-type program is continuous.** -/
theorem hiProgram_continuous : ContinuousFunctionals.Continuous2 hiProgram :=
  (extract_tracked hiDeriv (fun α ↦ α) (fun _ hZ ↦ continuous2_eval hZ)).1

/-! ## It is readable -/

-- the realizer's type: (ℕ→ℕ) → (ℕ × 1)
#eval (Ty.arrow (.arrow .nat .nat) (.prod .nat .unit)).str
-- the extracted program, contentless parts elided
#eval hiRealizer.pretty' 0

#print axioms hiRealizer
#print axioms hiProgram_continuous

end HAomega
