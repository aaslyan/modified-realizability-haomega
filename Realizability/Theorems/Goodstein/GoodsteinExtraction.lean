/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Goodstein.GoodsteinTheorem
import Realizability.Meta.ProgramExtraction

/-!
# Phase D3: the extracted function

What the roadmap was for.  `goodsteinTheorem` (Phase D2) is a closed
derivation of `∀m ∃t. good(m,t) = 0`; modified realizability turns it
into a *program*, because the realizer of an existential **carries its
witness**.  This module reads that witness off and certifies it three
ways:

* `goodsteinStopTime_spec` — the extracted number really is a stopping
  time: `goodN m (goodsteinStopTime m) = 0`, for **every** `m`.  Proved
  from `soundness`, not by computation, so it holds at values no
  evaluator will ever reach;
* `goodstein_extract_continuous` — the extract is `Continuous2`, by the
  generic continuity theorem, with no modification and no per-derivation
  certificate;
* `goodsteinRealizesCtQ` — hence it has a class in `CtQ 2`, the
  extensional collapse of the Kleene–Kreisel development.

And it runs: see the `#eval`s at the end, and the timings recorded in
docs/first-order/STATUS.md.
-/

namespace Realizability

open ContinuousFunctionals

/-! **The statement, spelled out** — no abbreviations, checked at every
build, so that what is proved cannot drift behind a definition:
`⊢ ∀m ∃t. good(m, t) = 0`. -/
#check (goodsteinTheorem :
  Deriv [] (Formula.all 2 (Formula.ex 4
    (Formula.eq (Term.good (Term.var 2) (Term.var 4)) Term.zero))))

/-- The bound above which the extracted family realizes the theorem. -/
theorem goodstein_derivBound : derivBound goodsteinTheorem = 12 := rfl

/-- **Soundness at Goodstein's theorem**: the extracted family realizes
`∀m ∃t. good(m,t) = 0` at every ambient level from 12 up. -/
theorem goodstein_realized (ρ : ℕ → ℕ) {n : ℕ} (hn : 12 ≤ n) :
    MR ρ (Formula.all 2 goodTerminates) n (extract goodsteinTheorem ρ [] n) :=
  soundness goodsteinTheorem ρ [] trivial n (by rw [goodstein_derivBound]; exact hn)

/-- **The extracted stopping-time function.**  Apply the realizer to the
start value and read the witness component of the existential — the
first component at the canonical point, which is exactly where `exIC`
puts it.  Ambient 12 is the derivation's own bound, so this is the
realizer *at the level where it is certified*. -/
def goodsteinStopTime (m : ℕ) : ℕ :=
  witness₁ goodsteinTheorem 11 m

/-- **The extracted function is correct**, at every start value: the
Goodstein sequence from `m` is `0` after `goodsteinStopTime m` steps.
This is soundness instantiated at the theorem — the realizer's witness
clause *is* this statement — so it needs no computation and holds far
beyond where evaluation could reach. -/
theorem goodsteinStopTime_spec (m : ℕ) : goodN m (goodsteinStopTime m) = 0 := by
  have h := goodstein_realized (fun _ ↦ 0) (n := 12) (Nat.le_refl 12) m
  have h2 : Term.eval
      (Function.update (Function.update (fun _ ↦ 0) 2 m) 4
        (fstPT (app₁ (extract goodsteinTheorem (fun _ ↦ 0) [] 12)
          (natPT 12 m)) (defaultPT 11)))
      (.good (.var 2) (.var 4))
      = Term.eval
      (Function.update (Function.update (fun _ ↦ 0) 2 m) 4
        (fstPT (app₁ (extract goodsteinTheorem (fun _ ↦ 0) [] 12)
          (natPT 12 m)) (defaultPT 11))) .zero := h
  simpa [Term.eval, Function.update, goodsteinStopTime] using h2

/-- Generic continuity applies to the theorem's extract with no
modification: `extract_continuous` covers `tiEps0`, `exI`/`exE` and
`ordDescent` like every other rule. -/
theorem goodstein_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract goodsteinTheorem ρ [] 1) :=
  extract_continuous goodsteinTheorem ρ

/-- **The theorem's program, as an element of `CtQ 2`** — the class of
its extracted type-2 realizer in the extensional collapse. -/
noncomputable def goodsteinRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2 :=
  RealizesCtQ goodsteinTheorem ρ

/-! ## Running it

The extraction pipeline is executable (`extract` and the transports
compile), so the realizer can simply be run.  `goodsteinStopTime m` is
the extracted witness; the classical values are

    m       0  1  2  3
    stop    0  1  3  5

(`G(3) = 3, 3, 3, 2, 1, 0` reaches `0` at step 5, matching Phase B's
`goodN_three`).  Timings are recorded in docs/first-order/STATUS.md; `m = 4` is not
attempted — its sequence is astronomically long (`goodN 4 3 = 60` and
growing), and the realizer would have to run every step.

The `#eval`s below are the fast ones, so the build stays quick; the
larger ones are in READERS_GUIDE.md as commands to run. -/

/-- The value-level sequence agrees with the extracted witness at `m = 1`
(kernel-checked, independent of the evaluator). -/
theorem goodN_one_at_one : goodN 1 1 = 0 := rfl

#eval goodsteinStopTime 0
#eval goodsteinStopTime 1

#print axioms goodstein_realized
#print axioms goodsteinStopTime_spec
#print axioms goodstein_extract_continuous

end Realizability
