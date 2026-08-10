/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Mathlib
import HAomega.Rationals

/-!
# Arithmetic for `Q` — the well-definedness lemma and what follows

This is the proof-side companion to `Rationals.lean`, and it exists because
five separate pieces of work were blocked on the same missing fact.

## The constraint does not bind here, and that was the unblock

`Rationals.lean` hand-rolls `Q` because Mathlib's `Rat` arithmetic drags in
`Classical.choice`, and `Tm.eval` must stay `[propext, Quot.sound]`. It is
easy to conclude from that — as the status document did until now — that the
*lemmas* about `Q` must also be choice-free, which would rule out Mathlib and
force either a quotient re-representation or hand-rolled `gcd` theory.

That inference is wrong, and measuring it is what unstuck this. The rule
base's lemmas are consumed by `soundness`, whose footprint already is

    'HAomega.soundness'  [propext, Classical.choice, Quot.sound]

Only the *definitions* reachable from `Tm.eval` must be clean, and `Q.add`,
`Q.mul`, `Q.div` are already measured **axiom-free**. So the lemmas below may
use Mathlib freely, including its `Rat`, and nothing is contaminated by it.

## What was measured on the way

Reported exactly, since the plan branched on it:

    crossTrans  via  mul_left_cancel₀            [propext, Classical.choice, Quot.sound]
    crossTrans  via  Int.eq_of_mul_eq_mul_left   [propext]
    addRespects via  ring                        [propext]

So `ring` is clean; the generic `mul_left_cancel₀` is not, and the
`Int`-specific cancellation is. That mattered while a quotient
re-representation was still on the table — under it, `Quotient.lift`'s proof
argument becomes part of the *definition*, so the respect proofs would have
had to be clean. Once the paragraph above was checked, the quotient stopped
being necessary at all, and `Q`'s representation is unchanged.

## Status of the ring laws

`of_eq_of` is the fact everything wanted: equivalent fractions normalize to
the same `Q`. With it, a ring identity reduces to an `Int` polynomial
identity that `ring` closes — demonstrated below for commutativity of `+`
and `×`.

**They carry a hypothesis, and that is a real limitation, not a formality.**
`Q`'s denominator field is a `Nat` with no positivity invariant, so `⟨5, 0⟩`
inhabits `Q`, and the object language's `∀x^rat` ranges over it. The laws
below therefore assume `den ≠ 0`. Removing the hypothesis needs the invariant
built into the representation — storing `den : Nat` to mean `den + 1`, which
makes positivity structural — and that change ripples through every site that
reads `.num`/`.den`. It is the remaining step before these become `Deriv`
rules, and it is not done here.
-/

namespace HAomega

/-- `Q.of` agrees with Mathlib's normalization. -/
theorem Q.of_eq_mkRat (n : Int) (d : Nat) (hd : d ≠ 0) :
    Q.of n d = ⟨(mkRat n d).num, (mkRat n d).den⟩ := by
  have hg : Nat.gcd n.natAbs d ≠ 0 := Nat.gcd_ne_zero_right hd
  unfold Q.of
  rw [if_neg hd, if_neg hg, Rat.mkRat_def, dif_neg hd, Rat.normalize_eq hd]
  congr 1
  exact Int.tdiv_eq_ediv_of_dvd
    (Int.dvd_natAbs.mp (Int.ofNat_dvd.mpr (Nat.gcd_dvd_left n.natAbs d)))

/-- **Well-definedness** — the lemma the rule base was blocked on: equivalent
fractions normalize to the same `Q`.  Every ring identity below reduces to an
`Int` identity through it. -/
theorem Q.of_eq_of {a c : Int} {b d : Nat} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * (d : Int) = c * (b : Int)) : Q.of a b = Q.of c d := by
  rw [Q.of_eq_mkRat a b hb, Q.of_eq_mkRat c d hd]
  have hm : mkRat a b = mkRat c d := by
    rw [Rat.mkRat_eq_div, Rat.mkRat_eq_div,
      div_eq_div_iff (by exact_mod_cast hb) (by exact_mod_cast hd)]
    exact_mod_cast h
  rw [hm]

/-! ## The laws, on non-degenerate denominators

`Rationals.lean` writes its operations with `Int.add`/`Int.mul` rather than
`+`/`*`, to keep the definitions provably axiom-free; `ring` does not see
those as ring operations, so two `rfl` bridges are needed first.

This file imports `Mathlib` wholesale.  Narrower imports were tried and the
module paths do not exist in the pinned version; since the file is proof-side
only and nothing in `Tm.eval`'s graph reaches it, the cost is build time
rather than trust. -/

theorem intAdd_eq (x y : Int) : Int.add x y = x + y := rfl
theorem intMul_eq (x y : Int) : Int.mul x y = x * y := rfl

theorem Q.add_comm {a b : Q} (ha : a.den ≠ 0) (hb : b.den ≠ 0) :
    Q.add a b = Q.add b a := by
  refine Q.of_eq_of (Nat.mul_ne_zero ha hb) (Nat.mul_ne_zero hb ha) ?_
  simp only [intAdd_eq, intMul_eq]
  push_cast
  ring

theorem Q.mul_comm {a b : Q} (ha : a.den ≠ 0) (hb : b.den ≠ 0) :
    Q.mul a b = Q.mul b a := by
  refine Q.of_eq_of (Nat.mul_ne_zero ha hb) (Nat.mul_ne_zero hb ha) ?_
  simp only [intMul_eq]
  push_cast
  ring

#print axioms Q.of_eq_mkRat
#print axioms Q.of_eq_of
#print axioms Q.add_comm
#print axioms Q.mul_comm

end HAomega
