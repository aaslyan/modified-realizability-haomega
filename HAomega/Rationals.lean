/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Ordinals.Epsilon0

/-!
# A hand-rolled rational layer

Groundwork for constructive analysis, and a measurement that constrains it.
This is the *stating* representation; `Dyadics.lean` is the computing one, and
`Syntax.lean` carries both as base types `rat` and `dyad`.

## The measurement: it cannot be Mathlib's `Rat`

## Why not `Rat`

Measured, not assumed:

    #print axioms (fun a b : Rat => a + b)        [propext, Classical.choice, Quot.sound]
    #print axioms (fun a b : Rat => Rat.add a b)  [propext, Classical.choice, Quot.sound]

Addition, multiplication, subtraction and division on `Rat` all depend on
`Classical.choice` once Mathlib is in scope. `Tm.eval` is required to report
`[propext, Quot.sound]` — that is the invariant behind "every extracted
program that runs is choice-free", which is the development's headline audit
claim — so a rational base type evaluated by `Rat.add` would break it.

This is the same trap `Epsilon0.lean` documents for `Nat.pair`, and it gets
the same answer: hand-roll the layer over primitives that are *measured*
axiom-free. `Int.add`, `Int.mul`, `Int.sub`, `Int.tdiv`, `Int.natAbs`,
`Nat.gcd`, `Nat.div` and the decidable comparisons all are; the `#print
axioms` block at the foot of this file re-checks it at every build.

## This representation, and why it may not be the right one

`Q` is a numerator and a **positive** denominator, kept in lowest terms by the
smart constructor `Q.of`. Normalization is what would make structural equality
the right notion: `Formula.eq` at a rational base type unfolds to equality of
the interpreting values, so `1/2` and `2/4` must be the *same* record, not
merely equivalent ones. Division by zero yields `0`, as it does in `Rat` and
for the same reason — totality keeps the evaluator free of side conditions.

**Settled: both.** `Q` states and `Dyadics.lean`'s `D` computes, and the
object language carries the base types `rat` and `dyad` together with the
bridge `dtoq`. The division of labour is that approximations are always *at* a
precision `2⁻ⁿ`, which dyadics represent directly, while the theorem being
approximated reads naturally over general fractions.

What this file settles regardless of that choice is the *constraint*: whatever
representation is chosen must be built from measured-axiom-free primitives,
because Mathlib's rational arithmetic is not.
-/

namespace HAomega

/-- A rational: numerator, and a denominator kept positive and coprime to it
by `Q.of`.

The denominator is stored as its **predecessor**, so positivity is structural:
there is no `Q` whose denominator is zero, and hence no degenerate value for
the arithmetic laws to exclude.  That matters because the object language's
`∀x^rat` ranges over *every* inhabitant of this type — with a bare `den : Nat`
it would range over `⟨5,0⟩` too, and every ring law would need a side
condition. -/
structure Q where
  num : Int
  denPred : Nat
  deriving DecidableEq, Repr, BEq

namespace Q

/-- The denominator.  Positive by construction. -/
def den (q : Q) : Nat := q.denPred + 1

@[simp] theorem den_ne_zero (q : Q) : q.den ≠ 0 := Nat.succ_ne_zero _

/-- Zero, and the canonical shape of every degenerate case. -/
def zero : Q := ⟨0, 0⟩

/-- The one representation, and hence the meaning of structural equality.
Named `of` rather than `mk`, which the structure already claims. -/
def of (n : Int) (d : Nat) : Q :=
  if d = 0 then zero
  else
    let g := Nat.gcd n.natAbs d
    if g = 0 then zero else ⟨Int.tdiv n (Int.ofNat g), d / g - 1⟩

def ofInt (n : Int) : Q := ⟨n, 0⟩
def ofNat (n : Nat) : Q := ⟨Int.ofNat n, 0⟩

def add (a b : Q) : Q :=
  of (Int.add (Int.mul a.num (Int.ofNat b.den)) (Int.mul b.num (Int.ofNat a.den)))
     (a.den * b.den)

def neg (a : Q) : Q := ⟨Int.neg a.num, a.denPred⟩

def sub (a b : Q) : Q := add a (neg b)

def mul (a b : Q) : Q := of (Int.mul a.num b.num) (a.den * b.den)

/-- Division, total: `a / 0 = 0`.  Dividing by a negative moves the sign to
the numerator, so the result stays in canonical form. -/
def div (a b : Q) : Q :=
  if b.num = 0 then zero
  else
    let q := of (Int.mul a.num (Int.ofNat b.den)) (a.den * b.num.natAbs)
    if b.num < 0 then neg q else q

/-- `|a|`. -/
def abs (a : Q) : Q := if a.num < 0 then neg a else a

/-- Strict order, as a numeral — the shape the object language branches on,
matching `prec` and `olte`. -/
def ltN (a b : Q) : Nat :=
  if Int.mul a.num (Int.ofNat b.den) < Int.mul b.num (Int.ofNat a.den) then 1 else 0

/-! ## The one arithmetic law provable without a gcd theory

`sub a a = zero` needs **no** normalization reasoning: the numerator collapses
to `0` before `of` ever looks at a gcd, and `Nat.gcd 0 d = d` then short-circuits
the whole normalization.  So this law — unlike the ring laws, which genuinely
need uniqueness of normal forms — is provable here, in the core, with no
Mathlib and no gcd machinery. -/

theorem sub_self (a : Q) : sub a a = zero := by
  have hd : a.den * a.den ≠ 0 := Nat.mul_ne_zero a.den_ne_zero a.den_ne_zero
  have hnum : Int.add (Int.mul a.num (Int.ofNat a.den))
      (Int.mul (Int.neg a.num) (Int.ofNat a.den)) = 0 := by
    show a.num * (Int.ofNat a.den) + (-a.num) * (Int.ofNat a.den) = 0
    rw [Int.neg_mul, Int.add_right_neg]
  show of (Int.add (Int.mul a.num (Int.ofNat a.den))
      (Int.mul (Int.neg a.num) (Int.ofNat a.den))) (a.den * a.den) = zero
  rw [hnum]
  unfold of
  rw [if_neg hd]
  simp only [Int.natAbs_zero, Nat.gcd_zero_left]
  rw [if_neg hd, Nat.div_self (Nat.pos_of_ne_zero hd)]
  have htd : Int.tdiv 0 (Int.ofNat (a.den * a.den)) = 0 := by
    simp [Int.tdiv, Nat.zero_div]
  rw [htd]
  rfl

/-- `1/(m+1)` in normal form.  Degenerate for the same reason as `sub_self`,
one step later: the gcd is `Nat.gcd 1 _`, which is `1`, so `of` normalizes by
dividing through by `1`. -/
theorem recip_eq (m : Nat) : div (ofNat 1) (ofNat (m + 1)) = ⟨1, m⟩ := by
  have hne : Int.ofNat (m + 1) ≠ 0 := fun h ↦ Nat.succ_ne_zero m (Int.ofNat.inj h)
  have hnn : ¬ (Int.ofNat (m + 1) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
  have habs : (Int.ofNat (m + 1)).natAbs = m + 1 := rfl
  have hmul : (Int.ofNat 1).mul (Int.ofNat (0 + 1)) = Int.ofNat 1 := rfl
  have habs1 : (Int.ofNat 1).natAbs = 1 := rfl
  simp only [div, ofNat, den, of, if_neg hne, if_neg hnn, habs, hmul, habs1,
    Nat.zero_add, Nat.one_mul, Nat.gcd_one_left, Nat.div_one]
  rw [if_neg (Nat.succ_ne_zero m), if_neg (by decide : ¬ ((1 : Nat) = 0))]
  congr 1

/-- **`0 < 1/(m+1)`** — the positivity the constant real's Cauchy bound needs.
Only the *sign* of the numerator matters, so this needs no more normalization
than `recip_eq` already gives. -/
theorem ltN_zero_recip (m : Nat) :
    ltN (ofNat 0) (div (ofNat 1) (ofNat (m + 1))) = 1 := by
  rw [recip_eq]
  unfold ltN
  have h1 : Int.mul (ofNat 0).num (Int.ofNat (Q.mk 1 m).den) = 0 := Int.zero_mul _
  have h2 : Int.mul (Q.mk 1 m).num (Int.ofNat (ofNat 0).den) = 1 := Int.one_mul _
  rw [h1, h2, if_pos (by decide : (0 : Int) < 1)]

#print axioms recip_eq
#print axioms ltN_zero_recip
#print axioms sub_self

/-- Equality test, as a numeral. -/
def eqN (a b : Q) : Nat := if a = b then 1 else 0

end Q

-- The layer computes, and normalizes: one representative per rational.
#guard Q.of 2 4 == Q.of 1 2
#guard Q.add (Q.of 1 2) (Q.of 1 3) == Q.of 5 6
#guard Q.sub (Q.of 1 2) (Q.of 1 2) == Q.zero
#guard Q.mul (Q.of 2 3) (Q.of 3 4) == Q.of 1 2
#guard Q.div (Q.of 1 2) (Q.of 1 4) == Q.ofNat 2
#guard Q.div (Q.ofNat 1) Q.zero == Q.zero
#guard Q.abs (Q.sub (Q.ofNat 1) (Q.ofNat 5)) == Q.ofNat 4
#guard (Q.ltN (Q.of 1 3) (Q.of 1 2), Q.ltN (Q.of 1 2) (Q.of 1 3)) == (1, 0)
#guard Q.eqN (Q.of 2 4) (Q.of 1 2) == 1
-- negative denominators and signs land in the canonical form
#guard Q.of (-2) 4 == Q.of (-1) 2
#guard Q.div (Q.ofNat 1) (Q.neg (Q.ofNat 2)) == Q.of (-1) 2
-- halving, the operation the analysis roadmap needs for `2⁻ⁿ`
#guard (List.range 4).map (fun n ↦ Nat.rec (Q.ofNat 1)
    (fun _ ih ↦ Q.div ih (Q.ofNat 2)) n)
  == [Q.ofNat 1, Q.of 1 2, Q.of 1 4, Q.of 1 8]

/-! ## The invariant this file exists to protect

Everything `Tm.eval` will call must be axiom-free, or the development's
audit claim fails. -/

#print axioms Q.add
#print axioms Q.sub
#print axioms Q.mul
#print axioms Q.div
#print axioms Q.abs
#print axioms Q.ltN
#print axioms Q.eqN
#print axioms Q.ofNat

end HAomega
