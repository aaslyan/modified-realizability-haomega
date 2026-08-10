/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Ordinals.Epsilon0

/-!
# A hand-rolled rational layer — value level only, not yet a base type

Groundwork for constructive analysis, and a measurement that constrains it.
**Nothing in the object language uses this yet**: `Ty` has no rational base
type, and adding one is deliberately deferred until the representation
question below is settled, since every base type enlarges every per-rule and
per-type site in the development permanently.

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

**Open question, deliberately not settled here.** Constructive analysis
usually wants *dyadic* rationals, `m · 2⁻ᵏ`: approximations are stated at
precision `2⁻ⁿ`, normalization is shifting rather than `gcd`, and denominators
do not grow the way general fractions' do. General `Q` is the better type for
*stating* theorems and dyadics the better one for *computing* with them, and
this framework can carry both — adding a base type is a known, mechanical
operation here, done twice already for `ord` and `hyd`. Which to wire in, and
whether to wire in one or two, is a design decision that should precede the
first analysis theorem rather than follow it.

What this file settles regardless of that choice is the *constraint*: whatever
representation is chosen must be built from measured-axiom-free primitives,
because Mathlib's rational arithmetic is not.
-/

namespace HAomega

/-- A rational: numerator, and a denominator kept positive and coprime to it
by `Q.of`. -/
structure Q where
  num : Int
  den : Nat
  deriving DecidableEq, Repr, BEq

namespace Q

/-- Zero, and the canonical shape of every degenerate case. -/
def zero : Q := ⟨0, 1⟩

/-- The one representation, and hence the meaning of structural equality.
Named `of` rather than `mk`, which the structure already claims. -/
def of (n : Int) (d : Nat) : Q :=
  if d = 0 then zero
  else
    let g := Nat.gcd n.natAbs d
    if g = 0 then zero else ⟨Int.tdiv n (Int.ofNat g), d / g⟩

def ofInt (n : Int) : Q := ⟨n, 1⟩
def ofNat (n : Nat) : Q := ⟨Int.ofNat n, 1⟩

def add (a b : Q) : Q :=
  of (Int.add (Int.mul a.num (Int.ofNat b.den)) (Int.mul b.num (Int.ofNat a.den)))
     (a.den * b.den)

def neg (a : Q) : Q := ⟨Int.neg a.num, a.den⟩

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
