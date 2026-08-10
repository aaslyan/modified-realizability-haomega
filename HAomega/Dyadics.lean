/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Rationals

/-!
# Dyadic rationals — the computing representation

`Rationals.lean` gives general `Q`. This gives `D`, the dyadics `m · 2⁻ᵏ`, and
the embedding `D.toQ`. The division of labour is deliberate:

* **`Q` states.** A theorem of constructive analysis says things like
  `|p² − q| < 2⁻ⁿ`, and general fractions are the natural vocabulary for that.
* **`D` computes.** Approximation is always *at* a precision `2⁻ⁿ`, so the
  exponent is the precision index rather than a number to be recovered;
  normalization is shifting out trailing zero bits rather than a `gcd`; and
  denominators cannot grow the way general fractions' do, which is precisely
  the failure mode the hydra work measured and removed.

Dyadics are not closed under division, and that is not worked around here.
Halving is primitive (it is what `2⁻ⁿ` needs); anything else divides in `Q`.

## Same constraint as `Q`

Every operation must be built from measured-axiom-free primitives, so `2ᵏ` is
hand-rolled rather than taken from `Monoid.npow`, for the reason
`Rationals.lean` records about `Rat`. The `#print axioms` block below rechecks
it at every build.

## What is not proved yet

`toQ` is an embedding, and the alignment lemmas one would want —
`toQ (add a b) = Q.add (toQ a) (toQ b)`, and agreement of the two order tests
— are **not** proved here; the instances are guarded instead. That is
honest bookkeeping rather than a shortcut: nothing yet transfers a *fact*
across the bridge, and when the first analysis theorem does, those lemmas are
what it will need. Contrast `OrdCnf.lean`, where the alignment lemmas came
first because every certified fact was inherited through them.
-/

namespace HAomega

/-- `2ᵏ`, hand-rolled: `Monoid.npow` is not axiom-free here. -/
def twoPowN : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * twoPowN k

def twoPowI (k : Nat) : Int := Int.ofNat (twoPowN k)

/-- A dyadic rational: `mant · 2⁻ᵉˣᵖ`, kept canonical by `D.of`. -/
structure D where
  mant : Int
  exp : Nat
  deriving DecidableEq, Repr, BEq

namespace D

def zero : D := ⟨0, 0⟩

/-- Canonical form: strip trailing zero bits, so structural equality is
equality of the rationals denoted.  Recursion is on the exponent. -/
def of : Int → Nat → D
  | m, 0 => ⟨m, 0⟩
  | m, k + 1 =>
      if Int.emod m 2 = 0 then of (Int.tdiv m 2) k else ⟨m, k + 1⟩

def ofInt (n : Int) : D := ⟨n, 0⟩
def ofNat (n : Nat) : D := ⟨Int.ofNat n, 0⟩

/-- Both mantissas scaled to the common exponent `max`. -/
def scaled (a : D) (e : Nat) : Int := Int.mul a.mant (twoPowI (e - a.exp))

def add (a b : D) : D :=
  let e := Nat.max a.exp b.exp
  of (Int.add (scaled a e) (scaled b e)) e

def neg (a : D) : D := ⟨Int.neg a.mant, a.exp⟩

def sub (a b : D) : D := add a (neg b)

def mul (a b : D) : D := of (Int.mul a.mant b.mant) (a.exp + b.exp)

/-- Halving — the operation `2⁻ⁿ` is built from, and the reason the exponent
is the right thing to carry. -/
def half (a : D) : D := of a.mant (a.exp + 1)

/-- `2⁻ᵏ`. -/
def pow2neg (k : Nat) : D := ⟨1, k⟩

def abs (a : D) : D := if a.mant < 0 then neg a else a

/-- Strict order, as a numeral — the shape a derivation branches on. -/
def ltN (a b : D) : Nat :=
  let e := Nat.max a.exp b.exp
  if scaled a e < scaled b e then 1 else 0

/-- **The bridge**: every dyadic is a rational. -/
def toQ (a : D) : Q := Q.of a.mant (twoPowN a.exp)

end D

-- Canonical form, and the arithmetic.
#guard D.of 4 2 == D.of 1 0
#guard D.of 6 1 == D.ofNat 3
#guard D.add (D.pow2neg 1) (D.pow2neg 1) == D.ofNat 1
#guard D.sub (D.pow2neg 1) (D.pow2neg 2) == D.pow2neg 2
#guard D.mul (D.pow2neg 2) (D.pow2neg 3) == D.pow2neg 5
#guard D.half (D.ofNat 1) == D.pow2neg 1
#guard D.abs (D.sub (D.ofNat 1) (D.ofNat 5)) == D.ofNat 4
#guard (D.ltN (D.pow2neg 3) (D.pow2neg 2), D.ltN (D.pow2neg 2) (D.pow2neg 3)) == (1, 0)
-- `2⁻ⁿ` by iterated halving: the roadmap's precision sequence
#guard (List.range 5).map (fun n ↦ Nat.rec (D.ofNat 1) (fun _ ih ↦ D.half ih) n)
  == (List.range 5).map D.pow2neg

-- The bridge lands where it should, at instances.  (The alignment *lemmas*
-- are future work; see the header.)
#guard D.toQ (D.pow2neg 3) == Q.of 1 8
#guard D.toQ (D.ofNat 5) == Q.ofNat 5
#guard D.toQ (D.add (D.pow2neg 1) (D.pow2neg 2))
  == Q.add (D.toQ (D.pow2neg 1)) (D.toQ (D.pow2neg 2))
#guard D.toQ (D.mul (D.pow2neg 2) (D.ofNat 3)) == Q.of 3 4
#guard D.ltN (D.pow2neg 3) (D.pow2neg 2)
  == Q.ltN (D.toQ (D.pow2neg 3)) (D.toQ (D.pow2neg 2))

/-! ## The invariant -/

#print axioms D.add
#print axioms D.sub
#print axioms D.mul
#print axioms D.half
#print axioms D.ltN
#print axioms D.toQ
#print axioms twoPowN

end HAomega
