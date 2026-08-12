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
the same `Q`.  With it, a ring identity reduces to an identity about the
rational a `Q` denotes, which `ring` closes.

**The laws below have no side conditions.**  They did, until `Q`'s denominator
was changed to store its *predecessor*: with a bare `Nat` there, `⟨5, 0⟩`
inhabited `Q` and the object language's `∀x^rat` ranged over it, so every law
had to assume `den ≠ 0` and none could become a `Deriv` rule.  Positivity is
now structural and the hypothesis is gone.

What that refactor did **not** buy is coprimality, and the identity laws need
it — see the section on `add_zero_norm` at the bottom, where the failure is
exhibited by `decide` rather than described.

-/

namespace HAomega

/-- `Q.of` agrees with Mathlib's normalization. -/
theorem Q.of_eq_mkRat (n : Int) (d : Nat) (hd : d ≠ 0) :
    Q.of n d = ⟨(mkRat n d).num, (mkRat n d).den - 1⟩ := by
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

/-! ## The value bridge

`Rationals.lean` writes its operations with `Int.add`/`Int.mul` rather than
`+`/`*`, to keep the definitions provably axiom-free; `ring` does not see
those as ring operations, so two `rfl` bridges are needed first.

Beyond that, proving a law directly through `of_eq_of` means clearing
denominators by hand, and for a law with a nested operation (associativity,
distributivity) the inner `Q.of` has already normalized, so its numerator is
*not* the cross-multiplied one and the identity is no longer polynomial.  The
fix is one indirection: send a `Q` to the Mathlib rational it denotes, prove
each operation commutes with that map, and let `ring` work there.  `Q.val` is
proof-side only — nothing in `Tm.eval`'s graph mentions it.

This file imports `Mathlib` wholesale.  Narrower imports were tried and the
module paths do not exist in the pinned version; since the file is proof-side
only, the cost is build time rather than trust. -/

theorem intAdd_eq (x y : Int) : Int.add x y = x + y := rfl
theorem intMul_eq (x y : Int) : Int.mul x y = x * y := rfl
theorem intNeg_eq (x : Int) : Int.neg x = -x := rfl

/-- The rational a `Q` denotes.  Proof-side only. -/
def Q.val (q : Q) : Rat := (q.num : Rat) / (q.den : Rat)

theorem Q.den_cast_ne_zero (q : Q) : ((q.den : Rat)) ≠ 0 :=
  Nat.cast_ne_zero.mpr q.den_ne_zero

theorem Q.val_of (n : Int) (d : Nat) (hd : d ≠ 0) :
    (Q.of n d).val = (n : Rat) / (d : Rat) := by
  have hpos : 1 ≤ (mkRat n d).den := Nat.pos_of_ne_zero (mkRat n d).den_nz
  unfold Q.val Q.den
  rw [Q.of_eq_mkRat n d hd]
  show ((mkRat n d).num : Rat) / ((((mkRat n d).den - 1) + 1 : Nat) : Rat) = _
  rw [Nat.sub_add_cancel hpos, Rat.num_div_den]
  exact Rat.mkRat_eq_div n d

/-- Equal values force equal normal forms.  This is `of_eq_of` with the
cross-multiplication done once, so that later laws never see it. -/
theorem Q.of_inj_val {n n' : Int} {d d' : Nat} (hd : d ≠ 0) (hd' : d' ≠ 0)
    (h : (Q.of n d).val = (Q.of n' d').val) : Q.of n d = Q.of n' d' := by
  rw [Q.val_of _ _ hd, Q.val_of _ _ hd'] at h
  refine Q.of_eq_of hd hd' ?_
  rw [div_eq_div_iff (Nat.cast_ne_zero.mpr hd) (Nat.cast_ne_zero.mpr hd')] at h
  exact_mod_cast h

/-! ## Each operation commutes with the value map -/

theorem Q.val_add (a b : Q) : (Q.add a b).val = a.val + b.val := by
  unfold Q.add
  rw [Q.val_of _ _ (Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero)]
  unfold Q.val
  have ha := a.den_cast_ne_zero
  have hb := b.den_cast_ne_zero
  simp only [intAdd_eq, intMul_eq, Int.ofNat_eq_natCast]
  push_cast
  field_simp

theorem Q.val_mul (a b : Q) : (Q.mul a b).val = a.val * b.val := by
  unfold Q.mul
  rw [Q.val_of _ _ (Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero)]
  unfold Q.val
  have ha := a.den_cast_ne_zero
  have hb := b.den_cast_ne_zero
  simp only [intMul_eq]
  push_cast
  field_simp

theorem Q.val_neg (a : Q) : (Q.neg a).val = -a.val := by
  unfold Q.neg Q.val Q.den
  simp only [intNeg_eq]
  push_cast
  ring

theorem Q.val_sub (a b : Q) : (Q.sub a b).val = a.val - b.val := by
  unfold Q.sub
  rw [Q.val_add, Q.val_neg, sub_eq_add_neg]

/-! ## The laws, with no side conditions

Each is `of_inj_val` followed by `ring` on the value side.  Note what the
hypothesis-free statements cost: nothing, now that a denominator cannot be
zero. -/

theorem Q.add_comm (a b : Q) : Q.add a b = Q.add b a :=
  Q.of_inj_val (Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero)
    (Nat.mul_ne_zero b.den_ne_zero a.den_ne_zero)
    (by rw [show Q.of _ _ = Q.add a b from rfl, show Q.of _ _ = Q.add b a from rfl,
      Q.val_add, Q.val_add]; ring)

theorem Q.mul_comm (a b : Q) : Q.mul a b = Q.mul b a :=
  Q.of_inj_val (Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero)
    (Nat.mul_ne_zero b.den_ne_zero a.den_ne_zero)
    (by rw [show Q.of _ _ = Q.mul a b from rfl, show Q.of _ _ = Q.mul b a from rfl,
      Q.val_mul, Q.val_mul]; ring)

theorem Q.add_assoc (a b c : Q) :
    Q.add (Q.add a b) c = Q.add a (Q.add b c) :=
  Q.of_inj_val (Nat.mul_ne_zero (Q.add a b).den_ne_zero c.den_ne_zero)
    (Nat.mul_ne_zero a.den_ne_zero (Q.add b c).den_ne_zero)
    (by rw [show Q.of _ _ = Q.add (Q.add a b) c from rfl,
      show Q.of _ _ = Q.add a (Q.add b c) from rfl,
      Q.val_add, Q.val_add, Q.val_add, Q.val_add]; ring)

theorem Q.mul_assoc (a b c : Q) :
    Q.mul (Q.mul a b) c = Q.mul a (Q.mul b c) :=
  Q.of_inj_val (Nat.mul_ne_zero (Q.mul a b).den_ne_zero c.den_ne_zero)
    (Nat.mul_ne_zero a.den_ne_zero (Q.mul b c).den_ne_zero)
    (by rw [show Q.of _ _ = Q.mul (Q.mul a b) c from rfl,
      show Q.of _ _ = Q.mul a (Q.mul b c) from rfl,
      Q.val_mul, Q.val_mul, Q.val_mul, Q.val_mul]; ring)

theorem Q.mul_add (a b c : Q) :
    Q.mul a (Q.add b c) = Q.add (Q.mul a b) (Q.mul a c) :=
  Q.of_inj_val (Nat.mul_ne_zero a.den_ne_zero (Q.add b c).den_ne_zero)
    (Nat.mul_ne_zero (Q.mul a b).den_ne_zero (Q.mul a c).den_ne_zero)
    (by rw [show Q.of _ _ = Q.mul a (Q.add b c) from rfl,
      show Q.of _ _ = Q.add (Q.mul a b) (Q.mul a c) from rfl,
      Q.val_mul, Q.val_add, Q.val_add, Q.val_mul, Q.val_mul]; ring)

theorem Q.add_neg (a : Q) : Q.add a (Q.neg a) = Q.zero := by
  have h : Q.add a (Q.neg a) = Q.of 0 1 := by
    refine Q.of_inj_val (Nat.mul_ne_zero a.den_ne_zero (Q.neg a).den_ne_zero)
      one_ne_zero ?_
    rw [show Q.of _ _ = Q.add a (Q.neg a) from rfl, Q.val_add, Q.val_neg,
      Q.val_of _ _ one_ne_zero]
    simp
  rw [h]; rfl


/-! ## The order bridge

`Q.ltN` is a `0`/`1` numeral, not a `Prop`, because the object language has no
propositions to return.  Characterizing it through `Q.val` is what turns every
order obligation in the analysis files into an inequality between Mathlib
rationals, where `linarith`/`nlinarith` apply.  Without this the error
estimates have to be done by hand on cross-multiplied integers. -/

theorem Q.den_cast_pos (q : Q) : (0 : Rat) < (q.den : Rat) := by
  exact_mod_cast Nat.pos_of_ne_zero q.den_ne_zero

theorem Q.val_lt_iff (a b : Q) :
    a.val < b.val ↔ a.num * (b.den : Int) < b.num * (a.den : Int) := by
  unfold Q.val
  rw [div_lt_div_iff₀ a.den_cast_pos b.den_cast_pos]
  constructor <;> intro h <;> exact_mod_cast h

theorem Q.ltN_eq_one_iff (a b : Q) : Q.ltN a b = 1 ↔ a.val < b.val := by
  rw [Q.val_lt_iff]
  unfold Q.ltN
  simp only [intMul_eq, Int.ofNat_eq_natCast]
  split <;> simp_all

theorem Q.ltN_eq_zero_iff (a b : Q) : Q.ltN a b = 0 ↔ b.val ≤ a.val := by
  rw [← not_lt, ← Q.ltN_eq_one_iff]
  unfold Q.ltN
  split <;> simp_all

/-- `Q.ltN` is `0` or `1` and nothing else. -/
theorem Q.ltN_eq_zero_or_one (a b : Q) : Q.ltN a b = 0 ∨ Q.ltN a b = 1 := by
  unfold Q.ltN; split <;> simp

theorem Q.val_abs (a : Q) : (Q.abs a).val = |a.val| := by
  have hd := a.den_cast_pos
  unfold Q.abs
  split
  · rename_i h
    have hn : (a.num : Rat) < 0 := by exact_mod_cast h
    have hlt : a.val < 0 := by unfold Q.val; exact div_neg_of_neg_of_pos hn hd
    rw [Q.val_neg, abs_of_neg hlt]
  · rename_i h
    have hn : (0 : Rat) ≤ (a.num : Rat) := by exact_mod_cast Int.not_lt.mp h
    have hge : 0 ≤ a.val := by unfold Q.val; exact div_nonneg hn (le_of_lt hd)
    rw [abs_of_nonneg hge]

theorem Q.val_ofNat (n : Nat) : (Q.ofNat n).val = (n : Rat) := by
  unfold Q.ofNat Q.val Q.den
  simp

theorem Q.val_ofInt (n : Int) : (Q.ofInt n).val = (n : Rat) := by
  unfold Q.ofInt Q.val Q.den
  simp

theorem natAbs_cast_rat (n : Int) : ((n.natAbs : Nat) : Rat) = |(n : Rat)| := by
  simp [Int.cast_abs]

theorem Q.val_div (a b : Q) (hb : b.num ≠ 0) :
    (Q.div a b).val = a.val / b.val := by
  have hbn : b.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
  have hden : a.den * b.num.natAbs ≠ 0 := Nat.mul_ne_zero a.den_ne_zero hbn
  have ha0 := ne_of_gt a.den_cast_pos
  have hb0 := ne_of_gt b.den_cast_pos
  have hn0 : (b.num : Rat) ≠ 0 := Int.cast_ne_zero.mpr hb
  unfold Q.div
  rw [if_neg hb]
  rcases lt_or_ge b.num 0 with h | h
  · rw [if_pos h, Q.val_neg, Q.val_of _ _ hden]
    have hR : (b.num : Rat) < 0 := by exact_mod_cast h
    have habs : ((b.num.natAbs : Nat) : Rat) = -(b.num : Rat) := by
      rw [natAbs_cast_rat, abs_of_neg hR]
    unfold Q.val
    simp only [intMul_eq, Int.ofNat_eq_natCast]
    push_cast
    rw [habs]
    field_simp
  · rw [if_neg (Int.not_lt.mpr h), Q.val_of _ _ hden]
    have hR : (0 : Rat) ≤ (b.num : Rat) := by exact_mod_cast h
    have habs : ((b.num.natAbs : Nat) : Rat) = (b.num : Rat) := by
      rw [natAbs_cast_rat, abs_of_nonneg hR]
    unfold Q.val
    simp only [intMul_eq, Int.ofNat_eq_natCast]
    push_cast
    rw [habs]
    field_simp

/-! ## Where the refactor stops: the identity laws

`den+1` made positivity structural.  It did **not** make *coprimality*
structural, and the identity laws need that.  `⟨2, denPred := 3⟩` — the
fraction `2/4` — is a perfectly good inhabitant of `Q` that `Q.of` never
produces, and adding zero to it reduces it.  So `x + 0 = x` is **false** in
this model, and cannot be a `Deriv` rule:

    Q.add ⟨2, 3⟩ Q.zero  =  ⟨1, 1⟩  ≠  ⟨2, 3⟩

checked by `decide` below, not argued.  What is true is that adding zero
*normalizes*, which is the law's honest form.

The distinction is exactly whether both sides of a law pass through `Q.of`.
Commutativity, associativity, distributivity and `x + (−x) = 0` do, so they
hold on the nose for every inhabitant; a law with a bare variable on one side
does not.  Closing that gap means carrying a coprimality proof in the data (a
subtype) or quotienting — a change of a different size from this one, and it
would have to keep `Tm.eval` axiom-free through the proof component.  Not
attempted here. -/

theorem Q.val_zero : Q.zero.val = 0 := by
  unfold Q.val Q.zero Q.den
  simp

/-- Adding zero **normalizes** rather than acting as the identity. -/
theorem Q.add_zero_norm (a : Q) : Q.add a Q.zero = Q.of a.num a.den :=
  Q.of_inj_val (Nat.mul_ne_zero a.den_ne_zero Q.zero.den_ne_zero) a.den_ne_zero
    (by rw [show Q.of _ _ = Q.add a Q.zero from rfl, Q.val_add, Q.val_zero,
      Q.val_of _ _ a.den_ne_zero, add_zero]; rfl)

/-- **`x + 0 = x` is not valid here**, and this is the witness. -/
theorem Q.add_zero_not_id : Q.add ⟨2, 3⟩ Q.zero ≠ ⟨2, 3⟩ := by decide

#print axioms Q.of_eq_mkRat
#print axioms Q.of_eq_of
#print axioms Q.add_comm
#print axioms Q.mul_comm
#print axioms Q.add_assoc
#print axioms Q.mul_assoc
#print axioms Q.mul_add
#print axioms Q.add_neg

end HAomega
