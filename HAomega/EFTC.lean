/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniformContinuity
import HAomega.QOrder

/-!
# The positive half of Newton–Leibniz adequacy: `A₁ ⊨ EFTC2`

`EFTC2(f)` asserts a witness `(F, (qₖ))` with `F` a representation of `f'` and
`|qₖ − (f b − f a)| < 2⁻ᵏ`, the `qₖ` computed *from `F`*. The witness has to
carry the derivative: the numeral `f b − f a` alone is computable from `f`
whatever `f'` does, so it cannot be what the theorem is about.

Two representations, as structures:

* **`A0`** — an evaluator for `f` on rationals plus a modulus of continuity
  `ω`. The standard "computable `f`".
* **`A1`** — `A0`'s data plus a modulus of *uniform differentiability* `δ`:
  for `x`, `x+h` in `[a,b]` with `0 < |h| ≤ 2⁻ᵟ⁽ᵏ⁾`,
  `|(f(x+h) − f x)/h − f' x| < 2⁻ᵏ`.

## Status: constructions and statements, not derivations

**Read this before the claims.** What is built here is the two constructions
of Lemmas 1 and 2 and the Theorem 2 witness, as *programs that run*, together
with precise statements of what they are supposed to satisfy. The error
analyses — the triangle inequalities bounding quadrature and evaluation error
— are **not derived**. They cannot be: they are arithmetic reasoning about
`Q`, and `Deriv` still has no conversion equations for it, nor does the value
layer have a ring theory. Every correctness claim below is therefore either

* a `Prop` that is *stated* and explicitly flagged as unproved, or
* a `#guard` checking the construction at concrete instances.

This is the same posture `UniformContinuity.lean` and `SquareRoot.lean` take
at the same fork, and the same thing blocks all three: the arithmetic rule
base for `Q`. Nothing here is claimed to be a proof of Theorem 2.

## What `Modulus.lean` does *not* give

`HasMod F m` is continuity in the Baire sense — how much of an *oracle*
`ℕ → ℕ` a functional inspects — with `m` a bound on queried indices. The `ω`
and `δ` here are *metric* moduli on `ℚ`. The two notions coincide nowhere in
this development, and no lemma from `Modulus.lean` transfers. (They would meet
if reals were represented as `ℕ → ℚ` and `f` were type-2; `f : Q → Q` is
type-1.)

## Scope

The negative half — `A₀ ⊭ EFTC2`, Myhill's continuously-differentiable
function with non-computable derivative — is **not** formalized and is not
claimed; it is a citation. There is no bridge to Mathlib's `ℝ`: the embedding
is shallow throughout, matching the choice-free-extraction invariant that
`Rationals.lean` measures Mathlib's own `Rat.add` to violate.
-/

namespace HAomega

/-! ## Rational helpers the constructions need -/

def Qle (x y : Q) : Bool := Q.ltN y x == 0
def Qmin (x y : Q) : Q := if Qle x y then x else y
def Qmax (x y : Q) : Q := if Qle x y then y else x

theorem Qle_eq_true_iff (x y : Q) : Qle x y = true ↔ x.val ≤ y.val := by
  unfold Qle
  simp only [beq_iff_eq]
  exact Q.ltN_eq_zero_iff y x

theorem Qmin_val (x y : Q) : (Qmin x y).val = min x.val y.val := by
  unfold Qmin
  split
  · rename_i h
    exact (min_eq_left ((Qle_eq_true_iff x y).mp h)).symm
  · rename_i h
    have hx : ¬ (x.val ≤ y.val) := fun hc ↦ h ((Qle_eq_true_iff x y).mpr hc)
    exact (min_eq_right (le_of_not_ge hx)).symm

/-- `2ᵉ` as a rational. -/
def twoPowQ (e : Nat) : Q := Q.ofNat (twoPowN e)

/-- `⌈q⌉` as a natural, clamped at `0`. -/
def ceilNatQ (q : Q) : Nat :=
  if q.num ≤ 0 then 0
  else (Int.tdiv (Int.add q.num (Int.ofNat (q.den - 1))) (Int.ofNat q.den)).toNat

/-- Least `ℓ ≤ fuel` with `L ≤ 2ˡ`. -/
def ceilLog2Aux (L : Q) : Nat → Nat → Nat
  | _, 0 => 0
  | acc, fuel + 1 => if Qle L (twoPowQ acc) then acc else ceilLog2Aux L (acc + 1) fuel

def ceilLog2Q (L : Q) : Nat := ceilLog2Aux L 0 64

/-- Least `η ≤ fuel` with `2⁻ᵑ ≤ L/2`. -/
def etaAux (L : Q) : Nat → Nat → Nat
  | _, 0 => 0
  | acc, fuel + 1 =>
      if Qle (D.toQ (D.pow2neg acc)) (Q.div L (Q.ofNat 2)) then acc
      else etaAux L (acc + 1) fuel

/-- `Σ_{i<n} g i`, as a loop.  Not a fold: the Riemann sums below run to `N`
in the tens of thousands, and Lean's interpreter does not eliminate tail
calls, so both the naive right fold and an accumulator-passing recursion
exhaust the stack past roughly `2¹³` — measured, at `N = 32768`. -/
def sumQ (g : Nat → Q) (n : Nat) : Q := Id.run do
  let mut acc := Q.zero
  for i in [0:n] do
    acc := Q.add acc (g i)
  return acc

/-! ## The representations -/

/-- **`A₀`** — a computable `f` on `[a,b]`: an evaluator and a modulus of
continuity.  `ω k` is meant to satisfy `|x−y| ≤ 2⁻ω⁽ᵏ⁾ → |f x − f y| < 2⁻ᵏ`. -/
structure A0 where
  a : Q
  b : Q
  f : Q → Q
  ω : Nat → Nat

/-- **`A₁`** — `A₀` plus a modulus of uniform differentiability, **and the
conditions making `ω` and `δ` moduli of anything**.

The three `Prop` fields are not decoration.  Without them `A1` is five
unrelated pieces of data, `∀ A : A1` ranges over data where `ω` and `δ` are
arbitrary functions, and the correctness claims at the bottom of this file are
false — refuted, at one point, by taking the `x²` instance below and replacing
its moduli with the constant `0`.  The conditions were always in the
docstrings; they are now in the type.

`diff` is stated **existentially**.  Putting `f'` in as *data* would be a
different representation — one that hands the derivative over for free — and
would trivialise the theorem this file exists to state.  As a `Prop` the
witness is not computationally available, which is exactly the point: `f'`
exists, and the content of Lemma 1 is that `δ` lets you *compute* it.

All three are written in `Q`'s own vocabulary (`Qle`, `Q.ltN`, `2⁻ᵏ` as a
dyadic) rather than through the Mathlib rational a `Q` denotes.  That is not a
style choice: field types stated with `Q.val` put `Rat`'s order instances into
`A1`'s type, and then *every* construction taking an `A1` — `derivEval`,
`integral`, `eftc2` — reports `Classical.choice`.  Measured, and the reason
this file keeps its own idiom.  The proofs discharging the fields may of
course use Mathlib freely; only the statements must not. -/
structure A1 extends A0 where
  δ : Nat → Nat
  /-- the interval is nondegenerate -/
  ivl : Q.ltN a b = 1
  /-- `ω` is a modulus of continuity for `f` on `[a,b]` -/
  cont : ∀ (k : Nat) (x y : Q), Qle a x = true → Qle x b = true →
      Qle a y = true → Qle y b = true →
      Qle (Q.abs (Q.sub x y)) (D.toQ (D.pow2neg (ω k))) = true →
      Q.ltN (Q.abs (Q.sub (f x) (f y))) (D.toQ (D.pow2neg k)) = 1
  /-- `δ` is a modulus of uniform differentiability, for *some* derivative -/
  diff : ∃ F : Q → Q, ∀ (k : Nat) (x h : Q),
      Qle a x = true → Qle x b = true →
      Qle a (Q.add x h) = true → Qle (Q.add x h) b = true →
      h.num ≠ 0 → Qle (Q.abs h) (D.toQ (D.pow2neg (δ k))) = true →
      Q.ltN (Q.abs (Q.sub (Q.div (Q.sub (f (Q.add x h)) (f x)) h) (F x)))
        (D.toQ (D.pow2neg k)) = 1

namespace A1

/-! ## Lemma 1 — the derivative is computable, with an explicit modulus

The step is shrunk to `h₀ := min(2⁻ᵟ⁽ʲ⁾, (b−a)/4)` with `j := k+3`, which
costs nothing because the `δ`-guarantee holds for every smaller admissible
step.  The sign is chosen so that `x + s·h₀` stays inside `[a,b]`: step right
from the left half, left from the right half.  For two points within
`(b−a)/2` of each other the same sign is admissible for both, which is the
pigeonhole the modulus estimate needs. -/

/-- `h₀` — the endpoint-safe step at precision `k`. -/
def stepSize (A : A1) (k : Nat) : Q :=
  Qmin (D.toQ (D.pow2neg (A.δ (k + 3))))
    (Q.div (Q.sub A.b A.a) (Q.ofNat 4))

/-- Step right from the left half of the interval, left from the right half.
Either choice keeps `x + s·h₀` inside `[a,b]`, since `h₀ ≤ (b−a)/4`. -/
def stepRight (A : A1) (x : Q) : Bool :=
  Qle x (Q.div (Q.add A.a A.b) (Q.ofNat 2))

/-- **The computable derivative**: `derivEval k x` approximates `f' x` to
`2⁻ᵏ`, by a difference quotient over the safe signed step. -/
def derivEval (A : A1) (k : Nat) (x : Q) : Q :=
  let h₀ := A.stepSize k
  let h := if A.stepRight x then h₀ else Q.neg h₀
  Q.div (Q.sub (A.f (Q.add x h)) (A.f x)) h

/-- `η₂` — a fixed constant with `2⁻ᵑ² ≤ (b−a)/2`. -/
def eta2 (A : A1) : Nat := etaAux (Q.sub A.b A.a) 0 64

/-- **The modulus of continuity of `f'`.**  The two evaluations of `f` inside
the difference quotient are divided by the step, so the estimate multiplies by
`1/h₀`, and

    h₀ = min(2⁻ᵟ⁽ᵏ⁺³⁾, (b−a)/4)   so   1/h₀ ≤ max(2^δ(k+3), 2^(η₂+1))

using `2⁻ᵑ² ≤ (b−a)/2`.  **The second alternative is why `δ(k+3)` alone is not
enough**: when the interval is short compared with `2⁻ᵟ`, the minimum is
`(b−a)/4` and the reciprocal step is governed by `η₂`, which a `δ`-only index
does not see.  Hence the `max` inside `ω`'s argument.  `η₂` appears a second
time, at the outside, for the proximity that makes a common step admissible
for both points. -/
def omega' (A : A1) (k : Nat) : Nat :=
  Nat.max (A.ω (k + 5 + Nat.max (A.δ (k + 3)) (A.eta2 + 1))) A.eta2

/-! ## Lemma 2 — integrate `f'` by a Riemann sum

`L := b−a`, `ℓ := ⌈log₂ L⌉` so `L ≤ 2ˡ`, `m := k+2+ℓ`,
`N := ⌈L · 2^ω'(m)⌉` so the mesh is `L/N ≤ 2^-ω'(m)`.  The quadrature error
is then at most `L·2⁻ᵐ ≤ 2⁻⁽ᵏ⁺²⁾`, and sampling `f'` to `2⁻ᵐ` per point
contributes at most as much again, for a total below `2⁻ᵏ`. -/

def intL (A : A1) : Q := Q.sub A.b A.a
def intEll (A : A1) : Nat := ceilLog2Q A.intL
def intM (A : A1) (k : Nat) : Nat := k + 2 + A.intEll
def intN (A : A1) (k : Nat) : Nat :=
  Nat.max 1 (ceilNatQ (Q.mul A.intL (twoPowQ (A.omega' (A.intM k)))))

/-- **The computed integral**: `∫_a^b f'` to precision `2⁻ᵏ`, as a left
Riemann sum of the *computable derivative*, not of `f`. -/
def integral (A : A1) (k : Nat) : Q :=
  let N := A.intN k
  let h := Q.div A.intL (Q.ofNat N)
  let m := A.intM k
  Q.mul h (sumQ (fun i ↦ A.derivEval m (Q.add A.a (Q.mul (Q.ofNat i) h))) N)

/-! ## Theorem 2 — the `EFTC2` witness -/

/-- **The witness `(F, (qₖ))`.**  `F` is the derivative representation from
Lemma 1 and `qₖ` the Riemann sums from Lemma 2 — computed *from `F`*, which is
what makes this a statement about `f'` rather than about the numeral
`f b − f a`. -/
def eftc2 (A : A1) : (Nat → Q → Q) × (Nat → Q) := (A.derivEval, A.integral)

end A1

/-! ## What the constructions are supposed to satisfy

Stated, **not proved**.  Each is an arithmetic claim about `Q` of exactly the
kind the missing rule base would discharge. -/

/-- Lemma 1's correctness: `derivEval` is a modulus-`ω'` representation of a
function that the `δ`-data pins down.  **Not proved.** -/
def Lemma1Claim (A : A1) : Prop :=
  ∀ k : Nat, ∀ x y : Q,
    Qle (Q.abs (Q.sub x y)) (D.toQ (D.pow2neg (A.omega' k))) = true →
    Q.ltN (Q.abs (Q.sub (A.derivEval k x) (A.derivEval k y)))
      (D.toQ (D.pow2neg k)) = 1

/-- Lemma 2's correctness: the Riemann sums converge to `f b − f a` at the
stated rate.  **Not proved.** -/
def Lemma2Claim (A : A1) : Prop :=
  ∀ k : Nat,
    Q.ltN (Q.abs (Q.sub (A.integral k) (Q.sub (A.f A.b) (A.f A.a))))
      (D.toQ (D.pow2neg k)) = 1

/-! ## Instances — what actually runs

Two `A₁` data sets, with `ω` and `δ` supplied by hand (that is the caller's
half of the bargain, exactly as in `UniformContinuity.lean`).

* `f x = 3x` on `[0,2]`: `f' = 3`, `∫ = 6`.  The difference quotient is exact,
  so `δ = 0`; `|3x − 3y| = 3|x−y|` gives `ω k = k+2`.
* `f x = x²` on `[0,1]`: `f' = 2x`, `∫ = 1`.  The quotient is `2x + h`, so
  `δ k = k`; `|x²−y²| ≤ 2|x−y|` gives `ω k = k+1`. -/

def linEx : A1 :=
  { a := Q.ofNat 0, b := Q.ofNat 2, f := fun x ↦ Q.mul (Q.ofNat 3) x,
    ω := fun k ↦ k + 2, δ := fun _ ↦ 0,
    ivl := by rw [Q.ltN_eq_one_iff, Q.val_ofNat, Q.val_ofNat]; norm_num,
    cont := by
      intro k x y _ _ _ _ h
      rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val] at h
      rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val]
      simp only [Q.val_mul, Q.val_ofNat]
      push_cast
      rw [show (3 : Rat) * x.val - 3 * y.val = 3 * (x.val - y.val) by ring, abs_mul,
        show |(3 : Rat)| = 3 by norm_num]
      rw [quarter_pow] at h
      have hp : (0 : Rat) < 1 / 2 ^ k := by positivity
      linarith,
    diff := ⟨fun _ ↦ Q.ofNat 3, by
      intro k x h _ _ _ _ hh _
      rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, Q.val_div _ _ hh, Q.val_sub,
        toQ_pow2neg_val]
      simp only [Q.val_mul, Q.val_ofNat, Q.val_add]
      push_cast
      have hv : h.val ≠ 0 := by
        unfold Q.val
        exact div_ne_zero (Int.cast_ne_zero.mpr hh) (ne_of_gt h.den_cast_pos)
      rw [show (3 : Rat) * (x.val + h.val) - 3 * x.val = 3 * h.val by ring,
        mul_div_assoc, div_self hv, mul_one, sub_self, abs_zero]
      positivity⟩ }

/-- `x²` on `[0,1]`.  Note `δ k = k+1`, not `k`: the difference quotient is
`2x + h`, so its error *is* `|h|`, and `|h| ≤ 2⁻ᵟ⁽ᵏ⁾` has to give `|h| < 2⁻ᵏ`
strictly.  With `δ k = k` the admissible step `|h| = 2⁻ᵏ` meets the bound with
equality and misses.  The old value was off by one — the kind of thing only a
field with a proof obligation catches. -/
def sqEx : A1 :=
  { a := Q.ofNat 0, b := Q.ofNat 1, f := fun x ↦ Q.mul x x,
    ω := fun k ↦ k + 1, δ := fun k ↦ k + 1,
    ivl := by rw [Q.ltN_eq_one_iff, Q.val_ofNat, Q.val_ofNat]; norm_num,
    cont := by
      intro k x y hax hxb hay hyb h
      rw [Qle_eq_true_iff, Q.val_ofNat] at hax hay
      rw [Qle_eq_true_iff, Q.val_ofNat] at hxb hyb
      rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val] at h
      rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val]
      push_cast at hax hay hxb hyb
      simp only [Q.val_mul]
      rw [halve_pow] at h
      have hp : (0 : Rat) < 1 / 2 ^ k := by positivity
      rcases eq_or_ne x.val y.val with he | he
      · rw [he, sub_self, abs_zero]; exact hp
      · have hd : 0 < |x.val - y.val| := abs_pos.mpr (sub_ne_zero.mpr he)
        have hs : x.val + y.val < 2 := by
          by_contra hc
          push_neg at hc
          exact he (by linarith)
        rw [show x.val * x.val - y.val * y.val = (x.val + y.val) * (x.val - y.val) by ring,
          abs_mul, abs_of_nonneg (by linarith : (0 : Rat) ≤ x.val + y.val)]
        have := mul_lt_mul_of_pos_right hs hd
        linarith,
    diff := ⟨fun x ↦ Q.mul (Q.ofNat 2) x, by
      intro k x h _ _ _ _ hh hb
      rw [Qle_eq_true_iff, Q.val_abs, toQ_pow2neg_val] at hb
      rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, Q.val_div _ _ hh, Q.val_sub,
        toQ_pow2neg_val]
      simp only [Q.val_mul, Q.val_ofNat, Q.val_add]
      push_cast
      have hv : h.val ≠ 0 := by
        unfold Q.val
        exact div_ne_zero (Int.cast_ne_zero.mpr hh) (ne_of_gt h.den_cast_pos)
      rw [show (x.val + h.val) * (x.val + h.val) - x.val * x.val
            = (2 * x.val + h.val) * h.val by ring,
        mul_div_assoc, div_self hv, mul_one,
        show 2 * x.val + h.val - 2 * x.val = h.val by ring]
      rw [halve_pow] at hb
      have hp : (0 : Rat) < 1 / 2 ^ k := by positivity
      linarith [abs_nonneg h.val]⟩ }

-- **Lemma 1's construction is right at instances.**  `f' = 3` exactly for the
-- linear case; for `x²` the quotient lands within `2⁻¹²` of `2x` at `k = 8`.
#guard linEx.derivEval 5 (Q.of 1 2) == Q.ofNat 3
#guard linEx.derivEval 5 (Q.of 7 4) == Q.ofNat 3
#guard sqEx.derivEval 8 (Q.of 1 2) == Q.of 4097 4096
#guard sqEx.derivEval 8 (Q.ofNat 0) == Q.of 1 4096
-- the endpoint-safe sign really does flip past the midpoint
#guard (linEx.stepRight (Q.of 1 2), linEx.stepRight (Q.of 7 4)) == (true, false)

-- **Lemma 2's construction is right at instances.**  Exact for the linear
-- case; for `x²` the error is inside `2⁻ᵏ` with room to spare.
#guard linEx.integral 0 == Q.ofNat 6
#guard sqEx.integral 0 == Q.of 524257 524288
#guard Q.ltN (Q.abs (Q.sub (sqEx.integral 0) (Q.ofNat 1)))
    (D.toQ (D.pow2neg 0)) == 1

/-! ### Measured beyond the guards

`N` grows as `2^ω'(m)`, and `ω'` compounds `ω` with `δ`, so the sample count
is exponential in the requested precision even for these easy functions.  The
following were run rather than guarded, since `#guard` would evaluate them at
elaboration time:

    sqEx.integral 0   N =  16384   error 31/524288      ≈ 5.9e-5
    sqEx.integral 1   N =  65536   error 63/4194304     ≈ 1.5e-5
    sqEx.integral 2   N = 262144   (sample count computed, value not re-run)
    linEx.integral 0..3   N = 4096..32768   value 6 exactly

Every sample count above is **twice** what it was before `omega'` gained its
`η₂` term and `sqEx.δ` was corrected.  That is the price of the two fixes, and
it is paid in constant factors rather than in the growth rate: the count is
still `2^ω'(m)`, exponential in the requested precision, which is §8's
optimal-adequacy question and not something either fix was aimed at.

Two honest remarks.  The errors are far *inside* the targets, which says the
bookkeeping is very conservative, not that it is wrong.  And `sumQ` is written
as a loop rather than a fold on purpose: Lean's interpreter does not eliminate
tail calls, and both a right fold and an accumulator-passing recursion
exhausted the stack at `N = 32768` — measured, not anticipated.

-/

/-- **Theorem 2**, `A₁ ⊨ EFTC2`: the witness satisfies both halves.
**Not proved** — this is the statement the constructions above are aimed at,
and its two conjuncts are exactly `Lemma1Claim` and `Lemma2Claim`. -/
def EFTC2Claim (A : A1) : Prop := Lemma1Claim A ∧ Lemma2Claim A

-- The constructions are choice-free, like everything else that runs here.
#print axioms A1.derivEval
#print axioms A1.omega'
#print axioms A1.integral
#print axioms A1.eftc2

end HAomega
