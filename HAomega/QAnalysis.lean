/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.EFTC
import HAomega.QArith

/-!
# Discharging the analysis files' side hypotheses

`SquareRoot.lean`, `UniformContinuity.lean` and `EFTC.lean` each leave an
arithmetic obligation to the caller and check it at instances with `#guard`.
With `QArith.lean`'s order bridge those obligations become inequalities
between Mathlib rationals, so they can be *proved* for every input instead.

This is a leaf module: it imports the analysis chain rather than sitting
inside it, so nothing certified changes build shape, and `Mathlib` stays out
of `Tm.eval`'s import graph exactly as before.

## What lands here, and what does not

* `SquareRoot`'s bound `K` — **discharged**. `sqrtBound` computes one and
  both colouring premises are proved for every `q ≥ 0`, at every precision.
* `UniformContinuity`'s Lipschitz premise — **discharged for the instances
  that were guarded** (doubling, translation), for all `x`, `y`, `m`.
* `EFTC`'s `Lemma1Claim`/`Lemma2Claim` — **refuted as stated**, see the last
  section. They quantify over an arbitrary `A1`, whose fields carry no
  hypothesis that `ω` and `δ` are moduli of anything, so they are false for
  trivial reasons that have nothing to do with the analysis. The repaired
  statements are given; how far they are proved is stated there, not here.
-/

namespace HAomega

/-! ## The dyadic-to-rational value bridge -/

theorem twoPowN_pos (k : Nat) : 0 < twoPowN k := by
  induction k with
  | zero => decide
  | succ n ih => unfold twoPowN; omega

theorem twoPowN_ne_zero (k : Nat) : twoPowN k ≠ 0 := Nat.ne_of_gt (twoPowN_pos k)

theorem twoPowN_cast (k : Nat) : ((twoPowN k : Nat) : Rat) = 2 ^ k := by
  induction k with
  | zero => decide
  | succ n ih =>
    show ((2 * twoPowN n : Nat) : Rat) = _
    push_cast
    rw [ih, pow_succ]
    ring

/-- `2⁻ᵏ` denotes what it should. -/
theorem toQ_pow2neg_val (k : Nat) : (D.toQ (D.pow2neg k)).val = 1 / 2 ^ k := by
  show (Q.of 1 (twoPowN k)).val = _
  rw [Q.val_of _ _ (twoPowN_ne_zero k), twoPowN_cast]
  norm_num

theorem toQ_pow2neg_pos (k : Nat) : (0 : Rat) < (D.toQ (D.pow2neg k)).val := by
  rw [toQ_pow2neg_val]
  positivity

/-! ## Step 4.1 — `SquareRoot`'s bound `K`, discharged

`sqrtApproxD` proves: *given* a bound `K` whose scaled square exceeds `q`, the
search finds the crossing.  Producing such a `K` is the Archimedean step the
file's header names as needing the arithmetic, and `#guard`s discharged it at
the inputs the build could run.  It is now proved at **every** input.

The bound is `(⌊q⌋+1)·2ⁿ`, i.e. the numeral `⌊q⌋+1` at scale `n`: crude, but
`(c+1)² > c ≥ q` needs nothing sharper, and a sharper bound would only make
the extracted search shorter, not more correct. -/

theorem sqScaled_val (n k : Nat) :
    (Q.mul (Q.mul (Q.ofNat k) (D.toQ (D.pow2neg n)))
      (Q.mul (Q.ofNat k) (D.toQ (D.pow2neg n)))).val = ((k : Rat) / 2 ^ n) ^ 2 := by
  rw [Q.val_mul, Q.val_mul, Q.val_ofNat, toQ_pow2neg_val]
  ring

theorem sqColourVal_eq_one_iff (q : Q) (n k : Nat) :
    sqColourVal q n k = 1 ↔ q.val < ((k : Rat) / 2 ^ n) ^ 2 := by
  unfold sqColourVal
  rw [Q.ltN_eq_one_iff, sqScaled_val]

theorem sqColourVal_eq_zero_iff (q : Q) (n k : Nat) :
    sqColourVal q n k = 0 ↔ ((k : Rat) / 2 ^ n) ^ 2 ≤ q.val := by
  unfold sqColourVal
  rw [Q.ltN_eq_zero_iff, sqScaled_val]

/-- **The Archimedean bound.** -/
def sqrtBound (q : Q) (n : Nat) : Nat := (q.num.toNat + 1) * twoPowN n

theorem Q.num_nonneg_of_val_nonneg {q : Q} (hq : 0 ≤ q.val) : (0 : Rat) ≤ (q.num : Rat) := by
  unfold Q.val at hq
  rcases div_nonneg_iff.mp hq with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h1
  · exact absurd h2 (not_le.mpr q.den_cast_pos)

/-- **The lower premise, for every `q ≥ 0`.**  `colour(q,n,0) = 0`. -/
theorem sqrt_lower_premise (q : Q) (n : Nat) (hq : 0 ≤ q.val) :
    sqColourVal q n 0 = 0 := by
  rw [sqColourVal_eq_zero_iff]
  simpa using hq

/-- **The upper premise, for every `q ≥ 0` and every precision.**
`colour(q, n, sqrtBound q n) = 1` — this is the hypothesis `sqrtApproxD`
leaves to its caller, now discharged by proof rather than by `#guard`. -/
theorem sqrt_upper_premise (q : Q) (n : Nat) (hq : 0 ≤ q.val) :
    sqColourVal q n (sqrtBound q n) = 1 := by
  have hnumR : (0 : Rat) ≤ (q.num : Rat) := Q.num_nonneg_of_val_nonneg hq
  have hnumI : (0 : Int) ≤ q.num := by exact_mod_cast hnumR
  have hcast : ((q.num.toNat : Nat) : Rat) = (q.num : Rat) := by
    have hI : ((q.num.toNat : Nat) : Int) = q.num := Int.toNat_of_nonneg hnumI
    exact_mod_cast hI
  have hval_le : q.val ≤ (q.num : Rat) := by
    unfold Q.val
    exact div_le_self hnumR (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr q.den_ne_zero)
  have hb : ((sqrtBound q n : Nat) : Rat) / 2 ^ n = ((q.num.toNat : Nat) : Rat) + 1 := by
    unfold sqrtBound
    push_cast [twoPowN_cast]
    field_simp
  rw [sqColourVal_eq_one_iff, hb, hcast]
  nlinarith [hval_le, hnumR]

/-- Both premises at once: the caller's obligation, discharged. -/
theorem sqrt_premises (q : Q) (n : Nat) (hq : 0 ≤ q.val) :
    sqColourVal q n 0 = 0 ∧ sqColourVal q n (sqrtBound q n) = 1 :=
  ⟨sqrt_lower_premise q n hq, sqrt_upper_premise q n hq⟩

-- The computed bound is usable, not merely existent: the extracted search
-- run at `sqrtBound` returns the same roots the hand-picked bounds gave.
#guard sqrtApproxX (Q.ofNat 2) 4 (sqrtBound (Q.ofNat 2) 4) == 22
#guard sqrtApproxX (Q.ofNat 9) 0 (sqrtBound (Q.ofNat 9) 0) == 3
#guard sqrtApproxX (Q.of 1 4) 4 (sqrtBound (Q.of 1 4) 4) == 8

#print axioms sqrt_premises

/-! ## Step 4.2 — `UniformContinuity`'s Lipschitz premise, discharged

`uniContD` proves that *every* `2ʲ`-contracting map is uniformly continuous
with modulus `n + j`, taking the contraction as a premise.  The premise is an
arithmetic implication about a specific `f`, and the file discharges it by
`#guard` at sampled `x`, `y`, `n`.  Below it is proved for **all** `x`, `y`,
`m`, for each map the file guards.

Note what is and is not closed by this.  The *general* theorem was already
proved; what was outstanding is the side condition at each instance, and that
is what these three discharge.  A caller supplying some other `f` still owes
the same obligation for that `f` — there is no general theorem here saying
"every definable `f` contracts", because that is false. -/

theorem qabsExpr_val (d : Q) :
    (if d.num < 0 then Q.sub (Q.ofNat 0) d else d).val = |d.val| := by
  split
  · rename_i h
    have hn : (d.num : Rat) < 0 := by exact_mod_cast h
    have hlt : d.val < 0 := by unfold Q.val; exact div_neg_of_neg_of_pos hn d.den_cast_pos
    rw [Q.val_sub, Q.val_ofNat, abs_of_neg hlt]
    simp
  · rename_i h
    have hn : (0 : Rat) ≤ (d.num : Rat) := by exact_mod_cast Int.not_lt.mp h
    have hge : 0 ≤ d.val := by unfold Q.val; exact div_nonneg hn (le_of_lt d.den_cast_pos)
    rw [abs_of_nonneg hge]

/-- `close(k,x,y)` is exactly `|x − y| < 2⁻ᵏ`, on the Mathlib side. -/
theorem closeVal_eq_one_iff (k : Nat) (x y : Q) :
    closeVal k x y = 1 ↔ |x.val - y.val| < 1 / 2 ^ k := by
  unfold closeVal
  simp only [Q.ltN_eq_one_iff, qabsExpr_val, Q.val_sub, toQ_pow2neg_val]

theorem half_pow_succ (m : Nat) : (1 : Rat) / 2 ^ (m + 1) = (1 / 2 ^ m) / 2 := by
  rw [pow_succ]
  field_simp

theorem quarter_pow (m : Nat) : (1 : Rat) / 2 ^ (m + 2) = (1 / 2 ^ m) / 4 := by
  have hp : (2 : Rat) ^ m ≠ 0 := by positivity
  rw [pow_add]
  field_simp
  norm_num

/-- **Doubling contracts the dyadic scale by one**, at every input. -/
theorem doubling_lipschitz (x y : Q) (m : Nat) (h : closeVal (m + 1) x y = 1) :
    closeVal m (Q.add x x) (Q.add y y) = 1 := by
  rw [closeVal_eq_one_iff] at h ⊢
  rw [Q.val_add, Q.val_add,
    show x.val + x.val - (y.val + y.val) = 2 * (x.val - y.val) by ring, abs_mul]
  rw [half_pow_succ] at h
  have : |(2 : Rat)| = 2 := by norm_num
  rw [this]
  linarith

/-- **A translation is an isometry**, at every input. -/
theorem translation_lipschitz (x y : Q) (m : Nat) (h : closeVal (m + 0) x y = 1) :
    closeVal m (Q.add x (Q.ofNat 1)) (Q.add y (Q.ofNat 1)) = 1 := by
  rw [closeVal_eq_one_iff] at h ⊢
  rw [Q.val_add, Q.val_add,
    show x.val + (Q.ofNat 1).val - (y.val + (Q.ofNat 1).val) = x.val - y.val by ring]
  simpa using h

/-- **Quadrupling contracts the dyadic scale by two**, at every input. -/
theorem quadrupling_lipschitz (x y : Q) (m : Nat) (h : closeVal (m + 2) x y = 1) :
    closeVal m (Q.add (Q.add x x) (Q.add x x)) (Q.add (Q.add y y) (Q.add y y)) = 1 := by
  rw [closeVal_eq_one_iff] at h ⊢
  simp only [Q.val_add]
  rw [show x.val + x.val + (x.val + x.val) - (y.val + y.val + (y.val + y.val))
      = 4 * (x.val - y.val) by ring, abs_mul]
  rw [quarter_pow] at h
  have : |(4 : Rat)| = 4 := by norm_num
  rw [this]
  linarith

/-! ## Step 4.3 — `EFTC`'s claims: refuted as stated

Attempting these first turns up something prior to any arithmetic. `A1` is a
bare structure: `a`, `b`, `f`, `ω`, `δ` with **no fields relating them**.
Nothing says `ω` is a modulus of continuity for `f`, nothing says `δ` is a
modulus of uniform differentiability, and nothing says `a < b`.  Those
conditions are in the docstrings and in the manifesto's definition of `A₁`;
they are not in the type.  Since `Lemma1Claim`/`Lemma2Claim` quantify over an
arbitrary `A : A1`, they are **false**, and not for any subtle reason.

`lyingEx` is `sqEx` — `x²` on `[0,1]`, where the constructions are guarded and
correct — with `ω` and `δ` replaced by the constant `0`, which is a modulus of
nothing.  The effect is mechanical: `ω'` collapses to the constant `1`, so
`intN` is `2` at every precision and the Riemann sum never refines.

    lyingEx.intN     k = 2     for every k
    lyingEx.integral k = 3/4   for every k

so the error is stuck at `1/4` and beats `2⁻ᵏ` only for `k ≤ 1`.  Both
refutations below are by `decide`, i.e. checked by the kernel. -/

def lyingEx : A1 :=
  { a := Q.ofNat 0, b := Q.ofNat 1, f := fun x ↦ Q.mul x x,
    ω := fun _ ↦ 0, δ := fun _ ↦ 0 }

/-- **`Lemma1Claim` is false as stated.**  At `k = 0`, `x = 0`, `y = 1/2`:
the points are within `2⁻ω'⁽⁰⁾ = 1/2`, but the difference quotients are `1/4`
and `5/4`, a gap of `1`, which is not below `2⁰ = 1`. -/
theorem Lemma1Claim_false : ¬ Lemma1Claim lyingEx := by
  intro h
  exact absurd (h 0 (Q.ofNat 0) (Q.of 1 2) (by decide)) (by decide)

/-- Hence Theorem 2's statement is false as stated too. -/
theorem EFTC2Claim_false : ¬ EFTC2Claim lyingEx := fun h ↦ Lemma1Claim_false h.1

/-! ### `Lemma2Claim` is false too, but only by evaluation

`Lemma2Claim lyingEx` fails at `k = 2` — the error is `1/4` and the target is
`1/4`, so the strict inequality misses.  That is checked below by the
*evaluator*, not the kernel, and the difference is not a formality: no
`decide`-style proof about `integral` is possible at all, because `sumQ` is
written as a `do`-loop and the loop **does not reduce in the kernel**.
Measured, on the smallest possible instance:

    example : sumQ (fun _ ↦ Q.ofNat 1) 2 = Q.ofNat 2 := by rfl
    ⊢ failed — not definitionally equal

This is the `WellFounded.fix` wall the first-order development records for its
own value-level recursions, arriving from a different direction: `EFTC.lean`
chose the loop over a fold to survive `N = 32768` in the *interpreter*, and the
cost of that choice is that the kernel can no longer see through it.  Nothing
about `integral` can be settled by computation in a proof.  The headline
refutation does not depend on this, since `EFTC2Claim` is already refuted
through its first conjunct. -/

#guard Q.ltN (Q.abs (Q.sub (lyingEx.integral 2) (Q.ofNat 1)))
    (D.toQ (D.pow2neg 2)) == 0
#guard (List.range 6).map (fun k ↦ lyingEx.intN k) == [2, 2, 2, 2, 2, 2]

#print axioms Lemma1Claim_false
#print axioms EFTC2Claim_false

/-! ### The repaired statement

`IsA1` carries what the manifesto's `A₁` means and the Lean structure does
not: a derivative `f'` the `δ`-data is about, a nondegenerate interval, and
the two modulus properties.  It also restores the **interval restriction** —
`Lemma1Claim` quantifies over all `x y : Q`, including points outside `[a,b]`
where `f` is not even claimed continuous, and the manifesto's Lemma 1 does
not. -/

structure IsA1 (A : A1) where
  /-- the derivative the `δ`-data is about -/
  f' : Q → Q
  /-- the interval is nondegenerate -/
  ivl : A.a.val < A.b.val
  /-- `ω` is a modulus of continuity for `f` on `[a,b]` -/
  cont : ∀ (k : Nat) (x y : Q), A.a.val ≤ x.val → x.val ≤ A.b.val →
      A.a.val ≤ y.val → y.val ≤ A.b.val →
      |x.val - y.val| ≤ 1 / 2 ^ A.ω k → |(A.f x).val - (A.f y).val| < 1 / 2 ^ k
  /-- `δ` is a modulus of uniform differentiability for `f`, with derivative `f'` -/
  diff : ∀ (k : Nat) (x h : Q), A.a.val ≤ x.val → x.val ≤ A.b.val →
      A.a.val ≤ (Q.add x h).val → (Q.add x h).val ≤ A.b.val →
      h.val ≠ 0 → |h.val| ≤ 1 / 2 ^ A.δ k →
      |((A.f (Q.add x h)).val - (A.f x).val) / h.val - (f' x).val| < 1 / 2 ^ k

/-! ### The pieces the constructions rest on -/

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

theorem Q.num_ne_zero_of_val_ne_zero {q : Q} (h : q.val ≠ 0) : q.num ≠ 0 := by
  intro hn
  apply h
  unfold Q.val
  rw [hn]
  simp

theorem stepSize_val (A : A1) (k : Nat) :
    (A.stepSize k).val = min (1 / 2 ^ A.δ (k + 3)) ((A.b.val - A.a.val) / 4) := by
  unfold A1.stepSize
  rw [Qmin_val, toQ_pow2neg_val, Q.val_div _ _ (by decide), Q.val_sub, Q.val_ofNat]
  norm_num

theorem stepSize_pos (A : A1) (H : IsA1 A) (k : Nat) : 0 < (A.stepSize k).val := by
  rw [stepSize_val]
  refine lt_min (by positivity) ?_
  have := H.ivl
  linarith

theorem stepRight_iff (A : A1) (x : Q) :
    A.stepRight x = true ↔ x.val ≤ (A.a.val + A.b.val) / 2 := by
  unfold A1.stepRight
  rw [Qle_eq_true_iff, Q.val_div _ _ (by decide), Q.val_add, Q.val_ofNat]
  norm_num

/-- **Lemma 1's computable half, proved.**  The extracted `derivEval` really
does approximate the derivative to `2⁻⁽ᵏ⁺³⁾` at every point of `[a,b]` — this
is what makes the `EFTC2` witness a statement about `f'` rather than about the
numeral `f b − f a`.  The endpoint-safe sign is what the proof spends its
effort on: `h₀ ≤ (b−a)/4` and the midpoint test together keep `x + h` inside
`[a,b]` in both branches. -/
theorem derivEval_approx (A : A1) (H : IsA1 A) (k : Nat) (x : Q)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val) :
    |(A.derivEval k x).val - (H.f' x).val| < 1 / 2 ^ (k + 3) := by
  have hs := stepSize_pos A H k
  have hmin1 : (A.stepSize k).val ≤ 1 / 2 ^ A.δ (k + 3) := by
    rw [stepSize_val]; exact min_le_left _ _
  have hmin2 : (A.stepSize k).val ≤ (A.b.val - A.a.val) / 4 := by
    rw [stepSize_val]; exact min_le_right _ _
  cases hr : A.stepRight x
  · -- step left: `x` is in the right half, so `x − h₀ ≥ a`
    have hxm : ¬ (x.val ≤ (A.a.val + A.b.val) / 2) := by
      rw [← stepRight_iff]; simp [hr]
    have hnegv : (Q.neg (A.stepSize k)).val = -(A.stepSize k).val := Q.val_neg _
    have hne : (Q.neg (A.stepSize k)).val ≠ 0 := by rw [hnegv]; linarith
    have hnum : (Q.neg (A.stepSize k)).num ≠ 0 := Q.num_ne_zero_of_val_ne_zero hne
    have hin1 : A.a.val ≤ (Q.add x (Q.neg (A.stepSize k))).val := by
      rw [Q.val_add, hnegv]; push_neg at hxm; linarith
    have hin2 : (Q.add x (Q.neg (A.stepSize k))).val ≤ A.b.val := by
      rw [Q.val_add, hnegv]; linarith
    have habs : |(Q.neg (A.stepSize k)).val| ≤ 1 / 2 ^ A.δ (k + 3) := by
      rw [hnegv, abs_of_neg (by linarith : -(A.stepSize k).val < 0)]; linarith
    simp only [A1.derivEval, hr, Bool.false_eq_true, if_false]
    rw [Q.val_div _ _ hnum, Q.val_sub]
    exact H.diff (k + 3) x (Q.neg (A.stepSize k)) hxa hxb hin1 hin2 hne habs
  · -- step right: `x` is in the left half, so `x + h₀ ≤ b`
    have hxm : x.val ≤ (A.a.val + A.b.val) / 2 := (stepRight_iff A x).mp hr
    have hne : (A.stepSize k).val ≠ 0 := ne_of_gt hs
    have hnum : (A.stepSize k).num ≠ 0 := Q.num_ne_zero_of_val_ne_zero hne
    have hin1 : A.a.val ≤ (Q.add x (A.stepSize k)).val := by
      rw [Q.val_add]; linarith
    have hin2 : (Q.add x (A.stepSize k)).val ≤ A.b.val := by
      rw [Q.val_add]; linarith
    have habs : |(A.stepSize k).val| ≤ 1 / 2 ^ A.δ (k + 3) := by
      rw [abs_of_pos hs]; exact hmin1
    simp only [A1.derivEval, hr, if_true]
    rw [Q.val_div _ _ hnum, Q.val_sub]
    exact H.diff (k + 3) x (A.stepSize k) hxa hxb hin1 hin2 hne habs

#print axioms derivEval_approx

/-! ### What the rest of Lemma 1 needs, and why it is not here

The remaining half — that `derivEval` is *uniformly continuous* with modulus
`ω'`, which is `Lemma1Claim`'s actual content — does not follow from the
manifesto's §5.2 argument as written.  Three obstructions, each found by
attempting the proof, each stated so it can be checked rather than taken on
trust:

**1. Pointwise sign versus common sign.**  §5.2 bounds `|DQ(x) − DQ(y)|` by
algebraic cancellation:

    DQ(x) − DQ(y) = [(f(x+h) − f(y+h)) − (f(x) − f(y))] / h

which needs `x` and `y` to use the **same** `h`.  `stepRight` chooses the sign
*pointwise*, so two points either side of the midpoint — arbitrarily close to
each other — use opposite steps and nothing cancels.  §5.2's "for two points
within `(b−a)/2` a common sign is admissible" is true, but it is a statement
about a sign one may *choose*, not about the one `derivEval` does choose.
Repairing it means going through `f'` with a three-term triangle inequality,
using an auxiliary common-step quotient that is not the implemented one.

**2. Small intervals.**  `h₀ = min(2⁻ᵟ⁽ᵏ⁺³⁾, (b−a)/4)`, and the estimate
divides by `h₀`.  When the second term is the minimum, `1/h₀ = 4/(b−a)`, and
`ω'(k) = max(ω(k+5+δ(k+3)), η₂)` contains **no term bounding `4/(b−a)`** —
`η₂` bounds proximity of `x` and `y`, not the reciprocal step.  The bound
closes exactly when `2⁻ᵟ⁽ᵏ⁺³⁾ ≤ (b−a)/4`, which holds for all large `k`
whenever `δ → ∞`, but `Lemma1Claim` is asserted at every `k`.

**3. Non-monotone moduli.**  Even in the good regime, the three-term route
needs `ω` evaluated at `k+4+δ(k+4)`, while the construction supplies it at
`k+5+δ(k+3)`.  For arbitrary `ω` and `δ` neither dominates the other, and
neither `A1` nor `IsA1` requires them to be monotone.

None of these is an arithmetic gap of the kind the rule base was blocked on;
all three are about the *construction*.  Obstruction 2 in particular says
`omega'` as implemented is not large enough in general — a statement about
`EFTC.lean`'s code, not about its proof.

**Lemma 2 is further off, and for a different reason.**  §5.2 gets
`∫ f' = f(b) − f(a)` from *classical* FTC2 and then estimates the quadrature.
There is no real integral in this shallow embedding, so the classical step has
nothing to be imported into: the only available route is a discrete
telescoping argument, and the Riemann mesh `L/N` and the difference-quotient
step `h₀` are unrelated quantities here, so the sum does not telescope.  On
top of that, nothing about `integral` can be settled by computation inside a
proof, per the kernel-reduction measurement above. -/

#print axioms doubling_lipschitz
#print axioms translation_lipschitz
#print axioms quadrupling_lipschitz

end HAomega
