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
* `EFTC`'s `Lemma1Claim`/`Lemma2Claim` — the **computable half of Lemma 1** is
  proved, from `A1`'s own `diff` field. The rest is not; the obstructions are
  set out at the end.

An earlier version of this file refuted `Lemma1Claim` and `EFTC2Claim`
outright, because `A1` was five pieces of unrelated data and its `ω`, `δ` were
moduli of nothing. Those refutations are **gone, and their absence is the
result**: `A1` now carries `ivl`, `cont` and `diff`, so the counterexample —
the `x²` instance with its moduli replaced by the constant `0` — can no longer
be constructed. The record of what it showed is in `docs/haomega/STATUS.md`.
-/

namespace HAomega
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

/-- **Doubling contracts the dyadic scale by one**, at every input. -/
theorem doubling_lipschitz (x y : Q) (m : Nat) (h : closeVal (m + 1) x y = 1) :
    closeVal m (Q.add x x) (Q.add y y) = 1 := by
  rw [closeVal_eq_one_iff] at h ⊢
  rw [Q.val_add, Q.val_add,
    show x.val + x.val - (y.val + y.val) = 2 * (x.val - y.val) by ring, abs_mul]
  rw [halve_pow] at h
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
/-! ## Step 4.3 — Lemma 1's computable half

`A1` now carries the modulus conditions, so they can simply be used.  The
work below is not the analysis — that is in the hypothesis — but the
**endpoint bookkeeping**: showing the step `derivEval` actually takes is one
the `diff` field accepts, which is where the `min(2⁻ᵟ, (b−a)/4)` and the
midpoint sign test earn their keep. -/

theorem A1.ivl_val (A : A1) : A.a.val < A.b.val := (Q.ltN_eq_one_iff _ _).mp A.ivl

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

theorem stepSize_pos (A : A1) (k : Nat) : 0 < (A.stepSize k).val := by
  rw [stepSize_val]
  refine lt_min (by positivity) ?_
  have := A.ivl_val
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
`[a,b]` in both branches. -/theorem derivEval_approx (A : A1) {F : Q → Q}
    (hF : ∀ (k : Nat) (x h : Q), Qle A.a x = true → Qle x A.b = true →
      Qle A.a (Q.add x h) = true → Qle (Q.add x h) A.b = true →
      h.num ≠ 0 → Qle (Q.abs h) (D.toQ (D.pow2neg (A.δ k))) = true →
      Q.ltN (Q.abs (Q.sub (Q.div (Q.sub (A.f (Q.add x h)) (A.f x)) h) (F x)))
        (D.toQ (D.pow2neg k)) = 1)
    (k : Nat) (x : Q) (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val) :
    |(A.derivEval k x).val - (F x).val| < 1 / 2 ^ (k + 3) := by
  have hs := stepSize_pos A k
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
    have := hF (k + 3) x (Q.neg (A.stepSize k))
      ((Qle_eq_true_iff _ _).mpr hxa) ((Qle_eq_true_iff _ _).mpr hxb)
      ((Qle_eq_true_iff _ _).mpr hin1) ((Qle_eq_true_iff _ _).mpr hin2) hnum
      ((Qle_eq_true_iff _ _).mpr (by rw [Q.val_abs, toQ_pow2neg_val]; exact habs))
    rwa [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, Q.val_div _ _ hnum, Q.val_sub,
      toQ_pow2neg_val] at this
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
    have := hF (k + 3) x (A.stepSize k)
      ((Qle_eq_true_iff _ _).mpr hxa) ((Qle_eq_true_iff _ _).mpr hxb)
      ((Qle_eq_true_iff _ _).mpr hin1) ((Qle_eq_true_iff _ _).mpr hin2) hnum
      ((Qle_eq_true_iff _ _).mpr (by rw [Q.val_abs, toQ_pow2neg_val]; exact habs))
    rwa [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, Q.val_div _ _ hnum, Q.val_sub,
      toQ_pow2neg_val] at this

/-- **The extracted derivative approximates *the* derivative.**  Same
statement, drawing the witness from `A1`'s own `diff` field instead of taking
it as a parameter: one `F`, uniformly in `k` and `x`. -/
theorem derivEval_approx_of_diff (A : A1) :
    ∃ F : Q → Q, ∀ (k : Nat) (x : Q), A.a.val ≤ x.val → x.val ≤ A.b.val →
      |(A.derivEval k x).val - (F x).val| < 1 / 2 ^ (k + 3) := by
  obtain ⟨F, hF⟩ := A.diff
  exact ⟨F, fun k x hxa hxb ↦ derivEval_approx A hF k x hxa hxb⟩

/-! ### What the rest of Lemma 1 needs

The remaining half — that `derivEval` is *uniformly continuous* with modulus
`ω'`, which is `Lemma1Claim`'s actual content — is **not proved here**.  What
has changed is why.  Three obstructions were recorded when `omega'` was the
old `ω(k+5+δ(k+3))` and `A1` carried no hypotheses; two are now gone, and it
is worth being exact about which.

**Gone — the reciprocal step.**  When `(b−a)/4` is the smaller half of `h₀`,
the estimate divides by `4/(b−a)`, and the old index had no term bounding it.
`omega'` now carries `max(δ(k+3), η₂+1)` inside `ω`'s argument, and
`2⁻ᵑ² ≤ (b−a)/2` gives `1/h₀ ≤ 2^max(δ(k+3), η₂+1)` in both branches of the
`min`.  That is what the fix is for.

**Gone — the index mismatch.**  It was an artefact of routing the estimate
through `f'` at precision `k+4`.  Taken at `k+3` instead — the precision
`stepSize` itself uses — the bookkeeping closes with room to spare, writing
`M` for `max(δ(k+3), η₂+1)` and `p` for `k+5+M`:

    |F(x) − DQ(x)|, |F(y) − DQ(y)| < 2⁻⁽ᵏ⁺³⁾           (diff, at j = k+3)
    |DQ(x) − DQ(y)| ≤ 2·2⁻ᵖ·2^M = 2⁻⁽ᵏ⁺⁴⁾              (cont, at p)
    |F(x) − F(y)| < 2⁻⁽ᵏ⁺²⁾ + 2⁻⁽ᵏ⁺⁴⁾
    |DE(x) − DE(y)| < 2⁻⁽ᵏ⁺¹⁾ + 2⁻⁽ᵏ⁺⁴⁾ < 2⁻ᵏ          (derivEval_approx twice)

**Remaining — the common step, and the assembly.**  `DQ` above is a difference
quotient at a step admissible for *both* points, which is not the step
`derivEval` takes: `stepRight` chooses the sign pointwise, so two points either
side of the midpoint use opposite steps and the cancellation in line two does
not happen for them.  Routing through `F` is what avoids that, and it needs the
pigeonhole — if `|x−y| ≤ (b−a)/2` and `h₀ ≤ (b−a)/4` then one of `±h₀` is
admissible for both, since either `max(x,y) ≤ b − h₀` or else
`min(x,y) ≥ a + h₀`.  That argument, and the assembly of the four lines above,
are **not formalized**.  The arithmetic closes; the Lean proof is not written.

**Lemma 2 is further off, and for a different reason.**  §5.2 gets
`∫ f' = f(b) − f(a)` from *classical* FTC2 and then estimates the quadrature.
There is no real integral in this shallow embedding, so the classical step has
nothing to be imported into: the only available route is a discrete
telescoping argument, and the Riemann mesh `L/N` and the difference-quotient
step `h₀` are unrelated quantities here, so the sum does not telescope.  On top
of that, nothing about `integral` can be settled by computation inside a proof:
`sumQ` is a `do`-loop and **does not reduce in the kernel**, measured on the
smallest instance —

    example : sumQ (fun _ ↦ Q.ofNat 1) 2 = Q.ofNat 2 := by rfl   -- fails

the `WellFounded.fix` wall the first-order development records for its own
value-level recursions, reached from the opposite direction: the loop was
chosen so the sums survive `N = 32768` in the *interpreter*, and the cost is
that the kernel can no longer see through it. -/

#print axioms derivEval_approx
#print axioms derivEval_approx_of_diff

#print axioms doubling_lipschitz
#print axioms translation_lipschitz
#print axioms quadrupling_lipschitz

end HAomega