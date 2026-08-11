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

/-- The property `A1.diff` asserts of its witness, named so it can be carried
around once `A.diff` has been opened. -/
def IsDeriv (A : A1) (F : Q → Q) : Prop :=
  ∀ (k : Nat) (x h : Q), Qle A.a x = true → Qle x A.b = true →
    Qle A.a (Q.add x h) = true → Qle (Q.add x h) A.b = true →
    h.num ≠ 0 → Qle (Q.abs h) (D.toQ (D.pow2neg (A.δ k))) = true →
    Q.ltN (Q.abs (Q.sub (Q.div (Q.sub (A.f (Q.add x h)) (A.f x)) h) (F x)))
      (D.toQ (D.pow2neg k)) = 1

/-- **Lemma 1's computable half, proved.**  The extracted `derivEval` really
does approximate the derivative to `2⁻⁽ᵏ⁺³⁾` at every point of `[a,b]` — this
is what makes the `EFTC2` witness a statement about `f'` rather than about the
numeral `f b − f a`.  The endpoint-safe sign is what the proof spends its
effort on: `h₀ ≤ (b−a)/4` and the midpoint test together keep `x + h` inside
`[a,b]` in both branches. -/
theorem derivEval_approx (A : A1) {F : Q → Q} (hF : IsDeriv A F)
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

/-! ## Lemma 1, the uniform-continuity half

The estimate needs three things the file did not have: that `η₂` really
satisfies `2⁻ᵑ² ≤ (b−a)/2`, a *lower* bound on the step (the reciprocal is what
the estimate multiplies by), and a step admissible for **both** points. -/

/-- `2⁻ᵐ ≤ 2⁻ⁿ` when `n ≤ m`. -/
theorem inv_pow_le {m n : Nat} (h : n ≤ m) : (1 : Rat) / 2 ^ m ≤ 1 / 2 ^ n := by
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) h

/-- The bounded search returns a value with the property it is searching for,
provided the fuel reaches one. -/
theorem etaAux_spec (L : Q) (fuel : Nat) : ∀ acc : Nat,
    (D.toQ (D.pow2neg (acc + fuel))).val ≤ (Q.div L (Q.ofNat 2)).val →
    (D.toQ (D.pow2neg (etaAux L acc fuel))).val ≤ (Q.div L (Q.ofNat 2)).val := by
  induction fuel with
  | zero => intro acc h; simpa using h
  | succ n ih =>
    intro acc h
    simp only [etaAux]
    split
    · rename_i hc; exact (Qle_eq_true_iff _ _).mp hc
    · exact ih (acc + 1) (by rw [show acc + 1 + n = acc + (n + 1) by ring]; exact h)

/-- **`η₂` is what it claims to be.**  The fuel is `L.den + 2` and `η = L.den+1`
already works, so the search cannot exhaust. -/
theorem eta2_spec (A : A1) : (1 : Rat) / 2 ^ A.eta2 ≤ (A.b.val - A.a.val) / 2 := by
  unfold A1.eta2
  set L := Q.sub A.b A.a with hLdef
  have hL : L.val = A.b.val - A.a.val := Q.val_sub _ _
  have hpos : 0 < L.val := by rw [hL]; linarith [A.ivl_val]
  have hdiv : (Q.div L (Q.ofNat 2)).val = (A.b.val - A.a.val) / 2 := by
    rw [Q.val_div _ _ (by decide), hL, Q.val_ofNat]; norm_num
  have hd : (0 : Rat) < (L.den : Rat) := L.den_cast_pos
  have hnumR : (0 : Rat) < (L.num : Rat) := by
    have hpos' : 0 < (L.num : Rat) / (L.den : Rat) := hpos
    rcases div_pos_iff.mp hpos' with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr (le_of_lt hd))
  have hnumI : (0 : Int) < L.num := by exact_mod_cast hnumR
  have h1 : (1 : Rat) ≤ (L.num : Rat) := by
    have hi : (1 : Int) ≤ L.num := by omega
    exact_mod_cast hi
  have hge : (1 : Rat) / (L.den : Rat) ≤ L.val := by
    have hnn : (0 : Rat) ≤ ((L.num : Rat) - 1) / (L.den : Rat) :=
      div_nonneg (by linarith) (le_of_lt hd)
    have heq : ((L.num : Rat) - 1) / (L.den : Rat)
        = (L.num : Rat) / (L.den : Rat) - 1 / (L.den : Rat) := by field_simp
    rw [heq] at hnn
    unfold Q.val
    linarith
  have hlt : (L.den : Rat) < 2 ^ L.den := by exact_mod_cast Nat.lt_two_pow_self
  have hsplit : (2 : Rat) ^ (L.den + 2) = 2 ^ L.den * 4 := by rw [pow_add]; norm_num
  have h2d : (2 : Rat) * (L.den : Rat) ≤ 2 ^ (L.den + 2) := by rw [hsplit]; linarith
  have hstart : (D.toQ (D.pow2neg (0 + (L.den + 2)))).val ≤ (Q.div L (Q.ofNat 2)).val := by
    rw [toQ_pow2neg_val, hdiv, Nat.zero_add, ← hL]
    calc (1 : Rat) / 2 ^ (L.den + 2) ≤ 1 / (2 * (L.den : Rat)) :=
          one_div_le_one_div_of_le (by linarith) h2d
      _ = (1 / (L.den : Rat)) / 2 := by field_simp
      _ ≤ L.val / 2 := by linarith
  have hfin := etaAux_spec L (L.den + 2) 0 hstart
  rw [toQ_pow2neg_val, hdiv] at hfin
  exact hfin

/-- The index `ω` is evaluated at, inside `omega'`. -/
abbrev stepIx (A : A1) (k : Nat) : Nat := Nat.max (A.δ (k + 3)) (A.eta2 + 1)

/-- **A lower bound on the step** — the reciprocal is what the estimate
multiplies by, and it is bounded in *both* branches of the `min`: by `δ` in
one, and by `η₂` in the other.  Bounding only the first is the gap the old
`omega'` had. -/
theorem stepSize_ge (A : A1) (k : Nat) :
    (1 : Rat) / 2 ^ stepIx A k ≤ (A.stepSize k).val := by
  rw [stepSize_val]
  refine le_min (inv_pow_le (Nat.le_max_left _ _)) ?_
  have h := eta2_spec A
  have h1 : (1 : Rat) / 2 ^ (A.eta2 + 1) ≤ (A.b.val - A.a.val) / 4 := by
    rw [halve_pow]; linarith
  exact le_trans (inv_pow_le (Nat.le_max_right _ _)) h1

/-- **The common step.**  If `x` and `y` are within `(b−a)/2` and the step is
at most `(b−a)/4`, then one of `±h₀` keeps *both* inside `[a,b]`.  This is what
lets the estimate use one step for two points, which the pointwise
`stepRight` does not. -/
theorem common_step (A : A1) (k : Nat) (x y : Q)
    (_hxa : A.a.val ≤ x.val) (_hxb : x.val ≤ A.b.val)
    (_hya : A.a.val ≤ y.val) (_hyb : y.val ≤ A.b.val)
    (hxy : |x.val - y.val| ≤ (A.b.val - A.a.val) / 2) :
    (x.val + (A.stepSize k).val ≤ A.b.val ∧ y.val + (A.stepSize k).val ≤ A.b.val)
      ∨ (A.a.val ≤ x.val - (A.stepSize k).val ∧ A.a.val ≤ y.val - (A.stepSize k).val) := by
  have hs := stepSize_pos A k
  have hq : (A.stepSize k).val ≤ (A.b.val - A.a.val) / 4 := by
    rw [stepSize_val]; exact min_le_right _ _
  obtain ⟨hd1, hd2⟩ := abs_le.mp hxy
  by_cases hc : x.val + (A.stepSize k).val ≤ A.b.val ∧ y.val + (A.stepSize k).val ≤ A.b.val
  · exact Or.inl hc
  · refine Or.inr ?_
    rcases not_and_or.mp hc with h | h <;> push_neg at h <;> constructor <;> linarith

/-! ### The estimate

Four terms of `2⁻⁽ᵏ⁺³⁾` and one of `2⁻⁽ᵏ⁺⁴⁾`, summing to
`2⁻⁽ᵏ⁺¹⁾ + 2⁻⁽ᵏ⁺⁴⁾ < 2⁻ᵏ`.  The route goes through `F` precisely because
`derivEval` picks its step pointwise: `DE(x)` and `DE(y)` may use *opposite*
steps, so nothing cancels between them directly.  Both are near `F`, and both
common-step quotients are near `F`, and *those* cancel. -/

theorem cont_val (A : A1) (p : Nat) (u v : Q)
    (hua : A.a.val ≤ u.val) (hub : u.val ≤ A.b.val)
    (hva : A.a.val ≤ v.val) (hvb : v.val ≤ A.b.val)
    (h : |u.val - v.val| ≤ 1 / 2 ^ A.ω p) :
    |(A.f u).val - (A.f v).val| < 1 / 2 ^ p := by
  have := A.cont p u v ((Qle_eq_true_iff _ _).mpr hua) ((Qle_eq_true_iff _ _).mpr hub)
    ((Qle_eq_true_iff _ _).mpr hva) ((Qle_eq_true_iff _ _).mpr hvb)
    ((Qle_eq_true_iff _ _).mpr (by rw [Q.val_abs, Q.val_sub, toQ_pow2neg_val]; exact h))
  rwa [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val] at this

theorem diff_val (A : A1) {F : Q → Q} (hF : IsDeriv A F) (j : Nat) (x s : Q)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (h1 : A.a.val ≤ (Q.add x s).val) (h2 : (Q.add x s).val ≤ A.b.val)
    (hs : s.num ≠ 0) (hstep : |s.val| ≤ 1 / 2 ^ A.δ j) :
    |((A.f (Q.add x s)).val - (A.f x).val) / s.val - (F x).val| < 1 / 2 ^ j := by
  have := hF j x s ((Qle_eq_true_iff _ _).mpr hxa) ((Qle_eq_true_iff _ _).mpr hxb)
    ((Qle_eq_true_iff _ _).mpr h1) ((Qle_eq_true_iff _ _).mpr h2) hs
    ((Qle_eq_true_iff _ _).mpr (by rw [Q.val_abs, toQ_pow2neg_val]; exact hstep))
  rwa [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, Q.val_div _ _ hs, Q.val_sub,
    toQ_pow2neg_val] at this

/-- The estimate, **given** a step admissible for both points. -/
theorem derivEval_uc_of_step (A : A1) {F : Q → Q} (hF : IsDeriv A F) (k : Nat) (x y s : Q)
    (hs : s.num ≠ 0) (hsabs : |s.val| = (A.stepSize k).val)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (hya : A.a.val ≤ y.val) (hyb : y.val ≤ A.b.val)
    (hxs1 : A.a.val ≤ (Q.add x s).val) (hxs2 : (Q.add x s).val ≤ A.b.val)
    (hys1 : A.a.val ≤ (Q.add y s).val) (hys2 : (Q.add y s).val ≤ A.b.val)
    (hcl : |x.val - y.val| ≤ 1 / 2 ^ A.omega' k) :
    |(A.derivEval k x).val - (A.derivEval k y).val| < 1 / 2 ^ k := by
  have hsv : 0 < |s.val| := by rw [hsabs]; exact stepSize_pos A k
  have hstep : |s.val| ≤ 1 / 2 ^ A.δ (k + 3) := by
    rw [hsabs, stepSize_val]; exact min_le_left _ _
  have hDEx := derivEval_approx A hF k x hxa hxb
  have hDEy := derivEval_approx A hF k y hya hyb
  have hqx := diff_val A hF (k + 3) x s hxa hxb hxs1 hxs2 hs hstep
  have hqy := diff_val A hF (k + 3) y s hya hyb hys1 hys2 hs hstep
  have hwo : (1 : Rat) / 2 ^ A.omega' k ≤ 1 / 2 ^ A.ω (k + 5 + stepIx A k) :=
    inv_pow_le (Nat.le_max_left _ _)
  have hc1 : |(A.f (Q.add x s)).val - (A.f (Q.add y s)).val| < 1 / 2 ^ (k + 5 + stepIx A k) :=
    cont_val A _ _ _ hxs1 hxs2 hys1 hys2 (by
      rw [Q.val_add, Q.val_add,
        show x.val + s.val - (y.val + s.val) = x.val - y.val by ring]
      exact le_trans hcl hwo)
  have hc2 : |(A.f x).val - (A.f y).val| < 1 / 2 ^ (k + 5 + stepIx A k) :=
    cont_val A _ _ _ hxa hxb hya hyb (le_trans hcl hwo)
  -- the two common-step quotients agree to `2⁻⁽ᵏ⁺⁴⁾`
  have hquot : |((A.f (Q.add x s)).val - (A.f x).val) / s.val
      - ((A.f (Q.add y s)).val - (A.f y).val) / s.val| < 1 / 2 ^ (k + 4) := by
    rw [div_sub_div_same, abs_div, div_lt_iff₀ hsv]
    have hMle : (1 : Rat) / 2 ^ stepIx A k ≤ |s.val| := by
      rw [hsabs]; exact stepSize_ge A k
    have hp4 : (0 : Rat) < 1 / 2 ^ (k + 4) := by positivity
    have hpow : (2 : Rat) * (1 / 2 ^ (k + 5 + stepIx A k))
        = 1 / 2 ^ (k + 4) * (1 / 2 ^ stepIx A k) := by
      rw [show k + 5 + stepIx A k = k + 4 + stepIx A k + 1 by ring, pow_succ, pow_add]
      field_simp
    rw [show (A.f (Q.add x s)).val - (A.f x).val - ((A.f (Q.add y s)).val - (A.f y).val)
        = ((A.f (Q.add x s)).val - (A.f (Q.add y s)).val)
          - ((A.f x).val - (A.f y).val) by ring]
    calc |((A.f (Q.add x s)).val - (A.f (Q.add y s)).val)
            - ((A.f x).val - (A.f y).val)|
        ≤ |(A.f (Q.add x s)).val - (A.f (Q.add y s)).val - 0|
            + |0 - ((A.f x).val - (A.f y).val)| := abs_sub_le _ _ _
      _ = |(A.f (Q.add x s)).val - (A.f (Q.add y s)).val|
            + |(A.f x).val - (A.f y).val| := by rw [sub_zero, zero_sub, abs_neg]
      _ < 2 * (1 / 2 ^ (k + 5 + stepIx A k)) := by linarith
      _ = 1 / 2 ^ (k + 4) * (1 / 2 ^ stepIx A k) := hpow
      _ ≤ 1 / 2 ^ (k + 4) * |s.val| := by
          exact mul_le_mul_of_nonneg_left hMle (le_of_lt hp4)
  -- assemble
  have t1 : |(A.derivEval k x).val - (A.derivEval k y).val|
      ≤ |(A.derivEval k x).val - ((A.f (Q.add x s)).val - (A.f x).val) / s.val|
        + |((A.f (Q.add x s)).val - (A.f x).val) / s.val - (A.derivEval k y).val| :=
    abs_sub_le _ _ _
  have t2 : |((A.f (Q.add x s)).val - (A.f x).val) / s.val - (A.derivEval k y).val|
      ≤ |((A.f (Q.add x s)).val - (A.f x).val) / s.val
          - ((A.f (Q.add y s)).val - (A.f y).val) / s.val|
        + |((A.f (Q.add y s)).val - (A.f y).val) / s.val - (A.derivEval k y).val| :=
    abs_sub_le _ _ _
  have t3 : |(A.derivEval k x).val - ((A.f (Q.add x s)).val - (A.f x).val) / s.val|
      ≤ |(A.derivEval k x).val - (F x).val|
        + |(F x).val - ((A.f (Q.add x s)).val - (A.f x).val) / s.val| :=
    abs_sub_le _ _ _
  have t4 : |((A.f (Q.add y s)).val - (A.f y).val) / s.val - (A.derivEval k y).val|
      ≤ |((A.f (Q.add y s)).val - (A.f y).val) / s.val - (F y).val|
        + |(F y).val - (A.derivEval k y).val| :=
    abs_sub_le _ _ _
  rw [abs_sub_comm (F x).val] at t3
  rw [abs_sub_comm (F y).val] at t4
  have p3 : (1 : Rat) / 2 ^ (k + 3) = 1 / 2 ^ k / 8 := by rw [pow_add]; field_simp; norm_num
  have p4 : (1 : Rat) / 2 ^ (k + 4) = 1 / 2 ^ k / 16 := by rw [pow_add]; field_simp; norm_num
  have hpk : (0 : Rat) < 1 / 2 ^ k := by positivity
  linarith

/-- **Lemma 1, the uniform-continuity half.**  Every `A₁` representation's
extracted derivative is uniformly continuous with modulus `ω'`. -/
theorem derivEval_uniformly_continuous (A : A1) (k : Nat) (x y : Q)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (hya : A.a.val ≤ y.val) (hyb : y.val ≤ A.b.val)
    (hcl : |x.val - y.val| ≤ 1 / 2 ^ A.omega' k) :
    |(A.derivEval k x).val - (A.derivEval k y).val| < 1 / 2 ^ k := by
  obtain ⟨F, hF⟩ := A.diff
  have hs := stepSize_pos A k
  have hnum : (A.stepSize k).num ≠ 0 := Q.num_ne_zero_of_val_ne_zero (ne_of_gt hs)
  have hprox : |x.val - y.val| ≤ (A.b.val - A.a.val) / 2 :=
    le_trans hcl (le_trans (inv_pow_le (Nat.le_max_right _ _)) (eta2_spec A))
  rcases common_step A k x y hxa hxb hya hyb hprox with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine derivEval_uc_of_step A hF k x y (A.stepSize k) hnum (abs_of_pos hs)
      hxa hxb hya hyb ?_ ?_ ?_ ?_ hcl <;> rw [Q.val_add] <;> linarith
  · have hnegv : (Q.neg (A.stepSize k)).val = -(A.stepSize k).val := Q.val_neg _
    have hnegnum : (Q.neg (A.stepSize k)).num ≠ 0 :=
      Q.num_ne_zero_of_val_ne_zero (by rw [hnegv]; linarith)
    refine derivEval_uc_of_step A hF k x y (Q.neg (A.stepSize k)) hnegnum ?_
      hxa hxb hya hyb ?_ ?_ ?_ ?_ hcl
    · rw [hnegv, abs_of_neg (by linarith : -(A.stepSize k).val < 0)]
      ring
    · rw [Q.val_add, hnegv]; linarith
    · rw [Q.val_add, hnegv]; linarith
    · rw [Q.val_add, hnegv]; linarith
    · rw [Q.val_add, hnegv]; linarith

/-- **Lemma 1**, in the form `EFTC.lean` states it. -/
theorem lemma1 (A : A1) : Lemma1Claim A := by
  intro k x y hxa hxb hya hyb h
  rw [Qle_eq_true_iff] at hxa hxb hya hyb
  rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val] at h
  rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val]
  exact derivEval_uniformly_continuous A k x y hxa hxb hya hyb h

#print axioms derivEval_uniformly_continuous
#print axioms lemma1

/-! ### Lemma 1 is done; what Lemma 2 still needs

Both halves of Lemma 1 are proved: `derivEval_approx` (it computes the
derivative) and `derivEval_uniformly_continuous` / `lemma1` (it does so
uniformly continuously, with modulus `ω'`).  Getting there needed four
corrections, all to the *constructions*, none to the arithmetic:

1. **`omega'` was too small.**  The estimate divides by
   `h₀ = min(2⁻ᵟ⁽ᵏ⁺³⁾, (b−a)/4)`, and when the second term is the minimum the
   factor is `4/(b−a)`, which a `δ`-only index cannot bound.  `omega'` now
   carries `max(δ(k+3), η₂+1)`.
2. **`etaAux` returned `0` when out of fuel** — a value that does not satisfy
   the property being searched for, so a caller past the fuel got a confident
   wrong answer.  It now returns the accumulator, and `eta2`'s fuel is taken
   from the data (`L.den + 2`), which provably cannot exhaust.
3. **`Lemma1Claim` was missing its interval premises**, so it ranged over
   points where `A1` says nothing about `f`.
4. **`sqEx.δ` was off by one** — caught by having to discharge `diff`.

The one mathematical subtlety is that `derivEval` picks its step *pointwise*,
so `DE(x)` and `DE(y)` may use opposite steps and nothing cancels between them
directly.  The proof therefore goes through `F`: both `DE`s are near `F` by
`derivEval_approx`, both *common-step* quotients are near `F` by `diff`, and
those two cancel.  The common step exists by `common_step` — if `|x−y| ≤
(b−a)/2` and `h₀ ≤ (b−a)/4` then one of `±h₀` keeps both points inside.

**Lemma 2 is a different problem and is still open.**  §5.2 gets
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
that the kernel can no longer see through it.  `ceilLog2Aux`, which Lemma 2's
`ℓ` comes from, still has the fuel-exhaustion bug fixed in `etaAux` at (2)
above; it is not on Lemma 1's path, and has been left alone. -/

#print axioms doubling_lipschitz
#print axioms translation_lipschitz
#print axioms quadrupling_lipschitz

end HAomega