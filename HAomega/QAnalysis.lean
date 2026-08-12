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
theorem abs_add_le' (a b : Rat) : |a + b| ≤ |a| + |b| := by
  simpa using abs_sub_le a 0 (-b)

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

theorem cont_val (A : A0) (p : Nat) (u v : Q)
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
    cont_val A.toA0 _ _ _ hxs1 hxs2 hys1 hys2 (by
      rw [Q.val_add, Q.val_add,
        show x.val + s.val - (y.val + s.val) = x.val - y.val by ring]
      exact le_trans hcl hwo)
  have hc2 : |(A.f x).val - (A.f y).val| < 1 / 2 ^ (k + 5 + stepIx A k) :=
    cont_val A.toA0 _ _ _ hxa hxb hya hyb (le_trans hcl hwo)
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

/-! ## Lemma 2 — the pieces

### The sum

`sumQ` is a `do`-loop, chosen so the Riemann sums survive `N = 32768` in the
interpreter; a structural recursion exhausts the interpreter stack at `4096`,
measured, so the loop is not a stylistic choice.  It does **not** reduce in the
kernel, which is why nothing about `integral` can be settled by `decide` — but
it is perfectly provable: the loop unfolds to a `foldl` over `List.range'`, and
from there a step lemma is one rewrite. -/

theorem sumQ_eq_foldl (g : Nat → Q) (n : Nat) :
    sumQ g n = (List.range n).foldl (fun acc i ↦ Q.add acc (g i)) Q.zero := by
  unfold sumQ
  simp [Std.Range.forIn_eq_forIn_range', List.range_eq_range']

theorem sumQ_zero (g : Nat → Q) : sumQ g 0 = Q.zero := by
  rw [sumQ_eq_foldl]; simp

theorem sumQ_succ (g : Nat → Q) (n : Nat) :
    sumQ g (n + 1) = Q.add (sumQ g n) (g n) := by
  rw [sumQ_eq_foldl, sumQ_eq_foldl, List.range_succ, List.foldl_append]
  simp

/-- The sum is **exact** at the value level: `Q.add` normalizes, but `Q.val` of
a sum is the sum of the values on the nose. -/
theorem sumQ_val (g : Nat → Q) (n : Nat) :
    (sumQ g n).val = ∑ i ∈ Finset.range n, (g i).val := by
  induction n with
  | zero => rw [sumQ_zero, Q.val_zero]; simp
  | succ m ih => rw [sumQ_succ, Q.val_add, ih, Finset.sum_range_succ]

/-! ### The two bounded searches -/

theorem twoPowQ_val (e : Nat) : (twoPowQ e).val = 2 ^ e := by
  unfold twoPowQ
  rw [Q.val_ofNat, twoPowN_cast]

theorem ceilLog2Aux_spec (L : Q) (fuel : Nat) : ∀ acc : Nat,
    L.val ≤ (twoPowQ (acc + fuel)).val →
    L.val ≤ (twoPowQ (ceilLog2Aux L acc fuel)).val := by
  induction fuel with
  | zero => intro acc h; simpa using h
  | succ n ih =>
    intro acc h
    simp only [ceilLog2Aux]
    split
    · rename_i hc; exact (Qle_eq_true_iff _ _).mp hc
    · exact ih (acc + 1) (by rw [show acc + 1 + n = acc + (n + 1) by ring]; exact h)

/-- **`ℓ` is what it claims to be**: `L ≤ 2ˡ`. -/
theorem ceilLog2Q_spec (L : Q) : L.val ≤ 2 ^ ceilLog2Q L := by
  have hstart : L.val ≤ (twoPowQ (0 + (L.num.toNat + 1))).val := by
    rw [twoPowQ_val]
    rcases le_or_gt L.num 0 with hn | hn
    · have h0 : L.val ≤ 0 := by
        unfold Q.val
        exact div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hn, le_of_lt L.den_cast_pos⟩)
      have : (0 : Rat) < 2 ^ (0 + (L.num.toNat + 1)) := by positivity
      linarith
    · have hcast : ((L.num.toNat : Nat) : Rat) = (L.num : Rat) := by
        have hI : ((L.num.toNat : Nat) : Int) = L.num := Int.toNat_of_nonneg (le_of_lt hn)
        exact_mod_cast hI
      have h1 : L.val ≤ (L.num : Rat) := by
        unfold Q.val
        exact div_le_self (by exact_mod_cast le_of_lt hn)
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr L.den_ne_zero)
      have h2 : (L.num : Rat) < 2 ^ L.num.toNat := by
        rw [← hcast]; exact_mod_cast Nat.lt_two_pow_self
      have h3 : (2 : Rat) ^ L.num.toNat ≤ 2 ^ (0 + (L.num.toNat + 1)) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
  have := ceilLog2Aux_spec L (L.num.toNat + 1) 0 hstart
  rwa [twoPowQ_val] at this

/-- **`ceilNatQ` really is a ceiling.** -/
theorem ceilNatQ_spec (q : Q) : q.val ≤ (ceilNatQ q : Rat) := by
  unfold ceilNatQ
  split
  · rename_i hn
    have h0 : q.val ≤ 0 := by
      unfold Q.val
      exact div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hn, le_of_lt q.den_cast_pos⟩)
    simpa using h0
  · rename_i hn
    push_neg at hn
    simp only [intAdd_eq, Int.ofNat_eq_natCast]
    have hdpos : (0 : Int) < (q.den : Int) := by
      exact_mod_cast Nat.pos_of_ne_zero q.den_ne_zero
    have hden1 : ((q.den - 1 : Nat) : Int) = (q.den : Int) - 1 := by
      have h1 := Nat.one_le_iff_ne_zero.mpr q.den_ne_zero
      omega
    have hnn : (0 : Int) ≤ q.num + ((q.den - 1 : Nat) : Int) := by
      have h0 : (0 : Int) ≤ ((q.den - 1 : Nat) : Int) := Int.natCast_nonneg _
      omega
    rw [Int.tdiv_eq_ediv_of_nonneg hnn]
    set c : Int := (q.num + ((q.den - 1 : Nat) : Int)) / (q.den : Int) with hc
    have hcnn : (0 : Int) ≤ c := Int.ediv_nonneg hnn (le_of_lt hdpos)
    have hmod : (0 : Int) ≤ (q.num + ((q.den - 1 : Nat) : Int)) % (q.den : Int) :=
      Int.emod_nonneg _ (ne_of_gt hdpos)
    have hmodlt : (q.num + ((q.den - 1 : Nat) : Int)) % (q.den : Int) < (q.den : Int) :=
      Int.emod_lt_of_pos _ hdpos
    have hdiv := Int.mul_ediv_add_emod (q.num + ((q.den - 1 : Nat) : Int)) (q.den : Int)
    rw [← hc] at hdiv
    have hcm : c * (q.den : Int) = (q.den : Int) * c := mul_comm _ _
    have hkey : q.num ≤ c * (q.den : Int) := by linarith
    have hcast : ((c.toNat : Nat) : Rat) = (c : Rat) := by
      have hI : ((c.toNat : Nat) : Int) = c := Int.toNat_of_nonneg hcnn
      exact_mod_cast hI
    rw [hcast]
    unfold Q.val
    rw [div_le_iff₀ q.den_cast_pos]
    exact_mod_cast hkey

/-! ### The mesh, and `f`'s indifference to representation -/

theorem Q.add_congr_val {a b c d : Q} (hv : a.val + b.val = c.val + d.val) :
    Q.add a b = Q.add c d := by
  refine Q.of_inj_val (Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero)
    (Nat.mul_ne_zero c.den_ne_zero d.den_ne_zero) ?_
  rw [show Q.of _ _ = Q.add a b from rfl, show Q.of _ _ = Q.add c d from rfl,
    Q.val_add, Q.val_add]
  exact hv

theorem intL_val (A : A1) : A.intL.val = A.b.val - A.a.val := Q.val_sub _ _

theorem intL_pos (A : A1) : 0 < A.intL.val := by rw [intL_val]; linarith [A.ivl_val]

theorem intN_pos (A : A1) (k : Nat) : 0 < A.intN k :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

/-- **`f` cannot tell two representations of the same rational apart.**  Not an
assumption: `cont` at every precision forces it, since two points at distance
`0` are within every `2⁻ω⁽ᵏ⁾`.  It is needed because the sample points are built
as `a + i·h`, and `a + 0·h` is a *different* `Q` from `a` — the same value in a
different representation, which `f : Q → Q` could otherwise distinguish. -/
theorem f_val_congr (A : A0) {u v : Q}
    (hua : A.a.val ≤ u.val) (hub : u.val ≤ A.b.val)
    (hva : A.a.val ≤ v.val) (hvb : v.val ≤ A.b.val)
    (h : u.val = v.val) : (A.f u).val = (A.f v).val := by
  by_contra hne
  have hpos : 0 < |(A.f u).val - (A.f v).val| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 : Rat) / 2 < 1)
  rw [div_pow, one_pow] at hn
  have hc := cont_val A n u v hua hub hva hvb (by rw [h]; simp)
  linarith

/-- The precision the mesh meets. -/
abbrev meshIx (A : A1) (k : Nat) : Nat := Nat.max (A.omega' (A.intM k)) (A.δ (A.intJ k))

theorem mesh_le (A : A1) (k : Nat) :
    (Q.div A.intL (Q.ofNat (A.intN k))).val ≤ 1 / 2 ^ meshIx A k := by
  have hNpos : (0 : Rat) < (A.intN k : Rat) := by exact_mod_cast intN_pos A k
  have hnum : (Q.ofNat (A.intN k)).num ≠ 0 := by
    have := intN_pos A k
    unfold Q.ofNat
    simpa using by omega
  have hN : A.intL.val * 2 ^ meshIx A k ≤ (A.intN k : Rat) := by
    have h1 := ceilNatQ_spec (Q.mul A.intL (twoPowQ (meshIx A k)))
    rw [Q.val_mul, twoPowQ_val] at h1
    have h2 : ((ceilNatQ (Q.mul A.intL (twoPowQ (meshIx A k))) : Nat) : Rat)
        ≤ (A.intN k : Rat) := by
      have : ceilNatQ (Q.mul A.intL (twoPowQ (meshIx A k))) ≤ A.intN k :=
        Nat.le_max_right _ _
      exact_mod_cast this
    linarith
  rw [Q.val_div _ _ hnum, Q.val_ofNat, div_le_div_iff₀ hNpos (by positivity)]
  linarith

/-! ### Lemma 2

`f b − f a = Σᵢ (f xᵢ₊₁ − f xᵢ)` is **exact** — no integral, no limit, just a
telescoping sum — and each term is `h` times a difference quotient *at the
mesh*.  So the quadrature error is not "Riemann sum versus integral" but
"`derivEval` at `xᵢ` versus the difference quotient at `xᵢ`", and both of those
are near `F`.  That is what replaces the classical FTC step, and it is why the
mesh had to become an admissible `δ`-step. -/

/-- The mesh. -/
def meshQ (A : A1) (k : Nat) : Q := Q.div A.intL (Q.ofNat (A.intN k))

/-- The sample points `a + i·h`. -/
def sampleQ (A : A1) (k i : Nat) : Q := Q.add A.a (Q.mul (Q.ofNat i) (meshQ A k))

theorem integral_eq (A : A1) (k : Nat) :
    A.integral k = Q.mul (meshQ A k)
      (sumQ (fun i ↦ A.derivEval (A.intM k) (sampleQ A k i)) (A.intN k)) := rfl

theorem meshQ_val (A : A1) (k : Nat) : (meshQ A k).val = A.intL.val / (A.intN k : Rat) := by
  have hnum : (Q.ofNat (A.intN k)).num ≠ 0 := by
    have := intN_pos A k
    unfold Q.ofNat; simpa using by omega
  rw [meshQ, Q.val_div _ _ hnum, Q.val_ofNat]

theorem meshQ_pos (A : A1) (k : Nat) : 0 < (meshQ A k).val := by
  rw [meshQ_val]
  exact div_pos (intL_pos A) (by exact_mod_cast intN_pos A k)

theorem meshQ_mul (A : A1) (k : Nat) :
    (A.intN k : Rat) * (meshQ A k).val = A.intL.val := by
  have hNposR : (0 : Rat) < (A.intN k : Rat) := by exact_mod_cast intN_pos A k
  have hNne : ((A.intN k : Nat) : Rat) ≠ 0 := ne_of_gt hNposR
  rw [meshQ_val]
  field_simp

theorem sampleQ_val (A : A1) (k i : Nat) :
    (sampleQ A k i).val = A.a.val + i * (meshQ A k).val := by
  rw [sampleQ]
  simp only [Q.val_add, Q.val_mul, Q.val_ofNat]

theorem sampleQ_step (A : A1) (k i : Nat) :
    Q.add (sampleQ A k i) (meshQ A k) = sampleQ A k (i + 1) := by
  show Q.add (sampleQ A k i) (meshQ A k) = Q.add A.a (Q.mul (Q.ofNat (i + 1)) (meshQ A k))
  refine Q.add_congr_val ?_
  rw [sampleQ_val]
  simp only [Q.val_mul, Q.val_ofNat]
  push_cast
  ring

theorem sampleQ_mem (A : A1) (k i : Nat) (hi : i ≤ A.intN k) :
    A.a.val ≤ (sampleQ A k i).val ∧ (sampleQ A k i).val ≤ A.b.val := by
  have hNhL := meshQ_mul A k
  have hpos := meshQ_pos A k
  have hiR : (i : Rat) ≤ (A.intN k : Rat) := by exact_mod_cast hi
  have hiN : (0 : Rat) ≤ (i : Rat) := Nat.cast_nonneg i
  have hL := intL_val A
  rw [sampleQ_val]
  have hnn : (0 : Rat) ≤ (i : Rat) * (meshQ A k).val := mul_nonneg hiN (le_of_lt hpos)
  refine ⟨by linarith, ?_⟩
  have hmul : (i : Rat) * (meshQ A k).val ≤ (A.intN k : Rat) * (meshQ A k).val :=
    mul_le_mul_of_nonneg_right hiR (le_of_lt hpos)
  linarith

theorem lemma2 (A : A1) : Lemma2Claim A := by
  intro k
  rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, Q.val_sub, toQ_pow2neg_val]
  obtain ⟨F, hF⟩ := A.diff
  have hNpos := intN_pos A k
  have hpos := meshQ_pos A k
  have hnum : (meshQ A k).num ≠ 0 := Q.num_ne_zero_of_val_ne_zero (ne_of_gt hpos)
  have hNhL := meshQ_mul A k
  have hmesh : |(meshQ A k).val| ≤ 1 / 2 ^ A.δ (A.intJ k) := by
    rw [abs_of_pos hpos]
    exact le_trans (mesh_le A k) (inv_pow_le (Nat.le_max_right _ _))
  have hMJ : A.intM k + 3 = A.intJ k := by unfold A1.intM A1.intJ; ring
  -- per-sample: the extracted derivative and the mesh difference quotient agree
  have hper : ∀ i ∈ Finset.range (A.intN k),
      |(A.derivEval (A.intM k) (sampleQ A k i)).val
        - ((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val)
            / (meshQ A k).val| < 2 * (1 / 2 ^ A.intJ k) := by
    intro i hi
    have hlt := Finset.mem_range.mp hi
    have hxi := sampleQ_mem A k i (le_of_lt hlt)
    have hxi1 := sampleQ_mem A k (i + 1) hlt
    have h1 := derivEval_approx A hF (A.intM k) (sampleQ A k i) hxi.1 hxi.2
    rw [hMJ] at h1
    have h2 := diff_val A hF (A.intJ k) (sampleQ A k i) (meshQ A k) hxi.1 hxi.2
      (by rw [sampleQ_step]; exact hxi1.1) (by rw [sampleQ_step]; exact hxi1.2) hnum hmesh
    rw [sampleQ_step] at h2
    have t : |(A.derivEval (A.intM k) (sampleQ A k i)).val
          - ((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val) / (meshQ A k).val|
        ≤ |(A.derivEval (A.intM k) (sampleQ A k i)).val - (F (sampleQ A k i)).val|
          + |(F (sampleQ A k i)).val
              - ((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val)
                  / (meshQ A k).val| := abs_sub_le _ _ _
    rw [abs_sub_comm (F (sampleQ A k i)).val] at t
    linarith
  -- sum the per-sample bounds
  have hne : (Finset.range (A.intN k)).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  have hsum : ∑ i ∈ Finset.range (A.intN k),
      |(A.derivEval (A.intM k) (sampleQ A k i)).val
        - ((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val)
            / (meshQ A k).val| < (A.intN k : Rat) * (2 * (1 / 2 ^ A.intJ k)) := by
    have h := Finset.sum_lt_sum_of_nonempty hne hper
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  -- telescoping: this is the step that replaces classical FTC
  have htel : ∑ i ∈ Finset.range (A.intN k),
      ((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val)
      = (A.f (sampleQ A k (A.intN k))).val - (A.f (sampleQ A k 0)).val :=
    Finset.sum_range_sub (fun i ↦ (A.f (sampleQ A k i)).val) (A.intN k)
  have hab := le_of_lt A.ivl_val
  have hX0 : (A.f (sampleQ A k 0)).val = (A.f A.a).val := by
    refine f_val_congr A.toA0 (sampleQ_mem A k 0 (by omega)).1 (sampleQ_mem A k 0 (by omega)).2
      le_rfl hab ?_
    rw [sampleQ_val]; simp
  have hXN : (A.f (sampleQ A k (A.intN k))).val = (A.f A.b).val := by
    refine f_val_congr A.toA0 (sampleQ_mem A k _ le_rfl).1 (sampleQ_mem A k _ le_rfl).2 hab le_rfl ?_
    rw [sampleQ_val, hNhL, intL_val]
    ring
  -- assemble the difference as `h · Σ (DE − DQ)`
  have hint : (A.integral k).val
      = (meshQ A k).val * ∑ i ∈ Finset.range (A.intN k),
          (A.derivEval (A.intM k) (sampleQ A k i)).val := by
    rw [integral_eq, Q.val_mul, sumQ_val]
  have e2 : (meshQ A k).val * ∑ i ∈ Finset.range (A.intN k),
      (((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val) / (meshQ A k).val)
      = (A.f A.b).val - (A.f A.a).val := by
    rw [Finset.mul_sum]
    have hterm : ∀ i ∈ Finset.range (A.intN k),
        (meshQ A k).val * (((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val)
          / (meshQ A k).val)
        = (A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val := by
      intro i _
      field_simp
    rw [Finset.sum_congr rfl hterm, htel, hX0, hXN]
  have hgap : (A.integral k).val - ((A.f A.b).val - (A.f A.a).val)
      = (meshQ A k).val * ∑ i ∈ Finset.range (A.intN k),
          ((A.derivEval (A.intM k) (sampleQ A k i)).val
            - ((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val)
                / (meshQ A k).val) := by
    rw [Finset.sum_sub_distrib, mul_sub, e2, hint]
  rw [hgap, abs_mul, abs_of_pos hpos]
  -- and bound it
  have habs := Finset.abs_sum_le_sum_abs
    (fun i ↦ (A.derivEval (A.intM k) (sampleQ A k i)).val
      - ((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val) / (meshQ A k).val)
    (Finset.range (A.intN k))
  have hstep : (meshQ A k).val * |∑ i ∈ Finset.range (A.intN k),
      ((A.derivEval (A.intM k) (sampleQ A k i)).val
        - ((A.f (sampleQ A k (i + 1))).val - (A.f (sampleQ A k i)).val) / (meshQ A k).val)|
      < (meshQ A k).val * ((A.intN k : Rat) * (2 * (1 / 2 ^ A.intJ k))) := by
    apply mul_lt_mul_of_pos_left _ hpos
    linarith
  have hrw : (meshQ A k).val * ((A.intN k : Rat) * (2 * (1 / 2 ^ A.intJ k)))
      = A.intL.val * (2 * (1 / 2 ^ A.intJ k)) := by rw [← hNhL]; ring
  -- `L ≤ 2ˡ` turns the sum's length into the target
  have hEll : A.intL.val ≤ 2 ^ A.intEll := ceilLog2Q_spec A.intL
  have hJ : A.intJ k = k + 5 + A.intEll := rfl
  have hfin : A.intL.val * (2 * (1 / 2 ^ A.intJ k)) ≤ 1 / 2 ^ (k + 4) := by
    rw [hJ, pow_add]
    have h1 : (0 : Rat) < 2 ^ A.intEll := by positivity
    have h2 : (0 : Rat) < 2 ^ (k + 5) := by positivity
    have key : A.intL.val * (2 * (1 / (2 ^ (k + 5) * 2 ^ A.intEll)))
        ≤ (2 : Rat) ^ A.intEll * (2 * (1 / (2 ^ (k + 5) * 2 ^ A.intEll))) :=
      mul_le_mul_of_nonneg_right hEll (by positivity)
    have heq : (2 : Rat) ^ A.intEll * (2 * (1 / (2 ^ (k + 5) * 2 ^ A.intEll)))
        = 1 / 2 ^ (k + 4) := by
      rw [show (2 : Rat) ^ (k + 5) = 2 ^ (k + 4) * 2 by
        rw [show k + 5 = k + 4 + 1 by ring, pow_succ]]
      field_simp
    linarith
  have hlast : (1 : Rat) / 2 ^ (k + 4) < 1 / 2 ^ k := by
    apply one_div_lt_one_div_of_lt (by positivity)
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  linarith

/-- **Theorem 2 — `A₁ ⊨ EFTC2`.**  Both conjuncts, for every `A₁`
representation: `derivEval` represents the derivative and is uniformly
continuous with modulus `ω'`, and the Riemann sums built *from it* converge to
`f b − f a` at the stated rate. -/
theorem eftc2_thm (A : A1) : EFTC2Claim A := ⟨lemma1 A, lemma2 A⟩

#print axioms lemma2
#print axioms eftc2_thm

/-! ## EFTC1

The asymmetry the manifesto's §7.2 describes, formalized at the level this
embedding can express.  For `EFTC2` the modulus of uniform differentiability
had to be handed in as `A₁`-data.  Here it is *derived*: the difference
quotient of a Riemann sum over `[x, x+h]` is the **average** of `f` at points
all within `|h|` of `x`, so if every one of them is within `2⁻ᵏ` of `f x` — 
which is exactly what `ω` says once `|h| ≤ 2⁻ω⁽ᵏ⁾` — then so is their average.

`δ := ω`, and only `A₀`-data is consumed. -/

theorem rStep_val (h : Q) {N : Nat} (hN : 0 < N) :
    (rStep h N).val = h.val / (N : Rat) := by
  have hnum : (Q.ofNat N).num ≠ 0 := by unfold Q.ofNat; simpa using by omega
  rw [rStep, Q.val_div _ _ hnum, Q.val_ofNat]

theorem rPt_val (x h : Q) {N : Nat} (hN : 0 < N) (i : Nat) :
    (rPt x h N i).val = x.val + (i : Rat) / (N : Rat) * h.val := by
  rw [rPt]
  simp only [Q.val_add, Q.val_mul, Q.val_ofNat, rStep_val h hN]
  ring

/-- **EFTC1.**  Every Riemann sum's difference quotient is within `2⁻ᵏ` of the
integrand, as soon as the step is `2⁻ω⁽ᵏ⁾` — uniformly in the number of
subdivisions, and with no differentiability data supplied.  The modulus of
uniform differentiability of the integral **is** `ω`. -/
theorem eftc1_quotient (A : A0) (k N : Nat) (hN : 0 < N) (x h : Q)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (hha : A.a.val ≤ x.val + h.val) (hhb : x.val + h.val ≤ A.b.val)
    (hh : h.val ≠ 0) (hsmall : |h.val| ≤ 1 / 2 ^ A.ω k) :
    |(A.riemann x h N).val / h.val - (A.f x).val| < 1 / 2 ^ k := by
  have hNR : (0 : Rat) < (N : Rat) := by exact_mod_cast hN
  -- the quotient is the average of the samples
  have hval : (A.riemann x h N).val / h.val
      = (1 / (N : Rat)) * ∑ i ∈ Finset.range N, (A.f (rPt x h N i)).val := by
    rw [A0.riemann, Q.val_mul, sumQ_val, rStep_val h hN]
    field_simp
  -- every sample sits in `[a,b]` and within `|h|` of `x`
  have hpt : ∀ i ∈ Finset.range N,
      |(A.f (rPt x h N i)).val - (A.f x).val| < 1 / 2 ^ k := by
    intro i hi
    have hlt := Finset.mem_range.mp hi
    have ht0 : (0 : Rat) ≤ (i : Rat) / (N : Rat) :=
      div_nonneg (Nat.cast_nonneg i) (le_of_lt hNR)
    have ht1 : (i : Rat) / (N : Rat) ≤ 1 := by
      rw [div_le_one hNR]; exact_mod_cast le_of_lt hlt
    have hmem : A.a.val ≤ (rPt x h N i).val ∧ (rPt x h N i).val ≤ A.b.val := by
      rw [rPt_val x h hN i]
      constructor <;> nlinarith
    refine cont_val A k _ x hmem.1 hmem.2 hxa hxb ?_
    rw [rPt_val x h hN i, show x.val + (i : Rat) / (N : Rat) * h.val - x.val
      = (i : Rat) / (N : Rat) * h.val by ring, abs_mul, abs_of_nonneg ht0]
    calc (i : Rat) / (N : Rat) * |h.val| ≤ 1 * |h.val| := by
          exact mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ = |h.val| := one_mul _
      _ ≤ 1 / 2 ^ A.ω k := hsmall
  -- an average of things within `2⁻ᵏ` is within `2⁻ᵏ`
  have hsum : |∑ i ∈ Finset.range N, ((A.f (rPt x h N i)).val - (A.f x).val)|
      < (N : Rat) * (1 / 2 ^ k) := by
    have hne : (Finset.range N).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
    have h1 := Finset.abs_sum_le_sum_abs
      (fun i ↦ (A.f (rPt x h N i)).val - (A.f x).val) (Finset.range N)
    have h2 := Finset.sum_lt_sum_of_nonempty hne hpt
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    linarith
  have hrw : (A.riemann x h N).val / h.val - (A.f x).val
      = (1 / (N : Rat)) * ∑ i ∈ Finset.range N,
          ((A.f (rPt x h N i)).val - (A.f x).val) := by
    rw [hval, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : Rat) ≤ 1 / (N : Rat))]
  rw [show (1 : Rat) / 2 ^ k = (1 / (N : Rat)) * ((N : Rat) * (1 / 2 ^ k)) by field_simp]
  exact mul_lt_mul_of_pos_left hsum (by positivity)

/-- **`EFTC1`**, in the form `EFTC.lean` states it: the integral of `f` is
uniformly differentiable with derivative `f`, at modulus `ω`. -/
theorem eftc1 (A : A0) : EFTC1Claim A := by
  intro k N x h hN hxa hxb hha hhb hh hsmall
  rw [Qle_eq_true_iff] at hxa hxb hha hhb
  rw [Qle_eq_true_iff, Q.val_abs, toQ_pow2neg_val] at hsmall
  rw [Q.val_add] at hha hhb
  rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, Q.val_div _ _ hh, toQ_pow2neg_val]
  exact eftc1_quotient A k N hN x h hxa hxb hha hhb
    (by unfold Q.val
        exact div_ne_zero (Int.cast_ne_zero.mpr hh) (ne_of_gt h.den_cast_pos)) hsmall

#print axioms eftc1_quotient

/-! ## Approximating evaluators

`A0.f : Q → Q` is an *exact* evaluator, and that is what stopped `EFTC1` from
saying "`∫f` is `A₁`-adequate": `∫f` is not rational-valued.  The standard
computable-analysis shape is an **approximating evaluator** `Nat → Q → Q`, and
what a representation then has to assert is that successive approximations
converge — there being no real number here for them to converge *to*.

The technical enabler is comparing two Riemann sums for the same interval.
Doing that for arbitrary subdivision counts needs a common refinement and an
index bijection; doing it for a **doubling** needs only that the even-indexed
fine points are the coarse points, which is an induction.  So the evaluator
below refines by doubling, and `riemann_refine` is the estimate everything
else rests on. -/

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (g : Nat → M) (N : Nat) :
    ∑ i ∈ Finset.range (2 * N), g i
      = ∑ i ∈ Finset.range N, (g (2 * i) + g (2 * i + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    rw [add_assoc]

theorem rPt_mem (A : A0) {x h : Q} {N : Nat} (hN : 0 < N) (i : Nat) (hi : i ≤ N)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (hha : A.a.val ≤ x.val + h.val) (hhb : x.val + h.val ≤ A.b.val) :
    A.a.val ≤ (rPt x h N i).val ∧ (rPt x h N i).val ≤ A.b.val := by
  have hNR : (0 : Rat) < (N : Rat) := by exact_mod_cast hN
  have ht0 : (0 : Rat) ≤ (i : Rat) / (N : Rat) :=
    div_nonneg (Nat.cast_nonneg i) (le_of_lt hNR)
  have ht1 : (i : Rat) / (N : Rat) ≤ 1 := by
    rw [div_le_one hNR]; exact_mod_cast hi
  rw [rPt_val x h hN i]
  constructor <;> nlinarith

/-- **Doubling the subdivision moves a Riemann sum by at most `|h|·2⁻ᵏ`.**
The even-indexed points of the fine grid *are* the coarse points — as values,
not as terms, which is why `f_val_congr` is needed — so the two sums differ
term by term only through the odd fine points, each one mesh-step from its
coarse neighbour. -/
theorem riemann_refine (A : A0) (k N : Nat) (hN : 0 < N) (x h : Q)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (hha : A.a.val ≤ x.val + h.val) (hhb : x.val + h.val ≤ A.b.val)
    (hmesh : |h.val| / (N : Rat) ≤ 1 / 2 ^ A.ω k) :
    |(A.riemann x h (2 * N)).val - (A.riemann x h N).val|
      ≤ |h.val| / 2 * (1 / 2 ^ k) := by
  have hNR : (0 : Rat) < (N : Rat) := by exact_mod_cast hN
  have h2N : 0 < 2 * N := by omega
  have h2NR : (0 : Rat) < ((2 * N : Nat) : Rat) := by exact_mod_cast h2N
  -- the two sums, as values
  have hfine : (A.riemann x h (2 * N)).val
      = h.val / ((2 * N : Nat) : Rat)
        * ∑ i ∈ Finset.range (2 * N), (A.f (rPt x h (2 * N) i)).val := by
    rw [A0.riemann, Q.val_mul, sumQ_val, rStep_val h h2N]
  have hcoarse : (A.riemann x h N).val
      = h.val / (N : Rat) * ∑ i ∈ Finset.range N, (A.f (rPt x h N i)).val := by
    rw [A0.riemann, Q.val_mul, sumQ_val, rStep_val h hN]
  -- even fine points are coarse points
  have heven : ∀ i ∈ Finset.range N,
      (A.f (rPt x h (2 * N) (2 * i))).val = (A.f (rPt x h N i)).val := by
    intro i hi
    have hlt := Finset.mem_range.mp hi
    refine f_val_congr A (rPt_mem A h2N (2 * i) (by omega) hxa hxb hha hhb).1
      (rPt_mem A h2N (2 * i) (by omega) hxa hxb hha hhb).2
      (rPt_mem A hN i (le_of_lt hlt) hxa hxb hha hhb).1
      (rPt_mem A hN i (le_of_lt hlt) hxa hxb hha hhb).2 ?_
    rw [rPt_val x h h2N, rPt_val x h hN]
    push_cast
    field_simp
  -- odd fine points are one fine step from their coarse neighbour
  have hodd : ∀ i ∈ Finset.range N,
      |(A.f (rPt x h (2 * N) (2 * i + 1))).val - (A.f (rPt x h N i)).val| < 1 / 2 ^ k := by
    intro i hi
    have hlt := Finset.mem_range.mp hi
    refine cont_val A k _ _ (rPt_mem A h2N (2 * i + 1) (by omega) hxa hxb hha hhb).1
      (rPt_mem A h2N (2 * i + 1) (by omega) hxa hxb hha hhb).2
      (rPt_mem A hN i (le_of_lt hlt) hxa hxb hha hhb).1
      (rPt_mem A hN i (le_of_lt hlt) hxa hxb hha hhb).2 ?_
    have hval : (rPt x h (2 * N) (2 * i + 1)).val - (rPt x h N i).val
        = h.val / ((2 : Rat) * (N : Rat)) := by
      rw [rPt_val x h h2N, rPt_val x h hN]
      push_cast
      field_simp
      ring
    rw [hval, abs_div, abs_of_pos (by positivity : (0 : Rat) < 2 * (N : Rat))]
    calc |h.val| / (2 * (N : Rat)) ≤ |h.val| / (N : Rat) := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) hNR
          linarith
      _ ≤ 1 / 2 ^ A.ω k := hmesh
  -- assemble
  have e : ∑ i ∈ Finset.range N,
      ((A.f (rPt x h (2 * N) (2 * i))).val + (A.f (rPt x h (2 * N) (2 * i + 1))).val)
      = ∑ i ∈ Finset.range N,
          ((A.f (rPt x h N i)).val + (A.f (rPt x h (2 * N) (2 * i + 1))).val) :=
    Finset.sum_congr rfl (fun i hi ↦ by rw [heven i hi])
  have hkey : (A.riemann x h (2 * N)).val - (A.riemann x h N).val
      = h.val / (2 * (N : Rat)) * ∑ i ∈ Finset.range N,
          ((A.f (rPt x h (2 * N) (2 * i + 1))).val - (A.f (rPt x h N i)).val) := by
    rw [hfine, hcoarse, sum_range_two_mul, e, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    push_cast
    field_simp
    ring
  have hb : |∑ i ∈ Finset.range N,
      ((A.f (rPt x h (2 * N) (2 * i + 1))).val - (A.f (rPt x h N i)).val)|
      ≤ (N : Rat) * (1 / 2 ^ k) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle := Finset.sum_le_card_nsmul (Finset.range N)
      (fun i ↦ |(A.f (rPt x h (2 * N) (2 * i + 1))).val - (A.f (rPt x h N i)).val|)
      (1 / 2 ^ k) (fun i hi ↦ le_of_lt (hodd i hi))
    rwa [Finset.card_range, nsmul_eq_mul] at hle
  rw [hkey, abs_mul, abs_div, abs_of_pos (by positivity : (0 : Rat) < 2 * (N : Rat))]
  calc |h.val| / (2 * (N : Rat)) * |∑ i ∈ Finset.range N,
          ((A.f (rPt x h (2 * N) (2 * i + 1))).val - (A.f (rPt x h N i)).val)|
      ≤ |h.val| / (2 * (N : Rat)) * ((N : Rat) * (1 / 2 ^ k)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = |h.val| / 2 * (1 / 2 ^ k) := by field_simp

/-! ### From doubling to arbitrary refinement

The doubling estimate is not enough, and the reason is worth recording.
Chaining it along a tower `N, 2N, 4N, …` **accumulates**: `j` steps give
`j·|h|·2⁻ᵏ`, which is unbounded, so it does not show the levels form a Cauchy
family.  The classical estimate does not accumulate, because it compares each
sum to a *common refinement* directly — every fine sample lies within the
**coarse** mesh of its block's left endpoint, however many fine samples there
are.  So the general block form is what a representation needs, and the tower
is only how the levels happen to be indexed. -/

theorem sum_range_mul_block {M : Type*} [AddCommMonoid M] (g : Nat → M) (N m : Nat) :
    ∑ i ∈ Finset.range (N * m), g i
      = ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range m, g (p * m + q) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1) * m = n * m + m by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ]

/-- **Refining a Riemann sum by any factor moves it by at most `|h|·2⁻ᵏ`** —
with no dependence on the factor.  This is the estimate the doubling one
should have been. -/
theorem riemann_refine_gen (A : A0) (k N m : Nat) (hN : 0 < N) (hm : 0 < m) (x h : Q)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (hha : A.a.val ≤ x.val + h.val) (hhb : x.val + h.val ≤ A.b.val)
    (hmesh : |h.val| / (N : Rat) ≤ 1 / 2 ^ A.ω k) :
    |(A.riemann x h (N * m)).val - (A.riemann x h N).val| ≤ |h.val| * (1 / 2 ^ k) := by
  have hNm : 0 < N * m := Nat.mul_pos hN hm
  have hNR : (0 : Rat) < (N : Rat) := by exact_mod_cast hN
  have hmR : (0 : Rat) < (m : Rat) := by exact_mod_cast hm
  have hNmR : (0 : Rat) < ((N * m : Nat) : Rat) := by exact_mod_cast hNm
  have hcast : ((N * m : Nat) : Rat) = (N : Rat) * (m : Rat) := by push_cast; ring
  have hfine : (A.riemann x h (N * m)).val
      = h.val / ((N * m : Nat) : Rat)
        * ∑ i ∈ Finset.range (N * m), (A.f (rPt x h (N * m) i)).val := by
    rw [A0.riemann, Q.val_mul, sumQ_val, rStep_val h hNm]
  have hcoarse : (A.riemann x h N).val
      = h.val / (N : Rat) * ∑ p ∈ Finset.range N, (A.f (rPt x h N p)).val := by
    rw [A0.riemann, Q.val_mul, sumQ_val, rStep_val h hN]
  -- every fine sample is within the *coarse* mesh of its block's left endpoint
  have hterm : ∀ p ∈ Finset.range N, ∀ q ∈ Finset.range m,
      |(A.f (rPt x h (N * m) (p * m + q))).val - (A.f (rPt x h N p)).val| < 1 / 2 ^ k := by
    intro p hp q hq
    have hpl := Finset.mem_range.mp hp
    have hql := Finset.mem_range.mp hq
    refine cont_val A k _ _
      (rPt_mem A hNm (p * m + q) (by nlinarith) hxa hxb hha hhb).1
      (rPt_mem A hNm (p * m + q) (by nlinarith) hxa hxb hha hhb).2
      (rPt_mem A hN p (le_of_lt hpl) hxa hxb hha hhb).1
      (rPt_mem A hN p (le_of_lt hpl) hxa hxb hha hhb).2 ?_
    have hd : (rPt x h (N * m) (p * m + q)).val - (rPt x h N p).val
        = (q : Rat) / ((N : Rat) * (m : Rat)) * h.val := by
      rw [rPt_val x h hNm, rPt_val x h hN, hcast]
      push_cast
      field_simp
      ring
    rw [hd, abs_mul, abs_div, abs_of_pos (by positivity : (0 : Rat) < (N : Rat) * (m : Rat)),
      abs_of_nonneg (Nat.cast_nonneg q)]
    have hq1 : (q : Rat) / ((N : Rat) * (m : Rat)) ≤ 1 / (N : Rat) := by
      rw [div_le_div_iff₀ (by positivity) hNR]
      have : (q : Rat) ≤ (m : Rat) := by exact_mod_cast le_of_lt hql
      nlinarith
    calc (q : Rat) / ((N : Rat) * (m : Rat)) * |h.val|
        ≤ 1 / (N : Rat) * |h.val| := mul_le_mul_of_nonneg_right hq1 (abs_nonneg _)
      _ = |h.val| / (N : Rat) := by ring
      _ ≤ 1 / 2 ^ A.ω k := hmesh
  -- rewrite the gap as one double sum
  have hkey : (A.riemann x h (N * m)).val - (A.riemann x h N).val
      = h.val / ((N : Rat) * (m : Rat)) * ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range m,
          ((A.f (rPt x h (N * m) (p * m + q))).val - (A.f (rPt x h N p)).val) := by
    have hinner : ∀ p ∈ Finset.range N, ∑ q ∈ Finset.range m,
        ((A.f (rPt x h (N * m) (p * m + q))).val - (A.f (rPt x h N p)).val)
        = (∑ q ∈ Finset.range m, (A.f (rPt x h (N * m) (p * m + q))).val)
          - (m : Rat) * (A.f (rPt x h N p)).val := by
      intro p _
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hfine, hcoarse, sum_range_mul_block, hcast]
    field_simp
  -- and bound it
  have hb : |∑ p ∈ Finset.range N, ∑ q ∈ Finset.range m,
      ((A.f (rPt x h (N * m) (p * m + q))).val - (A.f (rPt x h N p)).val)|
      ≤ (N : Rat) * ((m : Rat) * (1 / 2 ^ k)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hrow : ∀ p ∈ Finset.range N, |∑ q ∈ Finset.range m,
        ((A.f (rPt x h (N * m) (p * m + q))).val - (A.f (rPt x h N p)).val)|
        ≤ (m : Rat) * (1 / 2 ^ k) := by
      intro p hp
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have := Finset.sum_le_card_nsmul (Finset.range m)
        (fun q ↦ |(A.f (rPt x h (N * m) (p * m + q))).val - (A.f (rPt x h N p)).val|)
        (1 / 2 ^ k) (fun q hq ↦ le_of_lt (hterm p hp q hq))
      rwa [Finset.card_range, nsmul_eq_mul] at this
    have := Finset.sum_le_card_nsmul (Finset.range N)
      (fun p ↦ |∑ q ∈ Finset.range m,
        ((A.f (rPt x h (N * m) (p * m + q))).val - (A.f (rPt x h N p)).val)|)
      ((m : Rat) * (1 / 2 ^ k)) hrow
    rwa [Finset.card_range, nsmul_eq_mul] at this
  rw [hkey, abs_mul, abs_div, abs_of_pos (by positivity : (0 : Rat) < (N : Rat) * (m : Rat))]
  calc |h.val| / ((N : Rat) * (m : Rat)) * |∑ p ∈ Finset.range N, ∑ q ∈ Finset.range m,
          ((A.f (rPt x h (N * m) (p * m + q))).val - (A.f (rPt x h N p)).val)|
      ≤ |h.val| / ((N : Rat) * (m : Rat)) * ((N : Rat) * ((m : Rat) * (1 / 2 ^ k))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = |h.val| * (1 / 2 ^ k) := by field_simp

/-! ### Splitting a uniform grid exactly

Additivity is what `∫ₐˣ⁺ʰ ≈ ∫ₐˣ + ∫ₓˣ⁺ʰ` needs, and the obstacle recorded
earlier was that concatenating the grids of `[a,x]` and `[x,x+h]` gives a
*non-uniform* partition of `[a,x+h]`.  That obstacle is avoidable: the split
point is **rational**, so `h/(x−a)` is a ratio of integers, and cell counts in
that ratio make the concatenation uniform again.  A uniform grid of `[x, x+h₁+h₂]`
with `N₁+N₂` cells splits *exactly* at `x+h₁` whenever the two cell widths
agree — no tagged partitions, no common refinement of unequal grids. -/

theorem riemann_split (A : A0) (x h₁ h₂ : Q) (N₁ N₂ : Nat)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hw : h₁.val / (N₁ : Rat) = h₂.val / (N₂ : Rat))
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (h1a : A.a.val ≤ x.val + h₁.val) (h1b : x.val + h₁.val ≤ A.b.val)
    (h2a : A.a.val ≤ x.val + h₁.val + h₂.val)
    (h2b : x.val + h₁.val + h₂.val ≤ A.b.val) :
    (A.riemann x (Q.add h₁ h₂) (N₁ + N₂)).val
      = (A.riemann x h₁ N₁).val + (A.riemann (Q.add x h₁) h₂ N₂).val := by
  have hNs : 0 < N₁ + N₂ := by omega
  have h1R : (0 : Rat) < (N₁ : Rat) := by exact_mod_cast hN₁
  have h2R : (0 : Rat) < (N₂ : Rat) := by exact_mod_cast hN₂
  have hsR : (0 : Rat) < ((N₁ + N₂ : Nat) : Rat) := by exact_mod_cast hNs
  have hcast : ((N₁ + N₂ : Nat) : Rat) = (N₁ : Rat) + (N₂ : Rat) := by push_cast; ring
  -- the common cell width
  have hwidth : (h₁.val + h₂.val) / ((N₁ + N₂ : Nat) : Rat) = h₁.val / (N₁ : Rat) := by
    rw [hcast]
    field_simp at hw ⊢
    linarith
  -- the interval `[x, x+h₁]` sits inside `[a,b]`, and so does `[x+h₁, x+h₁+h₂]`
  have hmemS : ∀ i : Nat, i ≤ N₁ + N₂ →
      A.a.val ≤ (rPt x (Q.add h₁ h₂) (N₁ + N₂) i).val
        ∧ (rPt x (Q.add h₁ h₂) (N₁ + N₂) i).val ≤ A.b.val := by
    intro i hi
    exact rPt_mem A hNs i hi hxa hxb (by rw [Q.val_add]; linarith)
      (by rw [Q.val_add]; linarith)
  -- first block: the fine points coincide with `[x, x+h₁]`'s
  have hlow : ∀ i ∈ Finset.range N₁,
      (A.f (rPt x (Q.add h₁ h₂) (N₁ + N₂) i)).val = (A.f (rPt x h₁ N₁ i)).val := by
    intro i hi
    have hlt := Finset.mem_range.mp hi
    refine f_val_congr A (hmemS i (by omega)).1 (hmemS i (by omega)).2
      (rPt_mem A hN₁ i (le_of_lt hlt) hxa hxb h1a h1b).1
      (rPt_mem A hN₁ i (le_of_lt hlt) hxa hxb h1a h1b).2 ?_
    rw [rPt_val x _ hNs, rPt_val x h₁ hN₁]
    simp only [Q.val_add]
    have e : (i : Rat) / ((N₁ + N₂ : Nat) : Rat) * (h₁.val + h₂.val)
        = (i : Rat) * ((h₁.val + h₂.val) / ((N₁ + N₂ : Nat) : Rat)) := by ring
    rw [e, hwidth]
    ring
  -- second block: they coincide with `[x+h₁, x+h₁+h₂]`'s
  have hhigh : ∀ j ∈ Finset.range N₂,
      (A.f (rPt x (Q.add h₁ h₂) (N₁ + N₂) (N₁ + j))).val
        = (A.f (rPt (Q.add x h₁) h₂ N₂ j)).val := by
    intro j hj
    have hlt := Finset.mem_range.mp hj
    refine f_val_congr A (hmemS (N₁ + j) (by omega)).1 (hmemS (N₁ + j) (by omega)).2
      (rPt_mem A hN₂ j (le_of_lt hlt) (by rw [Q.val_add]; linarith)
        (by rw [Q.val_add]; linarith) (by rw [Q.val_add]; linarith)
        (by rw [Q.val_add]; linarith)).1
      (rPt_mem A hN₂ j (le_of_lt hlt) (by rw [Q.val_add]; linarith)
        (by rw [Q.val_add]; linarith) (by rw [Q.val_add]; linarith)
        (by rw [Q.val_add]; linarith)).2 ?_
    rw [rPt_val x _ hNs, rPt_val _ h₂ hN₂]
    simp only [Q.val_add]
    have e : ((N₁ + j : Nat) : Rat) / ((N₁ + N₂ : Nat) : Rat) * (h₁.val + h₂.val)
        = ((N₁ : Rat) + (j : Rat)) * ((h₁.val + h₂.val) / ((N₁ + N₂ : Nat) : Rat)) := by
      push_cast; ring
    have e2 : (j : Rat) / (N₂ : Rat) * h₂.val = (j : Rat) * (h₂.val / (N₂ : Rat)) := by ring
    rw [e, hwidth, e2, ← hw]
    field_simp
    ring
  rw [A0.riemann, A0.riemann, A0.riemann, Q.val_mul, Q.val_mul, Q.val_mul,
    sumQ_val, sumQ_val, sumQ_val, rStep_val _ hNs, rStep_val _ hN₁, rStep_val _ hN₂,
    Finset.sum_range_add, Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh,
    Q.val_add, hwidth, hw, mul_add]

/-- **Grid independence.**  Two uniform grids over the same interval, both with
mesh at most `2⁻ω⁽ᵏ⁾`, give sums within `2|h|·2⁻ᵏ` — compare each to the product
grid, which refines both.  This is the classical "any two fine partitions agree"
statement, restricted to uniform grids, which by `riemann_split` is no
restriction for the additivity it is wanted for. -/
theorem riemann_uniform_close (A : A0) (k N m : Nat) (hN : 0 < N) (hm : 0 < m) (x h : Q)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (hha : A.a.val ≤ x.val + h.val) (hhb : x.val + h.val ≤ A.b.val)
    (hmN : |h.val| / (N : Rat) ≤ 1 / 2 ^ A.ω k)
    (hmM : |h.val| / (m : Rat) ≤ 1 / 2 ^ A.ω k) :
    |(A.riemann x h N).val - (A.riemann x h m).val| ≤ 2 * (|h.val| * (1 / 2 ^ k)) := by
  have h1 := riemann_refine_gen A k N m hN hm x h hxa hxb hha hhb hmN
  have h2 := riemann_refine_gen A k m N hm hN x h hxa hxb hha hhb hmM
  rw [Nat.mul_comm m N] at h2
  have e1 : |(A.riemann x h N).val - (A.riemann x h (N * m)).val| ≤ |h.val| * (1 / 2 ^ k) := by
    rw [abs_sub_comm]; exact h1
  have t : |(A.riemann x h N).val - (A.riemann x h m).val|
      ≤ |(A.riemann x h N).val - (A.riemann x h (N * m)).val|
        + |(A.riemann x h (N * m)).val - (A.riemann x h m).val| := abs_sub_le _ _ _
  linarith

#print axioms riemann_split
#print axioms riemann_uniform_close

/-! ### The representation, and the integral as an inhabitant of it -/

theorem A0.len_val (A : A0) : A.len.val = A.b.val - A.a.val := Q.val_sub _ _

theorem A0.len_pos (A : A0) : 0 < A.len.val := by
  rw [A0.len_val]
  linarith [(Q.ltN_eq_one_iff _ _).mp A.ivl]

theorem A0.evN_pos (A : A0) (n : Nat) : 0 < A.evN n :=
  Nat.mul_pos (Nat.two_pow_pos n) (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _))

theorem A0.evN_mul (A : A0) {n m : Nat} (h : n ≤ m) :
    A.evN m = A.evN n * 2 ^ (m - n) := by
  unfold A0.evN
  rw [show m = n + (m - n) by omega, pow_add, show n + (m - n) - n = m - n by omega]
  ring

theorem A0.evBase_ge (A : A0) : A.len.val ≤ (A.evBase : Rat) := by
  have h := ceilNatQ_spec A.len
  have h2 : ((ceilNatQ A.len : Nat) : Rat) ≤ (A.evBase : Rat) := by
    exact_mod_cast Nat.le_max_right 1 (ceilNatQ A.len)
  linarith

/-- **Conservativity.**  Every exact representation is an approximating one —
the constant family, which converges instantly.  So generalizing the evaluator
loses nothing; it only admits more functions. -/
def A0.toE0 (A : A0) : E0 :=
  { a := A.a, b := A.b, ev := fun _ x ↦ A.f x, cm := fun _ ↦ 0, ivl := A.ivl,
    conv := by
      intro k n m _ _ x _ _
      rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, sub_self, abs_zero, toQ_pow2neg_val]
      positivity }

theorem A0.intEv_mesh (A : A0) (n : Nat) {x : Q}
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val) :
    |(Q.sub x A.a).val| / (A.evN n : Rat) ≤ 1 / 2 ^ n := by
  have hbase : (0 : Rat) < (A.evBase : Rat) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (ceilNatQ A.len))
  have hnn : (0 : Rat) ≤ x.val - A.a.val := by linarith
  have hh : |(Q.sub x A.a).val| ≤ (A.evBase : Rat) := by
    rw [Q.val_sub, abs_of_nonneg hnn]
    have := A.evBase_ge
    rw [A0.len_val] at this
    linarith
  have hNv : ((A.evN n : Nat) : Rat) = 2 ^ n * (A.evBase : Rat) := by
    unfold A0.evN; push_cast; ring
  rw [hNv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hh, hbase]

/-- **The integral of an `A₀` is an approximating evaluator.**  This is the
statement `EFTC1` could not make: `∫f` is now an inhabitant of the theory,
represented by its Riemann sums on the doubling grid, with an explicit modulus
of convergence built from `f`'s own modulus of continuity. -/
def A0.intE0 (A : A0) : E0 :=
  { a := A.a, b := A.b, ev := A.intEv, cm := fun k ↦ A.ω (k + A.ell), ivl := A.ivl,
    conv := by
      intro k n m hn hnm x hxa hxb
      rw [Qle_eq_true_iff] at hxa hxb
      rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, toQ_pow2neg_val]
      have hNpos := A.evN_pos n
      have hxab : A.a.val + (Q.sub x A.a).val = x.val := by rw [Q.val_sub]; ring
      have hmesh : |(Q.sub x A.a).val| / (A.evN n : Rat) ≤ 1 / 2 ^ A.ω (k + A.ell) :=
        le_trans (A.intEv_mesh n hxa hxb) (inv_pow_le hn)
      have href := riemann_refine_gen A (k + A.ell) (A.evN n) (2 ^ (m - n)) hNpos
        (Nat.two_pow_pos _) A.a (Q.sub x A.a)
        le_rfl (le_of_lt ((Q.ltN_eq_one_iff _ _).mp A.ivl))
        (by rw [hxab]; exact hxa) (by rw [hxab]; exact hxb) hmesh
      rw [← A.evN_mul hnm] at href
      rw [abs_sub_comm]
      refine le_trans href ?_
      have hnn : (0 : Rat) ≤ x.val - A.a.val := by linarith
      have hlen : |(Q.sub x A.a).val| ≤ 2 ^ A.ell := by
        rw [Q.val_sub, abs_of_nonneg hnn]
        have h1 : A.len.val ≤ 2 ^ A.ell := ceilLog2Q_spec A.len
        rw [A0.len_val] at h1
        linarith
      have hstep : |(Q.sub x A.a).val| * (1 / 2 ^ (k + A.ell))
          ≤ (2 : Rat) ^ A.ell * (1 / 2 ^ (k + A.ell)) :=
        mul_le_mul_of_nonneg_right hlen (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      rw [pow_add]
      field_simp }

/-! ### The counts

Concretely: `h/d` has numerator `p` and denominator `q`, and cells in the ratio
`q : p` have equal widths.  `splitScale` then scales both until the mesh meets
the target. -/

theorem splitScale_pos (d h : Q) (K : Nat) : 0 < splitScale d h K :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem splitLo_pos (d h : Q) (K : Nat) : 0 < splitLo d h K :=
  Nat.mul_pos (Nat.pos_of_ne_zero (Q.div h d).den_ne_zero) (splitScale_pos d h K)

theorem splitHi_pos (d h : Q) (K : Nat) (hd : d.num ≠ 0) (hh : h.num ≠ 0) :
    0 < splitHi d h K := by
  have hdv : d.val ≠ 0 := by
    unfold Q.val
    exact div_ne_zero (Int.cast_ne_zero.mpr hd) (ne_of_gt d.den_cast_pos)
  have hhv : h.val ≠ 0 := by
    unfold Q.val
    exact div_ne_zero (Int.cast_ne_zero.mpr hh) (ne_of_gt h.den_cast_pos)
  have hr : (Q.div h d).val ≠ 0 := by
    rw [Q.val_div _ _ hd]
    exact div_ne_zero hhv hdv
  exact Nat.mul_pos (Int.natAbs_pos.mpr (Q.num_ne_zero_of_val_ne_zero hr))
    (splitScale_pos d h K)

/-- **The two counts have equal cell widths** — which is `riemann_split`'s
hypothesis, and the only reason a uniform grid can be made to land on the
split point. -/
theorem split_widths (d h : Q) (K : Nat) (hd : 0 < d.val) (hh : h.num ≠ 0) :
    d.val / (splitLo d h K : Rat) = |h.val| / (splitHi d h K : Rat) := by
  have hdn : d.num ≠ 0 := Q.num_ne_zero_of_val_ne_zero (ne_of_gt hd)
  have hs := splitScale_pos d h K
  have hsR : (0 : Rat) < (splitScale d h K : Rat) := by exact_mod_cast hs
  have hqR : (0 : Rat) < ((Q.div h d).den : Rat) := (Q.div h d).den_cast_pos
  have hhv : h.val ≠ 0 := by
    unfold Q.val
    exact div_ne_zero (Int.cast_ne_zero.mpr hh) (ne_of_gt h.den_cast_pos)
  have hpNat : 0 < (Q.div h d).num.natAbs := by
    refine Int.natAbs_pos.mpr (Q.num_ne_zero_of_val_ne_zero ?_)
    rw [Q.val_div _ _ hdn]
    exact div_ne_zero hhv (ne_of_gt hd)
  have hpR : (0 : Rat) < (((Q.div h d).num.natAbs : Nat) : Rat) := by exact_mod_cast hpNat
  -- `|h|/d = p/q`
  have hkey : |h.val| * ((Q.div h d).den : Rat)
      = d.val * (((Q.div h d).num.natAbs : Nat) : Rat) := by
    have hrv : (Q.div h d).val = h.val / d.val := Q.val_div _ _ hdn
    have hrv2 : (Q.div h d).val
        = ((Q.div h d).num : Rat) / ((Q.div h d).den : Rat) := rfl
    have habs : (((Q.div h d).num.natAbs : Nat) : Rat) = |((Q.div h d).num : Rat)| :=
      natAbs_cast_rat _
    rw [habs]
    have h1 : |h.val| / d.val = |((Q.div h d).num : Rat)| / ((Q.div h d).den : Rat) := by
      rw [← abs_of_pos hqR, ← abs_div, ← hrv2, hrv, abs_div, abs_of_pos hd]
    rw [div_eq_div_iff (ne_of_gt hd) (ne_of_gt hqR)] at h1
    linarith
  unfold splitLo splitHi
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  calc d.val * ((((Q.div h d).num.natAbs : Nat) : Rat) * (splitScale d h K : Rat))
      = (d.val * (((Q.div h d).num.natAbs : Nat) : Rat)) * (splitScale d h K : Rat) := by ring
    _ = (|h.val| * ((Q.div h d).den : Rat)) * (splitScale d h K : Rat) := by rw [hkey]
    _ = |h.val| * (((Q.div h d).den : Rat) * (splitScale d h K : Rat)) := by ring

/-- **And the mesh meets the target.** -/
theorem split_mesh (d h : Q) (K : Nat) (hd : 0 < d.val) :
    d.val / (splitLo d h K : Rat) ≤ 1 / 2 ^ K := by
  have hqR : (0 : Rat) < ((Q.div h d).den : Rat) := (Q.div h d).den_cast_pos
  have hqn : (Q.ofNat (Q.div h d).den).num ≠ 0 := by
    have := (Q.div h d).den_ne_zero
    unfold Q.ofNat; simpa using by omega
  have h1 := ceilNatQ_spec (Q.mul (Q.div d (Q.ofNat (Q.div h d).den)) (twoPowQ K))
  rw [Q.val_mul, twoPowQ_val, Q.val_div _ _ hqn, Q.val_ofNat] at h1
  have h2 : ((ceilNatQ (Q.mul (Q.div d (Q.ofNat (Q.div h d).den)) (twoPowQ K)) : Nat) : Rat)
      ≤ (splitScale d h K : Rat) := by
    exact_mod_cast Nat.le_max_right 1 _
  have hsR : (0 : Rat) < (splitScale d h K : Rat) :=
    by exact_mod_cast splitScale_pos d h K
  have h3 : d.val / ((Q.div h d).den : Rat) * 2 ^ K ≤ (splitScale d h K : Rat) :=
    le_trans h1 h2
  rw [div_mul_eq_mul_div, div_le_iff₀ hqR] at h3
  have h4 : d.val * 2 ^ K ≤ ((Q.div h d).den : Rat) * (splitScale d h K : Rat) := by
    rw [mul_comm ((Q.div h d).den : Rat)]
    exact h3
  unfold splitLo
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

#print axioms split_widths
#print axioms split_mesh

/-! ### The bound on `|f|`

`cont` for the integral needs `|∫ₐˣ f − ∫ₐʸ f| ≤ M·|x−y|`, and `M` has to be
produced from the `A₀`-data.  It is: `ω` says `f` moves by less than `1` across
any step of `2⁻ω⁽⁰⁾`, and `bnd` such steps span the interval, so `f` cannot get
further than `bnd` from `f a`. -/

theorem A0.bnd_pos (A : A0) : 0 < A.bnd :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem A0.fBound_spec (A : A0) {x : Q}
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val) :
    |(A.f x).val| ≤ (A.fBound).val := by
  have hn := A.bnd_pos
  have hnR : (0 : Rat) < (A.bnd : Rat) := by exact_mod_cast hn
  have hab := le_of_lt ((Q.ltN_eq_one_iff _ _).mp A.ivl)
  have hxab : A.a.val + (Q.sub x A.a).val = x.val := by rw [Q.val_sub]; ring
  have hpow : (0 : Rat) < 2 ^ A.ω 0 := by positivity
  -- the walk is fine enough
  have hmesh : |(Q.sub x A.a).val| / (A.bnd : Rat) ≤ 1 / 2 ^ A.ω 0 := by
    have h1 := ceilNatQ_spec (Q.mul A.len (twoPowQ (A.ω 0)))
    rw [Q.val_mul, twoPowQ_val, A0.len_val] at h1
    have h2 : ((ceilNatQ (Q.mul A.len (twoPowQ (A.ω 0))) : Nat) : Rat) ≤ (A.bnd : Rat) := by
      exact_mod_cast Nat.le_max_right 1 (ceilNatQ (Q.mul A.len (twoPowQ (A.ω 0))))
    have h3 : |(Q.sub x A.a).val| ≤ A.b.val - A.a.val := by
      rw [Q.val_sub, abs_of_nonneg (by linarith)]; linarith
    rw [div_le_div_iff₀ hnR (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h3 (le_of_lt hpow)]
  -- each step moves `f` by less than 1
  have hstep : ∀ i ∈ Finset.range A.bnd,
      |(A.f (rPt A.a (Q.sub x A.a) A.bnd (i + 1))).val
        - (A.f (rPt A.a (Q.sub x A.a) A.bnd i)).val| < 1 := by
    intro i hi
    have hlt := Finset.mem_range.mp hi
    have m1 := rPt_mem A hn (i + 1) (by omega) le_rfl hab
      (by rw [hxab]; exact hxa) (by rw [hxab]; exact hxb)
    have m2 := rPt_mem A hn i (by omega) le_rfl hab
      (by rw [hxab]; exact hxa) (by rw [hxab]; exact hxb)
    have hd : (rPt A.a (Q.sub x A.a) A.bnd (i + 1)).val
        - (rPt A.a (Q.sub x A.a) A.bnd i).val = (Q.sub x A.a).val / (A.bnd : Rat) := by
      rw [rPt_val _ _ hn, rPt_val _ _ hn]
      push_cast
      field_simp
      ring
    have hc := cont_val A 0 _ _ m1.1 m1.2 m2.1 m2.2
      (by rw [hd, abs_div, abs_of_pos hnR]; exact hmesh)
    simpa using hc
  -- telescope
  have htel : ∑ i ∈ Finset.range A.bnd,
      ((A.f (rPt A.a (Q.sub x A.a) A.bnd (i + 1))).val
        - (A.f (rPt A.a (Q.sub x A.a) A.bnd i)).val)
      = (A.f (rPt A.a (Q.sub x A.a) A.bnd A.bnd)).val
        - (A.f (rPt A.a (Q.sub x A.a) A.bnd 0)).val :=
    Finset.sum_range_sub (fun i ↦ (A.f (rPt A.a (Q.sub x A.a) A.bnd i)).val) A.bnd
  have hsum : |(A.f (rPt A.a (Q.sub x A.a) A.bnd A.bnd)).val
      - (A.f (rPt A.a (Q.sub x A.a) A.bnd 0)).val| ≤ (A.bnd : Rat) := by
    rw [← htel]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle := Finset.sum_le_card_nsmul (Finset.range A.bnd)
      (fun i ↦ |(A.f (rPt A.a (Q.sub x A.a) A.bnd (i + 1))).val
        - (A.f (rPt A.a (Q.sub x A.a) A.bnd i)).val|)
      1 (fun i hi ↦ le_of_lt (hstep i hi))
    rwa [Finset.card_range, nsmul_eq_mul, mul_one] at hle
  -- endpoints
  have h0 : (A.f (rPt A.a (Q.sub x A.a) A.bnd 0)).val = (A.f A.a).val := by
    refine f_val_congr A (rPt_mem A hn 0 (by omega) le_rfl hab
      (by rw [hxab]; exact hxa) (by rw [hxab]; exact hxb)).1
      (rPt_mem A hn 0 (by omega) le_rfl hab
      (by rw [hxab]; exact hxa) (by rw [hxab]; exact hxb)).2 le_rfl hab ?_
    rw [rPt_val _ _ hn]; simp
  have hN : (A.f (rPt A.a (Q.sub x A.a) A.bnd A.bnd)).val = (A.f x).val := by
    refine f_val_congr A (rPt_mem A hn A.bnd le_rfl le_rfl hab
      (by rw [hxab]; exact hxa) (by rw [hxab]; exact hxb)).1
      (rPt_mem A hn A.bnd le_rfl le_rfl hab
      (by rw [hxab]; exact hxa) (by rw [hxab]; exact hxb)).2 hxa hxb ?_
    rw [rPt_val _ _ hn, Q.val_sub, div_self (ne_of_gt hnR)]
    ring
  rw [h0, hN] at hsum
  have htri : |(A.f x).val| ≤ |(A.f x).val - (A.f A.a).val| + |(A.f A.a).val| := by
    have h := abs_sub_le (A.f x).val (A.f A.a).val 0
    rwa [sub_zero, sub_zero] at h
  rw [A0.fBound, Q.val_add, Q.val_abs, Q.val_ofNat]
  linarith

#print axioms A0.fBound_spec

/-! ### `cont` for the integral

`|∫ₐˣ f − ∫ₐʸ f| ≲ M·|x−y|`, at the level of the approximants.  Splitting

    (u/N)·ΣF − (v/N)·ΣG  =  ((u−v)/N)·ΣF + (v/N)·Σ(F−G)

puts the two halves of the estimate on the two terms: the first is bounded by
`|x−y|·M` using `fBound_spec`, the second by `|v|·2⁻ᵏ` using `cont` on each
sample.  Note it holds at **every** level, with no condition on `n`. -/

theorem A0.intEv_cont (A : A0) (k n : Nat) (x y : Q)
    (hxa : A.a.val ≤ x.val) (hxb : x.val ≤ A.b.val)
    (hya : A.a.val ≤ y.val) (hyb : y.val ≤ A.b.val)
    (hxy : |x.val - y.val| ≤ 1 / 2 ^ A.intOmega k) :
    |(A.intEv n x).val - (A.intEv n y).val| ≤ 1 / 2 ^ k := by
  have hN := A.evN_pos n
  have hNR : (0 : Rat) < (A.evN n : Rat) := by exact_mod_cast hN
  have hab := le_of_lt ((Q.ltN_eq_one_iff _ _).mp A.ivl)
  have hxab : A.a.val + (Q.sub x A.a).val = x.val := by rw [Q.val_sub]; ring
  have hyab : A.a.val + (Q.sub y A.a).val = y.val := by rw [Q.val_sub]; ring
  have hEx : (A.intEv n x).val
      = (Q.sub x A.a).val / (A.evN n : Rat) * ∑ i ∈ Finset.range (A.evN n),
          (A.f (rPt A.a (Q.sub x A.a) (A.evN n) i)).val := by
    rw [A0.intEv, A0.riemann, Q.val_mul, sumQ_val, rStep_val _ hN]
  have hEy : (A.intEv n y).val
      = (Q.sub y A.a).val / (A.evN n : Rat) * ∑ i ∈ Finset.range (A.evN n),
          (A.f (rPt A.a (Q.sub y A.a) (A.evN n) i)).val := by
    rw [A0.intEv, A0.riemann, Q.val_mul, sumQ_val, rStep_val _ hN]
  -- membership of every sample
  have hmx : ∀ i, i ≤ A.evN n → A.a.val ≤ (rPt A.a (Q.sub x A.a) (A.evN n) i).val
      ∧ (rPt A.a (Q.sub x A.a) (A.evN n) i).val ≤ A.b.val := fun i hi ↦
    rPt_mem A hN i hi le_rfl hab (by rw [hxab]; exact hxa) (by rw [hxab]; exact hxb)
  have hmy : ∀ i, i ≤ A.evN n → A.a.val ≤ (rPt A.a (Q.sub y A.a) (A.evN n) i).val
      ∧ (rPt A.a (Q.sub y A.a) (A.evN n) i).val ≤ A.b.val := fun i hi ↦
    rPt_mem A hN i hi le_rfl hab (by rw [hyab]; exact hya) (by rw [hyab]; exact hyb)
  -- first half: `|ΣF| ≤ N·M`
  have hSF : |∑ i ∈ Finset.range (A.evN n),
      (A.f (rPt A.a (Q.sub x A.a) (A.evN n) i)).val| ≤ (A.evN n : Rat) * A.fBound.val := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle := Finset.sum_le_card_nsmul (Finset.range (A.evN n))
      (fun i ↦ |(A.f (rPt A.a (Q.sub x A.a) (A.evN n) i)).val|) A.fBound.val
      (fun i hi ↦ A.fBound_spec (hmx i (le_of_lt (Finset.mem_range.mp hi))).1
        (hmx i (le_of_lt (Finset.mem_range.mp hi))).2)
    rwa [Finset.card_range, nsmul_eq_mul] at hle
  -- second half: samples at matching indices are close
  have hFG : ∀ i ∈ Finset.range (A.evN n),
      |(A.f (rPt A.a (Q.sub x A.a) (A.evN n) i)).val
        - (A.f (rPt A.a (Q.sub y A.a) (A.evN n) i)).val| < 1 / 2 ^ (k + 1 + A.ell) := by
    intro i hi
    have hlt := Finset.mem_range.mp hi
    refine cont_val A _ _ _ (hmx i (le_of_lt hlt)).1 (hmx i (le_of_lt hlt)).2
      (hmy i (le_of_lt hlt)).1 (hmy i (le_of_lt hlt)).2 ?_
    have hd : (rPt A.a (Q.sub x A.a) (A.evN n) i).val
        - (rPt A.a (Q.sub y A.a) (A.evN n) i).val
        = (i : Rat) / (A.evN n : Rat) * (x.val - y.val) := by
      rw [rPt_val _ _ hN, rPt_val _ _ hN, Q.val_sub, Q.val_sub]
      ring
    have ht0 : (0 : Rat) ≤ (i : Rat) / (A.evN n : Rat) :=
      div_nonneg (Nat.cast_nonneg i) (le_of_lt hNR)
    have ht1 : (i : Rat) / (A.evN n : Rat) ≤ 1 := by
      rw [div_le_one hNR]; exact_mod_cast le_of_lt hlt
    rw [hd, abs_mul, abs_of_nonneg ht0]
    calc (i : Rat) / (A.evN n : Rat) * |x.val - y.val| ≤ 1 * |x.val - y.val| :=
          mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ = |x.val - y.val| := one_mul _
      _ ≤ 1 / 2 ^ A.intOmega k := hxy
      _ ≤ 1 / 2 ^ A.ω (k + 1 + A.ell) := inv_pow_le (Nat.le_max_left _ _)
  have hSFG : |∑ i ∈ Finset.range (A.evN n),
      ((A.f (rPt A.a (Q.sub x A.a) (A.evN n) i)).val
        - (A.f (rPt A.a (Q.sub y A.a) (A.evN n) i)).val)|
      ≤ (A.evN n : Rat) * (1 / 2 ^ (k + 1 + A.ell)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle := Finset.sum_le_card_nsmul (Finset.range (A.evN n))
      (fun i ↦ |(A.f (rPt A.a (Q.sub x A.a) (A.evN n) i)).val
        - (A.f (rPt A.a (Q.sub y A.a) (A.evN n) i)).val|)
      (1 / 2 ^ (k + 1 + A.ell)) (fun i hi ↦ le_of_lt (hFG i hi))
    rwa [Finset.card_range, nsmul_eq_mul] at hle
  -- assemble
  set SF := ∑ i ∈ Finset.range (A.evN n),
    (A.f (rPt A.a (Q.sub x A.a) (A.evN n) i)).val with hSFdef
  set SG := ∑ i ∈ Finset.range (A.evN n),
    (A.f (rPt A.a (Q.sub y A.a) (A.evN n) i)).val with hSGdef
  have hSFG' : |SF - SG| ≤ (A.evN n : Rat) * (1 / 2 ^ (k + 1 + A.ell)) := by
    rw [hSFdef, hSGdef, ← Finset.sum_sub_distrib]
    exact hSFG
  have hdec : (A.intEv n x).val - (A.intEv n y).val
      = ((Q.sub x A.a).val - (Q.sub y A.a).val) / (A.evN n : Rat) * SF
        + (Q.sub y A.a).val / (A.evN n : Rat) * (SF - SG) := by
    rw [hEx, hEy]; ring
  have huv : (Q.sub x A.a).val - (Q.sub y A.a).val = x.val - y.val := by
    rw [Q.val_sub, Q.val_sub]; ring
  have hM : A.fBound.val ≤ 2 ^ A.mLog := ceilLog2Q_spec A.fBound
  have hMpos : (0 : Rat) ≤ A.fBound.val :=
    le_trans (abs_nonneg _) (A.fBound_spec hxa hxb)
  have hvL : |(Q.sub y A.a).val| ≤ 2 ^ A.ell := by
    rw [Q.val_sub, abs_of_nonneg (by linarith)]
    have h1 : A.len.val ≤ 2 ^ A.ell := ceilLog2Q_spec A.len
    rw [A0.len_val] at h1
    linarith
  have b1 : |((Q.sub x A.a).val - (Q.sub y A.a).val) / (A.evN n : Rat) * SF|
      ≤ |x.val - y.val| * A.fBound.val := by
    rw [abs_mul, abs_div, abs_of_pos hNR, huv]
    calc |x.val - y.val| / (A.evN n : Rat) * |SF|
        ≤ |x.val - y.val| / (A.evN n : Rat) * ((A.evN n : Rat) * A.fBound.val) :=
          mul_le_mul_of_nonneg_left hSF (by positivity)
      _ = |x.val - y.val| * A.fBound.val := by field_simp
  have b2 : |(Q.sub y A.a).val / (A.evN n : Rat) * (SF - SG)|
      ≤ (2 : Rat) ^ A.ell * (1 / 2 ^ (k + 1 + A.ell)) := by
    rw [abs_mul, abs_div, abs_of_pos hNR]
    calc |(Q.sub y A.a).val| / (A.evN n : Rat) * |SF - SG|
        ≤ |(Q.sub y A.a).val| / (A.evN n : Rat)
            * ((A.evN n : Rat) * (1 / 2 ^ (k + 1 + A.ell))) :=
          mul_le_mul_of_nonneg_left hSFG' (by positivity)
      _ = |(Q.sub y A.a).val| * (1 / 2 ^ (k + 1 + A.ell)) := by field_simp
      _ ≤ (2 : Rat) ^ A.ell * (1 / 2 ^ (k + 1 + A.ell)) :=
          mul_le_mul_of_nonneg_right hvL (by positivity)
  have e1 : |x.val - y.val| * A.fBound.val ≤ 1 / 2 ^ (k + 1) := by
    have hxyM : |x.val - y.val| ≤ 1 / 2 ^ (k + 1 + A.mLog) :=
      le_trans hxy (inv_pow_le (Nat.le_max_right _ _))
    have h1 : |x.val - y.val| * A.fBound.val
        ≤ (1 / 2 ^ (k + 1 + A.mLog)) * 2 ^ A.mLog :=
      mul_le_mul hxyM hM hMpos (by positivity)
    have h2 : (1 : Rat) / 2 ^ (k + 1 + A.mLog) * 2 ^ A.mLog = 1 / 2 ^ (k + 1) := by
      rw [pow_add]; field_simp
    linarith
  have e2 : (2 : Rat) ^ A.ell * (1 / 2 ^ (k + 1 + A.ell)) = 1 / 2 ^ (k + 1) := by
    rw [pow_add]; field_simp
  have e3 : (1 : Rat) / 2 ^ (k + 1) + 1 / 2 ^ (k + 1) = 1 / 2 ^ k := by
    rw [pow_succ]; field_simp; ring
  rw [hdec]
  refine le_trans (abs_add_le' _ _) ?_
  linarith

#print axioms A0.intEv_cont

/-- **Conservativity for `E₁`**: every exact `A₁` is an approximating one, via
the constant family.  `dq := 0` — an exact evaluator has no error for the
difference quotient to amplify, which is precisely the degeneracy the
approximating case has to work around, and why `dq` has to depend on the step
at all. -/
def A1.toE1 (A : A1) : E1 :=
  { a := A.a, b := A.b, ev := fun _ x ↦ A.f x, cm := fun _ ↦ 0, ivl := A.ivl,
    ω := A.ω, δ := A.δ, dq := fun _ _ ↦ 0,
    conv := by
      intro k n m _ _ x _ _
      rw [Qle_eq_true_iff, Q.val_abs, Q.val_sub, sub_self, abs_zero, toQ_pow2neg_val]
      positivity,
    cont := by
      intro k n x y _ hax hxb hay hyb hxy
      have h := A.cont k x y hax hxb hay hyb hxy
      rw [Q.ltN_eq_one_iff] at h
      rw [Qle_eq_true_iff]
      exact le_of_lt h,
    diff := by
      obtain ⟨F, hF⟩ := A.diff
      refine ⟨F, ?_⟩
      intro k n x h _ hax hxb hha hhb hnum hstep
      have hd := hF k x h hax hxb hha hhb hnum hstep
      rw [Q.ltN_eq_one_iff] at hd
      rw [Qle_eq_true_iff]
      exact le_of_lt hd }

/-! ### What `∫f` still needs to be an `E₁`

**`E1.cont` is done** — `A0.intEv_cont`, with modulus `A0.intOmega`, and it
holds at *every* level, needing no condition on `n`.

**`E1.diff` is not.**  The chain is set out and every ingredient is proved;
what is missing is the chain itself:

    intEv n (x+h) − intEv n x                            two grids of `evN n` cells
      ≈ riemann a (x−a+h) (N₁+N₂) − riemann a (x−a) N₁    riemann_uniform_close, twice
      = riemann (a+(x−a)) h N₂                            riemann_split, via split_widths
      ≈ h · f x                                           eftc1_quotient

with `N₁ = splitLo`, `N₂ = splitHi` and `split_mesh` supplying the meshes.  The
two `≈`s each cost `2L·2⁻ᴷ`, and dividing by `h` turns that into `4L·2⁻ᴷ/|h|`,
which is what `dq k h` has to absorb — take `K` past `k+3+ℓ+⌈log₂(1/|h|)⌉`.

Two things the chain still needs written:

* a **congruence** lemma — `intEv n (x+h)` is `riemann a (Q.sub (Q.add x h) A.a)`
  while `riemann_split` produces `riemann a (Q.add (Q.sub x A.a) h)`, equal in
  value but different terms, so the sums must be shown equal through
  `f_val_congr`, as everywhere else in this file;
* the **`h < 0` orientation** — `riemann_split` lays two lengths end to end and
  its width hypothesis forces them to share a sign, so a negative step splits
  `[a,x]` as `[a,x+h] ++ [x+h,x]` instead, and the quotient is compared to
  `f (x+h)` and then moved to `f x` by one more use of `cont`.

So `A0.intE0` still stops at `E₀`. -/

#print axioms A1.toE1
#print axioms A0.toE0
#print axioms A0.intE0

/-! ### What it took

`EFTC2Claim` is now proved for every `A₁`.  Nothing in the *analysis* was
missing; six things in the **constructions and statements** were, and each was
found by a proof failing rather than by reading the code:

1. **`omega'` was too small.**  The Lemma 1 estimate divides by
   `h₀ = min(2⁻ᵟ⁽ᵏ⁺³⁾, (b−a)/4)`, and when the second term is the minimum the
   factor is `4/(b−a)`, which a `δ`-only index cannot bound.  It now carries
   `max(δ(k+3), η₂+1)`.
2. **`A1` carried no hypotheses at all** — `ω` and `δ` were moduli of nothing,
   and the claims were refutable.  `ivl`, `cont`, `diff` are now fields.
3. **`etaAux` returned `0` when out of fuel**, which is exactly a value failing
   the property it searches for.  Fixed, with data-derived fuel; `ceilLog2Aux`
   likewise, since Lemma 2 needs `L ≤ 2ˡ`.
4. **`Lemma1Claim` was missing its interval premises.**
5. **`intN` fixed the mesh by `ω'` alone.**  That is right for the classical
   argument — Riemann sum against `∫f'` — and wrong here.  What is available in
   a shallow embedding with no `∫` is the *exact* telescoping
   `f b − f a = Σᵢ (f xᵢ₊₁ − f xᵢ) = h·Σᵢ DQ_h(xᵢ)`, and that needs the **mesh
   itself** to be an admissible `δ`-step.  Hence the `δ` term in `intN`.
6. **`sqEx.δ` was off by one.**

Two facts were needed that look like technicalities and are not.  `f` must not
distinguish two `Q`s denoting the same rational — the samples are `a + i·h`,
and `a + 0·h` is a different `Q` from `a` — and `f_val_congr` derives that from
`cont` at every precision rather than assuming it.  And `sumQ`, the `do`-loop
chosen because a structural recursion exhausts the interpreter stack at `4096`
(measured), had to be reasoned about: it does not reduce in the kernel, so
`decide` is unavailable, but it unfolds to a `foldl` over `List.range'` and from
there a step lemma is one rewrite.  No `implemented_by`, no trusted swap.

**Cost.** The two index fixes double every Riemann sample count relative to the
original code; the growth rate is unchanged (still `2^ω'(m)`, exponential in the
requested precision), which is the optimal-adequacy question, not this one.

**Approximating evaluators** (below) close the half of `EFTC1` that the exact
representation could not state: `A0.intE0` makes `∫f` an inhabitant of the
theory.  What remains for "`∫f` is `A₁`-adequate" as a single sentence is an
`E₁` layer — continuity and differentiability moduli stated for approximating
evaluators rather than exact ones.

**`EFTC1`** is the integration-direction dual, and it needed none of
this: `δ := ω`, proved directly.  That contrast *is* the asymmetry the
manifesto's §7.2 describes — integration hands you the regularity for free,
differentiation cannot manufacture it.  What `EFTC1` does **not** say here is
"`∫f` is `A₁`-adequate", and the obstacle is representational rather than a
proof gap: `A0.f : Q → Q` is an exactly rational-valued evaluator and `∫f` is
not rational-valued, so stating it needs approximating evaluators
`Nat → Q → Q`.  The differentiability half is what carries the content, and it
is what is proved.

**Still out of scope and not claimed:** the negative half, `A₀ ⊭ EFTC2`, which
is Myhill's theorem and a citation here, not a formalization. -/

#print axioms doubling_lipschitz
#print axioms translation_lipschitz
#print axioms quadrupling_lipschitz

end HAomega