/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.CriticalPoints
import HAomega.ExtractedEngines

/-!
# Newton's method on the universe, with certified quadratic convergence

The universe is closed under `d/dx`, so Newton's iteration for an expression
`f` needs no outside derivative: with `P := S_{N+2}(f)`, its derivative is
exactly `P′ = S_{N+1}(f′)` and `P″ = S_N(f″)` (the partial sums of
`UExpr.deriv`, a fact about coefficients). `UExpr.newton e N x₀ j` is `j`
Newton steps for `P` from `x₀`.

`UExpr.newton_spec` is a Kantorovich-type theorem about the rational polynomial
`P`: if `|P′| ≥ m` and `|P″| ≤ K` on the ball of radius `r` about `x₀`, and
`K·|P(x₀)|/m² ≤ 1/2`, `2|P(x₀)|/m ≤ r`, then every iterate stays in the ball and

    |P(x_j)| ≤ |P(x₀)| · 2^{1 − 2^j}      (quadratic convergence).

Combined with the certified evaluator (`approx_spec`), `P` is within `2⁻ᵏ` of
every later partial sum on the disk; bisection (`UExpr.root`) supplies the
starting point. The hypotheses are checked numbers, not assumptions about
real roots: no exact root is claimed.
-/

namespace HAomega

/-- One Newton step for `P = S_{N+2}(e)`, with `P′ = S_{N+1}(e′)`. -/
def UExpr.newtonStep (e : UExpr) (N : Nat) (x : Q) : Q :=
  Q.sub x (Q.div (Jet.evalPoly ⟨e.eval⟩ (N + 2) x)
    (Jet.evalPoly ⟨(UExpr.deriv e).eval⟩ (N + 1) x))

/-- `j` Newton steps from `x₀`. -/
def UExpr.newton (e : UExpr) (N : Nat) (x₀ : Q) : Nat → Q
  | 0 => x₀
  | j + 1 => e.newtonStep N (e.newton N x₀ j)

/-- Embed a Mathlib rational `q : Rat` into `Q` with the same `.val`. -/
def nwtOfRat (q : Rat) : Q := Q.of q.num q.den

theorem nwt_ofRat_val (q : Rat) : (nwtOfRat q).val = q := by
  unfold nwtOfRat
  rw [Q.val_of q.num q.den q.den_nz, Rat.num_div_den]

/-- `Jet.evalPoly` depends on the evaluation point only through `.val`. -/
theorem nwt_evalPoly_val_congr (F : Jet) (M : Nat) {z w : Q} (h : z.val = w.val) :
    (F.evalPoly M z).val = (F.evalPoly M w).val := by
  induction M with
  | zero => rw [Jet.evalPoly_zero, Jet.evalPoly_zero]
  | succ M ih => rw [Jet.evalPoly_succ, Jet.evalPoly_succ, ih, h]

/-- Coefficient value of `UExpr.deriv`. -/
theorem nwt_deriv_eval_val (a : UExpr) (n : Nat) :
    ((UExpr.deriv a).eval n).val = ((n + 1 : Nat) : Rat) * (a.eval (n + 1)).val := by
  change (Q.mul (Q.ofNat (n + 1)) (a.eval (n + 1))).val = _
  rw [Q.val_mul, Q.val_ofNat]

/-- Monomial second-order Taylor remainder on `|z|, |w| ≤ R` (`1 ≤ R`). -/
theorem nwt_pow_lin_rem_bound (R : Rat) (hR : 1 ≤ R) (z w : Rat)
    (hz : |z| ≤ R) (hw : |w| ≤ R) (j : Nat) :
    |w ^ (j + 1) - z ^ (j + 1) - ((j + 1 : Nat) : Rat) * (w - z) * z ^ j|
      ≤ ((j + 1 : Nat) : Rat) ^ 2 * R ^ j * (w - z) ^ 2 := by
  have hR0 : 0 ≤ R := by linarith
  have hzw : |z + (w - z)| ≤ R := by rw [add_sub_cancel]; exact hw
  have hrem := RadiusJet.mul_radius_pow_lin_rem_le_disk z (w - z) R hR0 hz hzw j
  rw [add_sub_cancel, sq_abs] at hrem
  have h1 : 1 * |w ^ (j + 1) - z ^ (j + 1) - ((j + 1 : Nat) : Rat) * (w - z) * z ^ j|
      ≤ R * |w ^ (j + 1) - z ^ (j + 1) - ((j + 1 : Nat) : Rat) * (w - z) * z ^ j| :=
    mul_le_mul_of_nonneg_right hR (abs_nonneg _)
  linarith

/-- Quadratic remainder bound constant for `S_{M+1}(a)` on `|z| ≤ R`. -/
def nwtQuadBound (a : UExpr) : Nat → Rat → Rat
  | 0, _ => 0
  | M + 1, R => nwtQuadBound a M R + |(a.eval (M + 1)).val| * ((M + 1 : Nat) : Rat) ^ 2 * R ^ M

theorem nwtQuadBound_nonneg (a : UExpr) : ∀ (M : Nat) (R : Rat), 0 ≤ R → 0 ≤ nwtQuadBound a M R
  | 0, _, _ => le_refl 0
  | M + 1, R, hR => by
    dsimp [nwtQuadBound]
    have ih := nwtQuadBound_nonneg a M R hR
    have hterm : 0 ≤ |(a.eval (M + 1)).val| * ((M + 1 : Nat) : Rat) ^ 2 * R ^ M := by positivity
    linarith

/-- Exact first-order Taylor remainder bound between `S_{M+1}(a)` and `S_M(a′)` on `|z|, |w| ≤ R`. -/
theorem nwt_evalPoly_quad_rem (a : UExpr) : ∀ (M : Nat) (R : Rat), 1 ≤ R →
    ∀ (z w : Q), |z.val| ≤ R → |w.val| ≤ R →
      |(Jet.evalPoly ⟨a.eval⟩ (M + 1) w).val - (Jet.evalPoly ⟨a.eval⟩ (M + 1) z).val
        - (Jet.evalPoly ⟨(UExpr.deriv a).eval⟩ M z).val * (w.val - z.val)|
        ≤ nwtQuadBound a M R * (w.val - z.val) ^ 2
  | 0, R, _, z, w, _, _ => by
    rw [Jet.evalPoly_one, Jet.evalPoly_one, Jet.evalPoly_zero]
    dsimp [nwtQuadBound]
    simp
  | M + 1, R, hR, z, w, hz, hw => by
    have ih := nwt_evalPoly_quad_rem a M R hR z w hz hw
    have hsplit : (Jet.evalPoly ⟨a.eval⟩ (M + 2) w).val - (Jet.evalPoly ⟨a.eval⟩ (M + 2) z).val
        - (Jet.evalPoly ⟨(UExpr.deriv a).eval⟩ (M + 1) z).val * (w.val - z.val)
        = ((Jet.evalPoly ⟨a.eval⟩ (M + 1) w).val - (Jet.evalPoly ⟨a.eval⟩ (M + 1) z).val
            - (Jet.evalPoly ⟨(UExpr.deriv a).eval⟩ M z).val * (w.val - z.val))
          + (a.eval (M + 1)).val *
            (w.val ^ (M + 1) - z.val ^ (M + 1) - ((M + 1 : Nat) : Rat) * (w.val - z.val) * z.val ^ M) := by
      rw [Jet.evalPoly_succ ⟨a.eval⟩ (M + 1) w, Jet.evalPoly_succ ⟨a.eval⟩ (M + 1) z,
          Jet.evalPoly_succ ⟨(UExpr.deriv a).eval⟩ M z, nwt_deriv_eval_val a M]
      ring
    rw [hsplit]
    have htri := abs_add_le'
      ((Jet.evalPoly ⟨a.eval⟩ (M + 1) w).val - (Jet.evalPoly ⟨a.eval⟩ (M + 1) z).val
        - (Jet.evalPoly ⟨(UExpr.deriv a).eval⟩ M z).val * (w.val - z.val))
      ((a.eval (M + 1)).val *
        (w.val ^ (M + 1) - z.val ^ (M + 1) - ((M + 1 : Nat) : Rat) * (w.val - z.val) * z.val ^ M))
    rw [abs_mul] at htri
    have hpow := nwt_pow_lin_rem_bound R hR z.val w.val hz hw M
    have hmul : |(a.eval (M + 1)).val| *
        |w.val ^ (M + 1) - z.val ^ (M + 1) - ((M + 1 : Nat) : Rat) * (w.val - z.val) * z.val ^ M|
        ≤ |(a.eval (M + 1)).val| * (((M + 1 : Nat) : Rat) ^ 2 * R ^ M * (w.val - z.val) ^ 2) :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    dsimp [nwtQuadBound]
    linarith

/-- Archimedean elimination of `C / n` for all `n > 0`. -/
theorem nwt_le_of_forall_pos_div (A B C : Rat) (hC : 0 ≤ C)
    (h : ∀ n : Nat, 0 < n → A ≤ B + C / (n : Rat)) : A ≤ B := by
  by_contra hlt
  push_neg at hlt
  have hAB : 0 < A - B := sub_pos.mpr hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (A - B))
  have hn_pos_rat : (0 : Rat) < (n : Rat) :=
    lt_of_le_of_lt (div_nonneg hC (le_of_lt hAB)) hn
  have hn_pos : 0 < n := by exact_mod_cast hn_pos_rat
  have h1 := h n hn_pos
  have h2 : C < (n : Rat) * (A - B) := (div_lt_iff₀ hAB).mp hn
  have h3 : C / (n : Rat) < A - B := (div_lt_iff₀ hn_pos_rat).mpr (by linarith)
  linarith

/-- Rational grid point `x + k · (y − x) / n` on the segment from `x` to `y`. -/
def nwtGridPt (x y : Q) (n k : Nat) : Q :=
  nwtOfRat (x.val + (k : Rat) * ((y.val - x.val) / (n : Rat)))

theorem nwtGridPt_val (x y : Q) (n k : Nat) :
    (nwtGridPt x y n k).val = x.val + (k : Rat) * ((y.val - x.val) / (n : Rat)) :=
  nwt_ofRat_val _

theorem nwtGridPt_step (x y : Q) (n k : Nat) :
    (nwtGridPt x y n (k + 1)).val - (nwtGridPt x y n k).val = (y.val - x.val) / (n : Rat) := by
  rw [nwtGridPt_val, nwtGridPt_val]
  push_cast
  ring

theorem nwtGridPt_ball (x₀ x y : Q) (r : Rat)
    (hx : |x.val - x₀.val| ≤ r) (hy : |y.val - x₀.val| ≤ r)
    (n k : Nat) (hn : 0 < n) (hk : k ≤ n) :
    |(nwtGridPt x y n k).val - x₀.val| ≤ r ∧
    |(nwtGridPt x y n k).val - x.val| ≤ |y.val - x.val| ∧
    |(nwtGridPt x y n k).val| ≤ |x₀.val| + |r| + 1 := by
  have hnR : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  have hkR : (k : Rat) ≤ (n : Rat) := by exact_mod_cast hk
  set t : Rat := (k : Rat) / (n : Rat)
  have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg k) (le_of_lt hnR)
  have ht1 : t ≤ 1 := (div_le_one hnR).mpr hkR
  have h1t : 0 ≤ 1 - t := by linarith
  have hval : (nwtGridPt x y n k).val = x.val + t * (y.val - x.val) := by
    rw [nwtGridPt_val]; dsimp [t]; ring
  have hconv : (nwtGridPt x y n k).val - x₀.val =
      (1 - t) * (x.val - x₀.val) + t * (y.val - x₀.val) := by
    rw [hval]; ring
  have hball : |(nwtGridPt x y n k).val - x₀.val| ≤ r := by
    rw [hconv]
    have htri := abs_add_le' ((1 - t) * (x.val - x₀.val)) (t * (y.val - x₀.val))
    rw [abs_mul, abs_mul, abs_of_nonneg h1t, abs_of_nonneg ht0] at htri
    have h1 := mul_le_mul_of_nonneg_left hx h1t
    have h2 := mul_le_mul_of_nonneg_left hy ht0
    linarith
  have hdist : |(nwtGridPt x y n k).val - x.val| ≤ |y.val - x.val| := by
    have hsub : (nwtGridPt x y n k).val - x.val = t * (y.val - x.val) := by
      rw [hval]; ring
    rw [hsub, abs_mul, abs_of_nonneg ht0]
    have h1 := mul_le_mul_of_nonneg_right ht1 (abs_nonneg (y.val - x.val))
    linarith
  have hrad : |(nwtGridPt x y n k).val| ≤ |x₀.val| + |r| + 1 := by
    have htri := abs_add_le' ((nwtGridPt x y n k).val - x₀.val) x₀.val
    rw [sub_add_cancel] at htri
    have hr_le : r ≤ |r| := le_abs_self r
    linarith
  exact ⟨hball, hdist, hrad⟩

/-- Mean-value Lipschitz bound on the ball `|y − x₀| ≤ r` from a derivative bound `|S_M(a′)| ≤ K`. -/
theorem nwt_evalPoly_lip_ball (a : UExpr) (M : Nat) (x₀ : Q) (r K : Rat)
    (hd : ∀ y : Q, |y.val - x₀.val| ≤ r →
      |(Jet.evalPoly ⟨(UExpr.deriv a).eval⟩ M y).val| ≤ K)
    (x y : Q) (hx : |x.val - x₀.val| ≤ r) (hy : |y.val - x₀.val| ≤ r) :
    |(Jet.evalPoly ⟨a.eval⟩ (M + 1) y).val - (Jet.evalPoly ⟨a.eval⟩ (M + 1) x).val|
      ≤ K * |y.val - x.val| := by
  let R : Rat := |x₀.val| + |r| + 1
  have hR1 : 1 ≤ R := by
    dsimp [R]
    have h0a : (0 : Rat) ≤ |x₀.val| + |r| := by positivity
    linarith
  have hR0 : 0 ≤ R := by linarith
  let C : Rat := nwtQuadBound a M R
  have hC : 0 ≤ C := nwtQuadBound_nonneg a M R hR0
  refine nwt_le_of_forall_pos_div _ _ (C * (y.val - x.val) ^ 2) (by positivity) (fun n hn ↦ ?_)
  have hnR : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  set h : Rat := (y.val - x.val) / (n : Rat)
  let z : Nat → Q := nwtGridPt x y n
  let F : Q → Rat := fun p ↦ (Jet.evalPoly ⟨a.eval⟩ (M + 1) p).val
  let F' : Q → Rat := fun p ↦ (Jet.evalPoly ⟨(UExpr.deriv a).eval⟩ M p).val
  have hstep : ∀ k ∈ Finset.range n,
      |F (z (k + 1)) - F (z k)| ≤ K * |h| + C * h ^ 2 := by
    intro k hk
    have hkl : k < n := Finset.mem_range.mp hk
    have hzk := nwtGridPt_ball x₀ x y r hx hy n k hn (le_of_lt hkl)
    have hzk1 := nwtGridPt_ball x₀ x y r hx hy n (k + 1) hn hkl
    have hrem := nwt_evalPoly_quad_rem a M R hR1 (z k) (z (k + 1)) hzk.2.2 hzk1.2.2
    have hstep_val : (z (k + 1)).val - (z k).val = h := nwtGridPt_step x y n k
    rw [hstep_val] at hrem
    have hd_k : |F' (z k)| ≤ K := hd (z k) hzk.1
    have hdh : |F' (z k) * h| ≤ K * |h| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hd_k (abs_nonneg h)
    have htri := abs_add_le' (F (z (k + 1)) - F (z k) - F' (z k) * h) (F' (z k) * h)
    rw [sub_add_cancel] at htri
    linarith
  have htel : ∑ k ∈ Finset.range n, (F (z (k + 1)) - F (z k)) = F (z n) - F (z 0) :=
    Finset.sum_range_sub (fun k ↦ F (z k)) n
  have hz0 : F (z 0) = F x :=
    nwt_evalPoly_val_congr ⟨a.eval⟩ (M + 1) (by rw [nwtGridPt_val]; push_cast; ring)
  have hzn : F (z n) = F y :=
    nwt_evalPoly_val_congr ⟨a.eval⟩ (M + 1) (by
      rw [nwtGridPt_val, mul_div_cancel₀ _ (ne_of_gt hnR)]; ring)
  have hsum_abs : |F y - F x| ≤ (n : Rat) * (K * |h| + C * h ^ 2) := by
    rw [← hzn, ← hz0, ← htel]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle := Finset.sum_le_card_nsmul (Finset.range n)
      (fun k ↦ |F (z (k + 1)) - F (z k)|) (K * |h| + C * h ^ 2) hstep
    rwa [Finset.card_range, nsmul_eq_mul] at hle
  have hrhs : (n : Rat) * (K * |h| + C * h ^ 2) =
      K * |y.val - x.val| + C * (y.val - x.val) ^ 2 / (n : Rat) := by
    dsimp [h]
    rw [abs_div, abs_of_pos hnR]
    field_simp
  linarith

/-- Second-order Taylor remainder bound `|P(y) − P(x) − P′(x)(y − x)| ≤ K|y − x|²` on the ball. -/
theorem nwt_evalPoly_taylor2_ball (e : UExpr) (N : Nat) (x₀ : Q) (r K : Rat) (hK : 0 ≤ K)
    (hdd : ∀ y : Q, |y.val - x₀.val| ≤ r →
      |(Jet.evalPoly ⟨(UExpr.deriv (UExpr.deriv e)).eval⟩ N y).val| ≤ K)
    (x y : Q) (hx : |x.val - x₀.val| ≤ r) (hy : |y.val - x₀.val| ≤ r) :
    |(Jet.evalPoly ⟨e.eval⟩ (N + 2) y).val - (Jet.evalPoly ⟨e.eval⟩ (N + 2) x).val
      - (Jet.evalPoly ⟨(UExpr.deriv e).eval⟩ (N + 1) x).val * (y.val - x.val)|
      ≤ K * (y.val - x.val) ^ 2 := by
  let R : Rat := |x₀.val| + |r| + 1
  have hR1 : 1 ≤ R := by
    dsimp [R]
    have h0a : (0 : Rat) ≤ |x₀.val| + |r| := by positivity
    linarith
  have hR0 : 0 ≤ R := by linarith
  let C : Rat := nwtQuadBound e (N + 1) R
  have hC : 0 ≤ C := nwtQuadBound_nonneg e (N + 1) R hR0
  refine nwt_le_of_forall_pos_div _ _ (C * (y.val - x.val) ^ 2) (by positivity) (fun n hn ↦ ?_)
  have hnR : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  set h : Rat := (y.val - x.val) / (n : Rat)
  let z : Nat → Q := nwtGridPt x y n
  let P : Q → Rat := fun p ↦ (Jet.evalPoly ⟨e.eval⟩ (N + 2) p).val
  let P' : Q → Rat := fun p ↦ (Jet.evalPoly ⟨(UExpr.deriv e).eval⟩ (N + 1) p).val
  have hstep : ∀ k ∈ Finset.range n,
      |P (z (k + 1)) - P (z k) - P' x * h|
        ≤ K * |y.val - x.val| * |h| + C * h ^ 2 := by
    intro k hk
    have hkl : k < n := Finset.mem_range.mp hk
    have hzk := nwtGridPt_ball x₀ x y r hx hy n k hn (le_of_lt hkl)
    have hzk1 := nwtGridPt_ball x₀ x y r hx hy n (k + 1) hn hkl
    have hrem := nwt_evalPoly_quad_rem e (N + 1) R hR1 (z k) (z (k + 1)) hzk.2.2 hzk1.2.2
    have hstep_val : (z (k + 1)).val - (z k).val = h := nwtGridPt_step x y n k
    rw [hstep_val] at hrem
    have hlip := nwt_evalPoly_lip_ball (UExpr.deriv e) N x₀ r K hdd x (z k) hx hzk.1
    have hlip_x : |P' (z k) - P' x| ≤ K * |y.val - x.val| :=
      le_trans hlip (mul_le_mul_of_nonneg_left hzk.2.1 hK)
    have hdh : |(P' (z k) - P' x) * h| ≤ K * |y.val - x.val| * |h| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hlip_x (abs_nonneg h)
    have hid : P (z (k + 1)) - P (z k) - P' x * h =
        (P (z (k + 1)) - P (z k) - P' (z k) * h) + (P' (z k) - P' x) * h := by ring
    rw [hid]
    have htri := abs_add_le' (P (z (k + 1)) - P (z k) - P' (z k) * h) ((P' (z k) - P' x) * h)
    linarith
  have htel : ∑ k ∈ Finset.range n, (P (z (k + 1)) - P (z k) - P' x * h) =
      P (z n) - P (z 0) - (n : Rat) * (P' x * h) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun k ↦ P (z k)) n,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hz0 : P (z 0) = P x :=
    nwt_evalPoly_val_congr ⟨e.eval⟩ (N + 2) (by rw [nwtGridPt_val]; push_cast; ring)
  have hzn : P (z n) = P y :=
    nwt_evalPoly_val_congr ⟨e.eval⟩ (N + 2) (by
      rw [nwtGridPt_val, mul_div_cancel₀ _ (ne_of_gt hnR)]; ring)
  have hnh : (n : Rat) * (P' x * h) = P' x * (y.val - x.val) := by
    dsimp [h]
    field_simp
  have hsum_abs : |P y - P x - P' x * (y.val - x.val)|
      ≤ (n : Rat) * (K * |y.val - x.val| * |h| + C * h ^ 2) := by
    rw [← hzn, ← hz0, ← hnh, ← htel]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hle := Finset.sum_le_card_nsmul (Finset.range n)
      (fun k ↦ |P (z (k + 1)) - P (z k) - P' x * h|)
      (K * |y.val - x.val| * |h| + C * h ^ 2) hstep
    rwa [Finset.card_range, nsmul_eq_mul] at hle
  have hrhs : (n : Rat) * (K * |y.val - x.val| * |h| + C * h ^ 2) =
      K * (y.val - x.val) ^ 2 + C * (y.val - x.val) ^ 2 / (n : Rat) := by
    dsimp [h]
    rw [abs_div, abs_of_pos hnR]
    have h1 : (n : Rat) * (K * |y.val - x.val| * (|y.val - x.val| / (n : Rat))) =
        K * |y.val - x.val| ^ 2 := by
      field_simp
    have h2 : (n : Rat) * (C * ((y.val - x.val) / (n : Rat)) ^ 2) =
        C * (y.val - x.val) ^ 2 / (n : Rat) := by
      field_simp
    rw [mul_add, h1, h2, sq_abs]
  linarith

/-- One Newton step bound: step length `|x′ − x| ≤ |P(x)|/m` and quadratic residual `|P(x′)| ≤ (K|P(x)|/m²)|P(x)|`. -/
theorem nwt_step_bound (e : UExpr) (N : Nat) (x₀ : Q) (r m K : Rat)
    (hm : 0 < m) (hK : 0 ≤ K)
    (hd : ∀ y : Q, |y.val - x₀.val| ≤ r →
      m ≤ |(Jet.evalPoly ⟨(UExpr.deriv e).eval⟩ (N + 1) y).val|)
    (hdd : ∀ y : Q, |y.val - x₀.val| ≤ r →
      |(Jet.evalPoly ⟨(UExpr.deriv (UExpr.deriv e)).eval⟩ N y).val| ≤ K)
    (x : Q) (hx : |x.val - x₀.val| ≤ r) :
    |(e.newtonStep N x).val - x.val| ≤ |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x).val| / m ∧
    (|(e.newtonStep N x).val - x₀.val| ≤ r →
      |(Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newtonStep N x)).val|
        ≤ (K * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x).val| / m ^ 2)
          * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x).val|) := by
  let px := (Jet.evalPoly ⟨e.eval⟩ (N + 2) x).val
  let dpx := (Jet.evalPoly ⟨(UExpr.deriv e).eval⟩ (N + 1) x).val
  have hdpx_ge : m ≤ |dpx| := hd x hx
  have hdpx_pos : 0 < |dpx| := lt_of_lt_of_le hm hdpx_ge
  have hdpx_ne : dpx ≠ 0 := abs_pos.mp hdpx_pos
  have hstep_val : (e.newtonStep N x).val - x.val = -(px / dpx) := by
    unfold UExpr.newtonStep
    rw [Q.val_sub, Q.val_div_all]
    dsimp [px, dpx]
    ring
  have hstep_abs : |(e.newtonStep N x).val - x.val| ≤ |px| / m := by
    rw [hstep_val, abs_neg, abs_div]
    exact div_le_div_of_nonneg_left (abs_nonneg px) hm hdpx_ge
  refine ⟨hstep_abs, fun hx' ↦ ?_⟩
  have htaylor := nwt_evalPoly_taylor2_ball e N x₀ r K hK hdd x (e.newtonStep N x) hx hx'
  have hcancel : (Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newtonStep N x)).val - px
      - dpx * ((e.newtonStep N x).val - x.val) =
      (Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newtonStep N x)).val := by
    rw [hstep_val]
    field_simp
    ring
  rw [hcancel] at htaylor
  have hsq : ((e.newtonStep N x).val - x.val) ^ 2 ≤ (|px| / m) ^ 2 := by
    rw [← sq_abs ((e.newtonStep N x).val - x.val)]
    exact pow_le_pow_left₀ (abs_nonneg _) hstep_abs 2
  have hKsq := mul_le_mul_of_nonneg_left hsq hK
  have hrhs : K * (|px| / m) ^ 2 = (K * |px| / m ^ 2) * |px| := by ring
  linarith

/-- Elementary exponential dominance `j + 1 ≤ 2^j`. -/
theorem nwt_succ_le_two_pow : ∀ j : Nat, j + 1 ≤ 2 ^ j
  | 0 => by decide
  | k + 1 => by
    have ih := nwt_succ_le_two_pow k
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [Nat.pow_succ]
    omega

/-- Coupled inductive invariant for `UExpr.newton_spec`. -/
theorem nwt_iter_inv (e : UExpr) (N : Nat) (x₀ : Q) (r m K : Rat)
    (hm : 0 < m) (hK : 0 ≤ K)
    (hd : ∀ y : Q, |y.val - x₀.val| ≤ r →
      m ≤ |(Jet.evalPoly ⟨(UExpr.deriv e).eval⟩ (N + 1) y).val|)
    (hdd : ∀ y : Q, |y.val - x₀.val| ≤ r →
      |(Jet.evalPoly ⟨(UExpr.deriv (UExpr.deriv e)).eval⟩ N y).val| ≤ K)
    (h0 : K * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| / m ^ 2 ≤ 1 / 2)
    (hr : 2 * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| / m ≤ r) :
    ∀ j : Nat,
      |(e.newton N x₀ j).val - x₀.val|
        ≤ (2 * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| / m) * (1 - 1 / (2 : Rat) ^ j) ∧
      |(Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newton N x₀ j)).val|
        ≤ |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| * 2 / (2 : Rat) ^ (2 ^ j)
  | 0 => by
    dsimp [UExpr.newton]
    refine ⟨?_, ?_⟩
    · rw [sub_self, abs_zero, pow_zero, div_one, sub_self, mul_zero]
    · linarith
  | j + 1 => by
    obtain ⟨ih_x, ih_p⟩ := nwt_iter_inv e N x₀ r m K hm hK hd hdd h0 hr j
    let p0 := |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val|
    have hp0 : 0 ≤ p0 := abs_nonneg _
    have h2p0m : 0 ≤ 2 * p0 / m := by positivity
    have hxj_ball : |(e.newton N x₀ j).val - x₀.val| ≤ r := by
      have h1 : (2 * p0 / m) * (1 - 1 / (2 : Rat) ^ j) ≤ 2 * p0 / m := by
        have : (0 : Rat) ≤ (2 * p0 / m) * (1 / (2 : Rat) ^ j) := by positivity
        linarith
      exact le_trans ih_x (le_trans h1 hr)
    have hstep := nwt_step_bound e N x₀ r m K hm hK hd hdd (e.newton N x₀ j) hxj_ball
    have hpow_le : (2 : Rat) ^ (j + 1) ≤ (2 : Rat) ^ (2 ^ j) :=
      pow_le_pow_right₀ (by norm_num) (nwt_succ_le_two_pow j)
    have hdiv_le : p0 * 2 / (2 : Rat) ^ (2 ^ j) ≤ p0 * 2 / (2 : Rat) ^ (j + 1) :=
      div_le_div_of_nonneg_left (by positivity : 0 ≤ p0 * 2) (by positivity) hpow_le
    have hstep_dx : |(e.newton N x₀ (j + 1)).val - (e.newton N x₀ j).val|
        ≤ (2 * p0 / m) * (1 / (2 : Rat) ^ j - 1 / (2 : Rat) ^ (j + 1)) := by
      dsimp [UExpr.newton]
      have h1 : |(Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newton N x₀ j)).val| / m
          ≤ (p0 * 2 / (2 : Rat) ^ (j + 1)) / m :=
        div_le_div_of_nonneg_right (le_trans ih_p hdiv_le) (le_of_lt hm)
      have h2 : (p0 * 2 / (2 : Rat) ^ (j + 1)) / m =
          (2 * p0 / m) * (1 / (2 : Rat) ^ j - 1 / (2 : Rat) ^ (j + 1)) := by
        rw [pow_succ (2 : Rat) j]
        field_simp
        ring
      linarith [hstep.1, h1, h2]
    have hx_next : |(e.newton N x₀ (j + 1)).val - x₀.val|
        ≤ (2 * p0 / m) * (1 - 1 / (2 : Rat) ^ (j + 1)) := by
      have htri := abs_sub_le (e.newton N x₀ (j + 1)).val (e.newton N x₀ j).val x₀.val
      linarith
    have hx_next_ball : |(e.newton N x₀ (j + 1)).val - x₀.val| ≤ r := by
      have h1 : (2 * p0 / m) * (1 - 1 / (2 : Rat) ^ (j + 1)) ≤ 2 * p0 / m := by
        have : (0 : Rat) ≤ (2 * p0 / m) * (1 / (2 : Rat) ^ (j + 1)) := by positivity
        linarith
      exact le_trans hx_next (le_trans h1 hr)
    refine ⟨hx_next, ?_⟩
    have hq_next := hstep.2 hx_next_ball
    have hqj : K * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newton N x₀ j)).val| / m ^ 2
        ≤ 1 / (2 : Rat) ^ (2 ^ j) := by
      have h1 : K * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newton N x₀ j)).val| / m ^ 2
          ≤ (K * p0 / m ^ 2) * (2 / (2 : Rat) ^ (2 ^ j)) := by
        have hm1 := mul_le_mul_of_nonneg_left ih_p hK
        have hm2 := div_le_div_of_nonneg_right hm1 (by positivity : 0 ≤ m ^ 2)
        have heq : K * (p0 * 2 / (2 : Rat) ^ (2 ^ j)) / m ^ 2 =
            (K * p0 / m ^ 2) * (2 / (2 : Rat) ^ (2 ^ j)) := by ring
        linarith
      have h2 : (K * p0 / m ^ 2) * (2 / (2 : Rat) ^ (2 ^ j))
          ≤ (1 / 2) * (2 / (2 : Rat) ^ (2 ^ j)) :=
        mul_le_mul_of_nonneg_right h0 (by positivity)
      have h3 : (1 / 2 : Rat) * (2 / (2 : Rat) ^ (2 ^ j)) = 1 / (2 : Rat) ^ (2 ^ j) := by ring
      linarith
    have hp_next : (K * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newton N x₀ j)).val| / m ^ 2)
        * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newton N x₀ j)).val|
        ≤ (1 / (2 : Rat) ^ (2 ^ j)) * (p0 * 2 / (2 : Rat) ^ (2 ^ j)) :=
      mul_le_mul hqj ih_p (abs_nonneg _) (by positivity)
    have hpow_sq : (1 / (2 : Rat) ^ (2 ^ j)) * (p0 * 2 / (2 : Rat) ^ (2 ^ j)) =
        p0 * 2 / (2 : Rat) ^ (2 ^ (j + 1)) := by
      have hexp : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
      rw [hexp, pow_add (2 : Rat) (2 ^ j) (2 ^ j)]
      ring
    dsimp [UExpr.newton]
    linarith

/-- **Quadratic convergence, certified.** -/
theorem UExpr.newton_spec (e : UExpr) (N : Nat) (x₀ : Q) (r m K : Rat)
    (hm : 0 < m) (hK : 0 ≤ K)
    (hd : ∀ y : Q, |y.val - x₀.val| ≤ r →
      m ≤ |(Jet.evalPoly ⟨(UExpr.deriv e).eval⟩ (N + 1) y).val|)
    (hdd : ∀ y : Q, |y.val - x₀.val| ≤ r →
      |(Jet.evalPoly ⟨(UExpr.deriv (UExpr.deriv e)).eval⟩ N y).val| ≤ K)
    (h0 : K * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| / m ^ 2 ≤ 1 / 2)
    (hr : 2 * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| / m ≤ r) :
    ∀ j : Nat, |(e.newton N x₀ j).val - x₀.val| ≤ r ∧
      |(Jet.evalPoly ⟨e.eval⟩ (N + 2) (e.newton N x₀ j)).val|
        ≤ |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| * 2 / (2 : Rat) ^ (2 ^ j) := by
  intro j
  obtain ⟨hx, hp⟩ := nwt_iter_inv e N x₀ r m K hm hK hd hdd h0 hr j
  refine ⟨?_, hp⟩
  have h1 : (2 * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| / m) * (1 - 1 / (2 : Rat) ^ j)
      ≤ 2 * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| / m := by
    have : (0 : Rat) ≤
        (2 * |(Jet.evalPoly ⟨e.eval⟩ (N + 2) x₀).val| / m) * (1 / (2 : Rat) ^ j) := by
      positivity
    linarith
  exact le_trans hx (le_trans h1 hr)

/-! ## Checks

The plain definition agrees with the extracted Newton engine `newtonIterExtracted`
(`ExtractedEngines.lean`) run on `P`, `P′`. Example: `f = eˣ − 1 − 1/40`,
root `ln(41/40) = 0.0246926125903714…`; from `x₀ = 0`, three steps reach `10⁻¹⁴`, four `10⁻²⁸`
(quadratic: the digits double).

**Cost.** Exact rational iterates grow about twentyfold in bit length per step
(a degree-22 polynomial is evaluated at each): 172, 3696, 77688 bits for steps
2–4. Rounding each iterate to a dyadic, with the rounding error absorbed into
the contraction, is the open speed item. -/

/-- `eˣ − 1 − 1/40`. -/
def newtonExample : UExpr := .sub (.sub .exp (.const (Q.ofNat 1))) (.const ⟨1, 39⟩)

#guard (List.range 4).all fun j ↦
  Q.norm (newtonExample.newton 12 ⟨0, 0⟩ j)
    == Q.norm (newtonIterExtracted (fun x ↦ Jet.evalPoly ⟨newtonExample.eval⟩ 14 x)
        (fun x ↦ Jet.evalPoly ⟨(UExpr.deriv newtonExample).eval⟩ 13 x) Q.zero ⟨0, 0⟩ j)
#guard (let r := newtonExample.newton 20 ⟨0, 0⟩ 3
        decide (|r.val - (2469261259037150101430767543669 : Rat) / 10 ^ 32| < 1 / 10 ^ 14))
#guard (let r := newtonExample.newton 24 ⟨0, 0⟩ 4
        decide (|r.val - (2469261259037150101430767543669 : Rat) / 10 ^ 32| < 1 / 10 ^ 28))

#print axioms UExpr.newton
#print axioms UExpr.newton_spec

end HAomega
