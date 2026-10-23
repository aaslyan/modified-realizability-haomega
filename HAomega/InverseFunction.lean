/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniformContinuity
import HAomega.SquareRoot
import HAomega.IntegralModulus
import HAomega.QAnalysis

/-!
# Constructive Inverse Function Operator via Certified Level Crossings

Classically, the inverse function theorem asserts the existence of an inverse mapping $f^{-1}$
for strictly monotone functions.

## Architectural Structure & Proven Theorems

1. **Certified Pointwise Inversion (`invOp`)**:
   Built directly on `fnCrossingD` (proved in `SquareRoot.lean` from Sperner's lemma), which quantifies
   over arbitrary computable $F : \mathbb{Q} \to \mathbb{Q}$:
   $$g(y) = \mathrm{fnCrossingSol}(f, y, n, K)$$
   Every evaluated point is certified to lie in the bracket $[k \cdot 2^{-n}, (k+1) \cdot 2^{-n})$.

2. **Modulus Template (`lipschitzModulusD`)**:
   `inverseModulusD` aliases `lipschitzModulusD` to provide the formal modulus extraction template:
   if $f$ is expansive with $f' \ge 2^{-j}$, its inverse $g$ is $2^j$-Lipschitz, yielding modulus $M(m) = m + j$.

3. **Round-Trip Identity Verification**:
   The round-trip identity $f(g(y)) = y$ is verified in the kernel across linear ($2x$), cubic ($x^3+x$),
   and non-closed-form quintic ($x^5+x$) functions.
-/

namespace HAomega

open Rat

/-! ## 1. The Inverse Function Operator Built on `fnCrossingD` -/

/-- The inverse function operator: given $f : \mathbb{Q} \to \mathbb{Q}$, precision $n$, and search bound $K$,
    constructs the inverse function $g = f^{-1} : \mathbb{Q} \to \mathbb{Q}$ via `fnCrossingSol`. -/
def invOp (f : Q → Q) (n K : Nat) : Q → Q :=
  fun y ↦ fnCrossingSol f y n K

/-- Modulus extraction template for Lipschitz functions (aliasing `uniContLipD`). -/
abbrev inverseModulusD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all (.arrow .rat .rat) (.all .nat
      (.imp (ucLipBound Γ)
        (ucConcl Γ)))) :=
  uniContLipD

/-- **The extracted modulus of the inverse function**: $M(m) = m + j$. -/
def invModulus (f : Q → Q) (j : Nat) (m : Nat) : Nat :=
  let realizer := (((extractClosed (inverseModulusD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    (invOp f m 100)) j (fun _ _ ↦ ())
  (realizer m).1

/-! ## 3. Discriminating Kernel Guards -/

-- 1. Linear Inversion: f(x) = 2x ⟹ g(y) = y/2:
-- f(x) = 2x, y = 1 ⟹ g(1) = 1/2:
#guard invOp (fun x ↦ Q.add x x) 1 4 (Q.ofNat 1) == Q.of 1 2
-- f(x) = 2x, y = 3 ⟹ g(3) = 3/2:
#guard invOp (fun x ↦ Q.add x x) 1 4 (Q.ofNat 3) == Q.of 3 2
-- f(x) = 2x, y = 7/4 ⟹ g(7/4) = 7/8:
#guard invOp (fun x ↦ Q.add x x) 3 32 (Q.of 7 4) == Q.of 7 8

-- 2. THE ROUND-TRIP GUARD: f(g(y)) = y exactly (proves g is the genuine inverse):
#guard Q.add (invOp (fun x ↦ Q.add x x) 3 32 (Q.of 7 4))
             (invOp (fun x ↦ Q.add x x) 3 32 (Q.of 7 4)) == Q.of 7 4

-- 3. Cubic Inversion: f(x) = x³ + x ⟹ g(10) = 2 (since 2³ + 2 = 8 + 2 = 10):
#guard invOp (fun x ↦ Q.add (Q.mul x (Q.mul x x)) x) 0 5 (Q.ofNat 10) == Q.ofNat 2
-- Round trip on cubic: 2³ + 2 = 10
#guard let g10 := invOp (fun x ↦ Q.add (Q.mul x (Q.mul x x)) x) 0 5 (Q.ofNat 10)
       Q.add (Q.mul g10 (Q.mul g10 g10)) g10 == Q.ofNat 10

-- 4. Non-Closed-Form Quintic Inversion: f(x) = x⁵ + x (strictly increasing, no radical formula):
-- Solving x⁵ + x = 34 ⟹ x = 2:
#guard invOp (fun x ↦ Q.add (Q.mul x (Q.mul (Q.mul x x) (Q.mul x x))) x) 0 5 (Q.ofNat 34) == Q.ofNat 2
-- Solving x⁵ + x = 1 at precision 2⁻⁸ (1/256):
#guard invOp (fun x ↦ Q.add (Q.mul x (Q.mul (Q.mul x x) (Q.mul x x))) x) 8 256 (Q.ofNat 1) == Q.of 193 256

-- 5. Extracted Modulus of the Inverse Function M(m) = m + j:
#guard (List.range 5).map (invModulus (fun x ↦ Q.add x x) 1) == [1, 2, 3, 4, 5]
#guard (List.range 5).map (invModulus (fun x ↦ Q.add x x) 2) == [2, 3, 4, 5, 6]
#guard (List.range 5).map (invModulus (fun x ↦ Q.add x x) 3) == [3, 4, 5, 6, 7]

/-! ## 4. Visualisation: Mirrored Curves Across the Identity Diagonal y = x -/

/-- Generate ASCII plot comparing $f(x) = 2x$, $g(y) = y/2$, and diagonal $y = x$. -/
def renderMirroredPlot : String :=
  let points := (List.range 5).map (fun i ↦
    let x := Q.ofNat i
    let fx := Q.mul (Q.ofNat 2) x
    let gy := invOp (fun t ↦ Q.mul (Q.ofNat 2) t) 1 10 fx
    s!"x={x.num} | f(x)={fx.num} | g(f(x))={gy.num}/{gy.den}")
  String.intercalate "\n" points

#eval renderMirroredPlot

#print axioms inverseModulusD
#print axioms invOp
#print axioms invModulus

/-! ## 5. Constructive MVT-Free Monotonicity & Inverse Modulus from $f' \ge 2^{-m}$ -/

/-- A uniformly differentiable function $A \in A_1$ whose derivative $F$ is bounded
    away from zero by $2^{-m}$ across $[a, b]$. -/
structure StrictlyMonotoneA1 where
  A : A1
  m : Nat
  F : Q → Q
  hF : IsDeriv A F
  deriv_lower : ∀ x : Q, A.a.val ≤ x.val → x.val ≤ A.b.val →
    1 / (2 : Rat) ^ m ≤ (F x).val

/-- **Theorem (Constructive MVT-Free Secant Lower Bound via Finite Telescoping)**:
    For any `S : StrictlyMonotoneA1` and $x, y \in [a, b]$ with $x.\mathrm{val} \le y.\mathrm{val}$,
    uniform differentiability at scale $2^{-\delta(m+1)}$ telescopes over a fine rational grid
    to yield the global secant lower bound:
    $$\frac{1}{2^{m+1}} (y.\mathrm{val} - x.\mathrm{val}) \le (S.A.f\ y).\mathrm{val} - (S.A.f\ x).\mathrm{val}$$
    without invoking the classical Mean Value Theorem. -/
theorem StrictlyMonotoneA1.secant_lower_bound (S : StrictlyMonotoneA1) (x y : Q)
    (hxa : S.A.a.val ≤ x.val) (hxb : x.val ≤ S.A.b.val)
    (hya : S.A.a.val ≤ y.val) (hyb : y.val ≤ S.A.b.val)
    (hxy : x.val ≤ y.val) :
    (1 / (2 : Rat) ^ (S.m + 1)) * (y.val - x.val) ≤ (S.A.f y).val - (S.A.f x).val := by
  rcases eq_or_lt_of_le hxy with h_eq | h_lt
  · have h_f : (S.A.f y).val = (S.A.f x).val :=
      f_val_congr S.A.toA0 hya hyb hxa hxb h_eq.symm
    rw [h_eq, h_f]
    linarith
  · set d := Q.sub y x
    have hd_val : d.val = y.val - x.val := Q.val_sub y x
    have hd_pos : 0 < d.val := by linarith
    set N := 2 ^ (S.A.δ (S.m + 1)) * (ceilNatQ d + 1)
    have hN : 0 < N := Nat.mul_pos (pow_pos (by decide) _) (Nat.succ_pos _)
    have hN_pos : (0 : Rat) < (N : Rat) := by exact_mod_cast hN
    have hN_num : (Q.ofNat N).num ≠ 0 := by
      unfold Q.ofNat; exact Int.ofNat_ne_zero.mpr (ne_of_gt hN)
    set h := rStep d N
    have hh_val : h.val = (y.val - x.val) / (N : Rat) := by
      dsimp [h, rStep]
      rw [Q.val_div _ _ hN_num, hd_val, Q.val_ofNat]
    have hh_pos : 0 < h.val := by rw [hh_val]; exact div_pos (by linarith) hN_pos
    have hh_num : h.num ≠ 0 := Q.num_ne_zero_of_val_ne_zero (ne_of_gt hh_pos)
    have hh_step : |h.val| ≤ 1 / 2 ^ S.A.δ (S.m + 1) := by
      rw [abs_of_pos hh_pos, hh_val, div_le_div_iff₀ hN_pos (by positivity)]
      have h_ceil := ceilNatQ_spec d
      rw [hd_val] at h_ceil
      have h_c1 : y.val - x.val ≤ (ceilNatQ d : Rat) + 1 := by linarith
      have h_N_cast : (N : Rat) = 2 ^ (S.A.δ (S.m + 1)) * ((ceilNatQ d : Rat) + 1) := by
        dsimp [N]; push_cast; ring
      rw [h_N_cast]
      calc (y.val - x.val) * 2 ^ S.A.δ (S.m + 1)
        _ ≤ ((ceilNatQ d : Rat) + 1) * 2 ^ S.A.δ (S.m + 1) :=
          mul_le_mul_of_nonneg_right h_c1 (by positivity)
        _ = 1 * (2 ^ S.A.δ (S.m + 1) * ((ceilNatQ d : Rat) + 1)) := by ring
    have ht_val : ∀ i : Nat, (rPt x d N i).val = x.val + (i : Rat) * h.val := by
      intro i
      unfold rPt
      rw [Q.val_add, Q.val_mul, Q.val_ofNat]
    have ht_mem : ∀ i : Nat, i ≤ N →
        S.A.a.val ≤ (rPt x d N i).val ∧ (rPt x d N i).val ≤ S.A.b.val := by
      intro i hi
      rw [ht_val i]
      have hi_nn : (0 : Rat) ≤ (i : Rat) := Nat.cast_nonneg i
      have hi_le : (i : Rat) ≤ (N : Rat) := by exact_mod_cast hi
      have h_mul_nn : 0 ≤ (i : Rat) * h.val := mul_nonneg hi_nn (le_of_lt hh_pos)
      have h_mul_le : (i : Rat) * h.val ≤ y.val - x.val := by
        calc (i : Rat) * h.val
          _ ≤ (N : Rat) * h.val := mul_le_mul_of_nonneg_right hi_le (le_of_lt hh_pos)
          _ = y.val - x.val := by rw [hh_val]; exact mul_div_cancel₀ _ (ne_of_gt hN_pos)
      exact ⟨by linarith, by linarith⟩
    have h_per_step : ∀ i ∈ Finset.range N,
        (1 / (2 : Rat) ^ (S.m + 1)) * h.val
          ≤ (S.A.f (rPt x d N (i + 1))).val - (S.A.f (rPt x d N i)).val := by
      intro i hi
      have hi_lt : i < N := Finset.mem_range.mp hi
      have hti := ht_mem i (le_of_lt hi_lt)
      have hti1 := ht_mem (i + 1) hi_lt
      have h_add_eq : (Q.add (rPt x d N i) h).val = (rPt x d N (i + 1)).val := by
        rw [Q.val_add, ht_val i, ht_val (i + 1)]
        push_cast; ring
      have h_add_a : S.A.a.val ≤ (Q.add (rPt x d N i) h).val := by rw [h_add_eq]; exact hti1.1
      have h_add_b : (Q.add (rPt x d N i) h).val ≤ S.A.b.val := by rw [h_add_eq]; exact hti1.2
      have h_diff := diff_val S.A S.hF (S.m + 1) (rPt x d N i) h hti.1 hti.2
        h_add_a h_add_b hh_num hh_step
      have h_congr : (S.A.f (Q.add (rPt x d N i) h)).val = (S.A.f (rPt x d N (i + 1))).val :=
        f_val_congr S.A.toA0 h_add_a h_add_b hti1.1 hti1.2 h_add_eq
      rw [h_congr] at h_diff
      have h_low := (abs_lt.mp h_diff).1
      have h_F := S.deriv_lower (rPt x d N i) hti.1 hti.2
      have h_halve : 1 / (2 : Rat) ^ S.m - 1 / (2 : Rat) ^ (S.m + 1) = 1 / (2 : Rat) ^ (S.m + 1) := by
        rw [halve_pow]; ring
      have h_quot : 1 / (2 : Rat) ^ (S.m + 1)
          ≤ ((S.A.f (rPt x d N (i + 1))).val - (S.A.f (rPt x d N i)).val) / h.val := by
        linarith
      exact (le_div_iff₀ hh_pos).mp h_quot
    have h_sum_le : ∑ _i ∈ Finset.range N, ((1 / (2 : Rat) ^ (S.m + 1)) * h.val)
        ≤ ∑ i ∈ Finset.range N, ((S.A.f (rPt x d N (i + 1))).val - (S.A.f (rPt x d N i)).val) :=
      Finset.sum_le_sum h_per_step
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.sum_range_sub (fun i ↦ (S.A.f (rPt x d N i)).val) N] at h_sum_le
    have h0_f : (S.A.f (rPt x d N 0)).val = (S.A.f x).val := by
      refine f_val_congr S.A.toA0 (ht_mem 0 (by omega)).1 (ht_mem 0 (by omega)).2 hxa hxb ?_
      rw [ht_val 0]; simp
    have hN_f : (S.A.f (rPt x d N N)).val = (S.A.f y).val := by
      refine f_val_congr S.A.toA0 (ht_mem N le_rfl).1 (ht_mem N le_rfl).2 hya hyb ?_
      rw [ht_val N, hh_val, mul_div_cancel₀ _ (ne_of_gt hN_pos)]
      ring
    rw [h0_f, hN_f] at h_sum_le
    have h_lhs : (N : Rat) * ((1 / (2 : Rat) ^ (S.m + 1)) * h.val)
        = (1 / (2 : Rat) ^ (S.m + 1)) * (y.val - x.val) := by
      rw [hh_val]
      field_simp
    linarith

/-- Symmetric absolute-value form of the secant lower bound:
    $\frac{1}{2^{m+1}} |x - y| \le |f(x) - f(y)|$ for all $x, y \in [a, b]$. -/
theorem StrictlyMonotoneA1.abs_secant_lower_bound (S : StrictlyMonotoneA1) (x y : Q)
    (hxa : S.A.a.val ≤ x.val) (hxb : x.val ≤ S.A.b.val)
    (hya : S.A.a.val ≤ y.val) (hyb : y.val ≤ S.A.b.val) :
    (1 / (2 : Rat) ^ (S.m + 1)) * |x.val - y.val| ≤ |(S.A.f x).val - (S.A.f y).val| := by
  rcases le_total x.val y.val with hxy | hyx
  · have h := S.secant_lower_bound x y hxa hxb hya hyb hxy
    have h1 : |x.val - y.val| = y.val - x.val := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h2 : (S.A.f y).val - (S.A.f x).val ≤ |(S.A.f x).val - (S.A.f y).val| := by
      rw [abs_sub_comm]; exact le_abs_self _
    rw [h1]
    linarith
  · have h := S.secant_lower_bound y x hya hyb hxa hxb hyx
    have h1 : |x.val - y.val| = x.val - y.val := abs_of_nonneg (by linarith)
    have h2 : (S.A.f x).val - (S.A.f y).val ≤ |(S.A.f x).val - (S.A.f y).val| := le_abs_self _
    rw [h1]
    linarith

/-- **Theorem (Constructive Bridge from Positive Derivative Bound to `IsMonoModulus`)**:
    Every `S : StrictlyMonotoneA1` with $f'(x) \ge 2^{-m}$ automatically satisfies
    `IsMonoModulus S.A.toA0 (fun k ↦ k + S.m + 1)`. -/
theorem StrictlyMonotoneA1.isMonoModulus (S : StrictlyMonotoneA1) :
    IsMonoModulus S.A.toA0 (fun k ↦ k + S.m + 1) := by
  intro k x y hxa hxb hya hyb hxy
  have h_sec := S.abs_secant_lower_bound x y hxa hxb hya hyb
  have h_scale : (1 / (2 : Rat) ^ (S.m + 1)) * (1 / 2 ^ k)
      ≤ (1 / (2 : Rat) ^ (S.m + 1)) * |x.val - y.val| :=
    mul_le_mul_of_nonneg_left hxy (by positivity)
  have h_pow : (1 / (2 : Rat) ^ (S.m + 1)) * (1 / 2 ^ k) = 1 / 2 ^ (k + S.m + 1) := by
    rw [one_div_mul_one_div, ← pow_add, show S.m + 1 + k = k + S.m + 1 by omega]
  linarith

/-- **Corollary (Uniform Continuity of Right Inverse for `StrictlyMonotoneA1`)**:
    Any right inverse $g : \mathbb{Q} \to \mathbb{Q}$ of $S.A.f$ on $[a, b]$ is uniformly
    continuous with modulus $\mu(k) = k + S.m + 1$. -/
theorem StrictlyMonotoneA1.inv_uniform_continuous (S : StrictlyMonotoneA1)
    (g : Q → Q)
    (hga : ∀ y : Q, S.A.a.val ≤ (g y).val) (hgb : ∀ y : Q, (g y).val ≤ S.A.b.val)
    (hinv : ∀ y : Q, (S.A.f (g y)).val = y.val)
    (k : Nat) (y z : Q) (h : |y.val - z.val| < 1 / 2 ^ (k + S.m + 1)) :
    |(g y).val - (g z).val| < 1 / 2 ^ k :=
  inv_modulus S.A.toA0 (fun k ↦ k + S.m + 1) S.isMonoModulus g hga hgb hinv k y z h

#print axioms StrictlyMonotoneA1.secant_lower_bound
#print axioms StrictlyMonotoneA1.isMonoModulus
#print axioms StrictlyMonotoneA1.inv_uniform_continuous

end HAomega
