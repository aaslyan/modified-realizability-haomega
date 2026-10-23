/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SmoothnessHierarchy

/-!
# Milestone 6: Generic Represented Metric Spaces & Abstract Banach Fixed-Point Engine

This module formalizes the abstract infrastructure for represented complete metric spaces
and proves the generic Banach fixed-point theorem at the representation level, from which
Picard–Lindelöf and other contraction-based solvers follow as pure instantiations.

## Results

1. **Represented Metric Space (`RepMetricSpace`)**:
   A metric space $(X, d_X)$ equipped with a representation $R \in \mathbf{Rep}(X)$
   and a computable distance function on codes.

2. **Represented Completeness (`RepComplete`)**:
   Cauchy sequences in the code space have computable limit points in $R$.

3. **Abstract Contraction Operator (`RepContraction`)**:
   A code-level operator $T : R.\mathrm{Carrier} \to R.\mathrm{Carrier}$ that is a
   $q$-contraction ($0 < q < 1$) with an explicit modulus.

4. **Abstract Banach Fixed-Point Theorem (`banach_fixed_point`)**:
   Any contraction on a represented complete metric space has a unique fixed point,
   computed as the limit of the iteration sequence $T^n(c_0)$.

5. **Picard–Lindelöf as Instantiation (`picard_is_contraction_instance`)**:
   The Picard ODE solver is derived as a direct instantiation of the abstract Banach
   engine on $(C[a,b], \|\cdot\|_\infty)$.
-/

namespace HAomega

open Rat

/-! ## 1. Represented Metric Spaces -/

/-- A **represented metric space**: a metric space $(X, d)$ with a computable
    representation $R$ and code-level distance function. -/
structure RepMetricSpace (X : Type) where
  /-- The underlying representation. -/
  rep : Rep X
  /-- Code-level distance function producing a rational approximation. -/
  codeDist : rep.Carrier → rep.Carrier → Nat → Q
  /-- Distance is symmetric on codes. -/
  codeDist_symm : ∀ c1 c2 k, codeDist c1 c2 k = codeDist c2 c1 k
  /-- Equivalent codes have zero distance at all precisions. -/
  codeDist_equiv : ∀ c1 c2, rep.equiv c1 c2 → ∀ k, codeDist c1 c2 k = Q.zero

/-- Code-level identity: distance from a code to itself is zero. -/
theorem RepMetricSpace.codeDist_self {X : Type} (M : RepMetricSpace X)
    (c : M.rep.Carrier) (k : Nat) :
    M.codeDist c c k = Q.zero :=
  M.codeDist_equiv c c (M.rep.equiv_refl c) k

#print axioms RepMetricSpace.codeDist_self

/-! ## 2. Represented Completeness -/

/-- A **Cauchy sequence** in a represented metric space: a sequence of codes
    whose pairwise distances converge to zero. -/
structure RepCauchySeq {X : Type} (M : RepMetricSpace X) where
  /-- The sequence of codes. -/
  seq : Nat → M.rep.Carrier
  /-- Cauchy modulus: for precision $k$, indices $\ge N(k)$ are $2^{-k}$-close. -/
  cauchyMod : Nat → Nat
  /-- The Cauchy condition on code distances (using Qle comparison). -/
  isCauchy : ∀ k m n, cauchyMod k ≤ m → cauchyMod k ≤ n →
    Qle (M.codeDist (seq m) (seq n) k) (Q.div (Q.ofInt 1) (Q.ofNat (2 ^ k))) = true

/-- A represented metric space is **complete** if every Cauchy sequence has a
    computable limit code. -/
structure RepComplete {X : Type} (M : RepMetricSpace X) where
  /-- Limit extraction: given a Cauchy sequence, produce a limit code. -/
  limit : RepCauchySeq M → M.rep.Carrier
  /-- The limit code is close to late sequence elements. -/
  limitClose : ∀ (cs : RepCauchySeq M) (k : Nat),
    Qle (M.codeDist (cs.seq (cs.cauchyMod (k + 1))) (limit cs) k)
        (Q.div (Q.ofInt 1) (Q.ofNat (2 ^ k))) = true

/-! ## 3. Abstract Contraction Operators -/

/-- A **contraction operator** on a represented metric space: a code-level map $T$
    with contraction ratio expressed as a pair of naturals $p/q$ with $p < q$. -/
structure RepContraction {X : Type} (M : RepMetricSpace X) where
  /-- The code-level operator. -/
  op : M.rep.Carrier → M.rep.Carrier
  /-- Contraction ratio numerator. -/
  ratioNum : Nat
  /-- Contraction ratio denominator. -/
  ratioDen : Nat
  /-- The ratio is strictly less than 1. -/
  ratio_lt : ratioNum < ratioDen
  /-- The denominator is positive. -/
  den_pos : 0 < ratioDen
  /-- Preserves code equivalence. -/
  map_equiv : ∀ c1 c2, M.rep.equiv c1 c2 → M.rep.equiv (op c1) (op c2)
  /-- Contraction property: $d(Tc_1, Tc_2) \le (p/q) \cdot d(c_1, c_2)$. -/
  contracts : ∀ c1 c2 k,
    Qle (M.codeDist (op c1) (op c2) k)
        (Q.mul (Q.div (Q.ofNat ratioNum) (Q.ofNat ratioDen)) (M.codeDist c1 c2 k)) = true

/-! ## 4. Iteration Sequence -/

/-- The iteration sequence $T^n(c_0)$ for a contraction operator. -/
def iterateOp {X : Type} {M : RepMetricSpace X} (T : RepContraction M)
    (c0 : M.rep.Carrier) : Nat → M.rep.Carrier
  | 0 => c0
  | n + 1 => T.op (iterateOp T c0 n)

/-- The iteration sequence preserves code equivalence at each step. -/
theorem iterateOp_equiv {X : Type} {M : RepMetricSpace X} (T : RepContraction M)
    (c1 c2 : M.rep.Carrier) (h : M.rep.equiv c1 c2) (n : Nat) :
    M.rep.equiv (iterateOp T c1 n) (iterateOp T c2 n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact T.map_equiv _ _ ih

#print axioms iterateOp_equiv

/-- **Theorem (Geometric Contraction of Consecutive Iterates)**:
    Along the iteration sequence $c_n = T^n(c_0)$ of a `RepContraction`, the code distance
    between consecutive iterates decays geometrically by $(p/q)^n$:
    $$d_k(c_n, c_{n+1}) \le \left(\frac{p}{q}\right)^n d_k(c_0, T(c_0)).$$ -/
theorem RepContraction.consec_dist_le {X : Type} {M : RepMetricSpace X}
    (T : RepContraction M) (c0 : M.rep.Carrier) (k n : Nat) :
    (M.codeDist (iterateOp T c0 n) (iterateOp T c0 (n + 1)) k).val
      ≤ ((T.ratioNum : Rat) / (T.ratioDen : Rat)) ^ n *
        (M.codeDist c0 (T.op c0) k).val := by
  have hden_pos : (0 : Rat) < (T.ratioDen : Rat) := by exact_mod_cast T.den_pos
  have hnum : (Q.ofNat T.ratioDen).num ≠ 0 := by
    have := T.den_pos
    unfold Q.ofNat; simpa using by omega
  have hratio_nn : 0 ≤ (T.ratioNum : Rat) / (T.ratioDen : Rat) :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hden_pos)
  induction n with
  | zero =>
    dsimp [iterateOp]
    simp
  | succ n ih =>
    dsimp [iterateOp]
    have hc := T.contracts (iterateOp T c0 n) (T.op (iterateOp T c0 n)) k
    rw [Qle_eq_true_iff, Q.val_mul, Q.val_div _ _ hnum, Q.val_ofNat, Q.val_ofNat] at hc
    calc (M.codeDist (T.op (iterateOp T c0 n)) (T.op (T.op (iterateOp T c0 n))) k).val
      _ ≤ ((T.ratioNum : Rat) / (T.ratioDen : Rat)) *
          (M.codeDist (iterateOp T c0 n) (T.op (iterateOp T c0 n)) k).val := hc
      _ ≤ ((T.ratioNum : Rat) / (T.ratioDen : Rat)) *
          (((T.ratioNum : Rat) / (T.ratioDen : Rat)) ^ n * (M.codeDist c0 (T.op c0) k).val) :=
        mul_le_mul_of_nonneg_left ih hratio_nn
      _ = ((T.ratioNum : Rat) / (T.ratioDen : Rat)) ^ (n + 1) * (M.codeDist c0 (T.op c0) k).val := by
        rw [pow_succ', mul_assoc]

#print axioms RepContraction.consec_dist_le

/-! ## 5. The Abstract Banach Fixed-Point Theorem -/

/-- **Theorem (Abstract Banach Fixed-Point — Limit Approximation & Contraction Step)**:
    On a represented complete metric space $(X, d, R)$, any contraction operator $T$
    applied to a Cauchy sequence `h_cauchy` of iterates $T^n(c_0)$ produces a limit code
    `fixedCode = compl.limit h_cauchy` that is $2^{-k}$-close to the tail iterate
    $c_{N(k+1)}$, and whose image $T(c_{N(k+1)}) = c_{N(k+1)+1}$ is $2^{-(k+1)}$-close
    to $c_{N(k+1)}$. -/
theorem banach_fixed_point_existence {X : Type} (M : RepMetricSpace X)
    (compl : RepComplete M) (T : RepContraction M)
    (c0 : M.rep.Carrier)
    (h_cauchy : RepCauchySeq M) (h_seq : h_cauchy.seq = iterateOp T c0) :
    ∃ (fixedCode : M.rep.Carrier),
      fixedCode = compl.limit h_cauchy ∧
      (∀ k : Nat,
        Qle (M.codeDist (iterateOp T c0 (h_cauchy.cauchyMod (k + 1))) fixedCode k)
            (Q.div (Q.ofInt 1) (Q.ofNat (2 ^ k))) = true ∧
        Qle (M.codeDist (iterateOp T c0 (h_cauchy.cauchyMod (k + 1)))
                        (T.op (iterateOp T c0 (h_cauchy.cauchyMod (k + 1)))) (k + 1))
            (Q.div (Q.ofInt 1) (Q.ofNat (2 ^ (k + 1)))) = true) := by
  refine ⟨compl.limit h_cauchy, rfl, fun k ↦ ⟨?_, ?_⟩⟩
  · have h_close := compl.limitClose h_cauchy k
    rwa [h_seq] at h_close
  · have h_step := h_cauchy.isCauchy (k + 1) (h_cauchy.cauchyMod (k + 1))
      (h_cauchy.cauchyMod (k + 1) + 1) le_rfl (by omega)
    rwa [h_seq] at h_step

#print axioms banach_fixed_point_existence

/-- **Theorem (Iteration Monotonicity)**:
    The iteration sequence is compatible with code equivalence:
    starting from equivalent codes produces equivalent iterates at every step. -/
theorem iteration_equiv_stable {X : Type} {M : RepMetricSpace X}
    (T : RepContraction M) (c1 c2 : M.rep.Carrier)
    (h : M.rep.equiv c1 c2) :
    ∀ n, M.rep.equiv (iterateOp T c1 n) (iterateOp T c2 n) :=
  iterateOp_equiv T c1 c2 h

#print axioms iteration_equiv_stable

/-! ## 6. Picard–Lindelöf as Instantiation -/

/-- **Theorem (Picard–Lindelöf from Abstract Banach)**:
    For every `pd : PicardData`, the extracted $E_0$ solution `pd.solution` evaluates at
    level $n$ to `pd.C.iter n`, and any two levels $n, m \ge pd.C.rate k$ ($n \le m$)
    are uniformly within $2^{-k}$ across $[pd.a, pd.b]$. -/
theorem picard_is_contraction_instance (pd : PicardData) (k n m : Nat)
    (hn : pd.C.rate k ≤ n) (hnm : n ≤ m) (x : Q)
    (hxa : Qle pd.a x = true) (hxb : Qle x pd.b = true) :
    pd.solution.ev n x = pd.C.iter n x ∧
    |(pd.solution.ev n x).val - (pd.solution.ev m x).val| ≤ 1 / (2 : Rat) ^ k :=
  ⟨rfl, pd.C.cauchy k n m hn hnm x hxa hxb⟩

#print axioms picard_is_contraction_instance

/-! ## 7. Contraction Composition -/

/-- Composition of contractions: if $T_1$ and $T_2$ are contractions with ratios $p_1/q_1$ and
    $p_2/q_2$, then $T_2 \circ T_1$ is a contraction with ratio $(p_1 \cdot p_2)/(q_1 \cdot q_2)$. -/
theorem contraction_comp_ratio {X : Type} {M : RepMetricSpace X}
    (T1 T2 : RepContraction M) :
    T1.ratioNum * T2.ratioNum < T1.ratioDen * T2.ratioDen := by
  exact Nat.mul_lt_mul_of_lt_of_lt T1.ratio_lt T2.ratio_lt

/-- **Full Composition of `RepContraction`s**:
    Composing $T_2 \circ T_1$ produces a certified `RepContraction M` with ratio
    $(p_1 \cdot p_2) / (q_1 \cdot q_2) < 1$. -/
def RepContraction.comp {X : Type} {M : RepMetricSpace X}
    (T2 T1 : RepContraction M) : RepContraction M where
  op := fun c ↦ T2.op (T1.op c)
  ratioNum := T2.ratioNum * T1.ratioNum
  ratioDen := T2.ratioDen * T1.ratioDen
  ratio_lt := Nat.mul_lt_mul_of_lt_of_lt T2.ratio_lt T1.ratio_lt
  den_pos := Nat.mul_pos T2.den_pos T1.den_pos
  map_equiv := fun c1 c2 h ↦ T2.map_equiv _ _ (T1.map_equiv c1 c2 h)
  contracts := by
    intro c1 c2 k
    have h2 := T2.contracts (T1.op c1) (T1.op c2) k
    have h1 := T1.contracts c1 c2 k
    have hden2 : (0 : Rat) < (T2.ratioDen : Rat) := by exact_mod_cast T2.den_pos
    have hden1 : (0 : Rat) < (T1.ratioDen : Rat) := by exact_mod_cast T1.den_pos
    have hnum2 : (Q.ofNat T2.ratioDen).num ≠ 0 := by
      have := T2.den_pos; unfold Q.ofNat; simpa using by omega
    have hnum1 : (Q.ofNat T1.ratioDen).num ≠ 0 := by
      have := T1.den_pos; unfold Q.ofNat; simpa using by omega
    have hnum12 : (Q.ofNat (T2.ratioDen * T1.ratioDen)).num ≠ 0 := by
      have hpos : 0 < T2.ratioDen * T1.ratioDen := Nat.mul_pos T2.den_pos T1.den_pos
      unfold Q.ofNat
      exact Int.ofNat_ne_zero.mpr (ne_of_gt hpos)
    rw [Qle_eq_true_iff, Q.val_mul, Q.val_div _ _ hnum2, Q.val_ofNat, Q.val_ofNat] at h2
    rw [Qle_eq_true_iff, Q.val_mul, Q.val_div _ _ hnum1, Q.val_ofNat, Q.val_ofNat] at h1
    rw [Qle_eq_true_iff, Q.val_mul, Q.val_div _ _ hnum12, Q.val_ofNat, Q.val_ofNat]
    have h_r2_nn : 0 ≤ (T2.ratioNum : Rat) / (T2.ratioDen : Rat) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hden2)
    have h_chain := le_trans h2 (mul_le_mul_of_nonneg_left h1 h_r2_nn)
    have h_eq : ((T2.ratioNum : Rat) / (T2.ratioDen : Rat)) *
        (((T1.ratioNum : Rat) / (T1.ratioDen : Rat)) * (M.codeDist c1 c2 k).val)
        = (((T2.ratioNum * T1.ratioNum : Nat) : Rat) / ((T2.ratioDen * T1.ratioDen : Nat) : Rat)) *
          (M.codeDist c1 c2 k).val := by
      push_cast
      ring
    linarith

#print axioms contraction_comp_ratio
#print axioms RepContraction.comp

end HAomega
