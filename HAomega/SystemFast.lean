/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SystemEval

/-!
# A coefficient table for polynomial systems

`solN sys v n` runs `n + 1` Picard iterations and evaluates them lazily, so for
a nonlinear system the cost of coefficient `n` is exponential in `n`
(`SystemEval.lean`). The solution's coefficients satisfy the recurrence

    Y_v(0) = A_v(0),     Y_v(n+1) = F_v(Y)(n) / (n+1)

(`sbd_solN_succ_val`), and `F_v(Y)(n)` reads `Y` only up to degree `n`. So the
rows can be computed once each, in order, reading earlier rows from a table:
`solRows`. `solFast_val` proves the table equal in value to `solN`, and the
evaluator built on it (`GPACSys.approxFast`) carries the same certificate.
-/

namespace HAomega

/-- A table of rows (row `j` = the degree-`j` coefficients of every variable),
read as a state; missing entries read as `0`. -/
def tableW (rows : List (List Q)) : Nat → Nat → Q :=
  fun u j ↦ (rows.getD j []).getD u Q.zero

/-- Rows `0, …, n` of the solution table. -/
def solRows (sys : List (Tm [] JetTy × JExprN)) : Nat → List (List Q)
  | 0 => [sys.map fun p ↦ (p.1.eval Env.nil) 0]
  | n + 1 =>
    let rows := solRows sys n
    rows ++ [sys.map fun p ↦ Q.div (sbdEvalExpr p.2 (tableW rows) n) (Q.ofNat (n + 1))]

/-- Coefficient `n` of variable `v`, from the table. -/
def solFast (sys : List (Tm [] JetTy × JExprN)) (v n : Nat) : Q :=
  tableW (solRows sys n) v n

/-- `getD` on the left half of an append. -/
theorem sfst_getD_append_left {α : Type} (xs ys : List α) (d : α) (j : Nat) (hj : j < xs.length) :
    (xs ++ ys).getD j d = xs.getD j d := by
  have hj' : j < (xs ++ ys).length := by simp; omega
  rw [uDeriv_getD_eq_getElem (xs ++ ys) d j hj',
      uDeriv_getD_eq_getElem xs d j hj,
      List.getElem_append_left hj]

/-- `getD` at the newly appended element `xs ++ [y]`. -/
theorem sfst_getD_append_singleton {α : Type} (xs : List α) (y d : α) :
    (xs ++ [y]).getD xs.length d = y := by
  have hlt : xs.length < (xs ++ [y]).length := by simp
  rw [uDeriv_getD_eq_getElem (xs ++ [y]) d xs.length hlt,
      List.getElem_append_right (Nat.le_refl _)]
  simp

/-- `solRows sys n` has `n + 1` rows. -/
theorem sfst_solRows_length (sys : List (Tm [] JetTy × JExprN)) :
    ∀ n : Nat, (solRows sys n).length = n + 1
  | 0 => rfl
  | n + 1 => by
    simp [solRows, sfst_solRows_length sys n]

/-- Earlier rows of `solRows` are preserved when new rows are appended. -/
theorem sfst_solRows_getD_eq (sys : List (Tm [] JetTy × JExprN)) (j : Nat) :
    ∀ n : Nat, j ≤ n → (solRows sys n).getD j [] = (solRows sys j).getD j []
  | 0, hj => by
    have hj0 : j = 0 := by omega
    subst hj0
    rfl
  | n + 1, hj => by
    rcases Nat.of_le_succ hj with hle | rfl
    · dsimp only [solRows]
      have hlt : j < (solRows sys n).length := by
        rw [sfst_solRows_length]
        omega
      rw [sfst_getD_append_left _ _ [] j hlt]
      exact sfst_solRows_getD_eq sys j n hle
    · rfl

/-- For `j ≤ n`, `tableW (solRows sys n) v j` equals `solFast sys v j`. -/
theorem sfst_tableW_eq_solFast (sys : List (Tm [] JetTy × JExprN)) (v n j : Nat) (hj : j ≤ n) :
    tableW (solRows sys n) v j = solFast sys v j := by
  unfold solFast tableW
  rw [sfst_solRows_getD_eq sys j n hj]

/-- Row `0` of `solFast` is the initial coefficient `A_v(0)`. -/
theorem sfst_solFast_zero (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length) :
    solFast sys v 0 = (sys[v].1.eval Env.nil) 0 := by
  unfold solFast tableW solRows
  change (sys.map fun p ↦ (p.1.eval Env.nil) 0).getD v Q.zero = (sys[v].1.eval Env.nil) 0
  have hv' : v < (sys.map fun p ↦ (p.1.eval Env.nil) 0).length := by simp [hv]
  rw [uDeriv_getD_eq_getElem _ Q.zero v hv', List.getElem_map]

/-- Row `n + 1` of `solFast` is computed from `solRows sys n` by `F_v(W)(n) / (n + 1)`. -/
theorem sfst_solFast_succ (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (hv : v < sys.length)
    (n : Nat) :
    solFast sys v (n + 1) =
      Q.div (sbdEvalExpr sys[v].2 (tableW (solRows sys n)) n) (Q.ofNat (n + 1)) := by
  change ((solRows sys (n + 1)).getD (n + 1) []).getD v Q.zero = _
  have hrow := sfst_getD_append_singleton (solRows sys n)
    (sys.map fun p ↦ Q.div (sbdEvalExpr p.2 (tableW (solRows sys n)) n) (Q.ofNat (n + 1))) []
  rw [sfst_solRows_length sys n] at hrow
  dsimp only [solRows]
  rw [hrow]
  have hv' : v < (sys.map fun p ↦
      Q.div (sbdEvalExpr p.2 (tableW (solRows sys n)) n) (Q.ofNat (n + 1))).length := by
    simp [hv]
  rw [uDeriv_getD_eq_getElem _ Q.zero v hv', List.getElem_map]

/-- `sbdEvalExpr F W n` depends as a value only on `W u j` for `u < sysLen` and `j ≤ n`. -/
theorem sfst_sbdEvalExpr_congr (F : JExprN) (sysLen : Nat) (hF : F.WF sysLen)
    (W₁ W₂ : Nat → Nat → Q) (n : Nat)
    (hw : ∀ u < sysLen, ∀ j ≤ n, (W₁ u j).val = (W₂ u j).val) :
    (sbdEvalExpr F W₁ n).val = (sbdEvalExpr F W₂ n).val := by
  unfold sbdEvalExpr
  exact F.toTm_agreeV sysLen hF
    (Env.cons (σ := WTy) W₁ Env.nil) (Env.cons (σ := WTy) W₂ Env.nil)
    (.var .here) (.var .here) (n + 1)
    (fun u hu j hj ↦ hw u hu j (Nat.lt_succ_iff.mp hj))
    n (Nat.lt_succ_self n)

/-- **The table computes the solution.** -/
theorem solFast_val (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (v : Nat) (hv : v < sys.length) (n : Nat) :
    (solFast sys v n).val = (solN sys v n).val := by
  induction n using Nat.strongRecOn generalizing v with
  | ind m ih =>
    cases m with
    | zero =>
      rw [sfst_solFast_zero sys v hv, uMul_solN_zero_val sys (gpac_wf h) v hv]
    | succ k =>
      have hpv := h sys[v] (List.getElem_mem hv)
      have hne : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
      rw [sfst_solFast_succ sys v hv k, Q.val_div _ _ hne, Q.val_ofNat,
          sbd_solN_succ_val sys h v hv k]
      congr 1
      refine sfst_sbdEvalExpr_congr sys[v].2 sys.length hpv.1 (tableW (solRows sys k)) (solN sys) k ?_
      intro u hu j hj
      rw [sfst_tableW_eq_solFast sys u k j hj]
      exact ih j (Nat.lt_succ_of_le hj) u hu

/-- The certified approximation from the table. -/
def GPACSys.approxFast (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (x : Q) (k : Nat) : Q :=
  Jet.evalPoly ⟨solFast sys v⟩
    (extractedJetCauchyModulusComputed (solFast sys v) (sysParams sys).1 x k) x

/-- **Its certificate**, the same as `GPACSys.approx_spec`. -/
theorem GPACSys.approxFast_spec (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (v : Nat) (hv : v < sys.length) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams sys).2 + 1)) (k d : Nat) :
    |(Jet.evalPoly ⟨solFast sys v⟩
        (extractedJetCauchyModulusComputed (solFast sys v) (sysParams sys).1 x k + d) x).val
      - (GPACSys.approxFast sys v x k).val| < 1 / (2 : Rat) ^ k := by
  let F := (GPACSys.radiusJet sys h v hv).ofVal (solFast sys v) (solFast_val sys h v hv)
  have := F.cauchyComputed_correct x hx k 0 d
  dsimp only [F, RadiusJet.ofVal, GPACSys.radiusJet] at this
  rw [Nat.add_zero] at this
  rw [abs_sub_comm]
  exact this

/-! ## Examples

The table agrees with `solN` where `solN` still runs, and `tan` (Riccati
system `sysTan`) now evaluates at `k = 20`: modulus `N = 24`. -/

#guard (List.range 8).all fun n ↦
  Q.norm (solFast sysTan 0 n) == Q.norm (solN sysTan 0 n)
#guard (List.range 12).all fun n ↦
  Q.norm (solFast memSinCosSys 0 n) == Q.norm (solN memSinCosSys 0 n)
#guard extractedJetCauchyModulusComputed (solFast sysTan 0) (sysParams sysTan).1 ⟨1, 1023⟩ 20 = 24
#guard (let r := GPACSys.approxFast sysTan 0 ⟨1, 1023⟩ 20
        (Float.ofInt r.num / Float.ofNat r.den - Float.tan (1 / 1024)).abs < 1e-9)

#print axioms solFast
#print axioms GPACSys.approxFast
#print axioms solFast_val
#print axioms GPACSys.approxFast_spec

end HAomega
