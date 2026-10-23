/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PolyODESolve

/-!
# The scalar Picard solvers are instances of the general solver

`genSolveD A F` (`PolyODESolve.lean`) gives a proof-computed solver for every
`y = A + ∫F(y)`. This module shows that its extract coincides, coefficient by
coefficient and as values of the hand-rolled `Q` (not merely numerically), with
the three earlier scalar solvers:

* `y' = y`, `y(0) = 1`:   `A = 1`, `F = Y`       ↦ `extractedPicardJet`
* `y' = y²`, `y(0) = 1`:  `A = 1`, `F = Y·Y`     ↦ `extractedQuadBlowupJet`
* `y' = 1 + y²`, `y(0) = 0`: `A = 0`, `F = 1 + Y·Y` ↦ `extractedRiccatiJet`

The Duffing system is not an instance: `JExpr` has one jet variable.
-/

namespace HAomega

/-- Adding `Q.ofNat 0` on the left to a `Q` with coprime numerator and denominator is the identity. -/
theorem Q.zero_add_of_coprime (q : Q) (hq : Nat.gcd q.num.natAbs q.den = 1) :
    Q.add (Q.ofNat 0) q = q := by
  have hnum : Int.add (Int.mul (Q.ofNat 0).num (Int.ofNat q.den))
      (Int.mul q.num (Int.ofNat (Q.ofNat 0).den)) = q.num := by
    show 0 * (q.den : Int) + q.num * 1 = q.num
    omega
  have hden : (Q.ofNat 0).den * q.den = q.den := Nat.one_mul q.den
  unfold Q.add
  rw [hnum, hden]
  unfold Q.of
  rw [if_neg q.den_ne_zero, hq, if_neg Nat.one_ne_zero, Nat.div_one]
  change ⟨Int.tdiv q.num 1, q.denPred⟩ = q
  rw [Int.tdiv_one]

/-- Every `Q.of n d` has coprime numerator and denominator. -/
theorem Q.of_coprime (n : Int) (d : Nat) :
    Nat.gcd (Q.of n d).num.natAbs (Q.of n d).den = 1 := by
  by_cases hd : d = 0
  · subst hd
    exact Nat.gcd_zero_left 1
  · have hg : Nat.gcd n.natAbs d ≠ 0 := Nat.gcd_ne_zero_right hd
    have hg_pos : 0 < Nat.gcd n.natAbs d := Nat.pos_of_ne_zero hg
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    have hdiv_pos : 0 < d / Nat.gcd n.natAbs d :=
      Nat.div_pos (Nat.le_of_dvd hd_pos (Nat.gcd_dvd_right n.natAbs d)) hg_pos
    unfold Q.of
    rw [if_neg hd, if_neg hg]
    dsimp [Q.den]
    rw [Int.natAbs_tdiv, Nat.sub_add_cancel hdiv_pos]
    exact Nat.coprime_div_gcd_div_gcd hg_pos

/-- Dividing `a` by `Q.ofNat (m + 1)` produces a normalized `Q` unchanged by `Q.add (Q.ofNat 0)`. -/
theorem Q.zero_add_div_ofNat_succ (a : Q) (m : Nat) :
    Q.add (Q.ofNat 0) (Q.div a (Q.ofNat (m + 1))) = Q.div a (Q.ofNat (m + 1)) := by
  have hne : (Q.ofNat (m + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero m)
  have hnn : ¬ ((Q.ofNat (m + 1)).num < 0) := Int.not_lt.mpr (Int.natCast_nonneg (m + 1))
  have hdiv : Q.div a (Q.ofNat (m + 1)) =
      Q.of (Int.mul a.num (Int.ofNat (Q.ofNat (m + 1)).den))
           (a.den * (Q.ofNat (m + 1)).num.natAbs) := by
    unfold Q.div
    rw [if_neg hne, if_neg hnn]
  rw [hdiv]
  exact Q.zero_add_of_coprime _ (Q.of_coprime _ _)

/-- Adding `Q.ofNat 0` on the right of `Q.ofNat 1` yields `Q.ofNat 1`. -/
theorem Q.one_add_zero : Q.add (Q.ofNat 1) (Q.ofNat 0) = Q.ofNat 1 := by
  change Q.of 1 1 = Q.ofNat 1
  unfold Q.of
  rw [if_neg Nat.one_ne_zero]
  change (let g := Nat.gcd 1 1; if g = 0 then Q.zero else ⟨Int.tdiv 1 (Int.ofNat g), 1 / g - 1⟩) = Q.ofNat 1
  rw [Nat.gcd_self 1, if_neg Nat.one_ne_zero]
  rfl

/-- The general step for `A = 1, F = Y` evaluates to the same function as `tmPicardExpStep`. -/
theorem genStep_exp_eval :
    (genStep tmConstOneJet .var (Γ := [])).eval Env.nil =
      (tmPicardExpStep (Γ := [])).eval Env.nil := by
  funext Y n
  cases n with
  | zero => exact Q.one_add_zero
  | succ m => exact Q.zero_add_div_ofNat_succ (Y m) m

/-- The general step for `A = 0, F = 1 + Y·Y` evaluates to the same function as `tmRiccatiStep`. -/
theorem genStep_riccati_eval :
    (genStep tmZeroJet (.add (.const tmConstOneJet) (.mul .var .var)) (Γ := [])).eval Env.nil =
      (tmRiccatiStep (Γ := [])).eval Env.nil := by
  funext Y n
  cases n with
  | zero => exact Q.zero_add_of_coprime (Q.ofNat 0) (Nat.gcd_zero_left 1)
  | succ m => exact Q.zero_add_div_ofNat_succ _ m

/-- Iterating `step.eval Env.nil` from `y0.eval Env.nil` equals `extractClosed (iterSequenceD JetTy y0 step)`. -/
theorem iterate_eval_eq_iterSequenceD (y0 : Tm [] JetTy) (step : Tm [] (.arrow JetTy JetTy)) (k : Nat) :
    ((step.eval Env.nil)^[k] (y0.eval Env.nil)) =
      (((extractClosed (iterSequenceD JetTy y0 step)).eval Env.nil) k).1 := by
  induction k with
  | zero =>
    exact (extractClosed_iterSequenceD_zero JetTy y0 step).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih,
      extractClosed_iterSequenceD_succ JetTy y0 step m]

theorem genSolve_exp_eq (k : Nat) :
    (((extractClosed (genSolveD tmConstOneJet .var)).eval Env.nil) k).1 =
      extractedPicardJet k := by
  rw [extractClosed_genSolveD_fst, genStep_exp_eval]
  exact iterate_eval_eq_iterSequenceD tmConstOneJet tmPicardExpStep k

theorem genSolve_quadBlowup_eq (k : Nat) :
    (((extractClosed (genSolveD tmConstOneJet (.mul .var .var))).eval Env.nil) k).1 =
      extractedQuadBlowupJet k := by
  rw [extractClosed_genSolveD_fst]
  exact iterate_eval_eq_iterSequenceD tmConstOneJet tmQuadBlowupStep k

theorem genSolve_riccati_eq (k : Nat) :
    (((extractClosed (genSolveD tmZeroJet (.add (.const tmConstOneJet) (.mul .var .var)))).eval
      Env.nil) k).1 = extractedRiccatiJet k := by
  rw [extractClosed_genSolveD_fst, genStep_riccati_eval]
  exact iterate_eval_eq_iterSequenceD tmZeroJet tmRiccatiStep k

#print axioms genSolve_exp_eq
#print axioms genSolve_quadBlowup_eq
#print axioms genSolve_riccati_eq

end HAomega
