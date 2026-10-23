/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.TrigPoly

/-!
# Fourier modes from proofs

The modes `sin(mx)`, `cos(mx)` solve `u' = m·v, v' = −m·u`, `(u, v)(0) = (0, 1)`.
That is an instance of the general two-variable solver `genSolve2D`
(`PolyODESystem.lean`) with the constant jet `m`, so every Fourier mode has a
proof-computed Taylor solver. `genSolve2_mode_val`: below degree `k` the `k`-th
iterate has the Taylor coefficients of `sin(mx)` and `cos(mx)` (as values).

`genSolve2_mode_trig` closes the loop with the Fourier layer (`TrigPoly.lean`):
for frequencies `m + 1 ≥ 1`, the proof-computed solver agrees with the Taylor
jet `TrigPoly.toJet` of the Fourier modes `sinMode`, `cosMode`.
-/

namespace HAomega

/-- The numeral `n` as a term. -/
def natTm {Γ : List Ty} : Nat → Tm Γ .nat
  | 0 => .zero
  | n + 1 => .succ (natTm n)

/-- The constant jet `m`: coefficient `m` at degree `0`, else `0`. -/
def tmConstNatJet (m : Nat) : Tm [] JetTy :=
  .lam (.recNat (.qnat (natTm m)) (.lam (.lam (.qnat .zero))) (.var .here))

/-- The mode system `u' = m·v, v' = −m·u`, `(u, v)(0) = (0, 1)`. -/
def modeSolveD (m : Nat) :=
  genSolve2D tmZeroJet tmConstOneJet (.mul (.const (tmConstNatJet m)) .varV)
    (.sub (.const tmZeroJet) (.mul (.const (tmConstNatJet m)) .varU))

/-- Evaluating `natTm m` in any environment yields `m`. -/
theorem natTm_eval {Γ : List Ty} (e : Env Γ) : ∀ m : Nat, (natTm m).eval e = m
  | 0 => rfl
  | m + 1 => congrArg Nat.succ (natTm_eval e m)

/-- Partial Cauchy convolution of `tmConstNatJet m` with `c` at degree `j` and length `t + 1` has value `m * (c j).val`. -/
theorem cauchyConvAux_constNatJet_val (m : Nat) (c : Nat → Q) (j : Nat) : ∀ t : Nat,
    (Jet.cauchyConvAux ⟨(tmConstNatJet m).eval Env.nil⟩ ⟨c⟩ j (t + 1)).val =
      (m : Rat) * (c j).val
  | 0 => by
    change (Q.add Q.zero (Q.mul (Q.ofNat ((natTm m).eval (.cons 0 Env.nil))) (c j))).val =
      (m : Rat) * (c j).val
    rw [natTm_eval, Q.val_add, Q.val_zero, Q.val_mul, Q.val_ofNat, zero_add]
  | t + 1 => by
    change (Q.add (Jet.cauchyConvAux ⟨(tmConstNatJet m).eval Env.nil⟩ ⟨c⟩ j (t + 1))
      (Q.mul (Q.ofNat 0) (c (j - (t + 1))))).val = (m : Rat) * (c j).val
    rw [Q.val_add, cauchyConvAux_constNatJet_val m c j t, Q.val_mul, Q.val_ofNat]
    ring

/-- Multiplying `tmConstNatJet m` by `c` via `tmJetMul` at index `j` has rational value `m * (c j).val`. -/
theorem tmJetMul_constNatJet_val {Γ : List Ty} (e : Env Γ) (m : Nat) (c : Nat → Q) (j : Nat) :
    (((tmJetMul (Γ := Γ)).eval e) ((tmConstNatJet m).eval Env.nil) c j).val =
      (m : Rat) * (c j).val := by
  rw [tmJetMul_eval]
  exact cauchyConvAux_constNatJet_val m c j j

/-- Below degree `k`, the `k`-th iterate of the mode Picard operator has the rational values of `Jet.sinFreq m` and `Jet.cosFreq m`. -/
theorem mode_iterate_val (m : Nat) : ∀ (k i : Nat), i < k →
    let W := ((genStep2 tmZeroJet tmConstOneJet
      (.mul (.const (tmConstNatJet m)) .varV)
      (.sub (.const tmZeroJet) (.mul (.const (tmConstNatJet m)) .varU)) (Γ := [])).eval Env.nil)^[k]
        ((tmZeroJet (Γ := [])).eval Env.nil, (tmConstOneJet (Γ := [])).eval Env.nil)
    (W.1 i).val = ((Jet.sinFreq m).coeff i).val ∧
    (W.2 i).val = ((Jet.cosFreq m).coeff i).val
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, 0, _ => by
    dsimp only
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_⟩
    · change (Q.add (Q.ofNat 0) (Q.ofNat 0)).val = Q.zero.val
      rw [Q.zero_add_of_coprime (Q.ofNat 0) (Nat.gcd_zero_left 1)]
      rfl
    · change (Q.add (Q.ofNat 1) (Q.ofNat 0)).val = (Q.ofNat 1).val
      rw [Q.one_add_zero]
  | k + 1, j + 1, hi => by
    have hj : j < k := Nat.lt_of_succ_lt_succ hi
    have ih := mode_iterate_val m k j hj
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    set Wk := ((genStep2 tmZeroJet tmConstOneJet
      (.mul (.const (tmConstNatJet m)) .varV)
      (.sub (.const tmZeroJet) (.mul (.const (tmConstNatJet m)) .varU)) (Γ := [])).eval Env.nil)^[k]
        ((tmZeroJet (Γ := [])).eval Env.nil, (tmConstOneJet (Γ := [])).eval Env.nil)
    let ew : Env [JetPairTy] := Env.cons Wk Env.nil
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    refine ⟨?_, ?_⟩
    · change (Q.add (Q.ofNat 0)
        (Q.div (((tmJetMul (Γ := [JetPairTy])).eval ew)
          ((Tm.closedWk (Γ := [JetPairTy]) (tmConstNatJet m)).eval ew) Wk.2 j)
          (Q.ofNat (j + 1)))).val =
        (Q.div (Q.mul (Q.ofNat m) ((Jet.cosFreq m).coeff j)) (Q.ofNat (j + 1))).val
      rw [Q.zero_add_div_ofNat_succ, Q.val_div _ _ hne, Q.val_div _ _ hne,
          closedWk_eval (tmConstNatJet m) ew, tmJetMul_constNatJet_val ew m Wk.2 j,
          Q.val_mul, Q.val_ofNat, Q.val_ofNat, ih.2]
    · change (Q.add (Q.ofNat 0)
        (Q.div (Q.sub (((Tm.closedWk (Γ := [JetPairTy]) tmZeroJet).eval ew) j)
          (((tmJetMul (Γ := [JetPairTy])).eval ew)
            ((Tm.closedWk (Γ := [JetPairTy]) (tmConstNatJet m)).eval ew) Wk.1 j))
          (Q.ofNat (j + 1)))).val =
        (Q.div (Q.neg (Q.mul (Q.ofNat m) ((Jet.sinFreq m).coeff j))) (Q.ofNat (j + 1))).val
      rw [Q.zero_add_div_ofNat_succ, Q.val_div _ _ hne, Q.val_div _ _ hne,
          Q.val_sub, closedWk_eval tmZeroJet ew, closedWk_eval (tmConstNatJet m) ew,
          tmJetMul_constNatJet_val ew m Wk.1 j, Q.val_neg, Q.val_mul,
          show (tmZeroJet (Γ := [])).eval Env.nil j = Q.ofNat 0 from rfl,
          Q.val_ofNat, Q.val_ofNat, Q.val_ofNat, ih.1]
      ring

/-- Below degree `k`, the `k`-th iterate is the Taylor jet of `(sin mx, cos mx)`. -/
theorem genSolve2_mode_val (m k i : Nat) (hi : i < k) :
    let W := (((extractClosed (modeSolveD m)).eval Env.nil) k).1
    (W.1 i).val = ((Jet.sinFreq m).coeff i).val ∧
    (W.2 i).val = ((Jet.cosFreq m).coeff i).val := by
  dsimp only [modeSolveD]
  rw [extractClosed_genSolve2D_fst]
  exact mode_iterate_val m k i hi

/-- The loop closed: the proof-computed mode solver agrees with the Taylor jet
    of the Fourier modes of frequency `m + 1`. -/
theorem genSolve2_mode_trig (m k i : Nat) (hi : i < k) :
    let W := (((extractClosed (modeSolveD (m + 1))).eval Env.nil) k).1
    (W.1 i).val = ((TrigPoly.toJet (TrigPoly.sinMode (m + 1))).coeff i).val ∧
    (W.2 i).val = ((TrigPoly.toJet (TrigPoly.cosMode (m + 1))).coeff i).val := by
  have hval := genSolve2_mode_val (m + 1) k i hi
  have hmodes := TrigPoly.toJet_modes m i
  exact ⟨hval.1.trans hmodes.2.symm, hval.2.trans hmodes.1.symm⟩

#print axioms modeSolveD
#print axioms genSolve2_mode_val
#print axioms genSolve2_mode_trig

end HAomega
