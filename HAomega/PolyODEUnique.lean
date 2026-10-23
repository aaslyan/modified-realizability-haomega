/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.FourierModesSolve

/-!
# The proof-computed solver computes *the* solution

`genSolveD A F` proves that its witness solves `Y = A + ∫F(Y)` below degree
`k`. This module shows the witness is not merely *a* solution: any jet `Z`
that solves the equation (as values, at every index) agrees with the `k`-th
extracted iterate below degree `k`. Taylor coefficients of solutions of
`y = A + ∫F(y)` are unique, and the extract converges to them degree by degree.

Value level (metatheory): `F`'s operations respect value equality (`Q.val`),
and `∫` raises the agreement degree by one.
-/

namespace HAomega

/-- Two coefficient streams `u, v : Nat → Q` have equal rational values at all indices `< n`. -/
def AgreeV (n : Nat) (u v : Nat → Q) : Prop :=
  ∀ i < n, (u i).val = (v i).val

/-- `tmJetAdd` preserves `AgreeV n` across any environments `e₁, e₂`. -/
theorem tmJetAdd_agreeV {Γ : List Ty} (e₁ e₂ : Env Γ) (n : Nat) (a₁ a₂ b₁ b₂ : Nat → Q)
    (ha : AgreeV n a₁ a₂) (hb : AgreeV n b₁ b₂) :
    AgreeV n (((tmJetAdd (Γ := Γ)).eval e₁) a₁ b₁) (((tmJetAdd (Γ := Γ)).eval e₂) a₂ b₂) := by
  intro i hi
  show (Q.add (a₁ i) (b₁ i)).val = (Q.add (a₂ i) (b₂ i)).val
  rw [Q.val_add, Q.val_add, ha i hi, hb i hi]

/-- `tmJetSub` preserves `AgreeV n` across any environments `e₁, e₂`. -/
theorem tmJetSub_agreeV {Γ : List Ty} (e₁ e₂ : Env Γ) (n : Nat) (a₁ a₂ b₁ b₂ : Nat → Q)
    (ha : AgreeV n a₁ a₂) (hb : AgreeV n b₁ b₂) :
    AgreeV n (((tmJetSub (Γ := Γ)).eval e₁) a₁ b₁) (((tmJetSub (Γ := Γ)).eval e₂) a₂ b₂) := by
  intro i hi
  show (Q.sub (a₁ i) (b₁ i)).val = (Q.sub (a₂ i) (b₂ i)).val
  rw [Q.val_sub, Q.val_sub, ha i hi, hb i hi]

/-- `tmJetMul` preserves `AgreeV n` across any environments `e₁, e₂`. -/
theorem tmJetMul_agreeV {Γ : List Ty} (e₁ e₂ : Env Γ) (n : Nat) (a₁ a₂ b₁ b₂ : Nat → Q)
    (ha : AgreeV n a₁ a₂) (hb : AgreeV n b₁ b₂) :
    AgreeV n (((tmJetMul (Γ := Γ)).eval e₁) a₁ b₁) (((tmJetMul (Γ := Γ)).eval e₂) a₂ b₂) := by
  intro i hi
  rw [tmJetMul_eval, tmJetMul_eval]
  simp only [Jet.mul, TrigPoly.cauchyConvAux_val]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [ha j (by omega), hb (i - j) (by omega)]

/-- `tmJetInteg` maps `AgreeV n` to `AgreeV (n + 1)` across any environments `e₁, e₂`. -/
theorem tmJetInteg_agreeV_succ {Γ : List Ty} (e₁ e₂ : Env Γ) (n : Nat) (c₁ c₂ : Nat → Q)
    (hc : AgreeV n c₁ c₂) :
    AgreeV (n + 1) (((tmJetInteg (Γ := Γ)).eval e₁) c₁) (((tmJetInteg (Γ := Γ)).eval e₂) c₂) := by
  intro i hi
  cases i with
  | zero => rfl
  | succ j =>
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    show (Q.div (c₁ j) (Q.ofNat (j + 1))).val = (Q.div (c₂ j) (Q.ofNat (j + 1))).val
    rw [Q.val_div _ _ hne, Q.val_div _ _ hne, hc j (Nat.lt_of_succ_lt_succ hi)]

/-- Evaluating `F.toTm` on inputs satisfying `AgreeV n` preserves `AgreeV n`. -/
theorem JExpr.toTm_agreeV (F : JExpr) {Γ : List Ty} (e₁ e₂ : Env Γ) (y₁ y₂ : Tm Γ JetTy)
    (n : Nat) (hy : AgreeV n (y₁.eval e₁) (y₂.eval e₂)) :
    AgreeV n ((F.toTm y₁).eval e₁) ((F.toTm y₂).eval e₂) := by
  induction F with
  | var => exact hy
  | const c =>
    intro i _
    dsimp only [JExpr.toTm]
    rw [closedWk_eval c e₁, closedWk_eval c e₂]
  | add a b iha ihb =>
    exact tmJetAdd_agreeV e₁ e₂ n _ _ _ _ iha ihb
  | sub a b iha ihb =>
    exact tmJetSub_agreeV e₁ e₂ n _ _ _ _ iha ihb
  | mul a b iha ihb =>
    exact tmJetMul_agreeV e₁ e₂ n _ _ _ _ iha ihb
  | integ a iha =>
    intro i hi
    exact tmJetInteg_agreeV_succ e₁ e₂ n _ _ iha i (Nat.lt_succ_of_lt hi)

/-- `genStep A F` maps `AgreeV n u v` to `AgreeV (n + 1) (genStep A F u) (genStep A F v)`. -/
theorem genStep_agreeV_succ (A : Tm [] JetTy) (F : JExpr) (n : Nat) (u v : Nat → Q)
    (huv : AgreeV n u v) :
    AgreeV (n + 1) (((genStep A F (Γ := [])).eval Env.nil) u)
                   (((genStep A F (Γ := [])).eval Env.nil) v) := by
  let eu : Env [JetTy] := Env.cons u Env.nil
  let ev : Env [JetTy] := Env.cons v Env.nil
  have hA : AgreeV (n + 1) ((Tm.closedWk A).eval eu) ((Tm.closedWk A).eval ev) := by
    intro i _
    rw [closedWk_eval A eu, closedWk_eval A ev]
  have hF : AgreeV n ((F.toTm (.var .here)).eval eu) ((F.toTm (.var .here)).eval ev) :=
    F.toTm_agreeV eu ev (.var .here) (.var .here) n huv
  exact tmJetAdd_agreeV eu ev (n + 1) _ _ _ _ hA (tmJetInteg_agreeV_succ eu ev n _ _ hF)

/-- If `Z` is a value-level fixed point of `genStep A F`, then the `k`-th Picard iterate from `A` satisfies `AgreeV k` with `Z`. -/
theorem genStep_iterate_agreeV (A : Tm [] JetTy) (F : JExpr) (Z : Nat → Q)
    (hZ : ∀ n, ((((genStep A F (Γ := [])).eval Env.nil) Z) n).val = (Z n).val) :
    ∀ k : Nat, AgreeV k (((genStep A F (Γ := [])).eval Env.nil)^[k] (A.eval Env.nil)) Z
  | 0 => fun _ hi ↦ absurd hi (Nat.not_lt_zero _)
  | k + 1 => by
    intro i hi
    rw [Function.iterate_succ_apply']
    have hstep := genStep_agreeV_succ A F k
      (((genStep A F (Γ := [])).eval Env.nil)^[k] (A.eval Env.nil)) Z
      (genStep_iterate_agreeV A F Z hZ k) i hi
    exact hstep.trans (hZ i)

/-- Uniqueness: every value-level solution `Z` of `Z = A + ∫F(Z)` agrees with
    the `k`-th proof-computed iterate below degree `k`. -/
theorem genSolve_unique_val (A : Tm [] JetTy) (F : JExpr) (Z : Nat → Q)
    (hZ : ∀ n, ((((genStep A F (Γ := [])).eval Env.nil) Z) n).val = (Z n).val)
    (k i : Nat) (hi : i < k) :
    ((((extractClosed (genSolveD A F)).eval Env.nil) k).1 i).val = (Z i).val := by
  rw [extractClosed_genSolveD_fst]
  exact genStep_iterate_agreeV A F Z hZ k i hi

/-- Evaluating `F.toTm` on two-variable inputs satisfying `AgreeV n` preserves `AgreeV n`. -/
theorem JExpr2.toTm_agreeV (F : JExpr2) {Γ : List Ty} (e₁ e₂ : Env Γ)
    (u₁ u₂ v₁ v₂ : Tm Γ JetTy) (n : Nat)
    (hu : AgreeV n (u₁.eval e₁) (u₂.eval e₂))
    (hv : AgreeV n (v₁.eval e₁) (v₂.eval e₂)) :
    AgreeV n ((F.toTm u₁ v₁).eval e₁) ((F.toTm u₂ v₂).eval e₂) := by
  induction F with
  | varU => exact hu
  | varV => exact hv
  | const c =>
    intro i _
    dsimp only [JExpr2.toTm]
    rw [closedWk_eval c e₁, closedWk_eval c e₂]
  | add a b iha ihb =>
    exact tmJetAdd_agreeV e₁ e₂ n _ _ _ _ iha ihb
  | sub a b iha ihb =>
    exact tmJetSub_agreeV e₁ e₂ n _ _ _ _ iha ihb
  | mul a b iha ihb =>
    exact tmJetMul_agreeV e₁ e₂ n _ _ _ _ iha ihb
  | integ a iha =>
    intro i hi
    exact tmJetInteg_agreeV_succ e₁ e₂ n _ _ iha i (Nat.lt_succ_of_lt hi)

/-- `genStep2 A B F G` maps componentwise `AgreeV n` to componentwise `AgreeV (n + 1)`. -/
theorem genStep2_agreeV_succ (A B : Tm [] JetTy) (F G : JExpr2) (n : Nat)
    (W₁ W₂ : (Nat → Q) × (Nat → Q))
    (h1 : AgreeV n W₁.1 W₂.1) (h2 : AgreeV n W₁.2 W₂.2) :
    AgreeV (n + 1) ((((genStep2 A B F G (Γ := [])).eval Env.nil) W₁).1)
                   ((((genStep2 A B F G (Γ := [])).eval Env.nil) W₂).1) ∧
    AgreeV (n + 1) ((((genStep2 A B F G (Γ := [])).eval Env.nil) W₁).2)
                   ((((genStep2 A B F G (Γ := [])).eval Env.nil) W₂).2) := by
  let e₁ : Env [JetPairTy] := Env.cons W₁ Env.nil
  let e₂ : Env [JetPairTy] := Env.cons W₂ Env.nil
  have hA : AgreeV (n + 1) ((Tm.closedWk A).eval e₁) ((Tm.closedWk A).eval e₂) := by
    intro i _; rw [closedWk_eval A e₁, closedWk_eval A e₂]
  have hB : AgreeV (n + 1) ((Tm.closedWk B).eval e₁) ((Tm.closedWk B).eval e₂) := by
    intro i _; rw [closedWk_eval B e₁, closedWk_eval B e₂]
  have hF : AgreeV n ((F.toTm (.fst (.var .here)) (.snd (.var .here))).eval e₁)
                     ((F.toTm (.fst (.var .here)) (.snd (.var .here))).eval e₂) :=
    F.toTm_agreeV e₁ e₂ (.fst (.var .here)) (.fst (.var .here))
      (.snd (.var .here)) (.snd (.var .here)) n h1 h2
  have hG : AgreeV n ((G.toTm (.fst (.var .here)) (.snd (.var .here))).eval e₁)
                     ((G.toTm (.fst (.var .here)) (.snd (.var .here))).eval e₂) :=
    G.toTm_agreeV e₁ e₂ (.fst (.var .here)) (.fst (.var .here))
      (.snd (.var .here)) (.snd (.var .here)) n h1 h2
  exact ⟨tmJetAdd_agreeV e₁ e₂ (n + 1) _ _ _ _ hA (tmJetInteg_agreeV_succ e₁ e₂ n _ _ hF),
         tmJetAdd_agreeV e₁ e₂ (n + 1) _ _ _ _ hB (tmJetInteg_agreeV_succ e₁ e₂ n _ _ hG)⟩

/-- If `Z` is a value-level fixed point of `genStep2 A B F G`, then the `k`-th Picard iterate from `(A, B)` satisfies componentwise `AgreeV k` with `Z`. -/
theorem genStep2_iterate_agreeV (A B : Tm [] JetTy) (F G : JExpr2) (Z : (Nat → Q) × (Nat → Q))
    (hZ : ∀ n, ((((genStep2 A B F G (Γ := [])).eval Env.nil) Z).1 n).val = (Z.1 n).val ∧
               ((((genStep2 A B F G (Γ := [])).eval Env.nil) Z).2 n).val = (Z.2 n).val) :
    ∀ k : Nat,
      let W := ((genStep2 A B F G (Γ := [])).eval Env.nil)^[k] (A.eval Env.nil, B.eval Env.nil)
      AgreeV k W.1 Z.1 ∧ AgreeV k W.2 Z.2
  | 0 => ⟨fun _ hi ↦ absurd hi (Nat.not_lt_zero _), fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | k + 1 => by
    have ih := genStep2_iterate_agreeV A B F G Z hZ k
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    have hstep := genStep2_agreeV_succ A B F G k
      (((genStep2 A B F G (Γ := [])).eval Env.nil)^[k] (A.eval Env.nil, B.eval Env.nil))
      Z ih.1 ih.2
    exact ⟨fun i hi ↦ (hstep.1 i hi).trans (hZ i).1,
           fun i hi ↦ (hstep.2 i hi).trans (hZ i).2⟩

/-- The same for two-variable systems. -/
theorem genSolve2_unique_val (A B : Tm [] JetTy) (F G : JExpr2) (Z : (Nat → Q) × (Nat → Q))
    (hZ : ∀ n, ((((genStep2 A B F G (Γ := [])).eval Env.nil) Z).1 n).val = (Z.1 n).val ∧
               ((((genStep2 A B F G (Γ := [])).eval Env.nil) Z).2 n).val = (Z.2 n).val)
    (k i : Nat) (hi : i < k) :
    let W := (((extractClosed (genSolve2D A B F G)).eval Env.nil) k).1
    (W.1 i).val = (Z.1 i).val ∧ (W.2 i).val = (Z.2 i).val := by
  dsimp only
  rw [extractClosed_genSolve2D_fst]
  have h := genStep2_iterate_agreeV A B F G Z hZ k
  exact ⟨h.1 i hi, h.2 i hi⟩

#print axioms genSolve_unique_val
#print axioms genSolve2_unique_val

end HAomega
