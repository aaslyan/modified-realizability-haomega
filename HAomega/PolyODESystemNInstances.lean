/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PolyODESystemN

/-!
# The one- and two-variable solvers are instances of the n-variable solver

`JExpr` and `JExpr2` translate into `JExprN` (`Y ↦ var 0`; `U ↦ var 0`,
`V ↦ var 1`). The n-variable solver `genSolveND` at the translated one- or
two-equation system extracts exactly what `genSolveD` / `genSolve2D` extract,
as `Q`-valued functions. So `genSolveND` subsumes the earlier general solvers,
and through them every scalar and two-variable instance in the catalog.
-/

namespace HAomega

/-- `JExpr` into `JExprN`, with `Y ↦ var 0`. -/
def JExpr.toN : JExpr → JExprN
  | .var => .var 0
  | .const c => .const c
  | .add a b => .add a.toN b.toN
  | .sub a b => .sub a.toN b.toN
  | .mul a b => .mul a.toN b.toN
  | .integ a => .integ a.toN

/-- `JExpr2` into `JExprN`, with `U ↦ var 0`, `V ↦ var 1`. -/
def JExpr2.toN : JExpr2 → JExprN
  | .varU => .var 0
  | .varV => .var 1
  | .const c => .const c
  | .add a b => .add a.toN b.toN
  | .sub a b => .sub a.toN b.toN
  | .mul a b => .mul a.toN b.toN
  | .integ a => .integ a.toN

theorem JExpr.toN_wf (F : JExpr) : F.toN.WF 1 := by
  induction F with
  | var => exact Nat.succ_pos 0
  | const _ => trivial
  | add _ _ iha ihb => exact ⟨iha, ihb⟩
  | sub _ _ iha ihb => exact ⟨iha, ihb⟩
  | mul _ _ iha ihb => exact ⟨iha, ihb⟩
  | integ _ iha => exact iha

theorem JExpr2.toN_wf (F : JExpr2) : F.toN.WF 2 := by
  induction F with
  | varU => exact Nat.succ_pos 1
  | varV => exact Nat.lt_succ_self 1
  | const _ => trivial
  | add _ _ iha ihb => exact ⟨iha, ihb⟩
  | sub _ _ iha ihb => exact ⟨iha, ihb⟩
  | mul _ _ iha ihb => exact ⟨iha, ihb⟩
  | integ _ iha => exact iha

/-- Evaluating `F.toN.toTm w` in `e₁` equals evaluating `F.toTm y` in `e₂` when `w.eval e₁ 0 = y.eval e₂`. -/
theorem JExpr.toN_toTm_eval (F : JExpr) {Γ₁ Γ₂ : List Ty} (e₁ : Env Γ₁) (e₂ : Env Γ₂)
    (w : Tm Γ₁ WTy) (y : Tm Γ₂ JetTy) (h0 : w.eval e₁ 0 = y.eval e₂) :
    (F.toN.toTm w).eval e₁ = (F.toTm y).eval e₂ := by
  induction F with
  | var => exact h0
  | const c =>
    dsimp only [JExpr.toN, JExprN.toTm, JExpr.toTm]
    rw [closedWk_eval c e₁, closedWk_eval c e₂]
  | add a b iha ihb =>
    dsimp only [JExpr.toN, JExprN.toTm, JExpr.toTm, Tm.eval]
    rw [iha, ihb]
    rfl
  | sub a b iha ihb =>
    dsimp only [JExpr.toN, JExprN.toTm, JExpr.toTm, Tm.eval]
    rw [iha, ihb]
    rfl
  | mul a b iha ihb =>
    dsimp only [JExpr.toN, JExprN.toTm, JExpr.toTm, Tm.eval]
    rw [iha, ihb]
    rfl
  | integ a iha =>
    dsimp only [JExpr.toN, JExprN.toTm, JExpr.toTm, Tm.eval]
    rw [iha]
    rfl

/-- Evaluating `F.toN.toTm w` in `e₁` equals evaluating `F.toTm u v` in `e₂` when `w.eval e₁ 0 = u.eval e₂` and `w.eval e₁ 1 = v.eval e₂`. -/
theorem JExpr2.toN_toTm_eval (F : JExpr2) {Γ₁ Γ₂ : List Ty} (e₁ : Env Γ₁) (e₂ : Env Γ₂)
    (w : Tm Γ₁ WTy) (u v : Tm Γ₂ JetTy)
    (h0 : w.eval e₁ 0 = u.eval e₂) (h1 : w.eval e₁ 1 = v.eval e₂) :
    (F.toN.toTm w).eval e₁ = (F.toTm u v).eval e₂ := by
  induction F with
  | varU => exact h0
  | varV => exact h1
  | const c =>
    dsimp only [JExpr2.toN, JExprN.toTm, JExpr2.toTm]
    rw [closedWk_eval c e₁, closedWk_eval c e₂]
  | add a b iha ihb =>
    dsimp only [JExpr2.toN, JExprN.toTm, JExpr2.toTm, Tm.eval]
    rw [iha, ihb]
    rfl
  | sub a b iha ihb =>
    dsimp only [JExpr2.toN, JExprN.toTm, JExpr2.toTm, Tm.eval]
    rw [iha, ihb]
    rfl
  | mul a b iha ihb =>
    dsimp only [JExpr2.toN, JExprN.toTm, JExpr2.toTm, Tm.eval]
    rw [iha, ihb]
    rfl
  | integ a iha =>
    dsimp only [JExpr2.toN, JExprN.toTm, JExpr2.toTm, Tm.eval]
    rw [iha]
    rfl

/-- One Picard step of `genStepN [(A, F.toN)]` at index `0` equals `genStep A F` when `W 0 = Y`. -/
theorem genStepN_one_eval (A : Tm [] JetTy) (F : JExpr) (W : Nat → Nat → Q) (Y : Nat → Q)
    (h0 : W 0 = Y) :
    (((genStepN [(A, F.toN)] (Γ := [])).eval Env.nil) W) 0 =
      ((genStep A F (Γ := [])).eval Env.nil) Y := by
  let e₁ : Env [.nat, WTy] := Env.cons (σ := .nat) 0 (Env.cons (σ := WTy) W Env.nil)
  let e₂ : Env [JetTy] := Env.cons (σ := JetTy) Y Env.nil
  change ((tmJetAdd (Γ := [.nat, WTy])).eval e₁) ((Tm.closedWk A).eval e₁)
      (((tmJetInteg (Γ := [.nat, WTy])).eval e₁) ((F.toN.toTm (.var (.there .here))).eval e₁)) =
    ((tmJetAdd (Γ := [JetTy])).eval e₂) ((Tm.closedWk A).eval e₂)
      (((tmJetInteg (Γ := [JetTy])).eval e₂) ((F.toTm (.var .here)).eval e₂))
  rw [closedWk_eval A e₁, closedWk_eval A e₂,
      F.toN_toTm_eval e₁ e₂ (.var (.there .here)) (.var .here) h0]
  rfl

/-- The `k`-th Picard iterate of `genStepN [(A, F.toN)]` from `initN` at index `0` equals the `k`-th iterate of `genStep A F` from `A`. -/
theorem genStepN_one_iterate (A : Tm [] JetTy) (F : JExpr) (k : Nat) :
    ((((genStepN [(A, F.toN)] (Γ := [])).eval Env.nil)^[k]
      ((initN [(A, F.toN)] (Γ := [])).eval Env.nil)) 0) =
      (((genStep A F (Γ := [])).eval Env.nil)^[k] (A.eval Env.nil)) := by
  induction k with
  | zero => exact closedWk_eval A (Env.cons (σ := .nat) 0 Env.nil)
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact genStepN_one_eval A F _ _ ih

/-- The scalar solver is the one-equation instance. -/
theorem genSolveND_one_eq (A : Tm [] JetTy) (F : JExpr) (k : Nat) :
    (((extractClosed (genSolveND [(A, F.toN)]
        (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact F.toN_wf))).eval
      Env.nil) k).1 0 =
    (((extractClosed (genSolveD A F)).eval Env.nil) k).1 := by
  rw [extractClosed_genSolveND_fst, extractClosed_genSolveD_fst]
  exact genStepN_one_iterate A F k

/-- One Picard step of `genStepN [(A, F.toN), (B, G.toN)]` at indices `(0, 1)` equals `genStep2 A B F G` when `(W 0, W 1) = P`. -/
theorem genStepN_two_eval (A B : Tm [] JetTy) (F G : JExpr2)
    (W : Nat → Nat → Q) (P : (Nat → Q) × (Nat → Q))
    (h0 : W 0 = P.1) (h1 : W 1 = P.2) :
    ((((genStepN [(A, F.toN), (B, G.toN)] (Γ := [])).eval Env.nil) W) 0,
     (((genStepN [(A, F.toN), (B, G.toN)] (Γ := [])).eval Env.nil) W) 1) =
      ((genStep2 A B F G (Γ := [])).eval Env.nil) P := by
  let e₂ : Env [JetPairTy] := Env.cons (σ := JetPairTy) P Env.nil
  refine Prod.ext ?_ ?_
  · let e₀ : Env [.nat, WTy] := Env.cons (σ := .nat) 0 (Env.cons (σ := WTy) W Env.nil)
    change ((tmJetAdd (Γ := [.nat, WTy])).eval e₀) ((Tm.closedWk A).eval e₀)
        (((tmJetInteg (Γ := [.nat, WTy])).eval e₀) ((F.toN.toTm (.var (.there .here))).eval e₀)) =
      ((tmJetAdd (Γ := [JetPairTy])).eval e₂) ((Tm.closedWk A).eval e₂)
        (((tmJetInteg (Γ := [JetPairTy])).eval e₂)
          ((F.toTm (.fst (.var .here)) (.snd (.var .here))).eval e₂))
    rw [closedWk_eval A e₀, closedWk_eval A e₂,
        F.toN_toTm_eval e₀ e₂ (.var (.there .here)) (.fst (.var .here)) (.snd (.var .here)) h0 h1]
    rfl
  · let e₁ : Env [.nat, WTy] := Env.cons (σ := .nat) 1 (Env.cons (σ := WTy) W Env.nil)
    let acc₀ : Nat → Q :=
      (Tm.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toN.toTm (.var (.there .here))))).eval e₁
    let e₁' : Env [JetTy, .nat, .nat, WTy] :=
      Env.cons (σ := JetTy) acc₀ (Env.cons (σ := .nat) 0 e₁)
    change ((tmJetAdd (Γ := [JetTy, .nat, .nat, WTy])).eval e₁') ((Tm.closedWk B).eval e₁')
        (((tmJetInteg (Γ := [JetTy, .nat, .nat, WTy])).eval e₁')
          ((G.toN.toTm ((Tm.var (.there .here) : Tm [.nat, WTy] WTy).wk.wk)).eval e₁')) =
      ((tmJetAdd (Γ := [JetPairTy])).eval e₂) ((Tm.closedWk B).eval e₂)
        (((tmJetInteg (Γ := [JetPairTy])).eval e₂)
          ((G.toTm (.fst (.var .here)) (.snd (.var .here))).eval e₂))
    rw [closedWk_eval B e₁', closedWk_eval B e₂,
        G.toN_toTm_eval e₁' e₂ ((Tm.var (.there .here) : Tm [.nat, WTy] WTy).wk.wk)
          (.fst (.var .here)) (.snd (.var .here)) h0 h1]
    rfl

/-- The `k`-th Picard iterate of `genStepN [(A, F.toN), (B, G.toN)]` from `initN` at `(0, 1)` equals the `k`-th iterate of `genStep2 A B F G` from `(A, B)`. -/
theorem genStepN_two_iterate (A B : Tm [] JetTy) (F G : JExpr2) (k : Nat) :
    let W := (((genStepN [(A, F.toN), (B, G.toN)] (Γ := [])).eval Env.nil)^[k]
      ((initN [(A, F.toN), (B, G.toN)] (Γ := [])).eval Env.nil))
    (W 0, W 1) =
      (((genStep2 A B F G (Γ := [])).eval Env.nil)^[k] (A.eval Env.nil, B.eval Env.nil)) := by
  induction k with
  | zero =>
    refine Prod.ext (closedWk_eval A (Env.cons (σ := .nat) 0 Env.nil)) ?_
    exact closedWk_eval B
      (Env.cons (σ := JetTy) ((Tm.closedWk A).eval (Env.cons (σ := .nat) 1 Env.nil))
        (Env.cons (σ := .nat) 0 (Env.cons (σ := .nat) 1 Env.nil)))
  | succ m ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact genStepN_two_eval A B F G _ _ (congrArg Prod.fst ih) (congrArg Prod.snd ih)

/-- The two-variable solver is the two-equation instance. -/
theorem genSolveND_two_eq (A B : Tm [] JetTy) (F G : JExpr2) (k : Nat) :
    let W := (((extractClosed (genSolveND [(A, F.toN), (B, G.toN)]
        (by intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl
            · exact F.toN_wf
            · exact G.toN_wf))).eval Env.nil) k).1
    (W 0, W 1) = (((extractClosed (genSolve2D A B F G)).eval Env.nil) k).1 := by
  dsimp only
  rw [extractClosed_genSolveND_fst, extractClosed_genSolve2D_fst]
  exact genStepN_two_iterate A B F G k

#print axioms genSolveND_one_eq
#print axioms genSolveND_two_eq

end HAomega
