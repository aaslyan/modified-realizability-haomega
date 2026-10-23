/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ClosedFourierODE

/-!
# Degree locking for the extracted Picard jet solvers

`picard_jetAgree_lock` (`ClosedCalculus.lean`) proves, for a generic guarded step
`sysTPicardStep`, that `k` Picard steps fix the first `k` Taylor coefficients.
This module instantiates that fact at the four extracted solvers of
`HolonomicCS.lean` / `ClosedFourierODE.lean`: iterate `k + 1` agrees with
iterate `k` below degree `k`.

These are metatheory theorems about the extracted programs; they are not
derivations in `Deriv`, and they do not change the classification of
`picardJetIterD`, `riccatiPicardD`, `quadBlowupPicardD`, `duffingPicardD`
(witness-style).
-/

namespace HAomega

/-- Generic degree-locking for any 1D iterate sequence of a contractive step operator. -/
theorem contractive_iter_lock (S : (Nat → Q) → (Nat → Q))
    (hS : ∀ n u v, JetAgree n u v → JetAgree (n + 1) (S u) (S v))
    (f : Nat → (Nat → Q)) (hf : ∀ m, f (m + 1) = S (f m)) :
    ∀ k : Nat, JetAgree k (f (k + 1)) (f k)
  | 0 => jetAgree_zero _ _
  | m + 1 => by
    have hStep := hS m (f (m + 1)) (f m) (contractive_iter_lock S hS f hf m)
    rwa [← hf (m + 1), ← hf m] at hStep

/-- Generic degree-locking for any 2D iterate sequence of a contractive pair step operator. -/
theorem contractive_pair_iter_lock
    (S : ((Nat → Q) × (Nat → Q)) → ((Nat → Q) × (Nat → Q)))
    (hS : ∀ n u v, JetAgree n u.1 v.1 → JetAgree n u.2 v.2 →
      JetAgree (n + 1) (S u).1 (S v).1 ∧ JetAgree (n + 1) (S u).2 (S v).2)
    (f : Nat → ((Nat → Q) × (Nat → Q))) (hf : ∀ m, f (m + 1) = S (f m)) :
    ∀ k : Nat, JetAgree k (f (k + 1)).1 (f k).1 ∧ JetAgree k (f (k + 1)).2 (f k).2
  | 0 => ⟨jetAgree_zero _ _, jetAgree_zero _ _⟩
  | m + 1 => by
    have ih := contractive_pair_iter_lock S hS f hf m
    have hStep := hS m (f (m + 1)) (f m) ih.1 ih.2
    rwa [← hf (m + 1), ← hf m] at hStep

/-- Contractivity of `tmPicardExpStep` (`JetAgree n u v → JetAgree (n + 1) (S u) (S v)`). -/
theorem tmPicardExpStep_contractive (n : Nat) (u v : Nat → Q) (h : JetAgree n u v) :
    JetAgree (n + 1) (((tmPicardExpStep (Γ := [])).eval Env.nil) u)
                     (((tmPicardExpStep (Γ := [])).eval Env.nil) v) := by
  intro i hi
  cases i with
  | zero => rfl
  | succ j =>
    change Q.div (u j) (Q.ofNat (j + 1)) = Q.div (v j) (Q.ofNat (j + 1))
    rw [h j (Nat.lt_of_succ_lt_succ hi)]

/-- Evaluation of `tmRiccatiStep` in terms of `tmJetInteg`, `tmJetAdd`, and `Jet.mul`. -/
theorem tmRiccatiStep_eval_eq (u : Nat → Q) :
    ((tmRiccatiStep (Γ := [])).eval Env.nil) u =
      (((tmJetInteg (Γ := [])).eval Env.nil)
        ((((tmJetAdd (Γ := [])).eval Env.nil) ((tmConstOneJet (Γ := [])).eval Env.nil))
          (((Jet.mk u).mul (Jet.mk u)).coeff))) := by
  dsimp [tmRiccatiStep, Tm.eval]
  rw [tmJetMul_eval_fun, tmJetInteg_eval_fun, ← tmJetInteg_eval_fun Env.nil]
  rfl

/-- Contractivity of `tmRiccatiStep` (`JetAgree n u v → JetAgree (n + 1) (S u) (S v)`). -/
theorem tmRiccatiStep_contractive (n : Nat) (u v : Nat → Q) (h : JetAgree n u v) :
    JetAgree (n + 1) (((tmRiccatiStep (Γ := [])).eval Env.nil) u)
                     (((tmRiccatiStep (Γ := [])).eval Env.nil) v) := by
  rw [tmRiccatiStep_eval_eq u, tmRiccatiStep_eval_eq v]
  exact tmJetInteg_contractive_minus_one n _ _
    (tmJetAdd_lookahead_zero n _ _ _ _ (fun _ _ ↦ rfl) (jetMul_lookahead_zero n u v u v h h))

/-- Evaluation of `tmQuadBlowupStep` as `sysTPicardStep` on the squaring map. -/
theorem tmQuadBlowupStep_eval_eq (u : Nat → Q) :
    ((tmQuadBlowupStep (Γ := [])).eval Env.nil) u =
      sysTPicardStep ((tmConstOneJet (Γ := [])).eval Env.nil)
        (fun y ↦ ((Jet.mk y).mul (Jet.mk y)).coeff) u := by
  dsimp [tmQuadBlowupStep, sysTPicardStep, Tm.eval]
  rw [tmJetMul_eval_fun, tmJetInteg_eval_fun, ← tmJetInteg_eval_fun Env.nil]
  rfl

/-- Contractivity of `tmQuadBlowupStep` (`JetAgree n u v → JetAgree (n + 1) (S u) (S v)`). -/
theorem tmQuadBlowupStep_contractive (n : Nat) (u v : Nat → Q) (h : JetAgree n u v) :
    JetAgree (n + 1) (((tmQuadBlowupStep (Γ := [])).eval Env.nil) u)
                     (((tmQuadBlowupStep (Γ := [])).eval Env.nil) v) := by
  rw [tmQuadBlowupStep_eval_eq u, tmQuadBlowupStep_eval_eq v]
  exact sysTPicardStep_contractive ((tmConstOneJet (Γ := [])).eval Env.nil)
    (fun y ↦ ((Jet.mk y).mul (Jet.mk y)).coeff)
    (fun m a b hab ↦ jetMul_lookahead_zero m a b a b hab hab) n u v h

/-- Evaluation of the two components of `tmDuffingStep` in terms of `sysTPicardStep` and `tmJetInteg`. -/
theorem tmDuffingStep_eval_eq (w : (Nat → Q) × (Nat → Q)) :
    (((tmDuffingStep (Γ := [])).eval Env.nil) w).1 =
      sysTPicardStep ((tmConstOneJet (Γ := [])).eval Env.nil) id w.2 ∧
    (((tmDuffingStep (Γ := [])).eval Env.nil) w).2 =
      (((tmJetInteg (Γ := [])).eval Env.nil)
        ((((tmJetSub (Γ := [])).eval Env.nil)
          ((((tmJetSub (Γ := [])).eval Env.nil) ((tmZeroJet (Γ := [])).eval Env.nil)) w.1))
          (((Jet.mk w.1).mul (Jet.mk w.1)).coeff))) := by
  refine ⟨?_, ?_⟩
  · dsimp [tmDuffingStep, sysTPicardStep, Tm.eval]
    rw [tmJetInteg_eval_fun, ← tmJetInteg_eval_fun Env.nil]
    rfl
  · dsimp [tmDuffingStep, Tm.eval]
    rw [tmJetMul_eval_fun, tmJetInteg_eval_fun, ← tmJetInteg_eval_fun Env.nil]
    rfl

/-- Contractivity of `tmDuffingStep` on pairs of jets. -/
theorem tmDuffingStep_contractive (n : Nat) (u v : (Nat → Q) × (Nat → Q))
    (hu : JetAgree n u.1 v.1) (hv : JetAgree n u.2 v.2) :
    JetAgree (n + 1) (((tmDuffingStep (Γ := [])).eval Env.nil) u).1
                     (((tmDuffingStep (Γ := [])).eval Env.nil) v).1 ∧
    JetAgree (n + 1) (((tmDuffingStep (Γ := [])).eval Env.nil) u).2
                     (((tmDuffingStep (Γ := [])).eval Env.nil) v).2 := by
  rw [(tmDuffingStep_eval_eq u).1, (tmDuffingStep_eval_eq v).1,
      (tmDuffingStep_eval_eq u).2, (tmDuffingStep_eval_eq v).2]
  refine ⟨sysTPicardStep_contractive ((tmConstOneJet (Γ := [])).eval Env.nil) id (fun _ _ _ h ↦ h) n u.2 v.2 hv, ?_⟩
  exact tmJetInteg_contractive_minus_one n _ _
    (tmJetSub_lookahead_zero n _ _ _ _
      (tmJetSub_lookahead_zero n _ _ _ _ (fun _ _ ↦ rfl) hu)
      (jetMul_lookahead_zero n u.1 v.1 u.1 v.1 hu hu))

/-- Linear `y' = y` (catalog #22). -/
theorem extractedPicardJet_lock (k i : Nat) (hi : i < k) :
    extractedPicardJet (k + 1) i = extractedPicardJet k i :=
  contractive_iter_lock
    ((tmPicardExpStep (Γ := [])).eval Env.nil)
    tmPicardExpStep_contractive
    extractedPicardJet
    (extractClosed_iterSequenceD_succ JetTy tmConstOneJet tmPicardExpStep)
    k i hi

/-- Riccati `y' = 1 + y²` (catalog #23). -/
theorem extractedRiccatiJet_lock (k i : Nat) (hi : i < k) :
    extractedRiccatiJet (k + 1) i = extractedRiccatiJet k i :=
  contractive_iter_lock
    ((tmRiccatiStep (Γ := [])).eval Env.nil)
    tmRiccatiStep_contractive
    extractedRiccatiJet
    (extractClosed_iterSequenceD_succ JetTy tmZeroJet tmRiccatiStep)
    k i hi

/-- Quadratic blow-up `y' = y²` (catalog #24). -/
theorem extractedQuadBlowupJet_lock (k i : Nat) (hi : i < k) :
    extractedQuadBlowupJet (k + 1) i = extractedQuadBlowupJet k i :=
  contractive_iter_lock
    ((tmQuadBlowupStep (Γ := [])).eval Env.nil)
    tmQuadBlowupStep_contractive
    extractedQuadBlowupJet
    (extractClosed_iterSequenceD_succ JetTy tmConstOneJet tmQuadBlowupStep)
    k i hi

/-- Duffing `u' = v, v' = -u - u²` (catalog #25), both components. -/
theorem extractedDuffingJet_lock (k i : Nat) (hi : i < k) :
    (extractedDuffingJet (k + 1)).1 i = (extractedDuffingJet k).1 i ∧
    (extractedDuffingJet (k + 1)).2 i = (extractedDuffingJet k).2 i := by
  have h := contractive_pair_iter_lock
    ((tmDuffingStep (Γ := [])).eval Env.nil)
    tmDuffingStep_contractive
    extractedDuffingJet
    (extractClosed_iterSequenceD_succ JetPairTy tmDuffingInit tmDuffingStep)
    k
  exact ⟨h.1 i hi, h.2 i hi⟩

#print axioms extractedPicardJet_lock
#print axioms extractedRiccatiJet_lock
#print axioms extractedQuadBlowupJet_lock
#print axioms extractedDuffingJet_lock

end HAomega
