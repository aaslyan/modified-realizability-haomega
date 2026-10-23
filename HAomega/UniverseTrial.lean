/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PolyODESystemNInstances

/-!
# Trial: the polynomial-ODE universe as a layer on top of jets, and closure under `+`

A reversible trial (QUESTIONS.md item 19). Nothing existing changes: jets stay
the representation, and the universe is a *predicate* on jets.

* `solN sys v n` — the solution's coefficient `n` in variable `v`, read from the
  proof-computed iterate at step `n + 1` (Picard iteration fixes degree `n`
  after `n + 1` steps);
* `InUniverse f` — `f` is, as rational values, a component of the solution of
  some well-formed polynomial–integral system;
* `solN_fixed` — `solN` is a fixed point of the system's Picard operator;
* `InUniverse_add` — the universe is closed under `+`.

Every member has a proof-computed solver by definition (`genSolveND`). The
closure proof is meant to *build* a system for `f + g`: the system of `f`,
the system of `g` with its variables renumbered after it, and one new variable
`h = (A_f + A_g) + ∫(F_f + F_g)`, identified with `f + g` by uniqueness.
Value-level metatheory theorems (`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- The solution's coefficient `n` in variable `v`: the iterate at step `n + 1`. -/
def solN (sys : List (Tm [] JetTy × JExprN)) (v n : Nat) : Q :=
  (((genStepN sys (Γ := [])).eval Env.nil)^[n + 1] ((initN sys (Γ := [])).eval Env.nil)) v n

/-- `f` is, as values, a component of the solution of a well-formed system. -/
def InUniverse (f : Nat → Q) : Prop :=
  ∃ (sys : List (Tm [] JetTy × JExprN)) (_ : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat),
    v < sys.length ∧ ∀ n, (f n).val = (solN sys v n).val

/-- Consecutive Picard iterates of `genStepN sys` from `initN sys` satisfy `AgreeV k` in every variable. -/
theorem genStepN_iterate_lock_step (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) :
    ∀ k v : Nat,
      AgreeV k
        ((((genStepN sys (Γ := [])).eval Env.nil)^[k] ((initN sys (Γ := [])).eval Env.nil)) v)
        ((((genStepN sys (Γ := [])).eval Env.nil)^[k + 1] ((initN sys (Γ := [])).eval Env.nil)) v)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, v, i, hi => by
    have hstep := genStepN_agreeV_succ sys hwf k
      (((genStepN sys (Γ := [])).eval Env.nil)^[k] ((initN sys (Γ := [])).eval Env.nil))
      (((genStepN sys (Γ := [])).eval Env.nil)^[k + 1] ((initN sys (Γ := [])).eval Env.nil))
      (fun u _ ↦ genStepN_iterate_lock_step sys hwf k u) v i hi
    rwa [← Function.iterate_succ_apply' ((genStepN sys (Γ := [])).eval Env.nil) k,
         ← Function.iterate_succ_apply' ((genStepN sys (Γ := [])).eval Env.nil) (k + 1)] at hstep

/-- The `k`-th and `(k + d)`-th Picard iterates of `genStepN sys` satisfy `AgreeV k` in every variable. -/
theorem genStepN_iterate_lock_add (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (k : Nat) :
    ∀ d v : Nat,
      AgreeV k
        ((((genStepN sys (Γ := [])).eval Env.nil)^[k] ((initN sys (Γ := [])).eval Env.nil)) v)
        ((((genStepN sys (Γ := [])).eval Env.nil)^[k + d] ((initN sys (Γ := [])).eval Env.nil)) v)
  | 0, _, _, _ => rfl
  | d + 1, v, i, hi =>
    (genStepN_iterate_lock_add sys hwf k d v i hi).trans
      (genStepN_iterate_lock_step sys hwf (k + d) v i (by omega))

/-- Below degree `n`, `solN sys v` agrees as rational values with the `n`-th Picard iterate in variable `v`. -/
theorem solN_agreeV_iterate (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (n v : Nat) :
    AgreeV n (solN sys v)
      ((((genStepN sys (Γ := [])).eval Env.nil)^[n] ((initN sys (Γ := [])).eval Env.nil)) v) := by
  intro m hm
  have hlock := genStepN_iterate_lock_add sys hwf (m + 1) (n - (m + 1)) v m (Nat.lt_succ_self m)
  have heq : (m + 1) + (n - (m + 1)) = n := by omega
  rw [heq] at hlock
  exact hlock

/-- `solN` is a fixed point of the Picard operator, in every variable `v < n`. -/
theorem solN_fixed (sys : List (Tm [] JetTy × JExprN))
    (hwf : ∀ p ∈ sys, p.2.WF sys.length) (v : Nat) (hv : v < sys.length) (n : Nat) :
    ((((genStepN sys (Γ := [])).eval Env.nil) (solN sys)) v n).val = (solN sys v n).val := by
  have _ := hv
  have hstep := genStepN_agreeV_succ sys hwf n (solN sys)
    (((genStepN sys (Γ := [])).eval Env.nil)^[n] ((initN sys (Γ := [])).eval Env.nil))
    (fun u _ ↦ solN_agreeV_iterate sys hwf n u) v n (Nat.lt_succ_self n)
  rw [← Function.iterate_succ_apply' ((genStepN sys (Γ := [])).eval Env.nil) n] at hstep
  exact hstep

/-- Evaluating one equation `(A, F)` on state `W : Nat → Nat → Q`. -/
def eqStepEval (p : Tm [] JetTy × JExprN) (W : Nat → Nat → Q) : Nat → Q :=
  ((tmJetAdd (Γ := [])).eval Env.nil) (p.1.eval Env.nil)
    (((tmJetInteg (Γ := [])).eval Env.nil)
      ((p.2.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil)))

/-- Evaluating `F.toTm` in two environments that give the same state stream yields the same jet. -/
theorem JExprN.toTm_eval_eq (F : JExprN) {Γ₁ Γ₂ : List Ty} (e₁ : Env Γ₁) (e₂ : Env Γ₂)
    (w₁ : Tm Γ₁ WTy) (w₂ : Tm Γ₂ WTy) (hw : w₁.eval e₁ = w₂.eval e₂) :
    (F.toTm w₁).eval e₁ = (F.toTm w₂).eval e₂ := by
  induction F with
  | var i =>
    change w₁.eval e₁ ((natTm i).eval e₁) = w₂.eval e₂ ((natTm i).eval e₂)
    rw [natTm_eval, natTm_eval, hw]
  | const c =>
    dsimp only [JExprN.toTm]
    rw [closedWk_eval c e₁, closedWk_eval c e₂]
  | add a b iha ihb =>
    dsimp only [JExprN.toTm, Tm.eval]
    rw [iha, ihb]
    rfl
  | sub a b iha ihb =>
    dsimp only [JExprN.toTm, Tm.eval]
    rw [iha, ihb]
    rfl
  | mul a b iha ihb =>
    dsimp only [JExprN.toTm, Tm.eval]
    rw [iha, ihb]
    rfl
  | integ a iha =>
    dsimp only [JExprN.toTm, Tm.eval]
    rw [iha]
    rfl

/-- Evaluating `selectStep tail w tv` at index `v < tail.length` yields `eqStepEval tail[v] (w.eval e)`. -/
theorem selectStep_eval_getElem (tail : List (Tm [] JetTy × JExprN))
    {Γ : List Ty} (e : Env Γ) (w : Tm Γ WTy) (tv : Tm Γ .nat) (W : Nat → Nat → Q)
    (v : Nat) (hv : v < tail.length)
    (hw : w.eval e = W) (htv : tv.eval e = v) :
    (selectStep tail w tv).eval e = eqStepEval tail[v] W := by
  induction tail generalizing Γ v with
  | nil => exact absurd hv (Nat.not_lt_zero v)
  | cons hd rest ih =>
    rcases hd with ⟨A, F⟩
    let z := (Tm.app (.app tmJetAdd (Tm.closedWk A)) (.app tmJetInteg (F.toTm w))).eval e
    let s : Nat → (Nat → Q) → (Nat → Q) := fun u acc ↦
      (selectStep rest w.wk.wk (.var (.there .here))).eval
        (Env.cons (σ := JetTy) acc (Env.cons (σ := .nat) u e))
    change Nat.rec (motive := fun _ ↦ Nat → Q) z s (tv.eval e) = eqStepEval ((A, F) :: rest)[v] W
    rw [htv]
    cases v with
    | zero =>
      change ((tmJetAdd (Γ := Γ)).eval e) ((Tm.closedWk A).eval e)
          (((tmJetInteg (Γ := Γ)).eval e) ((F.toTm w).eval e)) =
        ((tmJetAdd (Γ := [])).eval Env.nil) (A.eval Env.nil)
          (((tmJetInteg (Γ := [])).eval Env.nil)
            ((F.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil)))
      rw [closedWk_eval A e,
          F.toTm_eval_eq e (Env.cons (σ := WTy) W Env.nil) w (.var .here) hw]
      rfl
    | succ u =>
      let acc := Nat.rec (motive := fun _ ↦ Nat → Q) z s u
      let e' : Env (JetTy :: .nat :: Γ) := Env.cons (σ := JetTy) acc (Env.cons (σ := .nat) u e)
      have hw' : w.wk.wk.eval e' = W :=
        (Tm.eval_wk (σ := JetTy) w.wk acc (Env.cons (σ := .nat) u e)).trans
          ((Tm.eval_wk (σ := .nat) w u e).trans hw)
      exact ih e' w.wk.wk (.var (.there .here)) u
        (Nat.lt_of_succ_lt_succ hv) hw' rfl

/-- Evaluating `genStepN sys` on `W` at variable `v < sys.length` yields `eqStepEval sys[v] W`. -/
theorem genStepN_eval_getElem (sys : List (Tm [] JetTy × JExprN))
    (W : Nat → Nat → Q) (v : Nat) (hv : v < sys.length) :
    (((genStepN sys (Γ := [])).eval Env.nil) W) v = eqStepEval sys[v] W :=
  selectStep_eval_getElem sys (Env.cons (σ := .nat) v (Env.cons (σ := WTy) W Env.nil))
    (.var (.there .here)) (.var .here) W v hv rfl rfl

/-- Shift every variable index in `F : JExprN` by `offset`. -/
def JExprN.shiftVars (offset : Nat) : JExprN → JExprN
  | .var i => .var (offset + i)
  | .const c => .const c
  | .add a b => .add (a.shiftVars offset) (b.shiftVars offset)
  | .sub a b => .sub (a.shiftVars offset) (b.shiftVars offset)
  | .mul a b => .mul (a.shiftVars offset) (b.shiftVars offset)
  | .integ a => .integ (a.shiftVars offset)

/-- Monotonicity of `JExprN.WF` in the variable bound. -/
theorem JExprN.WF.mono {F : JExprN} {n m : Nat} (hF : F.WF n) (hnm : n ≤ m) : F.WF m := by
  induction F with
  | var i => exact Nat.lt_of_lt_of_le hF hnm
  | const _ => trivial
  | add _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | mul _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | integ _ iha => exact iha hF

/-- Shifting variables by `offset` maps `F.WF n` to `(F.shiftVars offset).WF (offset + n)`. -/
theorem JExprN.shiftVars_wf (F : JExprN) (offset n : Nat) (hF : F.WF n) :
    (F.shiftVars offset).WF (offset + n) := by
  induction F with
  | var i => exact Nat.add_lt_add_left hF offset
  | const _ => trivial
  | add _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | mul _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | integ _ iha => exact iha hF

/-- If `F.WF n` and `w₁.eval e₁, w₂.eval e₂` agree on variables `< n`, then `F.toTm` evaluates identically. -/
theorem JExprN.toTm_eval_of_eq_below (F : JExprN) (n : Nat) (hF : F.WF n)
    {Γ₁ Γ₂ : List Ty} (e₁ : Env Γ₁) (e₂ : Env Γ₂) (w₁ : Tm Γ₁ WTy) (w₂ : Tm Γ₂ WTy)
    (hw : ∀ u < n, w₁.eval e₁ u = w₂.eval e₂ u) :
    (F.toTm w₁).eval e₁ = (F.toTm w₂).eval e₂ := by
  induction F with
  | var i =>
    change w₁.eval e₁ ((natTm i).eval e₁) = w₂.eval e₂ ((natTm i).eval e₂)
    rw [natTm_eval, natTm_eval]
    exact hw i hF
  | const c =>
    dsimp only [JExprN.toTm]
    rw [closedWk_eval c e₁, closedWk_eval c e₂]
  | add _ _ iha ihb =>
    dsimp only [JExprN.toTm, Tm.eval]
    rw [iha hF.1, ihb hF.2]
    rfl
  | sub _ _ iha ihb =>
    dsimp only [JExprN.toTm, Tm.eval]
    rw [iha hF.1, ihb hF.2]
    rfl
  | mul _ _ iha ihb =>
    dsimp only [JExprN.toTm, Tm.eval]
    rw [iha hF.1, ihb hF.2]
    rfl
  | integ _ iha =>
    dsimp only [JExprN.toTm, Tm.eval]
    rw [iha hF]
    rfl

/-- Evaluating `(F.shiftVars offset).toTm w₁` in `e₁` equals evaluating `F.toTm w₂` in `e₂` when `w₁.eval e₁ (offset + u) = w₂.eval e₂ u` for `u < n`. -/
theorem JExprN.shiftVars_toTm_eval (F : JExprN) (offset n : Nat) (hF : F.WF n)
    {Γ₁ Γ₂ : List Ty} (e₁ : Env Γ₁) (e₂ : Env Γ₂) (w₁ : Tm Γ₁ WTy) (w₂ : Tm Γ₂ WTy)
    (hw : ∀ u < n, w₁.eval e₁ (offset + u) = w₂.eval e₂ u) :
    ((F.shiftVars offset).toTm w₁).eval e₁ = (F.toTm w₂).eval e₂ := by
  induction F with
  | var i =>
    change w₁.eval e₁ ((natTm (offset + i)).eval e₁) = w₂.eval e₂ ((natTm i).eval e₂)
    rw [natTm_eval, natTm_eval]
    exact hw i hF
  | const c =>
    dsimp only [JExprN.shiftVars, JExprN.toTm]
    rw [closedWk_eval c e₁, closedWk_eval c e₂]
  | add _ _ iha ihb =>
    dsimp only [JExprN.shiftVars, JExprN.toTm, Tm.eval]
    rw [iha hF.1, ihb hF.2]
    rfl
  | sub _ _ iha ihb =>
    dsimp only [JExprN.shiftVars, JExprN.toTm, Tm.eval]
    rw [iha hF.1, ihb hF.2]
    rfl
  | mul _ _ iha ihb =>
    dsimp only [JExprN.shiftVars, JExprN.toTm, Tm.eval]
    rw [iha hF.1, ihb hF.2]
    rfl
  | integ _ iha =>
    dsimp only [JExprN.shiftVars, JExprN.toTm, Tm.eval]
    rw [iha hF]
    rfl

/-- `eqStepEval p` depends only on variables `< n` when `p.2.WF n`. -/
theorem eqStepEval_of_eq_below (p : Tm [] JetTy × JExprN) (n : Nat) (hp : p.2.WF n)
    (W₁ W₂ : Nat → Nat → Q) (hw : ∀ u < n, W₁ u = W₂ u) :
    eqStepEval p W₁ = eqStepEval p W₂ := by
  unfold eqStepEval
  rw [p.2.toTm_eval_of_eq_below n hp (Env.cons (σ := WTy) W₁ Env.nil)
    (Env.cons (σ := WTy) W₂ Env.nil) (.var .here) (.var .here) hw]

/-- `eqStepEval` on a variable-shifted equation reads the shifted block of `W₁`. -/
theorem eqStepEval_shiftVars (p : Tm [] JetTy × JExprN) (offset n : Nat) (hp : p.2.WF n)
    (W₁ W₂ : Nat → Nat → Q) (hw : ∀ u < n, W₁ (offset + u) = W₂ u) :
    eqStepEval (p.1, p.2.shiftVars offset) W₁ = eqStepEval p W₂ := by
  unfold eqStepEval
  dsimp only
  rw [p.2.shiftVars_toTm_eval offset n hp (Env.cons (σ := WTy) W₁ Env.nil)
    (Env.cons (σ := WTy) W₂ Env.nil) (.var .here) (.var .here) hw]

/-- Evaluating the sum equation `(A₁ + A₂, F₁ + F₂.shiftVars n₁)` on `W` gives the value sum of `eqStepEval p₁ W₁` and `eqStepEval p₂ W₂`. -/
theorem eqStepEval_add_val (p₁ p₂ : Tm [] JetTy × JExprN) (n₁ n₂ : Nat)
    (hp₁ : p₁.2.WF n₁) (hp₂ : p₂.2.WF n₂)
    (W W₁ W₂ : Nat → Nat → Q)
    (hw₁ : ∀ u < n₁, W u = W₁ u) (hw₂ : ∀ u < n₂, W (n₁ + u) = W₂ u) (n : Nat) :
    (eqStepEval (.app (.app tmJetAdd p₁.1) p₂.1, .add p₁.2 (p₂.2.shiftVars n₁)) W n).val =
      (eqStepEval p₁ W₁ n).val + (eqStepEval p₂ W₂ n).val := by
  unfold eqStepEval
  dsimp only [JExprN.toTm, Tm.eval]
  rw [p₁.2.toTm_eval_of_eq_below n₁ hp₁ (Env.cons (σ := WTy) W Env.nil)
        (Env.cons (σ := WTy) W₁ Env.nil) (.var .here) (.var .here) hw₁,
      p₂.2.shiftVars_toTm_eval n₁ n₂ hp₂ (Env.cons (σ := WTy) W Env.nil)
        (Env.cons (σ := WTy) W₂ Env.nil) (.var .here) (.var .here) hw₂]
  set F₁ := (p₁.2.toTm (.var .here)).eval (Env.cons (σ := WTy) W₁ Env.nil)
  set F₂ := (p₂.2.toTm (.var .here)).eval (Env.cons (σ := WTy) W₂ Env.nil)
  cases n with
  | zero =>
    change (Q.add (Q.add (p₁.1.eval Env.nil 0) (p₂.1.eval Env.nil 0)) (Q.ofNat 0)).val =
      (Q.add (p₁.1.eval Env.nil 0) (Q.ofNat 0)).val + (Q.add (p₂.1.eval Env.nil 0) (Q.ofNat 0)).val
    simp only [Q.val_add, Q.val_ofNat]
    ring
  | succ j =>
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    change (Q.add (Q.add (p₁.1.eval Env.nil (j + 1)) (p₂.1.eval Env.nil (j + 1)))
        (Q.div (Q.add (F₁ j) (F₂ j)) (Q.ofNat (j + 1)))).val =
      (Q.add (p₁.1.eval Env.nil (j + 1)) (Q.div (F₁ j) (Q.ofNat (j + 1)))).val +
      (Q.add (p₂.1.eval Env.nil (j + 1)) (Q.div (F₂ j) (Q.ofNat (j + 1)))).val
    rw [Q.val_add, Q.val_add, Q.val_add, Q.val_add,
        Q.val_div _ _ hne, Q.val_div _ _ hne, Q.val_div _ _ hne, Q.val_add]
    ring

/-- Combined system for `f + g`: `sys₁`, `sys₂` with variables shifted by `sys₁.length`, and the sum equation `(A_f + A_g, F_f + F_g.shiftVars sys₁.length)`. -/
def sumSys (sys₁ sys₂ : List (Tm [] JetTy × JExprN)) (v₁ v₂ : Nat)
    (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) : List (Tm [] JetTy × JExprN) :=
  (sys₁ ++ sys₂.map (fun p ↦ (p.1, p.2.shiftVars sys₁.length))) ++
    [(.app (.app tmJetAdd sys₁[v₁].1) sys₂[v₂].1,
      .add sys₁[v₁].2 (sys₂[v₂].2.shiftVars sys₁.length))]

/-- Length of `sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂`. -/
theorem sumSys_length (sys₁ sys₂ : List (Tm [] JetTy × JExprN)) (v₁ v₂ : Nat)
    (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    (sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂).length = sys₁.length + sys₂.length + 1 := by
  simp [sumSys]
  omega

/-- Well-formedness of `sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂`. -/
theorem sumSys_wf (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (hwf₁ : ∀ p ∈ sys₁, p.2.WF sys₁.length) (hwf₂ : ∀ p ∈ sys₂, p.2.WF sys₂.length)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    ∀ p ∈ sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂, p.2.WF (sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂).length := by
  rw [sumSys_length]
  intro p hp
  simp only [sumSys, List.mem_append, List.mem_map, List.mem_singleton] at hp
  rcases hp with (hp₁ | ⟨q, hq, rfl⟩) | rfl
  · exact (hwf₁ p hp₁).mono (by omega)
  · exact (q.2.shiftVars_wf sys₁.length sys₂.length (hwf₂ q hq)).mono (by omega)
  · refine ⟨(hwf₁ sys₁[v₁] (List.getElem_mem hv₁)).mono (by omega), ?_⟩
    exact (sys₂[v₂].2.shiftVars_wf sys₁.length sys₂.length
      (hwf₂ sys₂[v₂] (List.getElem_mem hv₂))).mono (by omega)

/-- Target solution state for `sumSys`: `solN sys₁` on `[0, n₁)`, `solN sys₂` shifted on `[n₁, n₁ + n₂)`, and `solN sys₁ v₁ + solN sys₂ v₂` at `n₁ + n₂`. -/
def sumTargetState (sys₁ sys₂ : List (Tm [] JetTy × JExprN)) (v₁ v₂ : Nat) : Nat → Nat → Q :=
  fun w n ↦
    if w < sys₁.length then solN sys₁ w n
    else if w < sys₁.length + sys₂.length then solN sys₂ (w - sys₁.length) n
    else Q.add (solN sys₁ v₁ n) (solN sys₂ v₂ n)

/-- `sumTargetState` is a value-level fixed point of `genStepN (sumSys ...)`. -/
theorem sumTargetState_fixed (sys₁ sys₂ : List (Tm [] JetTy × JExprN))
    (hwf₁ : ∀ p ∈ sys₁, p.2.WF sys₁.length) (hwf₂ : ∀ p ∈ sys₂, p.2.WF sys₂.length)
    (v₁ v₂ : Nat) (hv₁ : v₁ < sys₁.length) (hv₂ : v₂ < sys₂.length) :
    ∀ w < (sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂).length, ∀ n,
      ((((genStepN (sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂) (Γ := [])).eval Env.nil)
        (sumTargetState sys₁ sys₂ v₁ v₂)) w n).val =
        (sumTargetState sys₁ sys₂ v₁ v₂ w n).val := by
  intro w hw n
  rw [genStepN_eval_getElem _ _ w hw]
  have hw_len : w < sys₁.length + sys₂.length + 1 := by rwa [sumSys_length] at hw
  have hZ₁ : ∀ u < sys₁.length, sumTargetState sys₁ sys₂ v₁ v₂ u = solN sys₁ u := by
    intro u hu; funext m; exact if_pos hu
  have hZ₂ : ∀ u < sys₂.length, sumTargetState sys₁ sys₂ v₁ v₂ (sys₁.length + u) = solN sys₂ u := by
    intro u hu
    funext m
    unfold sumTargetState
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  by_cases hw₁ : w < sys₁.length
  · have hget : (sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂)[w] = sys₁[w] := by
      simp only [sumSys]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hw₁]
    rw [hget, eqStepEval_of_eq_below sys₁[w] sys₁.length (hwf₁ sys₁[w] (List.getElem_mem hw₁)) _ _ hZ₁,
        ← genStepN_eval_getElem sys₁ (solN sys₁) w hw₁]
    unfold sumTargetState
    rw [if_pos hw₁]
    exact solN_fixed sys₁ hwf₁ w hw₁ n
  · by_cases hw₂ : w < sys₁.length + sys₂.length
    · have hu : w - sys₁.length < sys₂.length := by omega
      have hget : (sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂)[w] =
          (sys₂[w - sys₁.length].1, sys₂[w - sys₁.length].2.shiftVars sys₁.length) := by
        simp only [sumSys]
        rw [List.getElem_append_left (by simp; omega),
            List.getElem_append_right (Nat.not_lt.mp hw₁), List.getElem_map]
      rw [hget, eqStepEval_shiftVars sys₂[w - sys₁.length] sys₁.length sys₂.length
            (hwf₂ sys₂[w - sys₁.length] (List.getElem_mem hu)) _ _ hZ₂,
          ← genStepN_eval_getElem sys₂ (solN sys₂) (w - sys₁.length) hu]
      unfold sumTargetState
      rw [if_neg hw₁, if_pos hw₂]
      exact solN_fixed sys₂ hwf₂ (w - sys₁.length) hu n
    · have hw_eq : w = sys₁.length + sys₂.length := by omega
      have hget : (sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂)[w] =
          (.app (.app tmJetAdd sys₁[v₁].1) sys₂[v₂].1,
           .add sys₁[v₁].2 (sys₂[v₂].2.shiftVars sys₁.length)) := by
        simp only [sumSys]
        rw [List.getElem_append_right (by simp; omega)]
        simp [hw_eq]
      rw [hget, eqStepEval_add_val sys₁[v₁] sys₂[v₂] sys₁.length sys₂.length
            (hwf₁ sys₁[v₁] (List.getElem_mem hv₁)) (hwf₂ sys₂[v₂] (List.getElem_mem hv₂))
            _ _ _ hZ₁ hZ₂ n,
          ← genStepN_eval_getElem sys₁ (solN sys₁) v₁ hv₁,
          ← genStepN_eval_getElem sys₂ (solN sys₂) v₂ hv₂,
          solN_fixed sys₁ hwf₁ v₁ hv₁ n, solN_fixed sys₂ hwf₂ v₂ hv₂ n]
      unfold sumTargetState
      rw [if_neg hw₁, if_neg hw₂, Q.val_add]

/-- **Closure under `+`.** -/
theorem InUniverse_add (f g : Nat → Q) (hf : InUniverse f) (hg : InUniverse g) :
    InUniverse (fun n ↦ Q.add (f n) (g n)) := by
  rcases hf with ⟨sys₁, hwf₁, v₁, hv₁, hf_val⟩
  rcases hg with ⟨sys₂, hwf₂, v₂, hv₂, hg_val⟩
  let S := sumSys sys₁ sys₂ v₁ v₂ hv₁ hv₂
  have hwfS := sumSys_wf sys₁ sys₂ hwf₁ hwf₂ v₁ v₂ hv₁ hv₂
  have hvS : sys₁.length + sys₂.length < S.length := by
    rw [sumSys_length]
    exact Nat.lt_succ_self _
  refine ⟨S, hwfS, sys₁.length + sys₂.length, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (sumTargetState sys₁ sys₂ v₁ v₂)
    (sumTargetState_fixed sys₁ sys₂ hwf₁ hwf₂ v₁ v₂ hv₁ hv₂)
    (n + 1) (sys₁.length + sys₂.length) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (Q.add (f n) (g n)).val =
    ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
      (sys₁.length + sys₂.length) n).val
  rw [huniq]
  unfold sumTargetState
  rw [if_neg (by omega), if_neg (by omega), Q.val_add, Q.val_add, hf_val n, hg_val n]

#print axioms solN_fixed
#print axioms InUniverse_add

end HAomega
