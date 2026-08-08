/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Extraction

/-!
# HA^ω, part 5: soundness

    soundness : (D : Deriv Δ φ) → Realizes Δ e ε → MR φ e ((extract D).eval ε)

Indexing `Formula` by its realizer type (part 2) is what made this reachable:
`MR_subst` / `MR_subst1` are cast-free, and `extract` contains no casts at all.
Before that redesign the eight substitution-instance rules could not even have
their obligations stated without relating `cast` along an opaque type equality
to casts on subformula components.

## The invariant

`Realizes Δ e ε` says the realizer environment `ε` agrees with `e` on the
object variables and supplies a realizer for each hypothesis of `Δ`.
-/

namespace HAomega

/-- **The soundness invariant.** -/
def Realizes : {Γ : List Ty} → {as : List Ty} → Ctx Γ as → Env Γ →
    Env (as ++ Γ) → Prop
  | _, _, .nil, e, ε => ∀ τ v, ε τ v = e τ v
  | _, _, .cons φ Δ, e, ε =>
      MR φ e (ε _ .here) ∧ Realizes Δ e (fun τ v ↦ ε τ (.there v))

/-- Under the invariant, an object term evaluates the same in the realizer
environment as in the object environment.  Needed by `allE`, `exI` and
`eqDec`, which inject object terms into the realizer. -/
theorem Realizes.eval_wkList : {Γ : List Ty} → {as : List Ty} →
    (Δ : Ctx Γ as) → (e : Env Γ) → (ε : Env (as ++ Γ)) → Realizes Δ e ε →
    ∀ {τ : Ty} (u : Tm Γ τ), (u.rename (Ren.wkList as)).eval ε = u.eval e := by
  intro Γ as Δ
  induction Δ with
  | nil =>
      intro e ε h τ u
      rw [Tm.eval_rename]
      have : (fun (σ : Ty) (v : Var Γ σ) ↦ ε σ (Ren.wkList [] σ v)) = e := by
        funext σ v; exact h σ v
      rw [this]
  | cons φ Δ ih =>
      intro e ε h τ u
      rw [Tm.eval_rename]
      have := ih e (fun σ v ↦ ε σ (.there v)) h.2 u
      rw [Tm.eval_rename] at this
      exact this

/-! ## Support lemmas for the cast-free cases

`eval_predT` … `eval_eqTest` verify that the System T decision terms `extract`
emits for `eqDec` really decide numeric equality — the one axiom with
computational content, so the one place extraction has to produce a genuine
algorithm rather than `star`.

`Realizes.exch` transports the invariant across `allI`'s context exchange: the
only rule that has to move a freshly bound object variable past the hypothesis
block. -/


theorem eval_predT {Γ : List Ty} (e : Env Γ) (n : Nat) :
    (Tm.predT (Γ := Γ)).eval e n = n - 1 := by cases n <;> rfl

theorem eval_subT {Γ : List Ty} (e : Env Γ) (x y : Nat) :
    (Tm.subT (Γ := Γ)).eval e x y = x - y := by
  induction y with
  | zero => rfl
  | succ k ih =>
      have h : (Tm.subT (Γ := Γ)).eval e x (k+1)
             = (Tm.subT (Γ := Γ)).eval e x k - 1 := by
        simp only [Tm.subT, Tm.eval, Env.cons, eval_predT]
      rw [h, ih]; exact Nat.sub_sub x k 1

theorem eval_isPos {Γ : List Ty} (e : Env Γ) (n : Nat) :
    (Tm.isPos (Γ := Γ)).eval e n = if n = 0 then 0 else 1 := by
  cases n <;> rfl

theorem eval_eqTest {Γ : List Ty} (e : Env Γ) (s t : Tm Γ .nat) :
    (Tm.eqTest s t).eval e = if s.eval e = t.eval e then 0 else 1 := by
  show (Tm.isPos (Γ := Γ)).eval e _ = _
  rw [eval_isPos]
  simp only [Tm.eval, eval_subT]
  -- isolate the arithmetic on plain `Nat`s, where `omega` can see it
  have key : ∀ a b : Nat, (if a - b + (b - a) = 0 then 0 else 1)
      = (if a = b then 0 else 1) := by
    intro a b
    by_cases hab : a = b
    · simp [hab]
    · have : a - b + (b - a) ≠ 0 := by omega
      rw [if_neg this, if_neg hab]
  exact key (s.eval e) (t.eval e)

theorem env_exch_step {Γ as : List Ty} {τ a : Ty} (v : τ.interp)
    (ε : Env (a :: (as ++ Γ))) (σ : Ty) (u : Var (τ :: (as ++ Γ)) σ) :
    Env.cons v (fun σ w ↦ ε σ w.there) σ u
      = Env.cons v ε σ ((Ren.wk a).ext σ u) := by
  cases u <;> rfl

theorem Realizes.exch : {Γ : List Ty} → {as : List Ty} → (Δ : Ctx Γ as) →
    (e : Env Γ) → (ε : Env (as ++ Γ)) → Realizes Δ e ε → {τ : Ty} →
    (v : τ.interp) →
    Realizes (Δ.wk (σ := τ)) (Env.cons v e)
      (fun σ w ↦ (Env.cons v ε) σ (Ren.exch as σ w)) := by
  intro Γ as Δ
  induction Δ with
  | nil =>
      intro e ε h τ v σ w
      cases w with
      | here => rfl
      | there w => exact h σ w
  | cons φ Δ ih =>
      intro e ε h τ v
      refine ⟨(MR_wk φ v e _).mpr h.1, ?_⟩
      have hrec := ih e (fun σ w ↦ ε σ (.there w)) h.2 v
      refine cast (congrArg _ ?_) hrec
      funext σ w
      exact env_exch_step v ε σ (Ren.exch _ σ w)


/-! ## Soundness

Every derivation's extracted term realizes its conclusion.  One case per rule,
28 of them, no wildcard. -/


theorem Realizes.congrEnv : {Γ : List Ty} → {as : List Ty} → (Δ : Ctx Γ as) →
    (e : Env Γ) → (ε ε' : Env (as ++ Γ)) → (∀ τ v, ε τ v = ε' τ v) →
    Realizes Δ e ε → Realizes Δ e ε' := by
  intro Γ as Δ
  induction Δ with
  | nil => intro e ε ε' hee h τ v; rw [← hee]; exact h τ v
  | cons φ Δ ih =>
      intro e ε ε' hee h
      exact ⟨by rw [← hee]; exact h.1,
             ih e _ _ (fun τ v ↦ hee τ (.there v)) h.2⟩

theorem soundness : {Γ : List Ty} → {as : List Ty} → {Δ : Ctx Γ as} → {a : Ty} →
    {φ : Formula Γ a} → (D : Deriv Δ φ) → ∀ (e : Env Γ) (ε : Env (as ++ Γ)),
      Realizes Δ e ε → MR φ e ((extract D).eval ε) := by
  intro Γ as Δ a φ D
  induction D with
  | ax => intro e ε h; exact h.1
  | wk D ih =>
      intro e ε h
      show MR _ e (((extract D).rename (Ren.wk _)).eval ε)
      rw [Tm.eval_rename]
      exact ih e _ h.2
  | andI D₁ D₂ ih₁ ih₂ => intro e ε h; exact ⟨ih₁ e ε h, ih₂ e ε h⟩
  | andE₁ D ih => intro e ε h; exact (ih e ε h).1
  | andE₂ D ih => intro e ε h; exact (ih e ε h).2
  | orI₁ D ih => intro e ε h; exact ⟨fun _ ↦ ih e ε h, fun hne ↦ absurd rfl hne⟩
  | orI₂ D ih =>
      intro e ε h
      exact ⟨fun h0 ↦ (Nat.succ_ne_zero 0 h0).elim, fun _ ↦ ih e ε h⟩
  | orE D D₁ D₂ ih₀ ih₁ ih₂ =>
      intro e ε h
      have h0 := ih₀ e ε h
      show MR _ e (Nat.rec _ _ ((Tm.fst (extract D)).eval ε))
      rw [Tm.eval_subst1]
      cases htag : (Tm.fst (extract D)).eval ε with
      | zero =>
          exact ih₁ e _ ⟨h0.1 htag,
            Realizes.congrEnv _ e ε _ (fun _ _ ↦ rfl) h⟩
      | succ k =>
          have htag' : ((extract D).eval ε).1 = k + 1 := htag
          show MR _ e ((((extract D₂).subst1 _).wk.wk).eval _)
          simp only [Tm.wk, Tm.eval_wk]
          rw [Tm.eval_subst1]
          exact ih₂ e _ ⟨h0.2 (by rw [htag']; simp),
            Realizes.congrEnv _ e ε _ (fun _ _ ↦ rfl) h⟩
  | impI D ih => intro e ε h z hz; exact ih e _ ⟨hz, h⟩
  | impE D₁ D₂ ih₁ ih₂ => intro e ε h; exact ih₁ e ε h _ (ih₂ e ε h)
  | botE D ih => intro e ε h; exact (ih e ε h).elim
  | allI D ih =>
      intro e ε h v
      show MR _ _ (((extract D).rename (Ren.exch _)).eval (Env.cons v ε))
      rw [Tm.eval_rename]
      exact ih _ _ (Realizes.exch _ e ε h v)
  | allE u D ih =>
      intro e ε h
      refine (MR_subst1 _ u e _).mpr ?_
      show MR _ _ (((extract D).eval ε) _)
      rw [Realizes.eval_wkList _ e ε h u]
      exact ih e ε h _
  | exI u D ih =>
      intro e ε h
      show MR _ (Env.cons (((u.rename _)).eval ε) e) _
      rw [Realizes.eval_wkList _ e ε h u]
      exact (MR_subst1 _ u e _).mp (ih e ε h)
  | exE D₁ D₂ ih₁ ih₂ =>
      intro e ε h
      have hp := ih₁ e ε h
      refine (MR_wk _ (((extract D₁).eval ε).1) e _).mp ?_
      show MR _ _ (((extract D₂).rename (Ren.exch _)).eval _)
      rw [Tm.eval_rename]
      refine ih₂ _ _ ⟨hp, ?_⟩
      refine Realizes.congrEnv _ _ _ _ ?_ (Realizes.exch _ e ε h _)
      intro σ w
      exact env_exch_step (((extract D₁).eval ε).1)
        (Env.cons (((extract D₁).eval ε).2) ε) σ (Ren.exch _ σ w)
  | ind D₁ D₂ ih₁ ih₂ =>
      intro e ε h n
      show MR _ _ (Nat.rec _ _ n)
      simp only [Tm.wk, Tm.eval_wk]
      induction n with
      | zero => exact (MR_subst1 _ .zero e _).mp (ih₁ e ε h)
      | succ k ihk =>
          have hstep := ih₂ e ε h k _ ihk
          have hsub := (MR_subst _ Sub.succHere (Env.cons k e) _).mp hstep
          refine MR_congrEnv _ _ _ ?_ _ hsub
          intro σ w; cases w <;> rfl
  | tiEps0 D ih =>
      intro e ε h
      have hstep := ih e ε h
      show ∀ n : ℕ, MR _ _
        (tiRecVal (((extract D).wk).eval (Env.cons (σ := .nat) n ε)) n)
      simp only [Tm.wk, Tm.eval_wk]
      intro n
      induction n using Realizability.oLt_wf.induction with
      | _ x ihx =>
          rw [tiRecVal]
          refine hstep x _ ?_
          intro y u hy
          have hOLt : Realizability.OLt y x := Realizability.oltN_eq_one_iff.mp hy
          simp only [dif_pos hOLt]
          refine (MR_rename _ _ _ _).mpr ?_
          refine MR_congrEnv _ _ _ ?_ _ (ihx y hOLt)
          intro σ w; cases w <;> rfl
  | eqRefl t => intro e ε h; rfl
  | eqSubst φ D₁ D₂ ih₁ ih₂ =>
      intro e ε h
      have heq := ih₁ e ε h
      refine (MR_subst1 _ _ e _).mpr ?_
      have := (MR_subst1 _ _ e _).mp (ih₂ e ε h)
      rwa [heq] at this
  | convBeta b u => intro e ε h; exact (Tm.eval_subst1 b u e).symm
  | convRecZero z s => intro e ε h; rfl
  | convRecSucc z s n => intro e ε h; rfl
  | convAddZero x => intro e ε h; rfl
  | convAddSucc x y => intro e ε h; rfl
  | convFst x y => intro e ε h; rfl
  | convSnd x y => intro e ε h; rfl
  | succNeZero t => intro e ε h z hz; exact Nat.succ_ne_zero _ hz
  | succInj s t => intro e ε h z hz; exact Nat.succ.inj hz
  | eqDec s t =>
      intro e ε h
      simp only [extract, Tm.eval, eval_eqTest,
        Realizes.eval_wkList _ e ε h]
      by_cases hst : s.eval e = t.eval e
      · exact ⟨fun _ ↦ hst, fun hne ↦ absurd (if_pos hst) hne⟩
      · refine ⟨fun h0 ↦ ?_, fun _ _ hc ↦ hst hc⟩
        rw [if_neg hst] at h0
        simp at h0


#print axioms Realizes.eval_wkList
#print axioms eval_eqTest
#print axioms Realizes.exch
#print axioms soundness

end HAomega
