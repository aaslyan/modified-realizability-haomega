/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Core.Extraction

/-!
# Soundness: every derivation extracts a realizer

The main theorem of the milestone's logical half: for every derivation
`D : Deriv Γ φ`, environment `ρ`, and context assignment `env` realizing
`Γ` (`CtxR`), the extracted family realizes `φ` at every ambient level
above `derivBound D`.  Proof by induction on the derivation; each case
invokes the corresponding named combinator's behavior, with the
transports supplying hypothesis families at binders (`FR_famOf`), the
substitution lemma at `∀`-elimination, and environment congruence at
`∀`-introduction.

Two "small" inductions live here, each invoked exactly once by the big
one: `MR_indRecC` (closure of `MR` under primitive recursion along
`succ`, rule `ind`) and `MR_tiRecC` (closure under transfinite recursion
along `≺`, rule `tiEps0`).
-/

namespace Realizability

open ContinuousFunctionals

/-- Context realization is stable under environment changes away from
the context's free variables. -/
theorem CtxR_congr {ρ ρ' : ℕ → ℕ} :
    ∀ (Γ : List Formula) (env : List Fam),
      (∀ ψ ∈ Γ, ∀ z, ψ.FreeIn z → ρ z = ρ' z) →
      CtxR ρ Γ env → CtxR ρ' Γ env := by
  intro Γ
  induction Γ with
  | nil => intro env _ _; trivial
  | cons ψ Γ ih =>
    intro env h hc
    refine ⟨?_, ih env.tail (fun χ hχ ↦ h χ (List.mem_cons_of_mem _ hχ)) hc.2⟩
    intro n hn
    exact (MR_congr ψ n _ (h ψ (List.mem_cons_self ..))).mp (hc.1 n hn)

/-- **Closure of `MR` under primitive recursion, uniformly in the
ambient level** — the new theorem of the induction extension: the
pure-type counterpart of the recursor's realizing clause in the
soundness of modified realizability for induction (Troelstra 1973; see
docs/first-order/STATUS.md for the exact citation).  Stated once for every ambient `m`,
per the level-free-core discipline; no level-by-level instances exist.

This is the **"small" induction**: ordinary natural-number induction on
the numeral `k` being realized, at a fixed ambient `m`, strictly nested
inside the "big" induction over `Deriv` that `soundness` performs
(which invokes this lemma exactly once, in its `ind` case).  The
iteration never changes ambient level: `MR`'s `→` clause consumes and
produces realizers at the same level, so the step realizer `b` —
consumed through the `∀` clause at ambient `m + 2` and the `→` clause
at `m + 1` — sends ambient-`m` realizers of `φ(k)` to ambient-`m`
realizers of `φ(succ k)`.  The substitution lemma converts between
`φ(0)` / `φ(succ x)` under `ρ` and `φ` under the updated environment at
both ends of each step. -/
theorem MR_indRecC {ρ : ℕ → ℕ} {x : ℕ} {φ : Formula}
    (hok : Formula.SubstOK (.succ (.var x)) φ) {m : ℕ}
    {a : PureType (m + 1)} {b : PureType (m + 3)}
    (ha : MR ρ (φ.subst x .zero) m a)
    (hb : MR ρ (.all x (φ.imp (φ.subst x (.succ (.var x))))) (m + 2) b) :
    ∀ k : ℕ, MR (Function.update ρ x k) φ m (indRecC a b k) := by
  intro k
  -- The small induction: on the numeral, at the fixed ambient `m`.
  induction k with
  | zero =>
    have h0 : Formula.SubstOK Term.zero φ := fun y hy ↦ by
      simp [Term.vars] at hy
    exact (MR_subst φ h0 ρ m a).mp ha
  | succ k ih =>
    -- One step: the `∀` clause of `hb` at the numeral `k`, then the
    -- `→` clause at the induction hypothesis.
    have hstep := hb k (indRecC a b k) ih
    have hconv := (MR_subst φ hok (Function.update ρ x k) m _).mp hstep
    have heval : Term.eval (Function.update ρ x k) (.succ (.var x))
        = k + 1 := by
      show Function.update ρ x k x + 1 = k + 1
      simp [Function.update]
    rw [heval, Function.update_idem] at hconv
    exact hconv

/-- **Closure of `MR` under transfinite recursion along `≺`** — the new
theorem of the Phase-C extension, and the exact counterpart of
`MR_indRecC` one level of recursion up: if `b` realizes the
progressiveness premise

    ∀x. (∀y. y ≺ x → φ(y)) → φ(x)

then the recursor's value at every notation code `k` realizes `φ(x)`
under `x ↦ k`.  Proved by **well-founded induction in Lean along `≺`**
(`oLt_wf`), the "small" induction of this rule — strictly nested inside
`soundness`'s big induction over `Deriv`, exactly as `MR_indRecC`'s
numeral induction is.

Three things are worth naming, since they are what makes the proof go:

* the hypothesis `y ≺ x` is an *equation* of the fragment, so its
  realizers carry no content — realizing it **is** the fact
  `oltN j k = 1`, i.e. `OLt j k`, which is precisely the descent the
  well-founded induction needs.  The rule's computational content is
  therefore entirely in the recursion, none of it in the order premise;
* the two `dropR φ` transports are forced by levels, not by taste: the
  premise's antecedent is itself a `∀→` pair, so it consumes realizers
  of `φ(y)` two ambient levels below the level at which the recursion
  produces them.  Hence the hypothesis `lvl φ ≤ m₂` and
  `derivBound`'s `lvl φ + 2`;
* the side conditions are each used once — `x ≠ y` to read `x`'s value
  through the inner binder, `SubstOK` for `MR_subst`, and `y` not free
  in `φ` for the `MR_congr` step that discards the inner binder's
  assignment. -/
theorem MR_tiRecC {ρ : ℕ → ℕ} {x y : ℕ} {φ : Formula}
    (hxy : x ≠ y) (hok : Formula.SubstOK (.var y) φ) (hfree : ¬ φ.FreeIn y)
    {m₂ : ℕ} (hlvl : lvl φ ≤ m₂) {b : PureType (m₂ + 5)}
    (hb : MR ρ (Formula.all x
      ((Formula.all y ((Formula.eq (.prec (.var y) (.var x)) (.succ .zero)).imp
        (φ.subst x (.var y)))).imp φ)) (m₂ + 4) b) :
    ∀ k : ℕ, MR (Function.update ρ x k) φ (m₂ + 2) (tiRecC φ b k) := by
  intro k
  refine oLt_wf.induction
    (C := fun k ↦ MR (Function.update ρ x k) φ (m₂ + 2) (tiRecC φ b k)) k ?_
  intro k ih
  rw [tiRecC_eq]
  -- The premise at the code `k`, then its `→` clause: it wants a
  -- realizer of progressiveness *at* `k`, which is what we build.
  refine hb k _ ?_
  intro j
  rw [app₁_abs₁]
  intro w hw
  rw [app₁_abs₁]
  -- Realizing the order premise *is* the descent `j ≺ k`.
  have hjk : OLt j k := by
    have hw' : Term.eval (Function.update (Function.update ρ x k) y j)
        (.prec (.var y) (.var x))
        = Term.eval (Function.update (Function.update ρ x k) y j)
          (.succ .zero) := hw
    show OLt j k
    refine oltN_eq_one_iff.mp ?_
    have hx : Function.update (Function.update ρ x k) y j x = k := by
      simp [Function.update, hxy]
    have hy : Function.update (Function.update ρ x k) y j y = j := by
      simp [Function.update]
    show oltN j k = 1
    simpa [Term.eval, hx, hy] using hw'
  rw [show natPT (m₂ + 2) j (defaultPT (m₂ + 1)) = j from rfl, if_pos hjk]
  -- The recursive value, transported down the two ambient levels the
  -- premise's nested binder pair costs.
  have hrec := ih j hjk
  have hd₁ : MR (Function.update ρ x j) φ (m₂ + 1) (dropR φ (tiRecC φ b j)) :=
    (MR_liftR_dropR φ (Function.update ρ x j) (m₂ + 1) (by omega)).2 _ hrec
  have hd₂ : MR (Function.update ρ x j) φ m₂
      (dropR φ (dropR φ (tiRecC φ b j))) :=
    (MR_liftR_dropR φ (Function.update ρ x j) m₂ hlvl).2 _ hd₁
  -- `φ(y)` under the inner environment is `φ` under `x ↦ j`: the
  -- substitution lemma, then environment congruence (`y` is not free).
  rw [MR_subst φ hok _ m₂ _]
  refine (MR_congr φ m₂ _ ?_).mp hd₂
  intro z hz
  by_cases hzx : z = x
  · subst hzx
    simp [Function.update, Term.eval]
  · have hzy : z ≠ y := fun h ↦ hfree (h ▸ hz)
    show Function.update ρ x j z
      = Function.update (Function.update (Function.update ρ x k) y j) x
          (Term.eval (Function.update (Function.update ρ x k) y j) (.var y)) z
    simp [Function.update, hzx, hzy]

/-- **Soundness of extraction** for the fragment: derivable formulas are
realized by their extracted families, above the derivation's bound. -/
theorem soundness {Γ : List Formula} {φ : Formula} (D : Deriv Γ φ) :
    ∀ (ρ : ℕ → ℕ) (env : List Fam), CtxR ρ Γ env →
      ∀ n, derivBound D ≤ n → MR ρ φ n (extract D ρ env n) := by
  induction D with
  | ax =>
    intro ρ env henv n hn
    exact henv.1 n hn
  | wk D ih =>
    intro ρ env henv n hn
    exact ih ρ env.tail henv.2 n hn
  | @andI Γ φ ψ D₁ D₂ ih₁ ih₂ =>
    intro ρ env henv n hn
    have hb : max (derivBound D₁) (derivBound D₂) ≤ n := hn
    refine ⟨?_, ?_⟩
    · show MR ρ φ n (fstPT (pairPT (extract D₁ ρ env n) (extract D₂ ρ env n)))
      rw [fstPT_pairPT]
      exact ih₁ ρ env henv n (by omega)
    · show MR ρ ψ n (sndPT (pairPT (extract D₁ ρ env n) (extract D₂ ρ env n)))
      rw [sndPT_pairPT]
      exact ih₂ ρ env henv n (by omega)
  | andE₁ D ih =>
    intro ρ env henv n hn
    exact (ih ρ env henv n hn).1
  | andE₂ D ih =>
    intro ρ env henv n hn
    exact (ih ρ env henv n hn).2
  | @orI₁ Γ φ ψ D ih =>
    intro ρ env henv n hn
    left
    refine ⟨?_, ?_⟩
    · show fstPT (pairPT (fun _ ↦ (0 : ℕ)) (extract D ρ env n))
        (defaultPT n) = 0
      rw [fstPT_pairPT]
    · show MR ρ φ n (sndPT (pairPT (fun _ ↦ (0 : ℕ)) (extract D ρ env n)))
      rw [sndPT_pairPT]
      exact ih ρ env henv n hn
  | @orI₂ Γ φ ψ D ih =>
    intro ρ env henv n hn
    right
    refine ⟨?_, ?_⟩
    · show fstPT (pairPT (fun _ ↦ (1 : ℕ)) (extract D ρ env n))
        (defaultPT n) ≠ 0
      rw [fstPT_pairPT]
      exact one_ne_zero
    · show MR ρ ψ n (sndPT (pairPT (fun _ ↦ (1 : ℕ)) (extract D ρ env n)))
      rw [sndPT_pairPT]
      exact ih ρ env henv n hn
  | @orE Γ φ ψ χ D D₁ D₂ ih ih₁ ih₂ =>
    intro ρ env henv n hn
    have hb : max (max (derivBound D) (max (lvl φ) (lvl ψ)))
        (max (derivBound D₁) (derivBound D₂)) ≤ n := hn
    have hmaj := ih ρ env henv n (by omega)
    show MR ρ χ n
      (if fstPT (extract D ρ env n) (defaultPT n) = 0 then
        extract D₁ ρ (famOf φ (sndPT (extract D ρ env n)) :: env) n
      else
        extract D₂ ρ (famOf ψ (sndPT (extract D ρ env n)) :: env) n)
    by_cases htag : fstPT (extract D ρ env n) (defaultPT n) = 0
    · rw [if_pos htag]
      rcases hmaj with ⟨-, hp⟩ | ⟨hne, -⟩
      · exact ih₁ ρ (famOf φ (sndPT (extract D ρ env n)) :: env)
          ⟨FR_famOf φ ρ (by omega) _ hp, henv⟩ n (by omega)
      · exact absurd htag hne
    · rw [if_neg htag]
      rcases hmaj with ⟨heq, -⟩ | ⟨-, hp⟩
      · exact absurd heq htag
      · exact ih₂ ρ (famOf ψ (sndPT (extract D ρ env n)) :: env)
          ⟨FR_famOf ψ ρ (by omega) _ hp, henv⟩ n (by omega)
  | @impI Γ φ ψ D ih =>
    intro ρ env henv n hn
    have hb : max (derivBound D) (lvl φ) + 1 ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show MR ρ ψ m
        (app₁ (abs₁ fun z ↦ extract D ρ (famOf φ z :: env) m) x)
      rw [app₁_abs₁]
      exact ih ρ (famOf φ x :: env)
        ⟨FR_famOf φ ρ (by omega) x hx, henv⟩ m (by omega)
  | impE D₁ D₂ ih₁ ih₂ =>
    intro ρ env henv n hn
    have hb : max (derivBound D₁) (derivBound D₂) ≤ n := hn
    exact ih₁ ρ env henv (n + 1) (by omega) _ (ih₂ ρ env henv n (by omega))
  | botE D ih =>
    intro ρ env henv n hn
    exact (ih ρ env henv n hn).elim
  | @allI Γ y φ D hfresh ih =>
    intro ρ env henv n hn
    have hb : derivBound D + 1 ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro k
      show MR (Function.update ρ y k) φ m
        (app₁ (abs₁ fun z ↦
          extract D (Function.update ρ y (z (defaultPT m))) env m)
          (natPT (m + 1) k))
      rw [app₁_abs₁]
      show MR (Function.update ρ y k) φ m
        (extract D (Function.update ρ y (natPT (m + 1) k (defaultPT m)))
          env m)
      rw [show natPT (m + 1) k (defaultPT m) = k from rfl]
      refine ih (Function.update ρ y k) env
        (CtxR_congr Γ env (fun ψ hψ z hz ↦ ?_) henv) m (by omega)
      by_cases hzy : z = y
      · exact absurd (hzy ▸ hz) (hfresh ψ hψ)
      · simp [Function.update, hzy]
  | @allE Γ y φ u D hok ih =>
    intro ρ env henv n hn
    rw [MR_subst φ hok ρ n _]
    exact ih ρ env henv (n + 1) (by
      have hb : derivBound D ≤ n := hn
      omega) (u.eval ρ)
  | @ind Γ x φ D₁ D₂ hok ih₁ ih₂ =>
    -- The "big"-induction case: unfold the `allIC` packaging, then hand
    -- everything to the "small" induction `MR_indRecC`, instantiated at
    -- the premises' extracted families (base at ambient `m`, step at
    -- ambient `m + 2`).
    intro ρ env henv n hn
    have hb : max (derivBound D₁) (derivBound D₂) + 1 ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro k
      show MR (Function.update ρ x k) φ m
        (app₁ (abs₁ fun z ↦
          indRecC (extract D₁ ρ env m) (extract D₂ ρ env (m + 2))
            (z (defaultPT m)))
          (natPT (m + 1) k))
      rw [app₁_abs₁]
      show MR (Function.update ρ x k) φ m
        (indRecC (extract D₁ ρ env m) (extract D₂ ρ env (m + 2))
          (natPT (m + 1) k (defaultPT m)))
      rw [show natPT (m + 1) k (defaultPT m) = k from rfl]
      exact MR_indRecC hok (ih₁ ρ env henv m (by omega))
        (ih₂ ρ env henv (m + 2) (by omega)) k
  | eqDec s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases hdec : decide (s.eval ρ = t.eval ρ) with
      | true =>
        have heq : Term.eval ρ s = Term.eval ρ t := of_decide_eq_true hdec
        show MR ρ _ (m + 1) (eqDecC (decide (s.eval ρ = t.eval ρ)) (m + 1))
        rw [hdec]
        left
        refine ⟨?_, heq⟩
        show fstPT (pairPT (fun _ ↦ (0 : ℕ)) (defaultPT (m + 2)))
          (defaultPT (m + 1)) = 0
        rw [fstPT_pairPT]
      | false =>
        have hne : ¬ (Term.eval ρ s = Term.eval ρ t) :=
          of_decide_eq_false hdec
        show MR ρ _ (m + 1) (eqDecC (decide (s.eval ρ = t.eval ρ)) (m + 1))
        rw [hdec]
        right
        refine ⟨?_, ?_⟩
        · show fstPT (pairPT (fun _ ↦ (1 : ℕ)) (defaultPT (m + 2)))
            (defaultPT (m + 1)) ≠ 0
          rw [fstPT_pairPT]
          exact one_ne_zero
        · intro x hx
          exact absurd (hx : Term.eval ρ s = Term.eval ρ t) hne
  | succNeZero s =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      exact absurd hx (Nat.succ_ne_zero _)
  | succInj s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show (Term.eval ρ s) = (Term.eval ρ t)
      have hx' : Term.eval ρ s + 1 = Term.eval ρ t + 1 := hx
      omega
  -- Phase A: the equational-logic kit — atomic conclusions carry no
  -- content, so each case is the equation's truth from its premises'.
  | eqRefl t =>
    intro ρ env henv n hn
    show Term.eval ρ t = Term.eval ρ t
    rfl
  | eqSymm s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show Term.eval ρ t = Term.eval ρ s
      exact (hx : Term.eval ρ s = Term.eval ρ t).symm
  | eqTrans s t u =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show Term.eval ρ s = Term.eval ρ u
        exact (hx : Term.eval ρ s = Term.eval ρ t).trans
          (hy : Term.eval ρ t = Term.eval ρ u)
  | eqCongSucc s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show Term.eval ρ s + 1 = Term.eval ρ t + 1
      have hx' : Term.eval ρ s = Term.eval ρ t := hx
      omega
  | eqCongPlus s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show Term.eval ρ s₁ + Term.eval ρ s₂
          = Term.eval ρ t₁ + Term.eval ρ t₂
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongTimes s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show Term.eval ρ s₁ * Term.eval ρ s₂
          = Term.eval ρ t₁ * Term.eval ρ t₂
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  -- Phase A: the first-argument recursion equations, true in `ℕ`.
  | zeroPlus t =>
    intro ρ env henv n hn
    show 0 + Term.eval ρ t = Term.eval ρ t
    omega
  | succPlus s t =>
    intro ρ env henv n hn
    show Term.eval ρ s + 1 + Term.eval ρ t = Term.eval ρ s + Term.eval ρ t + 1
    omega
  | zeroTimes t =>
    intro ρ env henv n hn
    show 0 * Term.eval ρ t = 0
    exact Nat.zero_mul _
  | succTimes s t =>
    intro ρ env henv n hn
    show (Term.eval ρ s + 1) * Term.eval ρ t
      = Term.eval ρ s * Term.eval ρ t + Term.eval ρ t
    exact Nat.succ_mul _ _
  -- Phase B: the recursion equations for `pred`/`exp`, true in `ℕ` …
  | predZero =>
    intro ρ env henv n hn
    show 0 - 1 = 0
    rfl
  | predSucc s =>
    intro ρ env henv n hn
    show Term.eval ρ s + 1 - 1 = Term.eval ρ s
    omega
  | expZero s =>
    intro ρ env henv n hn
    show Term.eval ρ s ^ 0 = 0 + 1
    exact Nat.pow_zero _
  | expSucc s t =>
    intro ρ env henv n hn
    show Term.eval ρ s ^ (Term.eval ρ t + 1)
      = Term.eval ρ s ^ Term.eval ρ t * Term.eval ρ s
    exact Nat.pow_succ ..
  -- … the two `bump` axioms (absorption at zero is the fueled
  -- function's base case; the numeral graph is its own graph) …
  | bumpZero s =>
    intro ρ env henv n hn
    show bumpN (Term.eval ρ s) 0 = 0
    rfl
  | bumpNum k n' =>
    intro ρ env henv n hn
    show bumpN ((numeral k).eval ρ) ((numeral n').eval ρ)
      = (numeral (bumpN k n')).eval ρ
    rw [numeral_eval, numeral_eval, numeral_eval]
  -- … the Goodstein recursion, which is `goodN`'s own definition …
  | goodZero s =>
    intro ρ env henv n hn
    show goodN (Term.eval ρ s) 0 = Term.eval ρ s
    rfl
  | goodSucc s t =>
    intro ρ env henv n hn
    show goodN (Term.eval ρ s) (Term.eval ρ t + 1)
      = bumpN (Term.eval ρ t + 1 + 1) (goodN (Term.eval ρ s) (Term.eval ρ t)) - 1
    rfl
  -- … and the congruence schemas.
  | eqCongPred s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show Term.eval ρ s - 1 = Term.eval ρ t - 1
      rw [(hx : Term.eval ρ s = Term.eval ρ t)]
  | eqCongExp s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show Term.eval ρ s₁ ^ Term.eval ρ s₂
          = Term.eval ρ t₁ ^ Term.eval ρ t₂
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongBump s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show bumpN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = bumpN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongGood s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show goodN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = goodN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  -- Phase C: the transfinite-induction rule — unfold the `allIC`
  -- packaging (as in the `ind` case) and hand everything to the small
  -- induction `MR_tiRecC`.
  | @tiEps0 Γ x y φ D hxy hok hfree ih =>
    intro ρ env henv n hn
    have hbnd : max (derivBound D) (lvl φ + 2) + 1 ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        cases m' with
        | zero => omega
        | succ m₂ =>
          intro k
          show MR (Function.update ρ x k) φ (m₂ + 2)
            (app₁ (abs₁ fun z ↦
              tiFamAt φ (extract D ρ env) (z (defaultPT (m₂ + 2))) (m₂ + 2))
              (natPT (m₂ + 3) k))
          rw [app₁_abs₁,
            show natPT (m₂ + 3) k (defaultPT (m₂ + 2)) = k from rfl]
          exact MR_tiRecC hxy hok hfree (by omega)
            (ih ρ env henv (m₂ + 4) (by omega)) k
  -- Phase C: the order's numeral graph is its own graph, and its
  -- congruence schema is one more true-equation case.
  | precNum a b =>
    intro ρ env henv n hn
    show oltN ((numeral a).eval ρ) ((numeral b).eval ρ)
      = (numeral (oltN a b)).eval ρ
    rw [numeral_eval, numeral_eval, numeral_eval]
  -- Phase D5: the three properties of the ordinal assignment the fragment
  -- imports.  Each soundness case is exactly one Phase-D1 theorem — the
  -- composite descent that D2 imported is now *derived* in the fragment
  -- (`OrdinalDescent.lean`), so `ordOf_descent` no longer appears here.
  | ordBump b n =>
    intro ρ env henv nn hn
    show ordOf (Term.eval ρ b + 1 + 1 + 1)
        (bumpN (Term.eval ρ b + 1 + 1) (Term.eval ρ n))
      = ordOf (Term.eval ρ b + 1 + 1) (Term.eval ρ n)
    exact ordOf_bumpN (by omega) _
  | ordPredLt b n =>
    intro ρ env henv nn hn
    have hb : (2 : ℕ) ≤ nn := hn
    cases nn with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx
        have hne : Term.eval ρ n ≠ 0 := by
          intro h0
          exact (hx (defaultPT (m' + 1)) h0).elim
        show oltN (ordOf (Term.eval ρ b + 1 + 1) (Term.eval ρ n - 1))
          (ordOf (Term.eval ρ b + 1 + 1) (Term.eval ρ n)) = 0 + 1
        exact oltN_eq_one_iff.mpr (olt_ordOf_of_lt (by omega) (by omega))
  | bumpNeZero b n =>
    intro ρ env henv nn hn
    have hb : (2 : ℕ) ≤ nn := hn
    cases nn with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        have hne : Term.eval ρ n ≠ 0 := by
          intro h0
          exact (hx (defaultPT (m' + 1)) h0).elim
        have hy' : bumpN (Term.eval ρ b + 1 + 1) (Term.eval ρ n) = 0 := hy
        exact absurd hy' (bumpN_ne_zero (by omega) hne)
  | eqCongOrd s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show ordOf (Term.eval ρ s₁) (Term.eval ρ s₂)
          = ordOf (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  -- Phase D0: `∃`-introduction pairs the witness with the payload …
  | @exI Γ x φ u D hok ih =>
    intro ρ env henv n hn
    show MR (Function.update ρ x
        (fstPT (pairPT (natPT (n + 1) (u.eval ρ)) (extract D ρ env n))
          (defaultPT n))) φ n
      (sndPT (pairPT (natPT (n + 1) (u.eval ρ)) (extract D ρ env n)))
    rw [fstPT_pairPT, sndPT_pairPT]
    show MR (Function.update ρ x (u.eval ρ)) φ n (extract D ρ env n)
    exact (MR_subst φ hok ρ n _).mp (ih ρ env henv n hn)
  -- … and `∃`-elimination consumes it: the witness goes into the
  -- environment, the payload becomes the hypothesis family (`FR_famOf`,
  -- exactly as in the `orE` case), freshness moves the context across the
  -- environment change (`CtxR_congr`), and non-occurrence in the
  -- conclusion moves the result back (`MR_congr`).
  | @exE Γ x φ ψ D₁ D₂ hfresh hnf ih₁ ih₂ =>
    intro ρ env henv n hn
    have hb : max (max (derivBound D₁) (lvl φ)) (derivBound D₂) ≤ n := hn
    have hmaj := ih₁ ρ env henv n (by omega)
    show MR ρ ψ n
      (extract D₂ (Function.update ρ x
        (fstPT (extract D₁ ρ env n) (defaultPT n)))
        (famOf φ (sndPT (extract D₁ ρ env n)) :: env) n)
    refine (MR_congr ψ n _ (fun z hz ↦ ?_)).mp
      (ih₂ (Function.update ρ x (fstPT (extract D₁ ρ env n) (defaultPT n)))
        (famOf φ (sndPT (extract D₁ ρ env n)) :: env)
        ⟨FR_famOf φ _ (by omega) _ hmaj,
          CtxR_congr Γ env (fun χ hχ z hz ↦ ?_) henv⟩ n (by omega))
    · have hzx : z ≠ x := fun h ↦ hnf (h ▸ hz)
      simp [Function.update, hzx]
    · have hzx : z ≠ x := fun h ↦ absurd (h ▸ hz) (hfresh χ hχ)
      simp [Function.update, hzx]
  | eqCongPrec s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show oltN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = oltN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  -- Phase H4: the Hydra layer.  The two battle equations are `hydraSeqN`'s
  -- own definition; the descent schema is Phase H3's theorem, read on
  -- codes, with "not dead" spelled as "code ≠ 0" (`hydraOf_eq_leaf_iff`).
  | hydraZero s =>
    intro ρ env henv n hn
    show hydraSeqN (Term.eval ρ s) 0 = Term.eval ρ s
    exact hydraSeqN_zero _
  | hydraSucc s t =>
    intro ρ env henv n hn
    show hydraSeqN (Term.eval ρ s) (Term.eval ρ t + 1)
      = hydraStepN (Term.eval ρ t + 1) (hydraSeqN (Term.eval ρ s) (Term.eval ρ t))
    exact hydraSeqN_succ _ _
  | hordCutLt nT c =>
    intro ρ env henv nn hn
    have hb : (2 : ℕ) ≤ nn := hn
    cases nn with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx
        have hne : Term.eval ρ c ≠ 0 := by
          intro h0
          exact (hx (defaultPT (m' + 1)) h0).elim
        show oltN (ordOfHydraN (hydraStepN (Term.eval ρ nT) (Term.eval ρ c)))
          (ordOfHydraN (Term.eval ρ c)) = 0 + 1
        exact oltN_eq_one_iff.mpr (olt_ordOfHydraN_step _ _ hne)
  | hcutNum k c =>
    intro ρ env henv n hn
    show hydraStepN ((numeral k).eval ρ) ((numeral c).eval ρ)
      = (numeral (hydraStepN k c)).eval ρ
    rw [numeral_eval, numeral_eval, numeral_eval]
  | eqCongHcut s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show hydraStepN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = hydraStepN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongHydra s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show hydraSeqN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = hydraSeqN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongHord s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show ordOfHydraN (Term.eval ρ s) = ordOfHydraN (Term.eval ρ t)
      rw [(hx : Term.eval ρ s = Term.eval ρ t)]
  -- Phase E2: the Hanoi layer.  The two `solves` schemas are exactly the
  -- two value-level theorems of `Hanoi.lean`; the two `mvcount` ones are
  -- the length function's own equations.  Nothing here is about ordinals.
  | solvesZero f t v =>
    intro ρ env henv n hn
    show solvesN 0 (Term.eval ρ f) (Term.eval ρ t) (Term.eval ρ v) 0 = 0 + 1
    rfl
  | solvesSucc nT f t v k₁ k₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        have h₁ : solvesN (Term.eval ρ nT) (Term.eval ρ f) (Term.eval ρ v)
            (Term.eval ρ t) (Term.eval ρ k₁) = 1 := hx
        have h₂ : solvesN (Term.eval ρ nT) (Term.eval ρ v) (Term.eval ρ t)
            (Term.eval ρ f) (Term.eval ρ k₂) = 1 := hy
        show solvesN (Term.eval ρ nT + 1) (Term.eval ρ f) (Term.eval ρ t)
          (Term.eval ρ v)
          (happN (Term.eval ρ k₁)
            (hconsN (Term.eval ρ f * (numeral 3).eval ρ + Term.eval ρ t)
              (Term.eval ρ k₂))) = 0 + 1
        rw [numeral_eval]
        exact solvesN_succ h₁ h₂
  | mvcountNil =>
    intro ρ env henv n hn
    show hlen 0 = 0
    rfl
  | mvcountApp k₁ m k₂ =>
    intro ρ env henv n hn
    show hlen (happN (Term.eval ρ k₁) (hconsN (Term.eval ρ m) (Term.eval ρ k₂))) + 1
      = (hlen (Term.eval ρ k₁) + 1) + (hlen (Term.eval ρ k₂) + 1)
    rw [hlen_happN, hlen_cons]
    omega
  | eqCongHcons s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show hconsN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = hconsN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongHapp s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show happN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = happN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongMvcount s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show hlen (Term.eval ρ s) = hlen (Term.eval ρ t)
      rw [(hx : Term.eval ρ s = Term.eval ρ t)]
  | eqCongSolves n₁ n₂ f₁ f₂ t₁ t₂ v₁ v₂ k₁ k₂ =>
    intro ρ env henv n hn
    have hb : (5 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ a =>
      cases a with
      | zero => omega
      | succ b =>
        cases b with
        | zero => omega
        | succ c =>
          cases c with
          | zero => omega
          | succ d =>
            cases d with
            | zero => omega
            | succ e =>
              intro w hw x hx y hy z hz u hu
              show solvesN (Term.eval ρ n₁) (Term.eval ρ f₁) (Term.eval ρ t₁)
                  (Term.eval ρ v₁) (Term.eval ρ k₁)
                = solvesN (Term.eval ρ n₂) (Term.eval ρ f₂) (Term.eval ρ t₂)
                  (Term.eval ρ v₂) (Term.eval ρ k₂)
              rw [(hw : Term.eval ρ n₁ = Term.eval ρ n₂),
                (hx : Term.eval ρ f₁ = Term.eval ρ f₂),
                (hy : Term.eval ρ t₁ = Term.eval ρ t₂),
                (hz : Term.eval ρ v₁ = Term.eval ρ v₂),
                (hu : Term.eval ρ k₁ = Term.eval ρ k₂)]

  -- Phase F2: the Pascal layer.  All four `pas` equations are `pasN`'s
  -- own definition, and `xorNum` is `xorN`'s graph on numerals.
  | pasZeroZero =>
    intro ρ env henv n hn
    show pasN 0 0 = 0 + 1
    rfl
  | pasZeroSucc k =>
    intro ρ env henv n hn
    show pasN 0 (Term.eval ρ k + 1) = 0
    rfl
  | pasSuccZero nT =>
    intro ρ env henv n hn
    show pasN (Term.eval ρ nT + 1) 0 = 0 + 1
    rfl
  | pasSuccSucc nT k =>
    intro ρ env henv n hn
    show pasN (Term.eval ρ nT + 1) (Term.eval ρ k + 1)
      = xorN (pasN (Term.eval ρ nT) (Term.eval ρ k))
          (pasN (Term.eval ρ nT) (Term.eval ρ k + 1))
    rfl
  | xorNum a b =>
    intro ρ env henv n hn
    show xorN ((numeral a).eval ρ) ((numeral b).eval ρ)
      = (numeral (xorN a b)).eval ρ
    rw [numeral_eval, numeral_eval, numeral_eval]
  | eqCongXor s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show xorN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = xorN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongPas s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show pasN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = pasN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | lookNum a b =>
    intro ρ env henv n hn
    show lookN ((numeral a).eval ρ) ((numeral b).eval ρ)
      = (numeral (lookN a b)).eval ρ
    rw [numeral_eval, numeral_eval, numeral_eval]
  | eqCongLook s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show lookN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = lookN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  -- Fibonacci: the three defining equations are `fibN`'s own recursion
  -- (`fibN_succ_succ` is `rfl`), the congruence is unary like `eqCongPred`.
  | fibZero =>
    intro ρ env henv n hn
    show fibN 0 = 0
    rfl
  | fibOne =>
    intro ρ env henv n hn
    show fibN (0 + 1) = 0 + 1
    rfl
  | fibSucc s =>
    intro ρ env henv n hn
    show fibN (Term.eval ρ s + 1 + 1)
      = fibN (Term.eval ρ s) + fibN (Term.eval ρ s + 1)
    rfl
  | eqCongFib s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show fibN (Term.eval ρ s) = fibN (Term.eval ρ t)
      rw [(hx : Term.eval ρ s = Term.eval ρ t)]

end Realizability
