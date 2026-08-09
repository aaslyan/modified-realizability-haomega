/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Soundness
import ContinuousFunctionals.Hierarchy

/-!
# HA^ω, part 6: continuity

Every extracted program denotes a **continuous** functional.

## The bridge problem, and how it is solved

The vendored Kleene–Kreisel development is indexed by *pure-type level*:

    PureType : ℕ → Type          PureType 0 = ℕ,  PureType (n+1) = PureType n → ℕ
    Ct : (n : ℕ) → Set (PureType n)

That tower has no products and no general arrows, while HA^ω's realizers live
at arbitrary `Ty`.  Indexing `Ct` by `Ty` directly would mean generalising
`Assoc` upstream.

The way through is the device the first-order development already uses for its
generic continuity theorem: instead of constructing **associates**, carry an
*oracle-parameterized logical relation*.  `Tracked τ X` says that `X`, a family
of type-`τ` objects varying over an oracle `α`, stays continuous in `α` however
it is applied to other tracked families.  Continuity at base type is
`Continuous2` — the vendored notion — and everything else is the logical
relation built over it.  No associate is ever constructed, so the pure-type
tower's shape never has to be matched.

Because `Tracked` recurses on `Ty`, products and general arrows are handled by
their own clauses.  That is the bridge: `Continuous2` supplies the base case,
and the finite-type structure is carried by the relation rather than by `Ct`'s
index.

## Why this induction is small

The first-order `GenericContinuity.lean` is 1304 lines, because it must prove a
preservation lemma for each of ~40 extraction combinators.  Here the realizer is
a **System T term**, so the induction runs over the constructors of `Tm`, one
case per constructor —
and `extract_continuous` is then a corollary of `eval_tracked` applied to the
extracted term.  The rules never appear.
-/

namespace HAomega

open ContinuousFunctionals

/-! ## Continuity at base type -/

/-- Constants are continuous. -/
theorem continuous2_const (c : ℕ) : Continuous2 fun _ ↦ c :=
  fun _ ↦ ⟨0, fun _ _ ↦ rfl⟩

/-- Any binary operation applied to two continuous families is continuous.
Covers `succ` (with a dummy second argument) and `add`. -/
theorem continuous2_binop {F G : (ℕ → ℕ) → ℕ} (op : ℕ → ℕ → ℕ)
    (hF : Continuous2 F) (hG : Continuous2 G) :
    Continuous2 fun α ↦ op (F α) (G α) := by
  intro α
  obtain ⟨m, hm⟩ := hF α
  obtain ⟨n, hn⟩ := hG α
  refine ⟨Nat.max m n, fun β hβ ↦ ?_⟩
  show op (F α) (G α) = op (F β) (G β)
  rw [hm β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)),
    hn β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))]

/-- The ternary analogue of `continuous2_binop`, for the three-argument
surgery primitive `hcutAt`. -/
theorem continuous2_ternop {F G H : (ℕ → ℕ) → ℕ} (op : ℕ → ℕ → ℕ → ℕ)
    (hF : Continuous2 F) (hG : Continuous2 G) (hH : Continuous2 H) :
    Continuous2 fun α ↦ op (F α) (G α) (H α) := by
  intro α
  obtain ⟨m, hm⟩ := hF α
  obtain ⟨n, hn⟩ := hG α
  obtain ⟨k, hk⟩ := hH α
  refine ⟨Nat.max m (Nat.max n k), fun β hβ ↦ ?_⟩
  show op (F α) (G α) (H α) = op (F β) (G β) (H β)
  rw [hm β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)),
    hn β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))),
    hk β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))]

/-- **Applying a continuously-computed numeral index.**  If `k` is continuous
and every fixed index gives a continuous family, so does the varying index.
This is the fact the recursor needs, and the only place continuity of the
*scrutinee* is used. -/
theorem continuous2_apply_nat {k : (ℕ → ℕ) → ℕ} {G : (ℕ → ℕ) → ℕ → ℕ}
    (hk : Continuous2 k) (hG : ∀ j, Continuous2 fun α ↦ G α j) :
    Continuous2 fun α ↦ G α (k α) := by
  intro α
  obtain ⟨m, hm⟩ := hk α
  obtain ⟨n, hn⟩ := hG (k α) α
  refine ⟨Nat.max m n, fun β hβ ↦ ?_⟩
  show G α (k α) = G β (k β)
  have hkβ : k α = k β := hm β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
  have hGβ : G α (k α) = G β (k α) :=
    hn β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))
  rw [hGβ, hkβ]

/-! ## Continuity into an arbitrary value type

`Continuous2` lands in `ℕ`; the typed ordinal layer needs the same notion for
families landing in `Eps0`.  `ContAt σ` is that notion, and `ContAt ℕ` is
`Continuous2` **definitionally** — so the vendored base case is untouched and
the ordinal clauses reuse these lemmas verbatim. -/

/-- Continuity of a family landing in an arbitrary type. -/
def ContAt (σ : Type) (F : (ℕ → ℕ) → σ) : Prop :=
  ∀ α : ℕ → ℕ, ∃ n : ℕ, ∀ β : ℕ → ℕ, (∀ i < n, α i = β i) → F α = F β

theorem contAt_const {σ : Type} (c : σ) : ContAt σ (fun _ ↦ c) :=
  fun _ ↦ ⟨0, fun _ _ ↦ rfl⟩

theorem contAt_binop {σ τ ρ : Type} {F : (ℕ → ℕ) → σ} {G : (ℕ → ℕ) → τ}
    (op : σ → τ → ρ) (hF : ContAt σ F) (hG : ContAt τ G) :
    ContAt ρ (fun α ↦ op (F α) (G α)) := by
  intro α
  obtain ⟨m, hm⟩ := hF α
  obtain ⟨n, hn⟩ := hG α
  refine ⟨Nat.max m n, fun β hβ ↦ ?_⟩
  show op (F α) (G α) = op (F β) (G β)
  rw [hm β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)),
    hn β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))]

/-- Applying a continuously-computed index, at arbitrary index and value
types.  Generalises `continuous2_apply_nat`. -/
theorem contAt_apply {ι σ : Type} {k : (ℕ → ℕ) → ι} {G : (ℕ → ℕ) → ι → σ}
    (hk : ContAt ι k) (hG : ∀ j, ContAt σ fun α ↦ G α j) :
    ContAt σ fun α ↦ G α (k α) := by
  intro α
  obtain ⟨m, hm⟩ := hk α
  obtain ⟨n, hn⟩ := hG (k α) α
  refine ⟨Nat.max m n, fun β hβ ↦ ?_⟩
  show G α (k α) = G β (k β)
  have hkβ : k α = k β :=
    hm β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
  have hGβ : G α (k α) = G β (k α) :=
    hn β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))
  rw [hGβ, hkβ]

/-! ## The logical relation -/

/-- **`Tracked τ X`** — the oracle-parameterized logical relation.

`X : (ℕ → ℕ) → τ.interp` is a family of type-`τ` objects varying over an
oracle.  At base type this is exactly the vendored `Continuous2`; at function
types it is closure under application to tracked families, which is what lets
the proof avoid constructing associates. -/
def Tracked : (τ : Ty) → ((ℕ → ℕ) → τ.interp) → Prop
  | .unit, _ => True
  | .nat, X => Continuous2 X
  | .ord, X => ContAt Eps0 X
  | .prod a b, X => Tracked a (fun α ↦ (X α).1) ∧ Tracked b (fun α ↦ (X α).2)
  | .arrow a b, X => ∀ Y, Tracked a Y → Tracked b (fun α ↦ X α (Y α))

/-- **Evaluating the oracle at a continuously-computed point is continuous.**
The fact that makes the identity family tracked at type 1, and the only place
the oracle is inspected. -/
theorem continuous2_eval {Z : (ℕ → ℕ) → ℕ} (hZ : Continuous2 Z) :
    Continuous2 fun α ↦ α (Z α) := by
  intro α
  obtain ⟨n, hn⟩ := hZ α
  refine ⟨Nat.max n (Z α + 1), fun β hβ ↦ ?_⟩
  show α (Z α) = β (Z β)
  have hZβ : Z α = Z β :=
    hn β fun i hi ↦ hβ i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
  have hval : α (Z α) = β (Z α) :=
    hβ (Z α) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
  rw [hval, hZβ]

/-- **Applying a continuously-computed numeral index, at every finite type.**
The level-free analogue of the first-order `tracked_apply_nat`. -/
theorem tracked_apply {ι : Type} : (τ : Ty) → {k : (ℕ → ℕ) → ι} →
    {G : (ℕ → ℕ) → ι → τ.interp} → ContAt ι k →
    (∀ j, Tracked τ fun α ↦ G α j) → Tracked τ fun α ↦ G α (k α)
  | .unit, _, _, _, _ => trivial
  | .nat, _, _, hk, hG => contAt_apply hk hG
  | .ord, _, _, hk, hG => contAt_apply hk hG
  | .prod a b, _, _, hk, hG =>
      ⟨tracked_apply (ι := ι) a hk fun j ↦ (hG j).1,
       tracked_apply (ι := ι) b hk fun j ↦ (hG j).2⟩
  | .arrow _ b, _, _, hk, hG =>
      fun Y hY ↦ tracked_apply (ι := ι) b hk fun j ↦ hG j Y hY

/-- The numeral-index instance, the one every `recNat`/`tiRec` case uses.
Fixing `ι` matters: with it a metavariable the higher-order unifier can solve
`k` against the *environment* family instead of the intended index. -/
theorem tracked_apply_nat (τ : Ty) {k : (ℕ → ℕ) → ℕ}
    {G : (ℕ → ℕ) → ℕ → τ.interp} (hk : Continuous2 k)
    (hG : ∀ j, Tracked τ fun α ↦ G α j) : Tracked τ fun α ↦ G α (k α) :=
  tracked_apply τ hk hG

/-- The ordinal-index instance, for `tiRecE`. -/
theorem tracked_apply_ord (τ : Ty) {k : (ℕ → ℕ) → Eps0}
    {G : (ℕ → ℕ) → Eps0 → τ.interp} (hk : ContAt Eps0 k)
    (hG : ∀ j, Tracked τ fun α ↦ G α j) : Tracked τ fun α ↦ G α (k α) :=
  tracked_apply τ hk hG

/-- **The canonical values are tracked.**  Needed by `tiRec`: when the
re-decided order test fails, the recursor returns `Ty.dfltVal`, and that branch
must be tracked too.

Note this is *not* "constant families are tracked" — that is false at arrow
types, since a constant *function* applied to a varying argument need not be
constant.  It holds for `dfltVal` specifically because `dfltVal` at an arrow is
the constantly-`dfltVal` function. -/
theorem tracked_dflt : (τ : Ty) → Tracked τ (fun _ ↦ τ.dfltVal)
  | .unit => trivial
  | .nat => continuous2_const 0
  | .ord => contAt_const Eps0.zero
  | .prod a b => ⟨tracked_dflt a, tracked_dflt b⟩
  | .arrow _ b => fun _ _ ↦ tracked_dflt b

/-! ## Every System T term is tracked -/

/-- An environment family is tracked when each variable's value is. -/
def TrackedEnv {Γ : List Ty} (E : (ℕ → ℕ) → Env Γ) : Prop :=
  ∀ (τ : Ty) (v : Var Γ τ), Tracked τ fun α ↦ E α τ v

/-- **Every System T term denotes a tracked family.**

One case per constructor of `Tm`.  `recNat` is the only one that needs
a closure fact — `tracked_apply_nat`, to absorb the oracle-dependent recursion
depth — and the fixed-depth statement it consumes is an ordinary induction on
the numeral. -/
theorem eval_tracked {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ (E : (ℕ → ℕ) → Env Γ), TrackedEnv E → Tracked τ fun α ↦ t.eval (E α) := by
  induction t with
  | var v => intro E hE; exact hE _ v
  | lam b ih =>
      intro E hE Y hY
      refine ih (fun α ↦ Env.cons (Y α) (E α)) ?_
      intro σ w
      cases w with
      | here => exact hY
      | there w => exact hE σ w
  | app f a ihf iha => intro E hE; exact ihf E hE _ (iha E hE)
  | star => intro E hE; trivial
  | pair a b iha ihb => intro E hE; exact ⟨iha E hE, ihb E hE⟩
  | fst t ih => intro E hE; exact (ih E hE).1
  | snd t ih => intro E hE; exact (ih E hE).2
  | zero => intro E hE; exact continuous2_const 0
  | succ t ih =>
      intro E hE
      exact continuous2_binop (fun x _ ↦ x + 1) (ih E hE) (continuous2_const 0)
  | add a b iha ihb =>
      intro E hE
      exact continuous2_binop (· + ·) (iha E hE) (ihb E hE)
  | prec a b iha ihb =>
      intro E hE
      exact continuous2_binop Realizability.oltN (iha E hE) (ihb E hE)
  | pred a ih =>
      intro E hE
      exact continuous2_binop (fun x _ ↦ Nat.pred x) (ih E hE) (continuous2_const 0)
  | bump a b iha ihb =>
      intro E hE
      exact continuous2_binop Realizability.bumpN (iha E hE) (ihb E hE)
  | good a b iha ihb =>
      intro E hE
      exact continuous2_binop Realizability.goodN (iha E hE) (ihb E hE)
  | ord a b iha ihb =>
      intro E hE
      exact continuous2_binop Realizability.ordOf (iha E hE) (ihb E hE)
  | hcut a b iha ihb =>
      intro E hE
      exact continuous2_binop Realizability.hydraStepN (iha E hE) (ihb E hE)
  | hcutAt p a b ihp iha ihb =>
      intro E hE
      exact continuous2_ternop playAtN (ihp E hE) (iha E hE) (ihb E hE)
  | ezero => intro E hE; exact contAt_const _
  | orde a b iha ihb =>
      intro E hE
      exact contAt_binop ordE (iha E hE) (ihb E hE)
  | olte a b iha ihb =>
      intro E hE
      exact contAt_binop Eps0.oltNE (iha E hE) (ihb E hE)
  | tiRecE s n ihs ihn =>
      intro E hE
      refine tracked_apply_ord _ (ihn E hE) fun j ↦ ?_
      induction j using Eps0.oLtE_wf.induction with
      | _ x ihx =>
          have hEq : (fun α ↦ tiRecEVal (s.eval (E α)) x)
              = fun α ↦ s.eval (E α) x (fun y _ ↦
                  if h : Eps0.OLtE y x then tiRecEVal (s.eval (E α)) y
                  else Ty.dfltVal _) := by
            funext α; rw [tiRecEVal]
          rw [hEq]
          refine ihs E hE (fun _ ↦ x) (contAt_const x) _ ?_
          intro Y hY U _
          show Tracked _ fun α ↦
            dite (Eps0.OLtE (Y α) x)
              (fun _ ↦ tiRecEVal (s.eval (E α)) (Y α))
              (fun _ ↦ Ty.dfltVal _)
          refine tracked_apply_ord _ (k := Y)
            (G := fun α y ↦ dite (Eps0.OLtE y x)
              (fun _ ↦ tiRecEVal (s.eval (E α)) y) (fun _ ↦ Ty.dfltVal _))
            hY fun y ↦ ?_
          by_cases hyx : Eps0.OLtE y x
          · simp only [dif_pos hyx]; exact ihx y hyx
          · simp only [dif_neg hyx]; exact tracked_dflt _
  | hydra a b iha ihb =>
      intro E hE
      exact continuous2_binop Realizability.hydraSeqN (iha E hE) (ihb E hE)
  | hord a ih =>
      intro E hE
      exact continuous2_binop (fun x _ ↦ Realizability.ordOfHydraN x)
        (ih E hE) (continuous2_const 0)
  | tiRec s n ihs ihn =>
      intro E hE
      refine tracked_apply_nat _ (ihn E hE) fun j ↦ ?_
      induction j using Realizability.oLt_wf.induction with
      | _ x ihx =>
          have hEq : (fun α ↦ tiRecVal (s.eval (E α)) x)
              = fun α ↦ s.eval (E α) x (fun y _ ↦
                  if h : Realizability.OLt y x then tiRecVal (s.eval (E α)) y
                  else Ty.dfltVal _) := by
            funext α; rw [tiRecVal]
          rw [hEq]
          refine ihs E hE (fun _ ↦ x) (continuous2_const x) _ ?_
          intro Y hY U _
          show Tracked _ fun α ↦
            dite (Realizability.OLt (Y α) x)
              (fun _ ↦ tiRecVal (s.eval (E α)) (Y α))
              (fun _ ↦ Ty.dfltVal _)
          refine tracked_apply_nat _ (k := Y)
            (G := fun α y ↦ dite (Realizability.OLt y x)
              (fun _ ↦ tiRecVal (s.eval (E α)) y) (fun _ ↦ Ty.dfltVal _))
            hY fun y ↦ ?_
          by_cases hyx : Realizability.OLt y x
          · simp only [dif_pos hyx]; exact ihx y hyx
          · simp only [dif_neg hyx]; exact tracked_dflt _
  | recNat z s n ihz ihs ihn =>
      intro E hE
      refine tracked_apply_nat _ (ihn E hE) fun j ↦ ?_
      induction j with
      | zero => exact ihz E hE
      | succ k ihk =>
          exact ihs E hE (fun _ ↦ k) (continuous2_const k) _ ihk

/-! ## The continuity theorem -/

/-- **Every extracted program is continuous.**

The realizer of a closed derivation denotes a tracked family at its realizer
type — for any oracle, since a closed term ignores it. -/
theorem extract_tracked {a : Ty} {φ : Formula [] a} (D : Deriv Ctx.nil φ) :
    Tracked a fun _ ↦ (extract D).eval Env.nil :=
  eval_tracked (extract D) (fun _ ↦ Env.nil) (fun _ v ↦ nomatch v)

/-- **The type-2 corollary.**  For a theorem quantifying over a function
variable, the extracted realizer is a continuous type-2 functional in the
vendored sense — so it has a class in `Ct 2`. -/
theorem extract_continuous2 {φ : Formula [] (.arrow (.arrow .nat .nat) .nat)}
    (D : Deriv Ctx.nil φ) :
    Continuous2 ((extract D).eval Env.nil) := by
  exact extract_tracked D (fun α ↦ α) (fun _ hZ ↦ continuous2_eval hZ)

#print axioms eval_tracked
#print axioms extract_tracked
#print axioms extract_continuous2

end HAomega
