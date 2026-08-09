/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Core.Extraction

/-!
# Generic continuity: every extracted realizer is continuous

The theorem closing the gap flagged in docs/first-order/STATUS.md: for **every** closed
derivation `D : Deriv [] φ`, the extracted type-2 realizer
`extract D ρ [] 1` is continuous (`Continuous2`), so `RealizesCtQ`
applies uniformly — no per-derivation certificate.

## The invariant

The compositional invariant is *not* "the extract has an associate at
every ambient" (that is the parent project's deferred countability
chapter, whose hard core is associate-level abstraction closure).  It is
the **oracle-parameterized continuity relation**, a logical relation on
families indexed by a Baire-space oracle `α`:

* a family `X : (ℕ → ℕ) → PureType 0` is *tracked* iff it is
  `Continuous2`;
* a family `X : (ℕ → ℕ) → PureType (n + 1)` is *tracked* iff its
  pointwise application to every tracked family of arguments is a
  continuous function of the oracle.

Tracking says nothing about any single functional `X α` in isolation —
it constrains only the ways a number can be read out of the family
through continuously supplied arguments.  That is exactly what the
capstone needs (`extract D ρ [] 1` applied to the tracked identity
family `α ↦ α` *is* the extract as a functional of `α`), and it is
closed under abstraction *by β-reduction*: `abs₁ G` applied to a tracked
argument family literally computes `G` at tracked components, so the
`impIC`/`allIC` cases cost nothing beyond the closure lemmas for the
pairing devices.  This is the classical relative-continuity argument
(the Kripke logical relation over the oracle) — it sidesteps associate
construction entirely, which is why the level-≤1 restriction of the
brief is not even needed: continuity of the extract holds for every
closed derivation, at every ambient the capstone consults.

## Contents

* `Continuous2` closure lemmas (constants, composition, diagonal
  evaluation, pointwise case split);
* `Tracked`, with closure under every pure-type device of
  `ModifiedRealizes.lean` (`up`/`down`, `pairPT`/`fstPT`/`sndPT`,
  `app₁`/`abs₁`, `natPT`, `defaultPT`);
* tracking preservation for the transports of `Transport.lean`
  (`liftR`/`dropR` by the same mutual formula induction as
  `MR_liftR_dropR`, then `liftIter`/`dropIter`/`famOf`);
* **one named preservation lemma per extraction combinator** (the same
  per-rule discipline as `Extraction.lean` — one lemma per rule, listed
  in docs/first-order/STATUS.md);
* `extract_tracked` — the induction on `Deriv` threading the invariant;
* **`extract_continuous`** — the capstone.
-/

namespace Realizability

open ContinuousFunctionals

/-! ## Closure lemmas for `Continuous2` -/

/-- Constant functions are continuous. -/
theorem continuous2_const (c : ℕ) : Continuous2 fun _ ↦ c :=
  fun _ ↦ ⟨0, fun _ _ ↦ rfl⟩

/-- Post-composition with any function of the value preserves
continuity. -/
theorem continuous2_comp₁ (g : ℕ → ℕ) {X : (ℕ → ℕ) → ℕ}
    (hX : Continuous2 X) : Continuous2 fun α ↦ g (X α) := by
  intro α
  obtain ⟨N, hN⟩ := hX α
  refine ⟨N, fun β hβ ↦ ?_⟩
  show g (X α) = g (X β)
  rw [hN β hβ]

/-- Binary composition: any function of two continuously computed
values is continuous. -/
theorem continuous2_comp₂ (g : ℕ → ℕ → ℕ) {X Y : (ℕ → ℕ) → ℕ}
    (hX : Continuous2 X) (hY : Continuous2 Y) :
    Continuous2 fun α ↦ g (X α) (Y α) := by
  intro α
  obtain ⟨N₁, h₁⟩ := hX α
  obtain ⟨N₂, h₂⟩ := hY α
  refine ⟨N₁ + N₂, fun β hβ ↦ ?_⟩
  show g (X α) (Y α) = g (X β) (Y β)
  rw [h₁ β fun i hi ↦ hβ i (by omega), h₂ β fun i hi ↦ hβ i (by omega)]

/-- Five-fold composition — the arity Phase E2's `solves` symbol needs.
Same proof as `continuous2_comp₂`, with five moduli summed. -/
theorem continuous2_comp₅ (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    {X₁ X₂ X₃ X₄ X₅ : (ℕ → ℕ) → ℕ}
    (h₁ : Continuous2 X₁) (h₂ : Continuous2 X₂) (h₃ : Continuous2 X₃)
    (h₄ : Continuous2 X₄) (h₅ : Continuous2 X₅) :
    Continuous2 fun α ↦ g (X₁ α) (X₂ α) (X₃ α) (X₄ α) (X₅ α) := by
  intro α
  obtain ⟨N₁, e₁⟩ := h₁ α
  obtain ⟨N₂, e₂⟩ := h₂ α
  obtain ⟨N₃, e₃⟩ := h₃ α
  obtain ⟨N₄, e₄⟩ := h₄ α
  obtain ⟨N₅, e₅⟩ := h₅ α
  refine ⟨N₁ + N₂ + N₃ + N₄ + N₅, fun β hβ ↦ ?_⟩
  show g (X₁ α) (X₂ α) (X₃ α) (X₄ α) (X₅ α)
    = g (X₁ β) (X₂ β) (X₃ β) (X₄ β) (X₅ β)
  rw [e₁ β fun i hi ↦ hβ i (by omega), e₂ β fun i hi ↦ hβ i (by omega),
    e₃ β fun i hi ↦ hβ i (by omega), e₄ β fun i hi ↦ hβ i (by omega),
    e₅ β fun i hi ↦ hβ i (by omega)]

/-- Diagonal evaluation: reading the oracle at a continuously computed
position is continuous. -/
theorem continuous2_eval {X : (ℕ → ℕ) → ℕ} (hX : Continuous2 X) :
    Continuous2 fun α ↦ α (X α) := by
  intro α
  obtain ⟨N, hN⟩ := hX α
  refine ⟨N + X α + 1, fun β hβ ↦ ?_⟩
  have hXβ : X α = X β := hN β fun i hi ↦ hβ i (by omega)
  have hval : α (X α) = β (X α) := hβ (X α) (by omega)
  show α (X α) = β (X β)
  rw [← hXβ, ← hval]

/-- Consulting a `ℕ`-indexed family of continuous functionals at a
continuously computed index is continuous: near any oracle the index is
locally constant, so the diagonal locally agrees with one member of the
family.  This is the countably-branching generalization of the binary
case split `continuous2_ite` below, added for rule `ind`, whose
iteration count is read off the oracle. -/
theorem continuous2_apply_nat {k : (ℕ → ℕ) → ℕ} {G : (ℕ → ℕ) → ℕ → ℕ}
    (hk : Continuous2 k) (hG : ∀ j, Continuous2 fun α ↦ G α j) :
    Continuous2 fun α ↦ G α (k α) := by
  intro α
  obtain ⟨N₁, h₁⟩ := hk α
  obtain ⟨N₂, h₂⟩ := hG (k α) α
  refine ⟨N₁ + N₂, fun β hβ ↦ ?_⟩
  have hkβ : k α = k β := h₁ β fun i hi ↦ hβ i (by omega)
  show G α (k α) = G β (k β)
  rw [← hkβ]
  exact h₂ β fun i hi ↦ hβ i (by omega)

/-- Pointwise case split on the equality of two continuously computed
scrutinees preserves continuity. -/
theorem continuous2_ite {c₁ c₂ X Y : (ℕ → ℕ) → ℕ}
    (hc₁ : Continuous2 c₁) (hc₂ : Continuous2 c₂)
    (hX : Continuous2 X) (hY : Continuous2 Y) :
    Continuous2 fun α ↦ if c₁ α = c₂ α then X α else Y α := by
  intro α
  obtain ⟨N₁, h₁⟩ := hc₁ α
  obtain ⟨N₂, h₂⟩ := hc₂ α
  obtain ⟨N₃, h₃⟩ := hX α
  obtain ⟨N₄, h₄⟩ := hY α
  refine ⟨N₁ + N₂ + N₃ + N₄, fun β hβ ↦ ?_⟩
  have e₁ : c₁ α = c₁ β := h₁ β fun i hi ↦ hβ i (by omega)
  have e₂ : c₂ α = c₂ β := h₂ β fun i hi ↦ hβ i (by omega)
  show (if c₁ α = c₂ α then X α else Y α) = if c₁ β = c₂ β then X β else Y β
  by_cases h : c₁ α = c₂ α
  · have h' : c₁ β = c₂ β := by rw [← e₁, ← e₂]; exact h
    rw [if_pos h, if_pos h']
    exact h₃ β fun i hi ↦ hβ i (by omega)
  · have h' : ¬ c₁ β = c₂ β := fun hc ↦ h (by rw [e₁, e₂]; exact hc)
    rw [if_neg h, if_neg h']
    exact h₄ β fun i hi ↦ hβ i (by omega)

/-! ## The tracking relation -/

/-- **The oracle-parameterized continuity relation.**  `Tracked n X`
says the oracle-indexed family `X` of pure-type-`n` objects is
continuously tracked: at the base, `X` is a continuous type-2
functional of the oracle; at function types, applying `X` pointwise to
any tracked argument family reads out a continuous function of the
oracle.  A Kripke-style logical relation over the oracle — the
compositional invariant of this module. -/
def Tracked : (n : ℕ) → ((ℕ → ℕ) → PureType n) → Prop
  | 0, X => Continuous2 X
  | n + 1, X => ∀ Y : (ℕ → ℕ) → PureType n, Tracked n Y →
      Continuous2 fun α ↦ X α (Y α)

/-- The identity family (the oracle itself) is tracked: evaluation at a
continuously computed position is continuous. -/
theorem id_tracked : Tracked 1 fun α ↦ α :=
  fun _ hZ ↦ continuous2_eval hZ

/-- The canonical elements form a tracked (constant) family at every
level. -/
theorem defaultPT_tracked : ∀ n, Tracked n fun _ ↦ defaultPT n
  | 0 => continuous2_const 0
  | _ + 1 => fun _ _ ↦ continuous2_const 0

/-- Numerals at a continuously computed value are tracked (they ignore
their argument). -/
theorem natPT_tracked {n : ℕ} {k : (ℕ → ℕ) → ℕ} (hk : Continuous2 k) :
    Tracked (n + 1) fun α ↦ natPT (n + 1) (k α) :=
  fun _ _ ↦ hk

/-- Pointwise pairing preserves tracking. -/
theorem pairPT_tracked {n : ℕ} {X Y : (ℕ → ℕ) → PureType (n + 1)}
    (hX : Tracked (n + 1) X) (hY : Tracked (n + 1) Y) :
    Tracked (n + 1) fun α ↦ pairPT (X α) (Y α) :=
  fun Z hZ ↦ continuous2_comp₂ Nat.pair (hX Z hZ) (hY Z hZ)

/-- First projection preserves tracking. -/
theorem fstPT_tracked {n : ℕ} {X : (ℕ → ℕ) → PureType (n + 1)}
    (hX : Tracked (n + 1) X) : Tracked (n + 1) fun α ↦ fstPT (X α) :=
  fun Z hZ ↦ continuous2_comp₁ (fun v ↦ v.unpair.1) (hX Z hZ)

/-- Second projection preserves tracking. -/
theorem sndPT_tracked {n : ℕ} {X : (ℕ → ℕ) → PureType (n + 1)}
    (hX : Tracked (n + 1) X) : Tracked (n + 1) fun α ↦ sndPT (X α) :=
  fun Z hZ ↦ continuous2_comp₁ (fun v ↦ v.unpair.2) (hX Z hZ)

/-- The standard embedding and projection preserve tracking, in one
mutual induction on the level. -/
theorem up_down_tracked : ∀ n : ℕ,
    (∀ {X : (ℕ → ℕ) → PureType n}, Tracked n X →
      Tracked (n + 1) fun α ↦ up n (X α)) ∧
    (∀ {Y : (ℕ → ℕ) → PureType (n + 1)}, Tracked (n + 1) Y →
      Tracked n fun α ↦ down n (Y α)) := by
  intro n
  induction n with
  | zero =>
    constructor
    · intro X hX Z _
      exact hX
    · intro Y hY
      exact hY (fun _ ↦ defaultPT 0) (defaultPT_tracked 0)
  | succ n ih =>
    constructor
    · intro X hX Z hZ
      exact hX _ (ih.2 hZ)
    · intro Y hY Z hZ
      exact hY _ (ih.1 hZ)

/-- Application through pairing preserves tracking. -/
theorem app₁_tracked {n : ℕ} {F : (ℕ → ℕ) → PureType (n + 2)}
    {x : (ℕ → ℕ) → PureType (n + 1)}
    (hF : Tracked (n + 2) F) (hx : Tracked (n + 1) x) :
    Tracked (n + 1) fun α ↦ app₁ (F α) (x α) :=
  fun _ hW ↦
    hF _ (pairPT_tracked hx ((up_down_tracked n).1 hW))

/-- **Abstraction preserves tracking, by β-reduction**: if the body
sends tracked argument families to tracked value families, the
abstraction is tracked.  This is the case that would require
associate-level closure under the "has an associate" invariant; under
the oracle-parameterized relation it is immediate, because tracking of
`abs₁ G` is *tested by application*, which computes `G`. -/
theorem abs₁_tracked {n : ℕ} {G : (ℕ → ℕ) → PureType (n + 1) → PureType (n + 1)}
    (hG : ∀ X, Tracked (n + 1) X → Tracked (n + 1) fun α ↦ G α (X α)) :
    Tracked (n + 2) fun α ↦ abs₁ (G α) :=
  fun Z hZ ↦
    hG (fun α ↦ fstPT (Z α)) (fstPT_tracked hZ) _
      ((up_down_tracked n).2 (sndPT_tracked hZ))

/-- Tracking at a continuously computed numeral index: consulting a
family of tracked families at a continuous index preserves tracking —
the level-lifted form of `continuous2_apply_nat`, and the only new
closure fact rule `ind` needs. -/
theorem tracked_apply_nat {n : ℕ} {k : (ℕ → ℕ) → ℕ}
    {G : (ℕ → ℕ) → ℕ → PureType (n + 1)}
    (hk : Continuous2 k) (hG : ∀ j, Tracked (n + 1) fun α ↦ G α j) :
    Tracked (n + 1) fun α ↦ G α (k α) :=
  fun Y hY ↦ continuous2_apply_nat hk fun j ↦ hG j Y hY

/-- Pointwise case split on two continuously computed scrutinees
preserves tracking at every level. -/
theorem ite_tracked {n : ℕ} (c₁ c₂ : (ℕ → ℕ) → ℕ)
    (X Y : (ℕ → ℕ) → PureType n)
    (hc₁ : Continuous2 c₁) (hc₂ : Continuous2 c₂)
    (hX : Tracked n X) (hY : Tracked n Y) :
    Tracked n fun α ↦ if c₁ α = c₂ α then X α else Y α := by
  cases n with
  | zero => exact continuous2_ite hc₁ hc₂ hX hY
  | succ n =>
    intro Z hZ
    have he : (fun α ↦ (if c₁ α = c₂ α then X α else Y α) (Z α))
        = fun α ↦ if c₁ α = c₂ α then X α (Z α) else Y α (Z α) := by
      funext α
      show (if c₁ α = c₂ α then X α else Y α) (Z α)
        = if c₁ α = c₂ α then X α (Z α) else Y α (Z α)
      by_cases h : c₁ α = c₂ α
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
    rw [he]
    exact continuous2_ite hc₁ hc₂ (hX Z hZ) (hY Z hZ)

/-- Tracking transports along equalities of the level. -/
theorem tracked_cast {a b : ℕ} (e : a = b) {X : (ℕ → ℕ) → PureType (a + 1)}
    (hX : Tracked (a + 1) X) : Tracked (b + 1) fun α ↦ e ▸ X α := by
  cases e
  exact hX

/-! ## Tracking preservation for the transports -/

/-- The formula-indexed transports preserve tracking, both directions
in one mutual induction on the formula — the same shape as
`MR_liftR_dropR`, with no level side condition (the junk defaults are
tracked too). -/
theorem liftR_dropR_tracked (φ : Formula) :
    (∀ {m : ℕ} {X : (ℕ → ℕ) → PureType (m + 1)}, Tracked (m + 1) X →
      Tracked (m + 2) fun α ↦ liftR φ (X α)) ∧
    (∀ {m : ℕ} {Y : (ℕ → ℕ) → PureType (m + 2)}, Tracked (m + 2) Y →
      Tracked (m + 1) fun α ↦ dropR φ (Y α)) := by
  induction φ with
  | bot =>
    exact ⟨fun hX ↦ (up_down_tracked _).1 hX,
      fun hY ↦ (up_down_tracked _).2 hY⟩
  | eq s t =>
    exact ⟨fun hX ↦ (up_down_tracked _).1 hX,
      fun hY ↦ (up_down_tracked _).2 hY⟩
  | and φ ψ ihφ ihψ =>
    constructor
    · intro m X hX
      exact pairPT_tracked (ihφ.1 (fstPT_tracked hX))
        (ihψ.1 (sndPT_tracked hX))
    · intro m Y hY
      exact pairPT_tracked (ihφ.2 (fstPT_tracked hY))
        (ihψ.2 (sndPT_tracked hY))
  | or φ ψ ihφ ihψ =>
    constructor
    · intro m X hX
      exact ite_tracked (fun α ↦ fstPT (X α) (defaultPT m)) (fun _ ↦ 0)
        (fun α ↦ pairPT (fun _ ↦ (0 : ℕ)) (liftR φ (sndPT (X α))))
        (fun α ↦ pairPT (fun _ ↦ (1 : ℕ)) (liftR ψ (sndPT (X α))))
        (fstPT_tracked hX _ (defaultPT_tracked m))
        (continuous2_const 0)
        (pairPT_tracked (natPT_tracked (continuous2_const 0))
          (ihφ.1 (sndPT_tracked hX)))
        (pairPT_tracked (natPT_tracked (continuous2_const 1))
          (ihψ.1 (sndPT_tracked hX)))
    · intro m Y hY
      exact ite_tracked (fun α ↦ fstPT (Y α) (defaultPT (m + 1))) (fun _ ↦ 0)
        (fun α ↦ pairPT (fun _ ↦ (0 : ℕ)) (dropR φ (sndPT (Y α))))
        (fun α ↦ pairPT (fun _ ↦ (1 : ℕ)) (dropR ψ (sndPT (Y α))))
        (fstPT_tracked hY _ (defaultPT_tracked (m + 1)))
        (continuous2_const 0)
        (pairPT_tracked (natPT_tracked (continuous2_const 0))
          (ihφ.2 (sndPT_tracked hY)))
        (pairPT_tracked (natPT_tracked (continuous2_const 1))
          (ihψ.2 (sndPT_tracked hY)))
  | imp φ ψ ihφ ihψ =>
    constructor
    · intro m X hX
      cases m with
      | zero => exact defaultPT_tracked 2
      | succ m' =>
        exact abs₁_tracked fun W hW ↦ ihψ.1 (app₁_tracked hX (ihφ.2 hW))
    · intro m Y hY
      cases m with
      | zero => exact defaultPT_tracked 1
      | succ m' =>
        exact abs₁_tracked fun W hW ↦ ihψ.2 (app₁_tracked hY (ihφ.1 hW))
  | ex y φ ih =>
    constructor
    · intro m X hX
      have he : (fun α ↦ liftR (.ex y φ) (X α))
          = fun α ↦ pairPT (natPT (m + 2) (fstPT (X α) (defaultPT m)))
              (liftR φ (sndPT (X α))) := by
        funext α
        exact liftR_ex y φ (X α)
      rw [he]
      exact pairPT_tracked
        (natPT_tracked (fstPT_tracked hX _ (defaultPT_tracked m)))
        (ih.1 (sndPT_tracked hX))
    · intro m Y hY
      have he : (fun α ↦ dropR (.ex y φ) (Y α))
          = fun α ↦ pairPT (natPT (m + 1) (fstPT (Y α) (defaultPT (m + 1))))
              (dropR φ (sndPT (Y α))) := by
        funext α
        exact dropR_ex y φ (Y α)
      rw [he]
      exact pairPT_tracked
        (natPT_tracked (fstPT_tracked hY _ (defaultPT_tracked (m + 1))))
        (ih.2 (sndPT_tracked hY))
  | all y φ ih =>
    constructor
    · intro m X hX
      cases m with
      | zero => exact defaultPT_tracked 2
      | succ m' =>
        refine abs₁_tracked fun W hW ↦ ?_
        have hk : Continuous2 fun α ↦ W α (defaultPT (m' + 1)) :=
          hW _ (defaultPT_tracked (m' + 1))
        exact ih.1 (app₁_tracked hX (natPT_tracked hk))
    · intro m Y hY
      cases m with
      | zero => exact defaultPT_tracked 1
      | succ m' =>
        refine abs₁_tracked fun W hW ↦ ?_
        have hk : Continuous2 fun α ↦ W α (defaultPT m') :=
          hW _ (defaultPT_tracked m')
        exact ih.2 (app₁_tracked hY (natPT_tracked hk))

/-- Iterated lifting preserves tracking. -/
theorem liftIter_tracked (φ : Formula) :
    ∀ (k : ℕ) {m : ℕ} {X : (ℕ → ℕ) → PureType (m + 1)},
      Tracked (m + 1) X → Tracked (m + k + 1) fun α ↦ liftIter φ k (X α)
  | 0, _, _, hX => hX
  | k + 1, _, _, hX => (liftR_dropR_tracked φ).1 (liftIter_tracked φ k hX)

/-- Iterated dropping preserves tracking. -/
theorem dropIter_tracked (φ : Formula) :
    ∀ (k : ℕ) {m : ℕ} {Y : (ℕ → ℕ) → PureType (m + k + 1)},
      Tracked (m + k + 1) Y → Tracked (m + 1) fun α ↦ dropIter φ k (Y α)
  | 0, _, _, hY => hY
  | k + 1, _, _, hY =>
      dropIter_tracked φ k ((liftR_dropR_tracked φ).2 hY)

/-- **The family generator preserves tracking**: a tracked realizer
family generates a family tracked at every ambient — the device that
lets the binder cases (`impIC`, `orEC`) feed tracked hypotheses to
bodies consuming them at arbitrary ambients. -/
theorem famOf_tracked (φ : Formula) {m : ℕ}
    {X : (ℕ → ℕ) → PureType (m + 1)} (hX : Tracked (m + 1) X) (n : ℕ) :
    Tracked (n + 1) fun α ↦ famOf φ (X α) n := by
  by_cases h : m ≤ n
  · have he : (fun α ↦ famOf φ (X α) n)
        = fun α ↦ (Nat.add_sub_cancel' h) ▸ liftIter φ (n - m) (X α) := by
      funext α
      show famOf φ (X α) n = _
      unfold famOf
      rw [dif_pos h]
    rw [he]
    exact tracked_cast _ (liftIter_tracked φ (n - m) hX)
  · have he : (fun α ↦ famOf φ (X α) n)
        = fun α ↦ dropIter φ (m - n)
            ((Nat.add_sub_cancel' (le_of_not_ge h)).symm ▸ X α) := by
      funext α
      show famOf φ (X α) n = _
      unfold famOf
      rw [dif_neg h]
    rw [he]
    exact dropIter_tracked φ (m - n) (tracked_cast _ hX)

/-! ## Tracked families and contexts -/

/-- A tracked oracle-indexed family of ambient-indexed realizer
families: tracked at every ambient. -/
def TrackedFam (f : (ℕ → ℕ) → Fam) : Prop :=
  ∀ n, Tracked (n + 1) fun α ↦ f α n

/-- A tracked oracle-indexed context: every hypothesis family is
tracked. -/
def TrackedCtx (E : List ((ℕ → ℕ) → Fam)) : Prop :=
  ∀ X ∈ E, TrackedFam X

/-- A tracked oracle-indexed arithmetic environment: every variable's
value is a continuous function of the oracle. -/
def TrackedEnv (R : (ℕ → ℕ) → ℕ → ℕ) : Prop :=
  ∀ i, Continuous2 fun α ↦ R α i

/-- The junk family is tracked. -/
theorem defaultFam_tracked : TrackedFam fun _ ↦ defaultFam :=
  fun n ↦ defaultPT_tracked (n + 1)

theorem TrackedCtx.cons {p : (ℕ → ℕ) → Fam} {E : List ((ℕ → ℕ) → Fam)}
    (hp : TrackedFam p) (hE : TrackedCtx E) : TrackedCtx (p :: E) := by
  intro X hX
  rcases List.mem_cons.mp hX with rfl | h
  · exact hp
  · exact hE X h

/-- Term evaluation in a tracked environment is continuous.  (Phase A
adds the `+`/`×` cases: a binary composition of two continuous reads —
`continuous2_comp₂` was already in the closure kit.) -/
theorem termEval_continuous {R : (ℕ → ℕ) → ℕ → ℕ} (hR : TrackedEnv R) :
    ∀ u : Term, Continuous2 fun α ↦ u.eval (R α)
  | .var i => hR i
  | .zero => continuous2_const 0
  | .succ u => continuous2_comp₁ (· + 1) (termEval_continuous hR u)
  | .plus s t => continuous2_comp₂ (· + ·)
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .times s t => continuous2_comp₂ (· * ·)
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .pred t => continuous2_comp₁ (· - 1) (termEval_continuous hR t)
  | .exp s t => continuous2_comp₂ (· ^ ·)
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .bump s t => continuous2_comp₂ bumpN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .good s t => continuous2_comp₂ goodN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .prec s t => continuous2_comp₂ oltN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .ord s t => continuous2_comp₂ ordOf
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .hcut s t => continuous2_comp₂ hydraStepN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .hydra s t => continuous2_comp₂ hydraSeqN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .hord t => continuous2_comp₁ ordOfHydraN (termEval_continuous hR t)
  | .hcons s t => continuous2_comp₂ hconsN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .happ s t => continuous2_comp₂ happN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .mvcount t => continuous2_comp₁ hlen (termEval_continuous hR t)
  | .xor s t => continuous2_comp₂ xorN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .pas s t => continuous2_comp₂ pasN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .look s t => continuous2_comp₂ lookN
      (termEval_continuous hR s) (termEval_continuous hR t)
  | .fib t => continuous2_comp₁ fibN (termEval_continuous hR t)
  | .solves n f t v k => continuous2_comp₅ solvesN
      (termEval_continuous hR n) (termEval_continuous hR f)
      (termEval_continuous hR t) (termEval_continuous hR v)
      (termEval_continuous hR k)

/-- Updating a tracked environment at a fixed variable with a
continuously computed value stays tracked (rule `allI`'s environment
step). -/
theorem trackedEnv_update {R : (ℕ → ℕ) → ℕ → ℕ} {y : ℕ}
    {k : (ℕ → ℕ) → ℕ} (hR : TrackedEnv R) (hk : Continuous2 k) :
    TrackedEnv fun α ↦ Function.update (R α) y (k α) := by
  intro i
  by_cases h : i = y
  · subst h
    have he : (fun α ↦ Function.update (R α) i (k α) i) = k := by
      funext α
      simp [Function.update]
    rw [he]
    exact hk
  · have he : (fun α ↦ Function.update (R α) y (k α) i)
        = fun α ↦ R α i := by
      funext α
      simp [Function.update, h]
    rw [he]
    exact hR i

/-! ## The per-combinator preservation lemmas, one per rule -/

/-- `axC` preserves tracking (rule `ax`): the head projection of a
tracked context is tracked. -/
theorem axC_tracked : ∀ (E : List ((ℕ → ℕ) → Fam)), TrackedCtx E →
    TrackedFam fun α ↦ axC (E.map (· α))
  | [], _ => defaultFam_tracked
  | X :: _, h => h X (List.mem_cons_self ..)

/-- The `wk` tail recursion preserves tracking (rule `wk`): the tail of
a tracked context is tracked. -/
theorem wk_tracked {E : List ((ℕ → ℕ) → Fam)} (hE : TrackedCtx E) :
    TrackedCtx E.tail := by
  cases E with
  | nil => exact hE
  | cons X E => exact fun Y hY ↦ hE Y (List.mem_cons_of_mem _ hY)

/-- `andIC` preserves tracking (rule `andI`). -/
theorem andIC_tracked {f g : (ℕ → ℕ) → Fam}
    (hf : TrackedFam f) (hg : TrackedFam g) :
    TrackedFam fun α ↦ andIC (f α) (g α) :=
  fun n ↦ pairPT_tracked (hf n) (hg n)

/-- `andE₁C` preserves tracking (rule `andE₁`). -/
theorem andE₁C_tracked {f : (ℕ → ℕ) → Fam} (hf : TrackedFam f) :
    TrackedFam fun α ↦ andE₁C (f α) :=
  fun n ↦ fstPT_tracked (hf n)

/-- `andE₂C` preserves tracking (rule `andE₂`). -/
theorem andE₂C_tracked {f : (ℕ → ℕ) → Fam} (hf : TrackedFam f) :
    TrackedFam fun α ↦ andE₂C (f α) :=
  fun n ↦ sndPT_tracked (hf n)

/-- `orI₁C` preserves tracking (rule `orI₁`). -/
theorem orI₁C_tracked {f : (ℕ → ℕ) → Fam} (hf : TrackedFam f) :
    TrackedFam fun α ↦ orI₁C (f α) :=
  fun n ↦ pairPT_tracked (natPT_tracked (continuous2_const 0)) (hf n)

/-- `orI₂C` preserves tracking (rule `orI₂`). -/
theorem orI₂C_tracked {f : (ℕ → ℕ) → Fam} (hf : TrackedFam f) :
    TrackedFam fun α ↦ orI₂C (f α) :=
  fun n ↦ pairPT_tracked (natPT_tracked (continuous2_const 1)) (hf n)

/-- `orEC` preserves tracking (rule `orE`): the tag read is continuous,
each branch consumes the payload's tracked `famOf` family, and the
pointwise case split preserves tracking. -/
theorem orEC_tracked (φ ψ : Formula) {d : (ℕ → ℕ) → Fam}
    {b₁ b₂ : (ℕ → ℕ) → Fam → Fam}
    (hd : TrackedFam d)
    (h₁ : ∀ p : (ℕ → ℕ) → Fam, TrackedFam p →
      TrackedFam fun α ↦ b₁ α (p α))
    (h₂ : ∀ p : (ℕ → ℕ) → Fam, TrackedFam p →
      TrackedFam fun α ↦ b₂ α (p α)) :
    TrackedFam fun α ↦ orEC φ ψ (d α) (b₁ α) (b₂ α) := by
  intro n
  show Tracked (n + 1) fun α ↦
    if fstPT (d α n) (defaultPT n) = 0 then
      b₁ α (famOf φ (sndPT (d α n))) n
    else
      b₂ α (famOf ψ (sndPT (d α n))) n
  exact ite_tracked (fun α ↦ fstPT (d α n) (defaultPT n)) (fun _ ↦ 0)
    (fun α ↦ b₁ α (famOf φ (sndPT (d α n))) n)
    (fun α ↦ b₂ α (famOf ψ (sndPT (d α n))) n)
    (fstPT_tracked (hd n) _ (defaultPT_tracked n))
    (continuous2_const 0)
    (h₁ (fun α ↦ famOf φ (sndPT (d α n)))
      (famOf_tracked φ (sndPT_tracked (hd n))) n)
    (h₂ (fun α ↦ famOf ψ (sndPT (d α n)))
      (famOf_tracked ψ (sndPT_tracked (hd n))) n)

/-- `impIC` preserves tracking (rule `impI`): the abstraction over the
bound realizer's transport-generated family is tracked as soon as the
body sends tracked hypothesis families to tracked value families —
"continuous at the level the family is eventually read at," by
β-reduction of `abs₁` under application. -/
theorem impIC_tracked (φ : Formula) {body : (ℕ → ℕ) → List Fam → Fam}
    {env : (ℕ → ℕ) → List Fam}
    (hbody : ∀ p : (ℕ → ℕ) → Fam, TrackedFam p →
      TrackedFam fun α ↦ body α (p α :: env α)) :
    TrackedFam fun α ↦ impIC φ (body α) (env α) := by
  intro n
  cases n with
  | zero => exact defaultPT_tracked 1
  | succ m =>
    show Tracked (m + 2) fun α ↦
      abs₁ fun x ↦ body α (famOf φ x :: env α) m
    exact abs₁_tracked fun X hX ↦
      hbody (fun α ↦ famOf φ (X α)) (famOf_tracked φ hX) m

/-- `impEC` preserves tracking (rule `impE`): application, major
premise one ambient up. -/
theorem impEC_tracked {f g : (ℕ → ℕ) → Fam}
    (hf : TrackedFam f) (hg : TrackedFam g) :
    TrackedFam fun α ↦ impEC (f α) (g α) :=
  fun n ↦ app₁_tracked (hf (n + 1)) (hg n)

/-- `botEC` preserves tracking (rule `botE`): the vacuous realizer is
tracked. -/
theorem botEC_tracked : TrackedFam fun _ ↦ botEC :=
  defaultFam_tracked

/-- `allIC` preserves tracking (rule `allI`): the abstraction reading
the numeral off its argument is tracked as soon as the body family is
tracked at every continuously computed numeral. -/
theorem allIC_tracked {bodyAt : (ℕ → ℕ) → ℕ → Fam}
    (hbody : ∀ k : (ℕ → ℕ) → ℕ, Continuous2 k →
      TrackedFam fun α ↦ bodyAt α (k α)) :
    TrackedFam fun α ↦ allIC (bodyAt α) := by
  intro n
  cases n with
  | zero => exact defaultPT_tracked 1
  | succ m =>
    show Tracked (m + 2) fun α ↦
      abs₁ fun z ↦ bodyAt α (z (defaultPT m)) m
    exact abs₁_tracked fun Z hZ ↦
      hbody (fun α ↦ Z α (defaultPT m)) (hZ _ (defaultPT_tracked m)) m

/-- `allEC` preserves tracking (rule `allE`): application at the
numeral of a continuously computed value. -/
theorem allEC_tracked {f : (ℕ → ℕ) → Fam} {k : (ℕ → ℕ) → ℕ}
    (hf : TrackedFam f) (hk : Continuous2 k) :
    TrackedFam fun α ↦ allEC (f α) (k α) :=
  fun n ↦ app₁_tracked (hf (n + 1)) (natPT_tracked hk)

/-- `indC` preserves tracking (rule `ind`) — combinator 17's
preservation lemma.  Two small inductions meet here: per *fixed*
iteration count `j` the recursor is tracked by induction on `j` (each
step is `app₁` of tracked pieces — the existing closure lemmas suffice),
and the *actual* count, read continuously off the abstraction's
argument, is absorbed by `tracked_apply_nat` (near any oracle the count
is locally constant).  The `allIC` packaging then closes the
abstraction by β-reduction exactly as in the `allI` case. -/
theorem indC_tracked {a b : (ℕ → ℕ) → Fam}
    (ha : TrackedFam a) (hb : TrackedFam b) :
    TrackedFam fun α ↦ indC (a α) (b α) := by
  have hrec : ∀ m j,
      Tracked (m + 1) fun α ↦ indRecC (a α m) (b α (m + 2)) j := by
    intro m j
    induction j with
    | zero => exact ha m
    | succ j ih =>
      exact app₁_tracked (app₁_tracked (hb (m + 2))
        (natPT_tracked (continuous2_const j))) ih
  show TrackedFam fun α ↦
    allIC fun k ↦ fun m ↦ indRecC (a α m) (b α (m + 2)) k
  exact allIC_tracked fun k hk m ↦ tracked_apply_nat hk fun j ↦ hrec m j

/-- **The transfinite recursor preserves tracking, at each fixed
notation** — the inner half of `tiC_tracked`, by well-founded induction
along `≺` (the same induction `MR_tiRecC` performs, for the other
invariant).  The recursive calls sit under a case split on `j' ≺ j` whose
condition does *not* depend on the oracle, so the split is discharged
index-by-index and the *oracle-dependent* index is absorbed by
`tracked_apply_nat` — exactly as the iteration count is in
`indC_tracked`.  The two `dropR` transports are handled by
`liftR_dropR_tracked`. -/
theorem tiRecC_tracked (φ : Formula) {m₂ : ℕ}
    {b : (ℕ → ℕ) → PureType (m₂ + 5)} (hb : Tracked (m₂ + 5) b) :
    ∀ j : ℕ, Tracked (m₂ + 3) fun α ↦ tiRecC φ (b α) j := by
  intro j
  refine oLt_wf.induction
    (C := fun j ↦ Tracked (m₂ + 3) fun α ↦ tiRecC φ (b α) j) j ?_
  intro j ih
  have he : (fun α ↦ tiRecC φ (b α) j) = fun α ↦
      app₁ (app₁ (b α) (natPT (m₂ + 4) j))
        (abs₁ fun ζ ↦ abs₁ fun _w ↦
          if OLt (ζ (defaultPT (m₂ + 1))) j then
            dropR φ (dropR φ (tiRecC φ (b α) (ζ (defaultPT (m₂ + 1)))))
          else defaultPT (m₂ + 1)) := by
    funext α
    exact tiRecC_eq φ (b α) j
  rw [he]
  refine app₁_tracked (app₁_tracked hb (natPT_tracked (continuous2_const j))) ?_
  refine abs₁_tracked fun Z hZ ↦ ?_
  refine abs₁_tracked fun W hW ↦ ?_
  have hk : Continuous2 fun α ↦ Z α (defaultPT (m₂ + 1)) :=
    hZ _ (defaultPT_tracked (m₂ + 1))
  refine tracked_apply_nat (n := m₂) (k := fun α ↦ Z α (defaultPT (m₂ + 1)))
    (G := fun α j' ↦
      if OLt j' j then dropR φ (dropR φ (tiRecC φ (b α) j'))
      else defaultPT (m₂ + 1)) hk (fun j' ↦ ?_)
  rcases dec_em (OLt j' j) with h | h
  · have he₂ : (fun α ↦
        if OLt j' j then dropR φ (dropR φ (tiRecC φ (b α) j'))
        else defaultPT (m₂ + 1))
        = fun α ↦ dropR φ (dropR φ (tiRecC φ (b α) j')) := by
      funext α
      rw [if_pos h]
    rw [he₂]
    exact (liftR_dropR_tracked φ).2 ((liftR_dropR_tracked φ).2 (ih j' h))
  · have he₂ : (fun α ↦
        if OLt j' j then dropR φ (dropR φ (tiRecC φ (b α) j'))
        else defaultPT (m₂ + 1))
        = fun _ ↦ defaultPT (m₂ + 1) := by
      funext α
      rw [if_neg h]
    rw [he₂]
    exact defaultPT_tracked (m₂ + 1)

/-- `tiC` preserves tracking (rule `tiEps0`) — combinator 40's
preservation lemma.  The `allIC` packaging closes the abstraction by
β-reduction, exactly as for `allI`/`ind`; the notation code read off the
argument is continuous, so `tracked_apply_nat` consults the family of
recursors at it. -/
theorem tiC_tracked (φ : Formula) {b : (ℕ → ℕ) → Fam} (hb : TrackedFam b) :
    TrackedFam fun α ↦ tiC φ (b α) := by
  refine allIC_tracked fun k hk ↦ ?_
  intro m
  cases m with
  | zero => exact defaultPT_tracked 1
  | succ m' =>
    cases m' with
    | zero => exact defaultPT_tracked 2
    | succ m₂ =>
      show Tracked (m₂ + 3) fun α ↦ tiRecC φ (b α (m₂ + 4)) (k α)
      exact tracked_apply_nat hk fun j ↦ tiRecC_tracked φ (hb (m₂ + 4)) j

/-- `exIC` preserves tracking (rule `exI`): the witness is a continuous
read, the payload is tracked, and pairing preserves tracking — the same
three facts `orI₁C_tracked` uses. -/
theorem exIC_tracked {k : (ℕ → ℕ) → ℕ} {f : (ℕ → ℕ) → Fam}
    (hk : Continuous2 k) (hf : TrackedFam f) :
    TrackedFam fun α ↦ exIC (k α) (f α) :=
  fun n ↦ pairPT_tracked (natPT_tracked hk) (hf n)

/-- `exEC` preserves tracking (rule `exE`): the witness read off the major
premise is continuous (so the body's *environment* stays tracked, via
`trackedEnv_update` at the use site), and the payload's `famOf` family is
tracked — `orEC_tracked` without the case split. -/
theorem exEC_tracked (φ : Formula) {d : (ℕ → ℕ) → Fam}
    {body : (ℕ → ℕ) → ℕ → Fam → Fam} (hd : TrackedFam d)
    (hbody : ∀ w : (ℕ → ℕ) → ℕ, Continuous2 w →
      ∀ p : (ℕ → ℕ) → Fam, TrackedFam p →
        TrackedFam fun α ↦ body α (w α) (p α)) :
    TrackedFam fun α ↦ exEC φ (d α) (body α) := by
  intro n
  show Tracked (n + 1) fun α ↦
    body α (fstPT (d α n) (defaultPT n)) (famOf φ (sndPT (d α n))) n
  exact hbody (fun α ↦ fstPT (d α n) (defaultPT n))
    (fstPT_tracked (hd n) _ (defaultPT_tracked n))
    (fun α ↦ famOf φ (sndPT (d α n)))
    (famOf_tracked φ (sndPT_tracked (hd n))) n

/-- `eqDecC` preserves tracking (rule `eqDec`): the decision tag of two
continuously computed values is a pointwise case split between two
constant tracked families. -/
theorem eqDecC_tracked {c₁ c₂ : (ℕ → ℕ) → ℕ}
    (h₁ : Continuous2 c₁) (h₂ : Continuous2 c₂) :
    TrackedFam fun α ↦ eqDecC (decide (c₁ α = c₂ α)) := by
  intro n
  have he : (fun α ↦ eqDecC (decide (c₁ α = c₂ α)) n)
      = fun α ↦ if c₁ α = c₂ α then
          pairPT (fun _ ↦ (0 : ℕ)) (defaultPT (n + 1))
        else
          pairPT (fun _ ↦ (1 : ℕ)) (defaultPT (n + 1)) := by
    funext α
    by_cases h : c₁ α = c₂ α
    · simp [eqDecC, h]
    · simp [eqDecC, h]
  rw [he]
  exact ite_tracked c₁ c₂ _ _ h₁ h₂
    (pairPT_tracked (natPT_tracked (continuous2_const 0))
      (defaultPT_tracked (n + 1)))
    (pairPT_tracked (natPT_tracked (continuous2_const 1))
      (defaultPT_tracked (n + 1)))

/-- `axiomC` preserves tracking, `succNeZero` instance (rule
`succNeZero`): the contentless realizer is tracked. -/
theorem axiomC_succNeZero_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `succInj` instance (rule `succInj`):
the contentless realizer is tracked. -/
theorem axiomC_succInj_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqRefl` instance (rule `eqRefl`). -/
theorem axiomC_eqRefl_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqSymm` instance (rule `eqSymm`). -/
theorem axiomC_eqSymm_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqTrans` instance (rule `eqTrans`). -/
theorem axiomC_eqTrans_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongSucc` instance (rule
`eqCongSucc`). -/
theorem axiomC_eqCongSucc_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongPlus` instance (rule
`eqCongPlus`). -/
theorem axiomC_eqCongPlus_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongTimes` instance (rule
`eqCongTimes`). -/
theorem axiomC_eqCongTimes_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `zeroPlus` instance (rule `zeroPlus`). -/
theorem axiomC_zeroPlus_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `succPlus` instance (rule `succPlus`). -/
theorem axiomC_succPlus_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `zeroTimes` instance (rule
`zeroTimes`). -/
theorem axiomC_zeroTimes_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `succTimes` instance (rule
`succTimes`). -/
theorem axiomC_succTimes_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `predZero` instance (rule `predZero`). -/
theorem axiomC_predZero_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `predSucc` instance (rule `predSucc`). -/
theorem axiomC_predSucc_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `expZero` instance (rule `expZero`). -/
theorem axiomC_expZero_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `expSucc` instance (rule `expSucc`). -/
theorem axiomC_expSucc_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `bumpZero` instance (rule `bumpZero`). -/
theorem axiomC_bumpZero_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `bumpNum` instance (rule `bumpNum`). -/
theorem axiomC_bumpNum_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `goodZero` instance (rule `goodZero`). -/
theorem axiomC_goodZero_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `goodSucc` instance (rule `goodSucc`). -/
theorem axiomC_goodSucc_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongPred` instance (rule
`eqCongPred`). -/
theorem axiomC_eqCongPred_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongExp` instance (rule
`eqCongExp`). -/
theorem axiomC_eqCongExp_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongBump` instance (rule
`eqCongBump`). -/
theorem axiomC_eqCongBump_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongGood` instance (rule
`eqCongGood`). -/
theorem axiomC_eqCongGood_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `precNum` instance (rule `precNum`). -/
theorem axiomC_precNum_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongPrec` instance (rule
`eqCongPrec`). -/
theorem axiomC_eqCongPrec_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `ordBump` instance (rule `ordBump`). -/
theorem axiomC_ordBump_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `ordPredLt` instance (rule
`ordPredLt`). -/
theorem axiomC_ordPredLt_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `bumpNeZero` instance (rule
`bumpNeZero`). -/
theorem axiomC_bumpNeZero_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongOrd` instance (rule
`eqCongOrd`). -/
theorem axiomC_eqCongOrd_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `hydraZero` instance (rule
`hydraZero`). -/
theorem axiomC_hydraZero_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `hydraSucc` instance (rule
`hydraSucc`). -/
theorem axiomC_hydraSucc_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `hordCutLt` instance (rule
`hordCutLt`). -/
theorem axiomC_hordCutLt_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, the Phase-F2 Pascal instances. -/
theorem axiomC_pasZeroZero_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_pasZeroSucc_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_pasSuccZero_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_pasSuccSucc_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_xorNum_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_eqCongXor_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_eqCongPas_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_lookNum_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_eqCongLook_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_fibZero_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_fibOne_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_fibSucc_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_eqCongFib_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

/-- `axiomC` preserves tracking, the Phase-E2 Hanoi instances. -/
theorem axiomC_solvesZero_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_solvesSucc_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_mvcountNil_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_mvcountApp_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_eqCongHcons_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_eqCongHapp_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_eqCongMvcount_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

theorem axiomC_eqCongSolves_tracked : TrackedFam fun _ ↦ axiomC := defaultFam_tracked

/-- `axiomC` preserves tracking, `hcutNum` instance (rule `hcutNum`). -/
theorem axiomC_hcutNum_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongHcut` instance (rule
`eqCongHcut`). -/
theorem axiomC_eqCongHcut_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongHydra` instance (rule
`eqCongHydra`). -/
theorem axiomC_eqCongHydra_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-- `axiomC` preserves tracking, `eqCongHord` instance (rule
`eqCongHord`). -/
theorem axiomC_eqCongHord_tracked : TrackedFam fun _ ↦ axiomC :=
  defaultFam_tracked

/-! ## The main induction and the capstone -/

/-- **The invariant, threaded through the derivation**: for every
derivation, tracked arithmetic environment family, and tracked context
family, the extracted family is tracked.  Induction on the derivation,
one per-combinator preservation lemma per case — the same shape as
`soundness`. -/
theorem extract_tracked {Γ : List Formula} {φ : Formula} (D : Deriv Γ φ) :
    ∀ (R : (ℕ → ℕ) → ℕ → ℕ), TrackedEnv R →
      ∀ (E : List ((ℕ → ℕ) → Fam)), TrackedCtx E →
        TrackedFam fun α ↦ extract D (R α) (E.map (· α)) := by
  induction D with
  | ax =>
    intro R hR E hE
    exact axC_tracked E hE
  | wk D ih =>
    intro R hR E hE
    cases E with
    | nil => exact ih R hR [] (wk_tracked hE)
    | cons X E => exact ih R hR E (wk_tracked hE)
  | andI D₁ D₂ ih₁ ih₂ =>
    intro R hR E hE
    exact andIC_tracked (ih₁ R hR E hE) (ih₂ R hR E hE)
  | andE₁ D ih =>
    intro R hR E hE
    exact andE₁C_tracked (ih R hR E hE)
  | andE₂ D ih =>
    intro R hR E hE
    exact andE₂C_tracked (ih R hR E hE)
  | orI₁ D ih =>
    intro R hR E hE
    exact orI₁C_tracked (ih R hR E hE)
  | orI₂ D ih =>
    intro R hR E hE
    exact orI₂C_tracked (ih R hR E hE)
  | @orE Γ φ ψ χ D D₁ D₂ ih ih₁ ih₂ =>
    intro R hR E hE
    show TrackedFam fun α ↦
      orEC φ ψ (extract D (R α) (E.map (· α)))
        (fun p ↦ extract D₁ (R α) (p :: E.map (· α)))
        (fun p ↦ extract D₂ (R α) (p :: E.map (· α)))
    exact orEC_tracked φ ψ (ih R hR E hE)
      (fun p hp ↦ ih₁ R hR (p :: E) (TrackedCtx.cons hp hE))
      (fun p hp ↦ ih₂ R hR (p :: E) (TrackedCtx.cons hp hE))
  | @impI Γ φ ψ D ih =>
    intro R hR E hE
    show TrackedFam fun α ↦
      impIC φ (fun env' ↦ extract D (R α) env') (E.map (· α))
    exact impIC_tracked φ fun p hp ↦ ih R hR (p :: E) (TrackedCtx.cons hp hE)
  | impE D₁ D₂ ih₁ ih₂ =>
    intro R hR E hE
    exact impEC_tracked (ih₁ R hR E hE) (ih₂ R hR E hE)
  | botE D ih =>
    intro R hR E hE
    exact botEC_tracked
  | @allI Γ y φ D hfresh ih =>
    intro R hR E hE
    show TrackedFam fun α ↦
      allIC fun k ↦ extract D (Function.update (R α) y k) (E.map (· α))
    exact allIC_tracked fun k hk ↦
      ih (fun α ↦ Function.update (R α) y (k α))
        (trackedEnv_update hR hk) E hE
  | @allE Γ y φ u D hok ih =>
    intro R hR E hE
    show TrackedFam fun α ↦
      allEC (extract D (R α) (E.map (· α))) (u.eval (R α))
    exact allEC_tracked (ih R hR E hE) (termEval_continuous hR u)
  | ind D₁ D₂ hok ih₁ ih₂ =>
    intro R hR E hE
    show TrackedFam fun α ↦
      indC (extract D₁ (R α) (E.map (· α))) (extract D₂ (R α) (E.map (· α)))
    exact indC_tracked (ih₁ R hR E hE) (ih₂ R hR E hE)
  | eqDec s t =>
    intro R hR E hE
    show TrackedFam fun α ↦
      eqDecC (decide (s.eval (R α) = t.eval (R α)))
    exact eqDecC_tracked (termEval_continuous hR s)
      (termEval_continuous hR t)
  | succNeZero s =>
    intro R hR E hE
    exact axiomC_succNeZero_tracked
  | succInj s t =>
    intro R hR E hE
    exact axiomC_succInj_tracked
  | eqRefl t =>
    intro R hR E hE
    exact axiomC_eqRefl_tracked
  | eqSymm s t =>
    intro R hR E hE
    exact axiomC_eqSymm_tracked
  | eqTrans s t u =>
    intro R hR E hE
    exact axiomC_eqTrans_tracked
  | eqCongSucc s t =>
    intro R hR E hE
    exact axiomC_eqCongSucc_tracked
  | eqCongPlus s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongPlus_tracked
  | eqCongTimes s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongTimes_tracked
  | zeroPlus t =>
    intro R hR E hE
    exact axiomC_zeroPlus_tracked
  | succPlus s t =>
    intro R hR E hE
    exact axiomC_succPlus_tracked
  | zeroTimes t =>
    intro R hR E hE
    exact axiomC_zeroTimes_tracked
  | succTimes s t =>
    intro R hR E hE
    exact axiomC_succTimes_tracked
  | predZero =>
    intro R hR E hE
    exact axiomC_predZero_tracked
  | predSucc s =>
    intro R hR E hE
    exact axiomC_predSucc_tracked
  | expZero s =>
    intro R hR E hE
    exact axiomC_expZero_tracked
  | expSucc s t =>
    intro R hR E hE
    exact axiomC_expSucc_tracked
  | bumpZero s =>
    intro R hR E hE
    exact axiomC_bumpZero_tracked
  | bumpNum k n =>
    intro R hR E hE
    exact axiomC_bumpNum_tracked
  | goodZero s =>
    intro R hR E hE
    exact axiomC_goodZero_tracked
  | goodSucc s t =>
    intro R hR E hE
    exact axiomC_goodSucc_tracked
  | eqCongPred s t =>
    intro R hR E hE
    exact axiomC_eqCongPred_tracked
  | eqCongExp s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongExp_tracked
  | eqCongBump s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongBump_tracked
  | eqCongGood s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongGood_tracked
  | @tiEps0 Γ x y φ D hxy hok hfree ih =>
    intro R hR E hE
    show TrackedFam fun α ↦ tiC φ (extract D (R α) (E.map (· α)))
    exact tiC_tracked φ (ih R hR E hE)
  | ordBump b n =>
    intro R hR E hE
    exact axiomC_ordBump_tracked
  | ordPredLt b n =>
    intro R hR E hE
    exact axiomC_ordPredLt_tracked
  | bumpNeZero b n =>
    intro R hR E hE
    exact axiomC_bumpNeZero_tracked
  | eqCongOrd s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongOrd_tracked
  | @exI Γ x φ u D hok ih =>
    intro R hR E hE
    have he : (fun α ↦ extract (Deriv.exI u D hok) (R α) (E.map (· α)))
        = fun α ↦ exIC (u.eval (R α)) (extract D (R α) (E.map (· α))) := by
      funext α
      exact extract_exI u D hok (R α) _
    rw [he]
    exact exIC_tracked (termEval_continuous hR u) (ih R hR E hE)
  | @exE Γ x φ ψ D₁ D₂ hfresh hnf ih₁ ih₂ =>
    intro R hR E hE
    have he : (fun α ↦ extract (Deriv.exE D₁ D₂ hfresh hnf) (R α) (E.map (· α)))
        = fun α ↦ exEC φ (extract D₁ (R α) (E.map (· α)))
            (fun w p ↦
              extract D₂ (Function.update (R α) x w) (p :: E.map (· α))) := by
      funext α
      exact extract_exE D₁ D₂ hfresh hnf (R α) _
    rw [he]
    exact exEC_tracked φ (ih₁ R hR E hE)
      (fun w hw p hp ↦ ih₂ (fun α ↦ Function.update (R α) x (w α))
        (trackedEnv_update hR hw) (p :: E) (TrackedCtx.cons hp hE))
  | precNum a b =>
    intro R hR E hE
    exact axiomC_precNum_tracked
  | eqCongPrec s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongPrec_tracked
  | hydraZero s =>
    intro R hR E hE
    exact axiomC_hydraZero_tracked
  | hydraSucc s t =>
    intro R hR E hE
    exact axiomC_hydraSucc_tracked
  | hordCutLt n c =>
    intro R hR E hE
    exact axiomC_hordCutLt_tracked
  | hcutNum n c =>
    intro R hR E hE
    exact axiomC_hcutNum_tracked
  | eqCongHcut s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongHcut_tracked
  | eqCongHydra s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongHydra_tracked
  | eqCongHord s t =>
    intro R hR E hE
    exact axiomC_eqCongHord_tracked
  | solvesZero f t v =>
    intro R hR E hE
    exact axiomC_solvesZero_tracked
  | solvesSucc n f t v k₁ k₂ =>
    intro R hR E hE
    exact axiomC_solvesSucc_tracked
  | mvcountNil =>
    intro R hR E hE
    exact axiomC_mvcountNil_tracked
  | mvcountApp k₁ m k₂ =>
    intro R hR E hE
    exact axiomC_mvcountApp_tracked
  | eqCongHcons s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongHcons_tracked
  | eqCongHapp s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongHapp_tracked
  | eqCongMvcount s t =>
    intro R hR E hE
    exact axiomC_eqCongMvcount_tracked
  | eqCongSolves n₁ n₂ f₁ f₂ t₁ t₂ v₁ v₂ k₁ k₂ =>
    intro R hR E hE
    exact axiomC_eqCongSolves_tracked
  | pasZeroZero =>
    intro R hR E hE
    exact axiomC_pasZeroZero_tracked
  | pasZeroSucc k =>
    intro R hR E hE
    exact axiomC_pasZeroSucc_tracked
  | pasSuccZero n =>
    intro R hR E hE
    exact axiomC_pasSuccZero_tracked
  | pasSuccSucc n k =>
    intro R hR E hE
    exact axiomC_pasSuccSucc_tracked
  | xorNum a b =>
    intro R hR E hE
    exact axiomC_xorNum_tracked
  | eqCongXor s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongXor_tracked
  | eqCongPas s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongPas_tracked
  | lookNum a b =>
    intro R hR E hE
    exact axiomC_lookNum_tracked
  | eqCongLook s₁ t₁ s₂ t₂ =>
    intro R hR E hE
    exact axiomC_eqCongLook_tracked
  | fibZero =>
    intro R hR E hE
    exact axiomC_fibZero_tracked
  | fibOne =>
    intro R hR E hE
    exact axiomC_fibOne_tracked
  | fibSucc s =>
    intro R hR E hE
    exact axiomC_fibSucc_tracked
  | eqCongFib s t =>
    intro R hR E hE
    exact axiomC_eqCongFib_tracked

/-- **Generic continuity of extraction** (the theorem closing the gap
flagged in docs/first-order/STATUS.md): the extracted type-2 realizer of *every* closed
derivation is continuous.  The brief's level restriction `lvl φ ≤ 1` is
not needed: continuity of the extract is a property of the extraction
combinators alone, independent of what the extract realizes (the level
enters only through `soundness`, when the realizer is asked to realize
`φ` at ambient 1).

Instantiate the invariant at the constant environment and empty
context, then read the extract off along the tracked identity family:
the extract applied to the oracle *is* the extract as a functional. -/
theorem extract_continuous {φ : Formula} (D : Deriv [] φ) (ρ : ℕ → ℕ) :
    Continuous2 (extract D ρ [] 1) := by
  have h : Tracked 2 fun α ↦ extract D ρ [] 1 :=
    extract_tracked D (fun _ ↦ ρ) (fun i ↦ continuous2_const (ρ i)) []
      (fun _ hX ↦ absurd hX List.not_mem_nil) 1
  exact h (fun α ↦ α) id_tracked

end Realizability
