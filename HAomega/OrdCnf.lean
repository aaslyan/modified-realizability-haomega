/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Ordinals.Epsilon0
import Realizability.Signature.OrdinalAssignment

/-!
# The typed ordinal layer: structural CNF notations below ε₀

The first-order development codes ordinal notations into `ℕ` through a
triangular pairing (`Epsilon0.lean`), because its object language has one
sort.  HA^ω has no such constraint, and this file gives ordinals their own
inductive type:

    Eps0 ::= zero | node e c r        -- meaning ω^e·(c+1) + r

Comparison (`olt`) and normal form (`nf`) are **structural** — pattern
matching, no decoding, no pairing arithmetic.  Normal forms are still not
optional: on raw notations the comparison has an infinite descending chain
(`ω ≻ 1+ω ≻ 1+1+ω ≻ …` — machine-checked on codes in `Epsilon0.lean`, and
the chain survives any change of representation), so the order the recursor
uses (`OLtE`) conjoins the comparison with normal form, exactly as the
first-order `oltB` does.

**Well-foundedness is inherited, not re-proved**: `toCode : Eps0 → ℕ` is the
evident encoding, the alignment lemmas show `olt`/`nf` compute precisely
`precB`/`nfB` through it, and `oLtE_wf` is `Epsilon0`'s certified `oLt_wf`
pulled back along `toCode`.  The coding thereby moves out of every
*computation* (the recursor re-decides `≺` structurally) and survives only
inside the well-foundedness *proof* — where it costs nothing at run time.

The Goodstein assignment `ordE` mirrors `ordOf`'s recursion constructor for
constructor, `toCode_ordE` certifies the mirror, and the two schema
discharges (`ordE_bumpN`, `oltE_ordE_of_lt`) transfer through it.  So the
typed layer imports **no new mathematical facts**: everything is the
first-order theorems, read structurally.

**Definitions here are inside `Tm.eval`'s dependency graph** (the `.orde`,
`.olte`, `.tiRecE` symbols evaluate by them), so they must stay choice-free
and kernel-computable; the proofs need not.
-/

namespace HAomega

open Realizability

/-- Ordinal notations below `ε₀`, structurally: `node e c r` means
`ω^e·(c+1) + r`.  The `+1` on the coefficient mirrors the code convention,
so no positivity side condition ever arises. -/
inductive Eps0 : Type where
  | zero : Eps0
  | node : Eps0 → ℕ → Eps0 → Eps0
  deriving DecidableEq, Repr

namespace Eps0

/-- The encoding into `Epsilon0.lean`'s codes — used only in *proofs*
(inheriting well-foundedness and the Goodstein theorems), never in
evaluation. -/
def toCode : Eps0 → ℕ
  | .zero => 0
  | .node e c r => mkO (toCode e) c (toCode r)

theorem toCode_inj : ∀ {a b : Eps0}, toCode a = toCode b → a = b
  | .zero, .zero, _ => rfl
  | .zero, .node e c r, h => absurd h.symm (mkO_ne_zero (toCode e) c (toCode r))
  | .node e c r, .zero, h => absurd h (mkO_ne_zero (toCode e) c (toCode r))
  | .node e₁ c₁ r₁, .node e₂ c₂ r₂, h => by
      simp only [toCode] at h
      have hE : toCode e₁ = toCode e₂ := by
        have := congrArg oE h; simpa only [oE_mkO] using this
      have hC : c₁ = c₂ := by
        have := congrArg oC h; simpa only [oC_mkO] using this
      have hR : toCode r₁ = toCode r₂ := by
        have := congrArg oR h; simpa only [oR_mkO] using this
      rw [toCode_inj hE, hC, toCode_inj hR]

/-- **Structural comparison** — the Cantor order on notations, by pattern
matching alone. -/
def olt : Eps0 → Eps0 → Bool
  | _, .zero => false
  | .zero, .node _ _ _ => true
  | .node e₁ c₁ r₁, .node e₂ c₂ r₂ =>
      if e₁ = e₂ then
        if c₁ < c₂ then true
        else if c₂ < c₁ then false
        else olt r₁ r₂
      else olt e₁ e₂

/-- The comparison computes `precB` through the coding. -/
theorem toCode_olt : ∀ a b : Eps0, precB (toCode a) (toCode b) = olt a b
  | a, .zero => by
      rw [show toCode .zero = 0 from rfl, precB_zero_right]
      cases a <;> rfl
  | .zero, .node e c r =>
      precB_zero_left (mkO_ne_zero (toCode e) c (toCode r))
  | .node e₁ c₁ r₁, .node e₂ c₂ r₂ => by
      simp only [toCode]
      rw [precB_pos (mkO_ne_zero _ _ _) (mkO_ne_zero _ _ _)]
      simp only [oE_mkO, oC_mkO, oR_mkO]
      by_cases hE : e₁ = e₂
      · subst hE
        simp [olt, toCode_olt r₁ r₂]
      · have hE' : toCode e₁ ≠ toCode e₂ := fun h ↦ hE (toCode_inj h)
        simp [olt, hE, hE', toCode_olt e₁ e₂]

/-- **Structural normal form**: exponents normal, rest normal, and the
rest's leading exponent strictly below this one. -/
def nf : Eps0 → Bool
  | .zero => true
  | .node e _ r => nf e && nf r &&
      (match r with
       | .zero => true
       | .node e' _ _ => olt e' e)

/-- Normal form computes `nfB` through the coding. -/
theorem toCode_nf : ∀ a : Eps0, nfB (toCode a) = nf a
  | .zero => nfB_zero
  | .node e c r => by
      simp only [toCode]
      rw [nfB_pos (mkO_ne_zero _ _ _)]
      simp only [oE_mkO, oR_mkO, toCode_nf e, toCode_nf r]
      cases r with
      | zero => simp [nf, toCode]
      | node e' c' r' =>
          simp [nf, toCode, mkO_ne_zero, oE_mkO, toCode_olt e' e]

/-- The order the recursor uses: comparison **conjoined with** normal form —
the structural mirror of `oltB`. -/
def oltE (a b : Eps0) : Bool := nf a && nf b && olt a b

/-- The strict order as a `Prop` (decidable by computation). -/
def OLtE (a b : Eps0) : Prop := oltE a b = true

instance (a b : Eps0) : Decidable (OLtE a b) :=
  inferInstanceAs (Decidable (oltE a b = true))

theorem toCode_oltB (a b : Eps0) : oltB (toCode a) (toCode b) = oltE a b := by
  simp only [oltB, oltE, toCode_nf, toCode_olt]

theorem OLtE_iff_OLt {a b : Eps0} :
    OLtE a b ↔ OLt (toCode a) (toCode b) := by
  simp only [OLtE, OLt, toCode_oltB]

/-- **Well-foundedness, inherited**: `oLt_wf` pulled back along the
coding.  No new descent argument — the certified first-order theorem *is*
the content. -/
theorem oLtE_wf : WellFounded OLtE :=
  Subrelation.wf (fun {a b} h ↦ (OLtE_iff_OLt.mp h : InvImage OLt toCode a b))
    (InvImage.wf toCode oLt_wf)

/-- The order test as a numeral — what the `.olte` symbol evaluates by. -/
def oltNE (a b : Eps0) : ℕ := if oltE a b then 1 else 0

theorem oltNE_eq_one_iff {a b : Eps0} : oltNE a b = 1 ↔ OLtE a b := by
  simp only [oltNE, OLtE]
  by_cases h : oltE a b = true <;> simp [h]

end Eps0

/-- The Goodstein ordinal assignment, structurally — `ordOfAux`'s recursion
constructor for constructor, building `Eps0` nodes instead of paired
codes. -/
def ordEAux (k : ℕ) : ℕ → ℕ → Eps0
  | 0, _ => .zero
  | _ + 1, 0 => .zero
  | f + 1, n + 1 =>
      .node (ordEAux k f (hlog k (n + 1)))
        ((n + 1) / k ^ hlog k (n + 1) - 1)
        (ordEAux k f ((n + 1) % k ^ hlog k (n + 1)))

/-- The ordinal of `n` in hereditary base `k` — what `.orde` evaluates by. -/
def ordE (k n : ℕ) : Eps0 := ordEAux k n n

/-- The mirror is exact: `ordE` encodes to `ordOf`. -/
theorem toCode_ordEAux (k : ℕ) : ∀ f n : ℕ,
    (ordEAux k f n).toCode = ordOfAux k f n
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | f + 1, n + 1 => by
      simp only [ordEAux, ordOfAux, Eps0.toCode,
        toCode_ordEAux k f]

theorem toCode_ordE (k n : ℕ) : (ordE k n).toCode = ordOf k n :=
  toCode_ordEAux k n n

/-- Base change preserves the ordinal — `ordOf_bumpN`, read structurally
through `toCode`-injectivity.  Discharges the `ordEBump` schema. -/
theorem ordE_bumpN {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    ordE (k + 1) (bumpN k n) = ordE k n :=
  Eps0.toCode_inj (by rw [toCode_ordE, toCode_ordE, ordOf_bumpN hk n])

/-- The assignment is strictly monotone — `olt_ordOf_of_lt`, read
structurally.  Discharges the `ordEPredLt` schema. -/
theorem oltE_ordE_of_lt {k m n : ℕ} (hk : 2 ≤ k) (hmn : m < n) :
    Eps0.OLtE (ordE k m) (ordE k n) :=
  Eps0.OLtE_iff_OLt.mpr (by rw [toCode_ordE, toCode_ordE]
                            exact olt_ordOf_of_lt hk hmn)

-- The mirror at instances, and the structural comparison agreeing with the
-- coded one where it matters.
#guard (ordE 2 5).toCode == Realizability.ordOf 2 5
#guard (ordE 3 100).toCode == Realizability.ordOf 3 100
#guard Eps0.oltNE (ordE 2 3) (ordE 2 4) == 1
#guard Eps0.oltNE (ordE 2 4) (ordE 2 4) == 0
#guard Eps0.nf (ordE 2 100) == true
-- The classical counterexample, structurally: ω and 1+ω as raw notations —
-- the non-normal 1+ω compares below ω, which is why `nf` is load-bearing.
#guard Eps0.olt (.node .zero 0 (.node (.node .zero 0 .zero) 0 .zero))
  (.node (.node .zero 0 .zero) 0 .zero) == true
#guard Eps0.nf (.node .zero 0 (.node (.node .zero 0 .zero) 0 .zero)) == false

/-- Node count of a notation — for the size comparison below. -/
def Eps0.size : Eps0 → ℕ
  | .zero => 1
  | .node e _ r => 1 + e.size + r.size

/-! ### What the typed layer buys, measured

The code and the tree denote the *same* ordinal (`toCode_ordE`), so this is a
like-for-like comparison of two representations of one object.  The code is a
single natural number built by iterated pairing, and it grows to thousands of
digits; the tree stays at dozens of nodes.

    n         code (decimal digits)      tree (nodes)
    10                3                      13
    100              10                      29
    500             506                      61
    1000          1,412                      67
    100000        1,782                      83

Guarded at every build.  Note the honest limit of the claim: this is
*representation size*, not speed — no reproducible difference was found in the
running time of the two extracted Goodstein programs (`GoodsteinTyped.lean`),
because Lean's `Nat` is GMP-backed and the arithmetic on even a 1,782-digit
code is cheap. What the typed layer removes is the encoding itself, and with
it the decode/normal-form side conditions in every proof. -/
#guard ((toString (Realizability.ordOf 2 1000)).length, (ordE 2 1000).size)
  == (1412, 67)
#guard ((toString (Realizability.ordOf 2 100000)).length, (ordE 2 100000).size)
  == (1782, 83)
#guard ((toString (Realizability.ordOf 2 10)).length, (ordE 2 10).size) == (3, 13)

-- Everything `Tm.eval` will depend on must be axiom-free.
#print axioms ordE
#print axioms Eps0.oltNE
#print axioms Eps0.oLtE_wf

end HAomega
