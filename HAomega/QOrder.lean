/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.QArith
import HAomega.Dyadics

/-!
# The dyadic-to-rational value bridge

`QArith.lean` sends a `Q` to the Mathlib rational it denotes; this adds the
dyadic side, so that `2⁻ᵏ` — the unit every modulus in the analysis files is
measured in — denotes what it should.

Proof-side only, like `QArith`: nothing here is reachable from `Tm.eval`.
-/

namespace HAomega


theorem twoPowN_ne_zero (k : Nat) : twoPowN k ≠ 0 := Nat.ne_of_gt (twoPowN_pos k)

/-- `2⁻ᵏ` denotes what it should. -/
theorem toQ_pow2neg_val (k : Nat) : (D.toQ (D.pow2neg k)).val = 1 / 2 ^ k := by
  show (Q.of 1 (twoPowN k)).val = _
  rw [Q.val_of _ _ (twoPowN_ne_zero k), twoPowN_cast]
  norm_num

theorem toQ_pow2neg_pos (k : Nat) : (0 : Rat) < (D.toQ (D.pow2neg k)).val := by
  rw [toQ_pow2neg_val]
  positivity

theorem halve_pow (k : Nat) : (1 : Rat) / 2 ^ (k + 1) = (1 / 2 ^ k) / 2 := by
  rw [pow_succ]
  field_simp

theorem quarter_pow (k : Nat) : (1 : Rat) / 2 ^ (k + 2) = (1 / 2 ^ k) / 4 := by
  have hp : (2 : Rat) ^ k ≠ 0 := by positivity
  rw [pow_add]
  field_simp
  norm_num

end HAomega
