/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Ordinals.Epsilon0

/-!
# Phase F1: Pascal's triangle mod 2, at the value level

The simplest of the development's showpieces, and deliberately so: the
statement is a **decidable equation**, not an existence statement, so the
extract is a genuine decision *function* rather than a witness — and what
it decides, drawn as a triangle, is the Sierpiński gasket.  No `TI(ε₀)`,
no ordinals, and (unlike Hanoi) no `∃` either: ordinary induction and the
arithmetic of Phase A suffice.

This module is the value layer and sits **before `Syntax.lean`**, so every
definition here must stay `Classical`-free and kernel-computable.

## The recursion

    pas(0, 0)         = 1
    pas(0, k + 1)     = 0
    pas(n + 1, 0)     = 1
    pas(n + 1, k + 1) = pas(n, k) XOR pas(n, k + 1)

Structural in the first argument, with both recursive calls at `n` — a
branching recursion like Hanoi's, though a cheap one.  The two clauses
the brief lists as characteristic, `pas(n,n) = 1` and (implicitly)
`pas(n,k) = 0` above the diagonal, are **not** axioms: they are derived
inside the fragment in Phase F3.

## Why `XOR` is a symbol and not a term

The brief offers `a + b − 2·a·b` or a case-split axiom.  Neither is used,
for a reason worth recording: **`a + b − 2ab` is not expressible in this
fragment at all.**  The signature's arithmetic is `+`, `×`, `exp` and
`pred`, and `pred` is the only non-monotone operation — it can subtract a
*constant* from a term (`x − 1`, `x − 2`, …) but there is no term for
`1 − x`, since a composition of monotone operations under finitely many
outer `pred`s is monotone in `x` and `1 − x` is not.

So `xor` enters as its own symbol, by its **numeral graph** — the
`bumpNum`/`precNum`/`hcutNum` pattern this development already uses three
times, and for the same reason each time: the function is decidable and
the fragment computes it on numerals, but its definition (here, parity of
a sum) is not a first-order equation schema over the fragment's terms.
The case analysis then happens where it belongs, in the *proofs*, driven
by the totality theorem rather than by four conditional axioms.
-/

namespace Realizability

/-- Exclusive or, as parity of the sum — total on `ℕ`, and `XOR` on
`{0,1}`. -/
def xorN (a b : ℕ) : ℕ := (a + b) % 2

@[simp] theorem xorN_zero_zero : xorN 0 0 = 0 := rfl
@[simp] theorem xorN_zero_one : xorN 0 1 = 1 := rfl
@[simp] theorem xorN_one_zero : xorN 1 0 = 1 := rfl
@[simp] theorem xorN_one_one : xorN 1 1 = 0 := rfl

/-- `xor` lands in `{0,1}`. -/
theorem xorN_total (a b : ℕ) : xorN a b = 1 ∨ xorN a b = 0 := by
  have h : (a + b) % 2 < 2 := Nat.mod_lt _ (by omega)
  show (a + b) % 2 = 1 ∨ (a + b) % 2 = 0
  omega

/-- **Pascal's triangle mod 2.**  Structural in the row index, with both
recursive calls one row up. -/
def pasN : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => xorN (pasN n k) (pasN n (k + 1))

/-! ### The four defining equations, as named facts

Each is one soundness case of the corresponding Phase-F2 schema. -/

@[simp] theorem pasN_zero_zero : pasN 0 0 = 1 := rfl

@[simp] theorem pasN_zero_succ (k : ℕ) : pasN 0 (k + 1) = 0 := rfl

@[simp] theorem pasN_succ_zero (n : ℕ) : pasN (n + 1) 0 = 1 := rfl

@[simp] theorem pasN_succ_succ (n k : ℕ) :
    pasN (n + 1) (k + 1) = xorN (pasN n k) (pasN n (k + 1)) := rfl

/-- Every entry is `0` or `1` — the fragment proves this itself in Phase
F3; the value-level version is here because the soundness cases need
nothing else about `pasN`. -/
theorem pasN_total : ∀ (n k : ℕ), pasN n k = 1 ∨ pasN n k = 0
  | 0, 0 => Or.inl rfl
  | 0, _ + 1 => Or.inr rfl
  | _ + 1, 0 => Or.inl rfl
  | n + 1, k + 1 => xorN_total (pasN n k) (pasN n (k + 1))

/-! ### The derived clauses, at the value level

These are what Phase F3 proves *inside the fragment*; having them here
too is what lets the two be compared. -/

/-- Above the diagonal everything vanishes. -/
theorem pasN_above : ∀ (n j : ℕ), pasN n (n + j + 1) = 0
  | 0, _ => rfl
  | n + 1, j => by
    have he : n + 1 + j + 1 = (n + j + 1) + 1 := by omega
    rw [he]
    show xorN (pasN n (n + j + 1)) (pasN n (n + j + 1 + 1)) = 0
    have h₁ := pasN_above n j
    have h₂ := pasN_above n (j + 1)
    have he₂ : n + (j + 1) + 1 = n + j + 1 + 1 := by omega
    rw [he₂] at h₂
    rw [h₁, h₂]
    rfl

/-- The diagonal is all ones. -/
theorem pasN_diag : ∀ n : ℕ, pasN n n = 1
  | 0 => rfl
  | n + 1 => by
    show xorN (pasN n n) (pasN n (n + 1)) = 1
    have h₁ := pasN_diag n
    have h₂ := pasN_above n 0
    have he : n + 0 + 1 = n + 1 := by omega
    rw [he] at h₂
    rw [h₁, h₂]
    rfl

/-! ### The triangle, kernel-checked at the top

Rows `0`–`4` of the parity triangle, read left to right. -/

theorem pas_rows_small :
    ((pasN 0 0),
     (pasN 1 0, pasN 1 1),
     (pasN 2 0, pasN 2 1, pasN 2 2),
     (pasN 3 0, pasN 3 1, pasN 3 2, pasN 3 3),
     (pasN 4 0, pasN 4 1, pasN 4 2, pasN 4 3, pasN 4 4))
      = (1, (1, 1), (1, 0, 1), (1, 1, 1, 1), (1, 0, 0, 0, 1)) := rfl

#print axioms pasN_total
#print axioms pasN_diag
#print axioms pasN_above

end Realizability
