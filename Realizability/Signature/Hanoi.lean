/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Ordinals.Epsilon0

/-!
# Phase E1: the Tower of Hanoi, at the value level

The third independence-flavoured showpiece of this development — except
that Hanoi is *not* independent of anything.  It is an ordinary
PA-provable statement, and that is exactly why it is here: it exercises
the pipeline on a theorem needing **no `TI(ε₀)` at all**, only ordinary
induction and the arithmetic of Phase A, and it has a genuinely
*branching* recursion (two sub-calls per level) where Goodstein and Hydra
both had linear chains.

This module is the value layer, and like `Hydra.lean` it sits **before
`Syntax.lean`**: `Term.eval` evaluates the Phase-E2 symbols by the
functions defined here, so every definition below must stay
`Classical`-free and kernel-computable.  Proofs are unconstrained.

## The encodings, both reused rather than rebuilt

A **move** is a pair of pegs, encoded arithmetically: `mvN src dst =
src * 3 + dst`.  Nothing new is needed for it — the fragment already has
`×` and `+`, so the fragment can *write* a move.

A **move sequence** is a list, encoded with the cons coding
`Hydra.lean` already uses for forests, over the triangular pairing of
`Epsilon0.lean`:

    ⌜nil⌝ = 0        ⌜cons m k⌝ = ⟪m, k⟫ + 1

That is the third client of that one pairing and the second client of
this list convention; no second scheme is introduced.

## The solver, in difference-list form

`hanoiAux n from to via rest` prepends the `n`-disk solution to `rest`:

    hanoiAux 0       f t v r = r
    hanoiAux (n + 1) f t v r = hanoiAux n f v t (cons (f,t) (hanoiAux n v t f r))

Writing it this way — an accumulator rather than an append — is what
keeps this module free of general list theory: the correctness proof
never needs associativity, only the two `hanoiAux` equations.  `happN`
(genuine concatenation) is defined anyway, because the *fragment's*
induction step has to build its witness from two sub-witnesses it
receives as opaque values, and `hanoiN_succ` connects the two forms.

## `Solves` as a parser

`hcheck n f t v k` reads an `n`-disk solution off the front of `k` and
returns the rest, or `none`.  `solvesN n f t v k = 1` exactly when the
whole of `k` is such a solution.  This is a genuine *validator* — it
checks the shape of an arbitrary `k` — not "`k` equals the canonical
answer", which is what makes the existence theorem say something.
-/

namespace Realizability

/-! ## Moves -/

/-- A move `src → dst`, encoded arithmetically.  Both pegs are `< 3`, so
this is injective on legal moves. -/
def mvN (src dst : ℕ) : ℕ := src * 3 + dst

/-! ## Move sequences: the cons coding of `Hydra.lean`, over the
triangular pairing of `Epsilon0.lean` -/

/-- The empty sequence. -/
def hnil : ℕ := 0

/-- Prepend a move. -/
def hconsN (m k : ℕ) : ℕ := pr m k + 1

/-- First move of a nonempty sequence. -/
def hhead (k : ℕ) : ℕ := pr1 (k - 1)

/-- The rest of a nonempty sequence. -/
def htail (k : ℕ) : ℕ := pr2 (k - 1)

@[simp] theorem hcons_ne_zero (m k : ℕ) : hconsN m k ≠ 0 := Nat.succ_ne_zero _

@[simp] theorem hhead_hcons (m k : ℕ) : hhead (hconsN m k) = m := by
  show pr1 (pr m k + 1 - 1) = m
  simp [pr1_pr]

@[simp] theorem htail_hcons (m k : ℕ) : htail (hconsN m k) = k := by
  show pr2 (pr m k + 1 - 1) = k
  simp [pr2_pr]

/-- Every nonempty sequence is a `cons` — the eta law the parser needs. -/
theorem hcons_eta {k : ℕ} (h : k ≠ 0) : hconsN (hhead k) (htail k) = k := by
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  subst hj
  show pr (pr1 (j + 1 - 1)) (pr2 (j + 1 - 1)) + 1 = j + 1
  simp [pr_pr1_pr2]

/-- The tail is strictly smaller, which is what the fueled recursions
below run on. -/
theorem htail_lt {k : ℕ} (h : k ≠ 0) : htail k < k := by
  have := pr2_le (k - 1)
  show pr2 (k - 1) < k
  omega

/-! ## The solver -/

/-- **The Tower of Hanoi solution**, in difference-list form:
`hanoiAux n f t v r` is the `n`-disk solution moving `f → t` using `v`,
followed by `r`.

The two recursive calls are the point of this phase: the recursion
*branches*, where Goodstein's and Hydra's were linear chains. -/
def hanoiAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _, r => r
  | n + 1, f, t, v, r => hanoiAux n f v t (hconsN (mvN f t) (hanoiAux n v t f r))

/-- The solution itself. -/
def hanoiN (n f t v : ℕ) : ℕ := hanoiAux n f t v 0

/-! ## `Solves`, as a parser -/

/-- Read an `n`-disk solution off the front of `k`, returning the rest. -/
def hcheck : ℕ → ℕ → ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _, _, k => some k
  | n + 1, f, t, v, k =>
      match hcheck n f v t k with
      | none => none
      | some k' =>
          if k' = 0 then none
          else if hhead k' = mvN f t then hcheck n v t f (htail k') else none

/-- **The `Solves` relation's characteristic function**: `1` exactly when
the whole of `k` is a valid `n`-disk solution from `f` to `t` via `v`.
The fragment's `Solves n f t v k` is the equation `solves(n,f,t,v,k) = 1`. -/
def solvesN (n f t v k : ℕ) : ℕ :=
  if hcheck n f t v k = some 0 then 1 else 0

/-- One unfolding of the parser, with the inner call's result named — the
form the proofs below rewrite with (the raw `match` is an iota-redex that
`rw` cannot see through). -/
theorem hcheck_succ_some (n f t v k k' : ℕ) (hk : hcheck n f v t k = some k') :
    hcheck (n + 1) f t v k =
      (if k' = 0 then none
       else if hhead k' = mvN f t then hcheck n v t f (htail k') else none) := by
  show (match hcheck n f v t k with
        | none => none
        | some k' => if k' = 0 then none
                     else if hhead k' = mvN f t then hcheck n v t f (htail k')
                     else none) = _
  rw [hk]

theorem hcheck_succ_none (n f t v k : ℕ) (hk : hcheck n f v t k = none) :
    hcheck (n + 1) f t v k = none := by
  show (match hcheck n f v t k with
        | none => none
        | some k' => if k' = 0 then none
                     else if hhead k' = mvN f t then hcheck n v t f (htail k')
                     else none) = _
  rw [hk]

/-- **The solver solves.**  Induction on `n`, with the accumulator
generalized — the difference-list form is what makes this three lines
instead of an append-associativity development. -/
theorem hcheck_hanoiAux : ∀ (n f t v r : ℕ),
    hcheck n f t v (hanoiAux n f t v r) = some r
  | 0, _, _, _, _ => rfl
  | n + 1, f, t, v, r => by
    show hcheck (n + 1) f t v
      (hanoiAux n f v t (hconsN (mvN f t) (hanoiAux n v t f r))) = some r
    rw [hcheck, hcheck_hanoiAux n f v t _]
    simp only [hcons_ne_zero, if_neg, hhead_hcons, if_pos, htail_hcons]
    exact hcheck_hanoiAux n v t f r

/-- The headline value-level fact, and the justification of the Phase-E2
schema `solvesHanoi`. -/
theorem solvesN_hanoiN (n f t v : ℕ) : solvesN n f t v (hanoiN n f t v) = 1 := by
  show (if hcheck n f t v (hanoiAux n f t v 0) = some 0 then 1 else 0) = 1
  rw [hcheck_hanoiAux]
  simp

/-! ## Concatenation

Needed only because the fragment's induction step receives its two
sub-solutions as opaque values and must join them. -/

/-- Fuelled worker for `happN`: concatenate two encoded move-sequences. -/
def happAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, r => r
  | _ + 1, 0, r => r
  | fuel + 1, k + 1, r => hconsN (pr1 k) (happAux fuel (pr2 k) r)

/-- Concatenation, at the adequate fuel. -/
def happN (k r : ℕ) : ℕ := happAux k k r

theorem happAux_succ_eq : ∀ (fuel k r : ℕ), k ≤ fuel →
    happAux (fuel + 1) k r = happAux fuel k r
  | 0, k, r, h => by
    have hk : k = 0 := by omega
    subst hk; rfl
  | fuel + 1, k, r, h => by
    cases k with
    | zero => rfl
    | succ j =>
      have h2 : pr2 j ≤ fuel := by
        have := pr2_le j
        omega
      show hconsN (pr1 j) (happAux (fuel + 1) (pr2 j) r) = _
      rw [happAux_succ_eq fuel _ r h2]
      rfl

theorem happAux_eq_of_le : ∀ (fuel k r : ℕ), k ≤ fuel →
    happAux fuel k r = happAux k k r
  | 0, k, r, h => by
    have hk : k = 0 := by omega
    subst hk; rfl
  | fuel + 1, k, r, h => by
    rcases dec_em (k = fuel + 1) with he | he
    · rw [he]
    · have hf : k ≤ fuel := by omega
      rw [happAux_succ_eq fuel k r hf, happAux_eq_of_le fuel k r hf]

@[simp] theorem happN_nil (r : ℕ) : happN 0 r = r := rfl

@[simp] theorem happN_cons (m k r : ℕ) :
    happN (hconsN m k) r = hconsN m (happN k r) := by
  show happAux (pr m k + 1) (pr m k + 1) r = _
  show hconsN (pr1 (pr m k)) (happAux (pr m k) (pr2 (pr m k)) r) = _
  rw [pr1_pr, pr2_pr]
  have hle : k ≤ pr m k := by
    have := pr2_le (pr m k)
    rw [pr2_pr] at this
    exact this
  rw [happAux_eq_of_le _ _ _ hle]
  rfl

/-- The difference-list form and the append form agree. -/
theorem happN_hanoiAux : ∀ (n f t v s r : ℕ),
    happN (hanoiAux n f t v s) r = hanoiAux n f t v (happN s r)
  | 0, _, _, _, _, _ => rfl
  | n + 1, f, t, v, s, r => by
    show happN (hanoiAux n f v t (hconsN (mvN f t) (hanoiAux n v t f s))) r
      = hanoiAux n f v t (hconsN (mvN f t) (hanoiAux n v t f (happN s r)))
    rw [happN_hanoiAux n f v t _ r, happN_cons, happN_hanoiAux n v t f s r]

/-- **The recursion the fragment's step case mirrors**: an `(n+1)`-disk
solution is an `n`-disk solution, the big move, and another `n`-disk
solution. -/
theorem hanoiN_succ (n f t v : ℕ) :
    hanoiN (n + 1) f t v
      = happN (hanoiN n f v t) (hconsN (mvN f t) (hanoiN n v t f)) := by
  show hanoiAux n f v t (hconsN (mvN f t) (hanoiAux n v t f 0))
    = happN (hanoiAux n f v t 0) (hconsN (mvN f t) (hanoiAux n v t f 0))
  rw [happN_hanoiAux, happN_nil]

/-- The parser consumes exactly its prefix: what it reads off `k` it also
reads off `k ++ r`, leaving `r` appended to the remainder.  This is what
justifies the Phase-E2 schema `solvesSucc`, whose two premises are
solutions *given as arbitrary values*, not as the canonical ones. -/
theorem hcheck_happN : ∀ (n f t v k s r : ℕ), hcheck n f t v k = some s →
    hcheck n f t v (happN k r) = some (happN s r)
  | 0, _, _, _, k, s, r, h => by
    have : s = k := by injection h with h'; exact h'.symm
    subst this; rfl
  | n + 1, f, t, v, k, s, r, h => by
    cases hk : hcheck n f v t k with
    | none => rw [hcheck_succ_none n f t v k hk] at h; exact absurd h (by simp)
    | some k' =>
      rw [hcheck_succ_some n f t v k k' hk] at h
      rcases dec_em (k' = 0) with h0 | h0
      · rw [if_pos h0] at h; exact absurd h (by simp)
      · rw [if_neg h0] at h
        rcases dec_em (hhead k' = mvN f t) with hh | hh
        · rw [if_pos hh] at h
          obtain ⟨m, w, hmw⟩ : ∃ m w, k' = hconsN m w :=
            ⟨hhead k', htail k', (hcons_eta h0).symm⟩
          rw [hcheck_succ_some n f t v _ _ (hcheck_happN n f v t k k' r hk),
            hmw, happN_cons]
          rw [hmw] at hh h
          rw [hhead_hcons] at hh
          rw [htail_hcons] at h
          simp only [hcons_ne_zero, if_neg, hhead_hcons, hh, if_pos, htail_hcons]
          exact hcheck_happN n v t f w s r h
        · rw [if_neg hh] at h; exact absurd h (by simp)

/-- **The step, at the value level**: joining two solutions with the big
move between them gives a solution one disk larger.  This is the fact the
fragment imports as `solvesSucc`. -/
theorem solvesN_succ {n f t v k₁ k₂ : ℕ}
    (h₁ : solvesN n f v t k₁ = 1) (h₂ : solvesN n v t f k₂ = 1) :
    solvesN (n + 1) f t v (happN k₁ (hconsN (mvN f t) k₂)) = 1 := by
  have e₁ : hcheck n f v t k₁ = some 0 := by
    by_contra hne
    rw [show solvesN n f v t k₁ = 0 from if_neg hne] at h₁
    exact absurd h₁ (by simp)
  have e₂ : hcheck n v t f k₂ = some 0 := by
    by_contra hne
    rw [show solvesN n v t f k₂ = 0 from if_neg hne] at h₂
    exact absurd h₂ (by simp)
  have hpre := hcheck_happN n f v t k₁ 0 (hconsN (mvN f t) k₂) e₁
  show (if hcheck (n + 1) f t v (happN k₁ (hconsN (mvN f t) k₂)) = some 0
    then 1 else 0) = 1
  rw [hcheck, hpre]
  simp only [happN_nil, hcons_ne_zero, if_neg, hhead_hcons, if_pos, htail_hcons, e₂]
  simp

/-! ## Uniqueness — what "optimal" does and does not mean here

`solvesN` accepts exactly one sequence, and it is the canonical solution.
That is worth proving rather than assuming, because it is what turns the
existence theorem's "`MoveCount k = 2^n − 1`" into a statement about
*every* solution the relation admits, not just the one the derivation
happens to produce.

What it does **not** give is classical minimality — "no legal sequence of
moves solves the puzzle in fewer steps".  That would need a different
`Solves`: a legality relation on arbitrary sequences, with a tower-state
semantics (a disk may only move onto a larger one), of which the
recursive shape here is one particular family.  The classical `2^n − 1`
lower bound over *that* relation is not formalized and is not claimed;
see docs/first-order/STATUS.md's Phase-E section. -/

/-- **The parser accepts only what the solver produces.**  Induction on
`n`, with the remainder generalized, mirroring `hcheck_hanoiAux` in the
other direction. -/
theorem hcheck_eq_hanoiAux : ∀ (n f t v k s : ℕ), hcheck n f t v k = some s →
    k = hanoiAux n f t v s
  | 0, _, _, _, k, s, h => by
    have : s = k := by injection h with h'; exact h'.symm
    subst this
    rfl
  | n + 1, f, t, v, k, s, h => by
    cases hk : hcheck n f v t k with
    | none => rw [hcheck_succ_none n f t v k hk] at h; exact absurd h (by simp)
    | some k' =>
      rw [hcheck_succ_some n f t v k k' hk] at h
      rcases dec_em (k' = 0) with h0 | h0
      · rw [if_pos h0] at h; exact absurd h (by simp)
      · rw [if_neg h0] at h
        rcases dec_em (hhead k' = mvN f t) with hh | hh
        · rw [if_pos hh] at h
          have e₁ : k = hanoiAux n f v t k' := hcheck_eq_hanoiAux n f v t k k' hk
          have e₂ : htail k' = hanoiAux n v t f s :=
            hcheck_eq_hanoiAux n v t f (htail k') s h
          obtain ⟨m, w, hmw⟩ : ∃ m w, k' = hconsN m w :=
            ⟨hhead k', htail k', (hcons_eta h0).symm⟩
          rw [hmw, hhead_hcons] at hh
          rw [hmw, htail_hcons] at e₂
          show k = hanoiAux n f v t (hconsN (mvN f t) (hanoiAux n v t f s))
          rw [e₁, hmw, hh, e₂]
        · rw [if_neg hh] at h; exact absurd h (by simp)

/-- **The solution is unique**: anything `solvesN` accepts *is* the
canonical solution. -/
theorem solvesN_unique {n f t v k : ℕ} (h : solvesN n f t v k = 1) :
    k = hanoiN n f t v := by
  have e : hcheck n f t v k = some 0 := by
    by_contra hne
    rw [show solvesN n f t v k = 0 from if_neg hne] at h
    exact absurd h (by simp)
  exact hcheck_eq_hanoiAux n f t v k 0 e

/-! ## The move count -/

/-- Fuelled worker for `hlen`: the length of an encoded move-sequence. -/
def hlenAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, k + 1 => hlenAux fuel (pr2 k) + 1

/-- **`MoveCount`**: the length of an encoded sequence. -/
def hlen (k : ℕ) : ℕ := hlenAux k k

theorem hlenAux_succ_eq : ∀ (fuel k : ℕ), k ≤ fuel →
    hlenAux (fuel + 1) k = hlenAux fuel k
  | 0, k, h => by
    have hk : k = 0 := by omega
    subst hk; rfl
  | fuel + 1, k, h => by
    cases k with
    | zero => rfl
    | succ j =>
      have h2 : pr2 j ≤ fuel := by
        have := pr2_le j
        omega
      show hlenAux (fuel + 1) (pr2 j) + 1 = _
      rw [hlenAux_succ_eq fuel _ h2]
      rfl

theorem hlenAux_eq_of_le : ∀ (fuel k : ℕ), k ≤ fuel →
    hlenAux fuel k = hlenAux k k
  | 0, k, h => by
    have hk : k = 0 := by omega
    subst hk; rfl
  | fuel + 1, k, h => by
    rcases dec_em (k = fuel + 1) with he | he
    · rw [he]
    · have hf : k ≤ fuel := by omega
      rw [hlenAux_succ_eq fuel k hf, hlenAux_eq_of_le fuel k hf]

@[simp] theorem hlen_nil : hlen 0 = 0 := rfl

@[simp] theorem hlen_cons (m k : ℕ) : hlen (hconsN m k) = hlen k + 1 := by
  show hlenAux (pr m k + 1) (pr m k + 1) = _
  show hlenAux (pr m k) (pr2 (pr m k)) + 1 = _
  rw [pr2_pr]
  have hle : k ≤ pr m k := by
    have := pr2_le (pr m k)
    rw [pr2_pr] at this
    exact this
  rw [hlenAux_eq_of_le _ _ hle]
  rfl

/-- Concatenation adds lengths.  Strong induction on the first argument,
whose tail strictly decreases (`htail_lt`). -/
theorem hlen_happN : ∀ (k r : ℕ), hlen (happN k r) = hlen k + hlen r := by
  refine nat_strong_ind (fun k ih ↦ ?_)
  intro r
  rcases dec_em (k = 0) with h0 | h0
  · subst h0; simp
  · obtain ⟨m, w, hmw⟩ : ∃ m w, k = hconsN m w :=
      ⟨hhead k, htail k, (hcons_eta h0).symm⟩
    have hlt : w < k := by
      have hx := htail_lt h0
      rw [hmw, htail_hcons] at hx
      rw [hmw]
      exact hx
    rw [hmw, happN_cons, hlen_cons, hlen_cons, ih w hlt r]
    omega

/-- **The move count, at the value level**, subtraction-free: the `n`-disk
solution has `2^n - 1` moves, stated as `count + 1 = 2^n` so that the
fragment (which has `pred` but no order) can carry it without
subtraction.  The accumulator is generalized, as in `hcheck_hanoiAux`. -/
theorem hlen_hanoiAux : ∀ (n f t v r : ℕ),
    hlen (hanoiAux n f t v r) + 1 = 2 ^ n + hlen r
  | 0, _, _, _, r => by
    show hlen r + 1 = 2 ^ 0 + hlen r
    simp only [Nat.pow_zero]
    omega
  | n + 1, f, t, v, r => by
    show hlen (hanoiAux n f v t (hconsN (mvN f t) (hanoiAux n v t f r))) + 1 = _
    have h₁ := hlen_hanoiAux n f v t (hconsN (mvN f t) (hanoiAux n v t f r))
    have h₂ := hlen_hanoiAux n v t f r
    rw [hlen_cons] at h₁
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [Nat.pow_succ]
      omega
    omega

/-- The count of the actual solution. -/
theorem hlen_hanoiN (n f t v : ℕ) : hlen (hanoiN n f t v) + 1 = 2 ^ n := by
  have := hlen_hanoiAux n f t v 0
  simpa using this

/-- **Every solution has exactly `2^n − 1` moves** — not just the one the
derivation produces.  Immediate from uniqueness, and the precise sense in
which the extracted solution is optimal *for this relation*. -/
theorem solvesN_length {n f t v k : ℕ} (h : solvesN n f t v k = 1) :
    hlen k + 1 = 2 ^ n := by
  rw [solvesN_unique h]
  exact hlen_hanoiN n f t v

/-! ### Small instances, kernel-checked

`hanoiN n 0 2 1` is the sequence for `n` disks from peg `0` to peg `2`
via peg `1`, and `mvN a b = 3a + b`, so `2` is `0 → 2`, `1` is `0 → 1`,
`7` is `2 → 1`, and so on. -/

/-- One disk: a single move `0 → 2`.  Kernel-checked. -/
theorem hanoi_one : hanoiN 1 0 2 1 = hconsN (mvN 0 2) 0 := rfl

/-! Two disks — `0 → 1`, `0 → 2`, `1 → 2` — and the counts and validations
at the first four sizes.  These are `#guard`s rather than `rfl` theorems
for the reason Phase H8 recorded: the cons coding squares magnitudes at
every step, so the code of a 7-move sequence is astronomically large and
kernel reduction of the fueled recursions on it is hopeless, while
compiled evaluation takes microseconds (the fuel bounds the recursion but
the *list length* ends it). -/

#guard hanoiN 2 0 2 1 == hconsN (mvN 0 1) (hconsN (mvN 0 2) (hconsN (mvN 1 2) 0))

#guard hlen (hanoiN 0 0 2 1) == 0
#guard hlen (hanoiN 1 0 2 1) == 1
#guard hlen (hanoiN 2 0 2 1) == 3
#guard hlen (hanoiN 3 0 2 1) == 7
#guard hlen (hanoiN 4 0 2 1) == 15

#guard solvesN 0 0 2 1 (hanoiN 0 0 2 1) == 1
#guard solvesN 1 0 2 1 (hanoiN 1 0 2 1) == 1
#guard solvesN 2 0 2 1 (hanoiN 2 0 2 1) == 1
#guard solvesN 3 0 2 1 (hanoiN 3 0 2 1) == 1
#guard solvesN 4 0 2 1 (hanoiN 4 0 2 1) == 1

/-! And the validator genuinely rejects: a sequence that is *not* a
solution scores `0`.  Without this the existence theorem would be
vacuous — `solves` could have been the constant `1`. -/

#guard solvesN 2 0 2 1 (hconsN (mvN 0 2) (hconsN (mvN 0 1) (hconsN (mvN 1 2) 0))) == 0
#guard solvesN 2 0 2 1 0 == 0
#guard solvesN 1 0 2 1 (hconsN (mvN 0 1) 0) == 0

#print axioms solvesN_hanoiN
#print axioms solvesN_succ
#print axioms hlen_hanoiN

end Realizability
