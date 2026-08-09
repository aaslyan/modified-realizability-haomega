/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Mathlib.Logic.Function.Basic

/-!
# Phase C: ordinal notations below `ε₀` and their order, at the value level

The value-level layer of the transfinite-induction rule `tiEps0`: the
notations, their order `≺`, the normal-form predicate that makes that
order well-founded, and the well-foundedness theorem itself.  It sits
*before* `Syntax.lean` in the module chain (like the Phase-B functions
`hlog`/`bumpN`/`goodN`) because `Term.eval` consumes the order as the
semantics of the new function symbol `prec`.

## Notations are natural numbers, and the coding is a bijection

The fragment's variables range over `ℕ` — it has no second sort — so the
rule `tiEps0` quantifies over *codes*.  A code is read as a
Cantor-normal-form tree:

    code 0                        ↦  the ordinal 0
    mkO e c r = ⟪e, ⟪c, r⟫⟫ + 1   ↦  ω^(e) · (c+1) + (r)

The pairing `⟪·,·⟫` is the triangular (Cantor) one, built from scratch
below.  It is a bijection, so `n ↦ (oE n, oC n, oR n)` inverts `mkO`
exactly (`mkO_oE_oC_oR`): **every** natural number is the code of exactly
one such tree, and every such tree has a code.  So the rule's
`∀x` ranges over precisely the notations — no unused codes, no partial
decoding.  The `+1`/`c+1` offsets are what make this exact: `0` is
reserved for the zero ordinal and coefficients are automatically
positive.

This is the same shape as Phase B's hereditary representations —
`hrep k n` is the term `x^e·c + r` in the base variable — with the base
variable read as `ω` instead of a numeral.  `TransfiniteInduction.lean`
makes that identification explicit (`ordTerm`, which decodes a code into
a Phase-B `HTerm`).

## The order, and why normal forms are not optional

`precB` is the standard Cantor-normal-form comparison: compare leading
exponents (recursively — ordinal comparison is always nested like
this), then coefficients, then remainders.  On **arbitrary** trees this
relation is *not* well-founded, and the counterexample is one line:

    ω  ≻  1 + ω  ≻  1 + (1 + ω)  ≻  1 + (1 + (1 + ω))  ≻  …

every step compares leading exponents `0 ≺ 1` and wins, while all four
trees denote the same ordinal `ω` (since `1 + ω = ω`).  Two
representations of one ordinal, and the comparison ranks one strictly
below the other: exactly the ambiguity Phase B could defer and this
phase cannot.  So the order used by the rule (`oltB`) conjoins the
comparison with the **normal-form predicate** `nfB` — remainders'
leading exponents strictly below the head exponent, hereditarily.  Non-
normal codes are then `≺`-isolated: nothing precedes them, so they are
trivially accessible, and the rule still concludes `∀x φ(x)` for every
natural number.

## Fuel, not well-founded recursion, at the value level

`precAux`/`nfAux` recurse structurally on fuel, with `oE`/`oR` strictly
decreasing (`oE_lt`, `oR_lt`) so that fuel `= a + b` (resp. `= n`) is
adequate.  Same reason as Phase B: `WellFounded.fix` does not reduce in
the kernel, and the concrete cross-checks of
`TransfiniteInduction.lean` are `rfl`/`decide`.  Since the pairing here
is also structural, the whole notation layer computes in the kernel.

The *realizer* combinator `tiRecC` (`Extraction.lean`) is the one place
genuine well-founded recursion is used — it is noncomputable and never
asked to reduce.  That is also why every proof in this file avoids
`Classical` (see `dec_em`): `tiRecC`'s **definition** mentions `oLt_wf`,
so this file's axiom footprint is inherited by every continuity theorem
downstream.  It stays at `[propext, Quot.sound]`.
-/

namespace Realizability

/-- Decidable case split, spelled out.  Mathlib's `by_cases` tactic can
fall back on `Classical.byCases`, and everything in this module feeds the
*definition* of the recursor `tiRecC` — so a stray `Classical.choice`
here would show up in the axioms of every continuity theorem downstream.
Each case split below goes through this instead. -/
theorem dec_em (p : Prop) [Decidable p] : p ∨ ¬ p :=
  if h : p then Or.inl h else Or.inr h

/-! ## A choice-free, kernel-computable pairing

Mathlib's `Nat.pair`/`Nat.unpair` cannot be used for the coding.  Its
inverse goes through `Nat.sqrt`, and *every* Mathlib lemma about that
pairing (`Nat.pair_unpair`, `Nat.unpair_left_le`, …) depends on
`Classical.choice`.  The coding enters the **definition** of the
recursor `tiRecC`, hence the axioms of every continuity theorem
downstream — where the budget is `[propext, Quot.sound]`.  `Nat.sqrt`
also fails to reduce in the kernel, which would cost the `rfl`
cross-checks.

So the triangular (Cantor) pairing is built here from scratch:
structural recursion, a fueled inverse (search downward for the largest
triangular number below `n`), and arithmetic-only proofs.  Both
directions reduce in the kernel, and nothing below depends on any axiom
beyond `propext`. -/

/-- Triangular numbers, structurally. -/
def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + (n + 1)

theorem tri_succ (n : ℕ) : tri (n + 1) = tri n + (n + 1) := rfl

theorem self_le_tri : ∀ n : ℕ, n ≤ tri n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    have := self_le_tri n
    rw [tri_succ]
    omega

theorem tri_le_tri : ∀ {m n : ℕ}, m ≤ n → tri m ≤ tri n := by
  intro m n h
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ n ih =>
    rcases dec_em (m = n + 1) with hm | hm
    · subst hm; exact Nat.le_refl _
    · have h' : m ≤ n := by omega
      have := ih h'
      rw [tri_succ]
      omega

/-- The closed form.  `tri` is defined by unary recursion — which is what
the proofs and the kernel want — but that makes *evaluation* `O(n)`, and
the Hydra layer's codes are large enough to overflow the interpreter's
stack.  `@[csimp]` swaps in the constant-time version for compiled code,
backed by the proof below.  The definition and every proof about it are
untouched. -/
def triFast (n : ℕ) : ℕ := n * (n + 1) / 2

theorem two_mul_tri : ∀ n : ℕ, 2 * tri n = n * (n + 1)
  | 0 => rfl
  | n + 1 => by
    have ih := two_mul_tri n
    have h1 : (n + 1) * (n + 1 + 1) = (n + 1) * (n + 1) + (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have h2 : (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [tri_succ]
    omega

theorem tri_eq_triFast (n : ℕ) : tri n = triFast n := by
  have h := two_mul_tri n
  simp only [triFast]
  omega

@[csimp] theorem tri_eq_triFast' : tri = triFast := funext tri_eq_triFast

/-- The largest `t` with `tri t ≤ n`, searching downward from the fuel. -/
def unTriAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if tri (f + 1) ≤ n then f + 1 else unTriAux f n

/-- The index of the triangular block containing `n`. -/
def unTri (n : ℕ) : ℕ := unTriAux n n

theorem tri_unTriAux_le : ∀ (f n : ℕ), tri (unTriAux f n) ≤ n
  | 0, n => Nat.zero_le n
  | f + 1, n => by
    show tri (if tri (f + 1) ≤ n then f + 1 else unTriAux f n) ≤ n
    rcases dec_em (tri (f + 1) ≤ n) with h | h
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact tri_unTriAux_le f n

theorem unTriAux_ge : ∀ (f n t : ℕ), t ≤ f → tri t ≤ n → t ≤ unTriAux f n
  | 0, n, t, hf, _ => by omega
  | f + 1, n, t, hf, ht => by
    show t ≤ if tri (f + 1) ≤ n then f + 1 else unTriAux f n
    rcases dec_em (tri (f + 1) ≤ n) with h | h
    · rw [if_pos h]; exact hf
    · rw [if_neg h]
      have htf : t ≤ f := by
        rcases dec_em (t = f + 1) with he | he
        · exact absurd (he ▸ ht) h
        · omega
      exact unTriAux_ge f n t htf ht

theorem tri_unTri_le (n : ℕ) : tri (unTri n) ≤ n :=
  tri_unTriAux_le n n

theorem unTri_ge {n t : ℕ} (ht : tri t ≤ n) : t ≤ unTri n :=
  unTriAux_ge n n t (Nat.le_trans (self_le_tri t) ht) ht

/-- `n` lies strictly below the next triangular number: the maximality
half of `unTri`. -/
theorem lt_tri_unTri_succ (n : ℕ) : n < tri (unTri n + 1) := by
  by_contra h
  have := unTri_ge (n := n) (t := unTri n + 1) (by omega)
  omega

/-! ### A fast inverse

`unTriAux` searches downward one step at a time, which is `O(n)` and, being
non-tail-recursive, overflows the stack on the Hydra layer's codes.  The
binary search below is `O(log n)`.  Proving them equal needs no new
arithmetic: `unTri` is *characterised* by the two inequalities
`tri t ≤ n < tri (t + 1)` (`tri_unTri_le`, `lt_tri_unTri_succ`), those
determine `t` uniquely, and the search maintains exactly them as its
invariant. -/

/-- Largest `t ∈ [lo, hi]` with `tri t ≤ n`, by bisection.  `fuel` bounds
the number of halvings; the invariant is `tri lo ≤ n < tri (hi + 1)`. -/
def unTriBin : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, lo, _ => lo
  | fuel + 1, n, lo, hi =>
      if hi ≤ lo then lo
      else
        let mid := (lo + hi + 1) / 2
        if tri mid ≤ n then unTriBin fuel n mid hi else unTriBin fuel n lo (mid - 1)

theorem unTriBin_zero (n lo hi : ℕ) : unTriBin 0 n lo hi = lo := rfl

theorem unTriBin_succ (fuel n lo hi : ℕ) :
    unTriBin (fuel + 1) n lo hi =
      if hi ≤ lo then lo
      else if tri ((lo + hi + 1) / 2) ≤ n then
        unTriBin fuel n ((lo + hi + 1) / 2) hi
      else unTriBin fuel n lo ((lo + hi + 1) / 2 - 1) := rfl

theorem unTriBin_spec : ∀ (fuel n lo hi : ℕ), hi - lo ≤ fuel → tri lo ≤ n →
    n < tri (hi + 1) →
    tri (unTriBin fuel n lo hi) ≤ n ∧ n < tri (unTriBin fuel n lo hi + 1)
  | 0, n, lo, hi, hf, hlo, hhi => by
    rw [unTriBin_zero]
    have h : tri (hi + 1) ≤ tri (lo + 1) := tri_le_tri (by omega)
    exact ⟨hlo, by omega⟩
  | fuel + 1, n, lo, hi, hf, hlo, hhi => by
    rw [unTriBin_succ]
    rcases dec_em (hi ≤ lo) with hc | hc
    · rw [if_pos hc]
      have h : tri (hi + 1) ≤ tri (lo + 1) := tri_le_tri (by omega)
      exact ⟨hlo, by omega⟩
    · rw [if_neg hc]
      have hmid1 : lo + 1 ≤ (lo + hi + 1) / 2 := by omega
      have hmid2 : (lo + hi + 1) / 2 ≤ hi := by omega
      rcases dec_em (tri ((lo + hi + 1) / 2) ≤ n) with ht | ht
      · rw [if_pos ht]
        exact unTriBin_spec fuel n _ hi (by omega) ht hhi
      · rw [if_neg ht]
        refine unTriBin_spec fuel n lo _ (by omega) hlo ?_
        have he : (lo + hi + 1) / 2 - 1 + 1 = (lo + hi + 1) / 2 := by omega
        rw [he]
        omega

/-- The fast inverse. -/
def unTriFast (n : ℕ) : ℕ := unTriBin n n 0 n

/-- The two inequalities determine the index uniquely. -/
theorem unTri_unique {n t : ℕ} (h1 : tri t ≤ n) (h2 : n < tri (t + 1)) :
    t = unTri n := by
  have hu1 := tri_unTri_le n
  have hu2 := lt_tri_unTri_succ n
  rcases dec_em (t ≤ unTri n) with hle | hle
  · rcases dec_em (t = unTri n) with he | he
    · exact he
    · have : tri (t + 1) ≤ tri (unTri n) := tri_le_tri (by omega)
      omega
  · have : tri (unTri n + 1) ≤ tri t := tri_le_tri (by omega)
    omega

theorem unTri_eq_unTriFast (n : ℕ) : unTri n = unTriFast n := by
  have hn : n < tri (n + 1) := by
    have := self_le_tri n
    rw [tri_succ]
    omega
  have h := unTriBin_spec n n 0 n (by omega) (by simp [tri]) hn
  exact (unTri_unique h.1 h.2).symm

@[csimp] theorem unTri_eq_unTriFast' : unTri = unTriFast :=
  funext unTri_eq_unTriFast

/-- The triangular pairing. -/
def pr (a b : ℕ) : ℕ := tri (a + b) + b

/-- Its second component. -/
def pr2 (n : ℕ) : ℕ := n - tri (unTri n)

/-- Its first component. -/
def pr1 (n : ℕ) : ℕ := unTri n - pr2 n

theorem pr_eq (a b : ℕ) : pr a b = tri (a + b) + b := rfl

theorem pr2_eq (n : ℕ) : pr2 n = n - tri (unTri n) := rfl

theorem pr1_eq (n : ℕ) : pr1 n = unTri n - pr2 n := rfl

theorem unTri_pr (a b : ℕ) : unTri (pr a b) = a + b := by
  have h5 := pr_eq a b
  have h1 : a + b ≤ unTri (pr a b) := unTri_ge (by omega)
  have h4 := tri_unTri_le (pr a b)
  by_contra h
  have h3 : tri (a + b + 1) ≤ tri (unTri (pr a b)) := tri_le_tri (by omega)
  rw [tri_succ] at h3
  omega

@[simp] theorem pr2_pr (a b : ℕ) : pr2 (pr a b) = b := by
  have h5 := pr_eq a b
  rw [pr2_eq, unTri_pr]
  omega

@[simp] theorem pr1_pr (a b : ℕ) : pr1 (pr a b) = a := by
  rw [pr1_eq, unTri_pr, pr2_pr]
  omega

/-- The pairing is surjective: every natural number is a pair. -/
theorem pr_pr1_pr2 (n : ℕ) : pr (pr1 n) (pr2 n) = n := by
  have h1 := tri_unTri_le n
  have h2 := lt_tri_unTri_succ n
  rw [tri_succ] at h2
  have hb := pr2_eq n
  have hsum : pr1 n + pr2 n = unTri n := by
    have := pr1_eq n
    omega
  rw [pr_eq, hsum]
  omega

theorem pr1_le (n : ℕ) : pr1 n ≤ n := by
  have h1 := tri_unTri_le n
  have h2 := self_le_tri (unTri n)
  have h3 := pr1_eq n
  omega

theorem pr2_le (n : ℕ) : pr2 n ≤ n := by
  have := pr2_eq n
  omega

/-- Strong induction on `ℕ`, proved here so that this module needs no
import beyond the `ℕ` notation itself (keeping its axiom footprint to
`propext` alone). -/
theorem nat_strong_ind {P : ℕ → Prop}
    (H : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n) : ∀ n : ℕ, P n := by
  have key : ∀ n m : ℕ, m < n → P m := by
    intro n
    induction n with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ n ih =>
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
      · exact ih m h
      · exact h ▸ H n ih
  intro n
  exact H n (key n)

/-! ## Codes -/

/-- The code of the notation `ω^e · (c+1) + r`. -/
def mkO (e c r : ℕ) : ℕ := pr e (pr c r) + 1

/-- The head exponent of a nonzero notation. -/
def oE (n : ℕ) : ℕ := pr1 (n - 1)

/-- The head coefficient (offset by one: `oC n + 1` is the coefficient). -/
def oC (n : ℕ) : ℕ := pr1 (pr2 (n - 1))

/-- The remainder of a nonzero notation. -/
def oR (n : ℕ) : ℕ := pr2 (pr2 (n - 1))

@[simp] theorem oE_mkO (e c r : ℕ) : oE (mkO e c r) = e := by
  simp [oE, mkO]

@[simp] theorem oC_mkO (e c r : ℕ) : oC (mkO e c r) = c := by
  simp [oC, mkO]

@[simp] theorem oR_mkO (e c r : ℕ) : oR (mkO e c r) = r := by
  simp [oR, mkO]

@[simp] theorem mkO_ne_zero (e c r : ℕ) : mkO e c r ≠ 0 := by
  simp [mkO]

/-- **The coding is a bijection**: every nonzero code decomposes, and
uniquely (the destructors are literal inverses of `mkO`). -/
theorem mkO_oE_oC_oR {n : ℕ} (h : n ≠ 0) : mkO (oE n) (oC n) (oR n) = n := by
  have h1 : n - 1 + 1 = n := by omega
  show pr (pr1 (n - 1)) (pr (pr1 (pr2 (n - 1))) (pr2 (pr2 (n - 1)))) + 1 = n
  rw [pr_pr1_pr2, pr_pr1_pr2, h1]

/-- The head exponent is a strictly smaller code (the fuel measure). -/
theorem oE_lt {n : ℕ} (h : n ≠ 0) : oE n < n := by
  have := pr1_le (n - 1)
  simp only [oE]
  omega

/-- The remainder is a strictly smaller code (the fuel measure). -/
theorem oR_lt {n : ℕ} (h : n ≠ 0) : oR n < n := by
  have h1 := pr2_le (n - 1)
  have h2 := pr2_le (pr2 (n - 1))
  simp only [oR]
  omega

/-! ## The Cantor-normal-form comparison -/

/-- **The order on notations**, fueled: compare leading exponents
(recursively), then coefficients, then remainders.  `precAux f a b`
decides `a ≺ b` provided `a + b ≤ f`. -/
def precAux : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
      if b = 0 then false
      else if a = 0 then true
      else if oE a = oE b then
        (if oC a < oC b then true
         else if oC b < oC a then false
         else precAux f (oR a) (oR b))
      else precAux f (oE a) (oE b)

/-- One unfolding of the comparison (the defining equation, stated so
that rewriting with it does not cascade into the recursive calls). -/
theorem precAux_succ (f a b : ℕ) :
    precAux (f + 1) a b =
      (if b = 0 then false
       else if a = 0 then true
       else if oE a = oE b then
         (if oC a < oC b then true
          else if oC b < oC a then false
          else precAux f (oR a) (oR b))
       else precAux f (oE a) (oE b)) := rfl

/-- Above the adequate fuel one more unit changes nothing. -/
theorem precAux_succ_eq : ∀ (f a b : ℕ), a + b ≤ f →
    precAux (f + 1) a b = precAux f a b
  | 0, a, b, h => by
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    simp [precAux]
  | f + 1, a, b, h => by
    rw [precAux_succ (f + 1) a b, precAux_succ f a b]
    rcases dec_em (b = 0) with hb | hb
    · rw [if_pos hb, if_pos hb]
    · rcases dec_em (a = 0) with ha | ha
      · rw [if_neg hb, if_neg hb, if_pos ha, if_pos ha]
      · have hE : oE a + oE b ≤ f := by
          have h1 := oE_lt ha
          have h2 := oE_lt hb
          omega
        have hR : oR a + oR b ≤ f := by
          have h1 := oR_lt ha
          have h2 := oR_lt hb
          omega
        rw [precAux_succ_eq f (oE a) (oE b) hE,
          precAux_succ_eq f (oR a) (oR b) hR]

/-- Any adequate fuel gives the same answer. -/
theorem precAux_eq_of_le : ∀ (f a b : ℕ), a + b ≤ f →
    precAux f a b = precAux (a + b) a b
  | 0, a, b, h => by
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb; rfl
  | f + 1, a, b, h => by
    rcases dec_em (a + b = f + 1) with he | he
    · rw [he]
    · have hf : a + b ≤ f := by omega
      rw [precAux_succ_eq f a b hf, precAux_eq_of_le f a b hf]

/-- **`a ≺ b`, decided**: the Cantor-normal-form comparison at its
adequate fuel. -/
def precB (a b : ℕ) : Bool := precAux (a + b) a b

theorem precB_zero_right (a : ℕ) : precB a 0 = false := by
  simp only [precB]
  cases h : a + 0 with
  | zero => simp [precAux]
  | succ f => simp [precAux]

theorem precB_zero_left {b : ℕ} (h : b ≠ 0) : precB 0 b = true := by
  simp only [precB]
  cases hb : 0 + b with
  | zero => omega
  | succ f => simp [precAux, h]

/-- **The characterization of the comparison** at nonzero arguments: one
unfolding, with the recursive calls back in `precB` form. -/
theorem precB_pos {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    precB a b =
      (if oE a = oE b then
        (if oC a < oC b then true
         else if oC b < oC a then false
         else precB (oR a) (oR b))
       else precB (oE a) (oE b)) := by
  have hab : a + b ≠ 0 := by omega
  obtain ⟨f, hf⟩ : ∃ f, a + b = f + 1 := ⟨a + b - 1, by omega⟩
  have hE : oE a + oE b ≤ f := by
    have h1 := oE_lt ha
    have h2 := oE_lt hb
    omega
  have hR : oR a + oR b ≤ f := by
    have h1 := oR_lt ha
    have h2 := oR_lt hb
    omega
  show precAux (a + b) a b = _
  rw [hf]
  simp only [precAux, if_neg hb, if_neg ha, precB,
    precAux_eq_of_le f (oE a) (oE b) hE, precAux_eq_of_le f (oR a) (oR b) hR]

/-! ## Normal forms

A code is in normal form when, hereditarily, the remainder's leading
exponent is strictly below the head exponent — the standard
Cantor-normal-form condition (strictly decreasing exponents), with
positive coefficients already built into the coding. -/

/-- The normal-form predicate, fueled (`nfAux f n` decides it provided
`n ≤ f`). -/
def nfAux : ℕ → ℕ → Bool
  | 0, n => decide (n = 0)
  | f + 1, n =>
      if n = 0 then true
      else nfAux f (oE n) && nfAux f (oR n) &&
        (decide (oR n = 0) || precB (oE (oR n)) (oE n))

/-- One unfolding of the normal-form test. -/
theorem nfAux_succ (f n : ℕ) :
    nfAux (f + 1) n =
      (if n = 0 then true
       else nfAux f (oE n) && nfAux f (oR n) &&
         (decide (oR n = 0) || precB (oE (oR n)) (oE n))) := rfl

theorem nfAux_succ_eq : ∀ (f n : ℕ), n ≤ f → nfAux (f + 1) n = nfAux f n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn; simp [nfAux]
  | f + 1, n, h => by
    rw [nfAux_succ (f + 1) n, nfAux_succ f n]
    rcases dec_em (n = 0) with hn | hn
    · rw [if_pos hn, if_pos hn]
    · have hE : oE n ≤ f := by
        have := oE_lt hn
        omega
      have hR : oR n ≤ f := by
        have := oR_lt hn
        omega
      rw [if_neg hn, if_neg hn, nfAux_succ_eq f (oE n) hE,
        nfAux_succ_eq f (oR n) hR]

theorem nfAux_eq_of_le : ∀ (f n : ℕ), n ≤ f → nfAux f n = nfAux n n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn; rfl
  | f + 1, n, h => by
    rcases dec_em (n = f + 1) with he | he
    · rw [he]
    · have hf : n ≤ f := by omega
      rw [nfAux_succ_eq f n hf, nfAux_eq_of_le f n hf]

/-- **Normal form**, at the adequate fuel. -/
def nfB (n : ℕ) : Bool := nfAux n n

@[simp] theorem nfB_zero : nfB 0 = true := rfl

/-- The characterization of normal form at a nonzero code. -/
theorem nfB_pos {n : ℕ} (h : n ≠ 0) :
    nfB n = (nfB (oE n) && nfB (oR n) &&
      (decide (oR n = 0) || precB (oE (oR n)) (oE n))) := by
  obtain ⟨f, hf⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega⟩
  have hE : oE n ≤ f := by
    have := oE_lt h
    omega
  have hR : oR n ≤ f := by
    have := oR_lt h
    omega
  show nfAux n n = _
  rw [hf]
  simp only [nfAux, if_neg (show ¬ f + 1 = 0 by omega), nfB,
    nfAux_eq_of_le f (oE (f + 1)) (by rw [← hf]; exact hE),
    nfAux_eq_of_le f (oR (f + 1)) (by rw [← hf]; exact hR)]

/-! ## The order used by the rule

The comparison, restricted to normal forms.  Restricting *inside the
relation* rather than by a side condition on the rule is what keeps the
rule's conclusion `∀x φ(x)` unrestricted: a non-normal code has no
`≺`-predecessors, so the progressiveness premise proves `φ` of it
outright. -/

/-- `a ≺ b`: both codes normal, and `a` below `b` in Cantor normal
form. -/
def oltB (a b : ℕ) : Bool := nfB a && nfB b && precB a b

/-- The order as a `Prop`-valued relation (the recursion argument of
`tiRecC`). -/
def OLt (a b : ℕ) : Prop := oltB a b = true

instance decidableOLt (a b : ℕ) : Decidable (OLt a b) :=
  inferInstanceAs (Decidable (oltB a b = true))

/-- The characteristic function of `≺`, the semantics of the fragment's
`prec` symbol. -/
def oltN (a b : ℕ) : ℕ := if oltB a b then 1 else 0

theorem oltN_eq_one_iff {a b : ℕ} : oltN a b = 1 ↔ OLt a b := by
  simp only [oltN, OLt]
  rcases dec_em (oltB a b = true) with h | h
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h]

theorem OLt.nf_left {a b : ℕ} (h : OLt a b) : nfB a = true := by
  simp only [OLt, oltB, Bool.and_eq_true] at h
  exact h.1.1

theorem OLt.nf_right {a b : ℕ} (h : OLt a b) : nfB b = true := by
  simp only [OLt, oltB, Bool.and_eq_true] at h
  exact h.1.2

theorem OLt.prec {a b : ℕ} (h : OLt a b) : precB a b = true := by
  simp only [OLt, oltB, Bool.and_eq_true] at h
  exact h.2

theorem olt_of {a b : ℕ} (ha : nfB a = true) (hb : nfB b = true)
    (h : precB a b = true) : OLt a b := by
  simp only [OLt, oltB, Bool.and_eq_true]
  exact ⟨⟨ha, hb⟩, h⟩

/-! ## The normal-form predicate, destructed and constructed -/

theorem nfB_exp {n : ℕ} (h : n ≠ 0) (hn : nfB n = true) : nfB (oE n) = true := by
  rw [nfB_pos h] at hn
  simp only [Bool.and_eq_true] at hn
  exact hn.1.1

theorem nfB_rem {n : ℕ} (h : n ≠ 0) (hn : nfB n = true) : nfB (oR n) = true := by
  rw [nfB_pos h] at hn
  simp only [Bool.and_eq_true] at hn
  exact hn.1.2

/-- `r` fits under the head exponent `e`: it is zero, or its own head
exponent is strictly below `e`.  Hereditarily, this is the
Cantor-normal-form condition. -/
def OBelow (e r : ℕ) : Prop := r = 0 ∨ precB (oE r) e = true

theorem nfB_below {n : ℕ} (h : n ≠ 0) (hn : nfB n = true) :
    OBelow (oE n) (oR n) := by
  rw [nfB_pos h] at hn
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hn
  exact hn.2

theorem nfB_mkO {e c r : ℕ} (he : nfB e = true) (hr : nfB r = true)
    (hbel : OBelow e r) : nfB (mkO e c r) = true := by
  rw [nfB_pos (mkO_ne_zero e c r), oE_mkO, oR_mkO]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨⟨he, hr⟩, hbel⟩

/-- The three ways one nonzero notation can precede another: a smaller
head exponent, an equal head exponent with a smaller coefficient, or
both equal and a smaller remainder. -/
theorem precB_cases {y x : ℕ} (hy : y ≠ 0) (hx : x ≠ 0)
    (h : precB y x = true) :
    precB (oE y) (oE x) = true ∨
      (oE y = oE x ∧
        (oC y < oC x ∨ (oC y = oC x ∧ precB (oR y) (oR x) = true))) := by
  rw [precB_pos hy hx] at h
  rcases dec_em (oE y = oE x) with he | he
  · rw [if_pos he] at h
    refine Or.inr ⟨he, ?_⟩
    rcases dec_em (oC y < oC x) with hc | hc
    · exact Or.inl hc
    · rw [if_neg hc] at h
      rcases dec_em (oC x < oC y) with hc' | hc'
      · rw [if_pos hc'] at h
        exact absurd h (by simp)
      · rw [if_neg hc'] at h
        exact Or.inr ⟨by omega, h⟩
  · rw [if_neg he] at h
    exact Or.inl h

/-! ## Well-foundedness

The theorem the recursor rests on.  Structure of the proof — the
classical one for Cantor normal forms, with each induction named:

* `acc_zero`: the zero notation has no predecessors.
* `acc_mkO`: **three nested inductions**.  Outer, on the accessibility
  of the head exponent `e` (this is where the notation system's height
  is consumed); middle, strong induction on the coefficient; inner, on
  the accessibility of the remainder — itself obtained from the *outer*
  induction hypothesis, since a normal form's remainder has a head
  exponent strictly below `e`.  The three cases of `precB_cases` are
  discharged by exactly these three induction hypotheses, in order.
* `acc_of_nf`: strong induction on the code (both destructors strictly
  decrease it) supplies the head exponent's accessibility to `acc_mkO`.
* `oLt_wf`: normal codes by `acc_of_nf`, non-normal codes trivially —
  `oltB` requires normality of *both* sides, so nothing precedes a
  non-normal code.

No ordinals, no choice, no `Classical` case split: `nfB`/`precB` are
`Bool`-valued, so every case split above is decidable.  That keeps the
continuity theorems' axiom budget at `[propext, Quot.sound]` even
though `tiRecC` is defined by well-founded recursion on `OLt`. -/

theorem acc_zero : Acc OLt 0 :=
  Acc.intro 0 fun _ hy ↦ absurd hy.prec (by simp [precB_zero_right])

theorem acc_mkO : ∀ {e : ℕ}, Acc OLt e → nfB e = true →
    ∀ (c r : ℕ), nfB r = true → OBelow e r → Acc OLt (mkO e c r) := by
  intro e he
  induction he with
  | intro e hpred ih =>
    intro hNFe
    refine nat_strong_ind (fun c ihc ↦ ?_)
    -- The remainder is accessible: its head exponent is below `e`, so
    -- the *outer* induction hypothesis applies to it.
    have haccr : ∀ r, nfB r = true → OBelow e r → Acc OLt r := by
      intro r hNFr hbel
      rcases dec_em (r = 0) with hr0 | hr0
      · subst hr0; exact acc_zero
      · have hbel' : precB (oE r) e = true := by
          rcases hbel with h | h
          · exact absurd h hr0
          · exact h
        have holt : OLt (oE r) e :=
          olt_of (nfB_exp hr0 hNFr) hNFe hbel'
        have := ih (oE r) holt (nfB_exp hr0 hNFr) (oC r) (oR r)
          (nfB_rem hr0 hNFr) (nfB_below hr0 hNFr)
        rwa [mkO_oE_oC_oR hr0] at this
    -- The inner induction, on the remainder's accessibility.
    have key : ∀ r, Acc OLt r → nfB r = true → OBelow e r →
        Acc OLt (mkO e c r) := by
      intro r har
      induction har with
      | intro r hpr ihr =>
        intro hNFr hbel
        refine Acc.intro _ ?_
        intro y hy
        rcases dec_em (y = 0) with hy0 | hy0
        · subst hy0; exact acc_zero
        · have hNFy : nfB y = true := hy.nf_left
          have hNFyE : nfB (oE y) = true := nfB_exp hy0 hNFy
          have hNFyR : nfB (oR y) = true := nfB_rem hy0 hNFy
          rcases precB_cases hy0 (mkO_ne_zero e c r) hy.prec with
            hcase | ⟨heq, hcase⟩
          · -- Smaller head exponent: the outer induction hypothesis.
            rw [oE_mkO] at hcase
            have := ih (oE y) (olt_of hNFyE hNFe hcase) hNFyE (oC y) (oR y)
              hNFyR (nfB_below hy0 hNFy)
            rwa [mkO_oE_oC_oR hy0] at this
          · rw [oE_mkO] at heq
            have hbelY : OBelow e (oR y) := by
              have := nfB_below hy0 hNFy
              rwa [heq] at this
            rcases hcase with hlt | ⟨hceq, hrlt⟩
            · -- Equal head exponent, smaller coefficient: the middle
              -- (coefficient) induction hypothesis.
              rw [oC_mkO] at hlt
              have := ihc (oC y) hlt (oR y) hNFyR hbelY
              rw [← heq] at this
              rwa [mkO_oE_oC_oR hy0] at this
            · -- Equal head and coefficient, smaller remainder: the
              -- inner (remainder) induction hypothesis.
              rw [oC_mkO] at hceq
              rw [oR_mkO] at hrlt
              have := ihr (oR y) (olt_of hNFyR hNFr hrlt) hNFyR hbelY
              rw [← hceq, ← heq] at this
              rwa [mkO_oE_oC_oR hy0] at this
    intro r hNFr hbel
    exact key r (haccr r hNFr hbel) hNFr hbel

theorem acc_of_nf : ∀ (n : ℕ), nfB n = true → Acc OLt n := by
  refine nat_strong_ind (fun n ihn ↦ ?_)
  intro hn
  rcases dec_em (n = 0) with h0 | h0
  · subst h0; exact acc_zero
  · have haccE : Acc OLt (oE n) :=
      ihn (oE n) (oE_lt h0) (nfB_exp h0 hn)
    have := acc_mkO haccE (nfB_exp h0 hn) (oC n) (oR n) (nfB_rem h0 hn)
      (nfB_below h0 hn)
    rwa [mkO_oE_oC_oR h0] at this

/-- **The order on notations below `ε₀` is well-founded.**  This is the
one theorem the transfinite recursor rests on; everything else about
`≺` is decidable computation. -/
theorem oLt_wf : WellFounded OLt := by
  refine ⟨fun n ↦ ?_⟩
  rcases dec_em (nfB n = true) with h | h
  · exact acc_of_nf n h
  · exact Acc.intro n fun _ hy ↦ absurd hy.nf_right h

/-! ## Constructors for the order

The three ways one notation can precede another, read as inference
rules.  Concrete comparisons *do* reduce in the kernel (so `decide`
works on closed instances), but proofs about symbolic notations —
what Phase D needs — go through these. -/

/-- Nothing precedes itself. -/
theorem precB_irrefl : ∀ (a : ℕ), precB a a = false := by
  refine nat_strong_ind (fun a ih ↦ ?_)
  rcases dec_em (a = 0) with h | h
  · subst h; exact precB_zero_right 0
  · rw [precB_pos h h, if_pos rfl, if_neg (Nat.lt_irrefl _),
      if_neg (Nat.lt_irrefl _)]
    exact ih (oR a) (oR_lt h)

/-- Zero precedes every nonzero notation. -/
theorem precB_zero_mkO (e c r : ℕ) : precB 0 (mkO e c r) = true :=
  precB_zero_left (mkO_ne_zero e c r)

/-- A strictly smaller head exponent wins. -/
theorem precB_mkO_exp {e₁ e₂ : ℕ} (c₁ r₁ c₂ r₂ : ℕ) (h : precB e₁ e₂ = true) :
    precB (mkO e₁ c₁ r₁) (mkO e₂ c₂ r₂) = true := by
  have hne : e₁ ≠ e₂ := by
    intro he
    rw [he, precB_irrefl] at h
    exact absurd h (by simp)
  rw [precB_pos (mkO_ne_zero _ _ _) (mkO_ne_zero _ _ _), oE_mkO, oE_mkO, if_neg hne]
  exact h

/-- Equal head exponents: the smaller coefficient wins. -/
theorem precB_mkO_coeff (e : ℕ) {c₁ c₂ : ℕ} (r₁ r₂ : ℕ) (h : c₁ < c₂) :
    precB (mkO e c₁ r₁) (mkO e c₂ r₂) = true := by
  rw [precB_pos (mkO_ne_zero _ _ _) (mkO_ne_zero _ _ _), oE_mkO, oE_mkO, if_pos rfl,
    oC_mkO, oC_mkO, if_pos h]

/-- Equal head exponents and coefficients: the smaller remainder wins. -/
theorem precB_mkO_rem (e c : ℕ) {r₁ r₂ : ℕ} (h : precB r₁ r₂ = true) :
    precB (mkO e c r₁) (mkO e c r₂) = true := by
  rw [precB_pos (mkO_ne_zero _ _ _) (mkO_ne_zero _ _ _), oE_mkO, oE_mkO, if_pos rfl,
    oC_mkO, oC_mkO, if_neg (Nat.lt_irrefl _), if_neg (Nat.lt_irrefl _), oR_mkO, oR_mkO]
  exact h

/-! ## The canonicity failure, exhibited

The statements below are the machine-checked form of the finding
recorded in this file's header and in docs/first-order/STATUS.md.  With `ω` coded as
`mkO 1 0 0` (that is `ω^1·1 + 0`, whose exponent is the code `1` of the
notation `1`) and `1 + t` as `mkO 0 0 t`, the bare comparison ranks
`1 + ω` strictly below `ω`, and `1 + (1 + ω)` strictly below `1 + ω`,
and so on without end — an infinite descending chain of notations all
denoting the ordinal `ω` (because `1 + ω = ω`).  Normality is exactly
what excludes them, and `oltB`'s normality check is exactly why
`oLt_wf` can hold. -/

/-- The code of the notation `1`. -/
theorem mkO_zero_zero_zero : mkO 0 0 0 = 1 := rfl

/-- The code of `ω`. -/
def omegaCode : ℕ := mkO 1 0 0

/-- The code of `1 + t`. -/
def onePlusCode (t : ℕ) : ℕ := mkO 0 0 t

/-- `1 + ω ≺ ω` in the bare comparison … -/
theorem precB_onePlus_omega :
    precB (onePlusCode omegaCode) omegaCode = true :=
  precB_mkO_exp _ _ _ _ (precB_zero_left Nat.one_ne_zero)

/-- … and the descent continues — the bare comparison, on arbitrary
notations, is *not* well-founded. -/
theorem precB_onePlus_onePlus_omega :
    precB (onePlusCode (onePlusCode omegaCode)) (onePlusCode omegaCode)
      = true :=
  precB_mkO_rem 0 0 precB_onePlus_omega

/-- The offending notations are not normal … -/
theorem nfB_onePlus_omega : nfB (onePlusCode omegaCode) = false := by
  rw [onePlusCode, nfB_pos (mkO_ne_zero _ _ _), oE_mkO, oR_mkO, omegaCode,
    oE_mkO, precB_zero_right]
  simp

/-- … so `≺` itself — the comparison restricted to normal forms — does
not relate them. -/
theorem not_olt_onePlus_omega : ¬ OLt (onePlusCode omegaCode) omegaCode := by
  intro h
  have h' := h.nf_left
  rw [nfB_onePlus_omega] at h'
  exact absurd h' (by simp)

/-! ## Sanity checks on normal notations: `1 ≺ ω ≺ ω^ω` -/

theorem nfB_one : nfB 1 = true := by
  rw [← mkO_zero_zero_zero]
  exact nfB_mkO nfB_zero nfB_zero (Or.inl rfl)

theorem nfB_omegaCode : nfB omegaCode = true :=
  nfB_mkO nfB_one nfB_zero (Or.inl rfl)

theorem nfB_omegaOmegaCode : nfB (mkO omegaCode 0 0) = true :=
  nfB_mkO nfB_omegaCode nfB_zero (Or.inl rfl)

theorem precB_one_omegaCode : precB 1 omegaCode = true := by
  have h : precB (mkO 0 0 0) (mkO 1 0 0) = true :=
    precB_mkO_exp _ _ _ _ (precB_zero_left Nat.one_ne_zero)
  rw [mkO_zero_zero_zero] at h
  exact h

theorem olt_one_omega : OLt 1 omegaCode :=
  olt_of nfB_one nfB_omegaCode precB_one_omegaCode

theorem olt_omega_omegaOmega : OLt omegaCode (mkO omegaCode 0 0) :=
  olt_of nfB_omegaCode nfB_omegaOmegaCode
    (precB_mkO_exp _ _ _ _ precB_one_omegaCode)

/-! ## Totality of the comparison on normal forms

Phase C needed the order to be well-founded and irreflexive, never
*total*: its descent always related two notations that were built to be
related.  The Hydra layer needs totality — inserting an exponent into a
normal form has to know that if it is neither equal to nor above the head,
it is below it — so it is proved here.

The induction is the same three-way shape as the comparison itself:
compare head exponents, then coefficients, then remainders, with the
recursive calls at `(oE a, oE b)` and `(oR a, oR b)`, both of which shrink
the sum. -/

theorem precB_trichotomy : ∀ (s a b : ℕ), a + b ≤ s → nfB a = true →
    nfB b = true → a = b ∨ precB a b = true ∨ precB b a = true
  | 0, a, b, h, _, _ => Or.inl (by omega)
  | s + 1, a, b, h, hna, hnb => by
    rcases dec_em (a = 0) with ha | ha
    · subst ha
      rcases dec_em (b = 0) with hb | hb
      · exact Or.inl hb.symm
      · exact Or.inr (Or.inl (precB_zero_left hb))
    · rcases dec_em (b = 0) with hb | hb
      · subst hb
        exact Or.inr (Or.inr (precB_zero_left ha))
      · have hE : oE a + oE b ≤ s := by
          have h1 := oE_lt ha
          have h2 := oE_lt hb
          omega
        have hR : oR a + oR b ≤ s := by
          have h1 := oR_lt ha
          have h2 := oR_lt hb
          omega
        have hA : mkO (oE a) (oC a) (oR a) = a := mkO_oE_oC_oR ha
        have hB : mkO (oE b) (oC b) (oR b) = b := mkO_oE_oC_oR hb
        rcases precB_trichotomy s (oE a) (oE b) hE (nfB_exp ha hna)
            (nfB_exp hb hnb) with he | he | he
        · -- equal head exponents: compare coefficients
          rcases dec_em (oC a < oC b) with hc | hc
          · refine Or.inr (Or.inl ?_)
            rw [← hA, ← hB, he]
            exact precB_mkO_coeff _ _ _ hc
          · rcases dec_em (oC b < oC a) with hc' | hc'
            · refine Or.inr (Or.inr ?_)
              rw [← hA, ← hB, he]
              exact precB_mkO_coeff _ _ _ hc'
            · -- equal coefficients: compare remainders
              have hceq : oC a = oC b := by omega
              rcases precB_trichotomy s (oR a) (oR b) hR (nfB_rem ha hna)
                  (nfB_rem hb hnb) with hr | hr | hr
              · refine Or.inl ?_
                rw [← hA, ← hB, he, hceq, hr]
              · refine Or.inr (Or.inl ?_)
                rw [← hA, ← hB, he, hceq]
                exact precB_mkO_rem _ _ hr
              · refine Or.inr (Or.inr ?_)
                rw [← hA, ← hB, he, hceq]
                exact precB_mkO_rem _ _ hr
        · refine Or.inr (Or.inl ?_)
          rw [← hA, ← hB]
          exact precB_mkO_exp _ _ _ _ he
        · refine Or.inr (Or.inr ?_)
          rw [← hA, ← hB]
          exact precB_mkO_exp _ _ _ _ he

/-- **Transitivity.**  The third order property this development turned
out to need: Phase C proved `≺` well-founded and irreflexive, the Hydra
layer added totality, and monotonicity of insertion needs to chain two
comparisons.  Same three-way induction as the comparison itself, with the
recursive calls at the three head exponents and at the three
remainders. -/
theorem precB_trans_aux : ∀ (s a b c : ℕ), a + b + c ≤ s →
    precB a b = true → precB b c = true → precB a c = true
  | 0, a, b, c, h, hab, _ => by
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    rw [ha, hb, precB_zero_right] at hab
    exact absurd hab (by simp)
  | s + 1, a, b, c, h, hab, hbc => by
    have hb : b ≠ 0 := by
      intro h0
      rw [h0, precB_zero_right] at hab
      exact absurd hab (by simp)
    have hc : c ≠ 0 := by
      intro h0
      rw [h0, precB_zero_right] at hbc
      exact absurd hbc (by simp)
    rcases dec_em (a = 0) with ha | ha
    · rw [ha]
      exact precB_zero_left hc
    · have hA := mkO_oE_oC_oR ha
      have hC := mkO_oE_oC_oR hc
      have hEs : oE a + oE b + oE c ≤ s := by
        have h1 := oE_lt ha
        have h2 := oE_lt hb
        have h3 := oE_lt hc
        omega
      have hRs : oR a + oR b + oR c ≤ s := by
        have h1 := oR_lt ha
        have h2 := oR_lt hb
        have h3 := oR_lt hc
        omega
      rcases precB_cases ha hb hab with h1 | ⟨e1, r1⟩
      · rcases precB_cases hb hc hbc with h2 | ⟨e2, r2⟩
        · rw [← hA, ← hC]
          exact precB_mkO_exp _ _ _ _ (precB_trans_aux s _ _ _ hEs h1 h2)
        · rw [← hA, ← hC]
          exact precB_mkO_exp _ _ _ _ (e2 ▸ h1)
      · rcases precB_cases hb hc hbc with h2 | ⟨e2, r2⟩
        · rw [← hA, ← hC]
          exact precB_mkO_exp _ _ _ _ (e1 ▸ h2)
        · rw [← hA, ← hC, e1, e2]
          rcases r1 with hc1 | ⟨hc1, hs1⟩
          · rcases r2 with hc2 | ⟨hc2, hs2⟩
            · exact precB_mkO_coeff _ _ _ (by omega)
            · exact precB_mkO_coeff _ _ _ (by omega)
          · rcases r2 with hc2 | ⟨hc2, hs2⟩
            · exact precB_mkO_coeff _ _ _ (by omega)
            · rw [show oC a = oC c by omega]
              exact precB_mkO_rem _ _ (precB_trans_aux s _ _ _ hRs hs1 hs2)

/-- Transitivity, at the adequate bound. -/
theorem precB_trans {a b c : ℕ} (hab : precB a b = true) (hbc : precB b c = true) :
    precB a c = true :=
  precB_trans_aux (a + b + c) a b c (Nat.le_refl _) hab hbc

/-- **Asymmetry**, from transitivity and irreflexivity. -/
theorem precB_asymm {a b : ℕ} (hab : precB a b = true) : precB b a = false := by
  rcases dec_em (precB b a = true) with hba | hba
  · have := precB_trans hab hba
    rw [precB_irrefl] at this
    exact absurd this (by simp)
  · simpa using hba

/-- Totality, at the adequate bound. -/
theorem precB_total {a b : ℕ} (hna : nfB a = true) (hnb : nfB b = true) :
    a = b ∨ precB a b = true ∨ precB b a = true :=
  precB_trichotomy (a + b) a b (Nat.le_refl _) hna hnb

/-- The form the Hydra layer's insertion needs: not equal and not above
means below. -/
theorem precB_of_ne_of_not_precB {a b : ℕ} (hna : nfB a = true)
    (hnb : nfB b = true) (hne : a ≠ b) (h : precB b a = false) :
    precB a b = true := by
  rcases precB_total hna hnb with he | hab | hba
  · exact absurd he hne
  · exact hab
  · rw [h] at hba
    exact absurd hba (by simp)

end Realizability

