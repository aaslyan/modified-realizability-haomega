/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Ordinals.Epsilon0
import Mathlib.Data.Nat.Basic

/-!
# The value-level layer between the notations and the fragment

Everything the fragment's function symbols evaluate by, that is not pure
arithmetic: the fueled base-`k` logarithm, hereditary base change
(`bumpN`), the Goodstein sequence (`goodN`), and — new in Phase D1 — the
**ordinal assignment** `ordOf`, which sends a Goodstein state `(k, n)` to
the code of the ordinal of `n`'s hereditary base-`k` representation read
at base `ω`.

## Why this module exists where it does

`hlog`/`bumpN`/`goodN` were introduced in Phase B at the head of
`Syntax.lean`, because `Term.eval` consumes them.  Phase D adds the
function symbol `ord`, evaluated by `ordOf`, and — this is the part that
forces a module of its own — `Soundness.lean` needs the *theorems* of
Phase D1 to discharge the `ordDescent` case.  So the definitions and
their theory both have to precede `Syntax.lean`.  The functions and their
Phase-B facts were moved here unchanged; `Goodstein.lean` and
`TransfiniteInduction.lean` keep everything else.

## What Phase D1 proves here (the three obligations Phase C named)

1. `nfB_ordOf` — the assignment lands in **normal form**, so Phase C's
   order applies to it.  This is Phase B's deferred canonicity, in code
   form: it needs the digit bounds and the exponent ordering, hence real
   logarithm theory (`lt_pow_hlog_succ` and friends), which Phase B did
   not build.
2. `ordOf_bumpN` — **bumping the base does not change the ordinal**, in
   general, not just at the instances Phase C kernel-checked.  Needs the
   fuel-adequacy lemma `ordOfAux_eq_of_le` first, as Phase C predicted,
   because the two sides recurse at different fuels.
3. `ordOf_descent` — **one Goodstein step strictly decreases the
   ordinal**.  Given 2, this is monotonicity of the assignment
   (`olt_ordOf_of_lt`) applied to `bumpN k n - 1 < bumpN k n`.

A correction to Phase C's own prediction, recorded in docs/first-order/STATUS.md: it
guessed that (3) would be the obligation using `tiEps0`'s machinery.  It
does not — all three are value-level arithmetic, and `tiEps0` enters only
in `GoodsteinTheorem.lean`, where the *induction* is performed.  What (3)
does need is (2) plus monotonicity, and monotonicity is the same
digit-comparison work as (1), so (1) and (3) share their hard core.
-/

namespace Realizability

/-! ## The value-level Goodstein functions (Phase B)

The semantics of the Phase-B function symbols `bump` and `good`, as
plain `ℕ`-functions defined *before* `Term` so `Term.eval` can consume
them.  All recursions are **fuel-structural** (fuel `= n` is adequate,
`Goodstein.lean` proves it) rather than well-founded: `WellFounded.fix`
does not reduce in the kernel, and the certifying derivations of
`Goodstein.lean` need concrete Goodstein values to compute by
`rfl`/`decide`.  For the same reason the base-`b` logarithm is a local
fueled definition rather than Mathlib's well-founded `Nat.log`. -/

/-- Fueled base-`b` logarithm: the number of times `b` divides into `n`
(zero when `b ≤ 1` or `n < b`).  Structural in the fuel. -/
def hlogAux (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if 1 < b ∧ b ≤ n then hlogAux b fuel (n / b) + 1 else 0

/-- The base-`b` logarithm, self-fueled: `hlog b n` is the largest `e`
with `b ^ e ≤ n` (for `1 < b ≤ n`; zero in the degenerate cases) —
`Goodstein.lean` proves the two facts used (`hlog_lt`,
`pow_hlog_le`). -/
def hlog (b n : ℕ) : ℕ :=
  hlogAux b n n

/-- **Hereditary base change, value level** (fueled): `bumpNAux k fuel n`
peels the leading base-`k` digit `n = k^e·c + r` (`e = hlog k n`,
`c = n / k^e`, `r = n % k^e`) and rewrites it at base `k + 1` with the
exponent *itself* hereditarily rewritten:
`(k+1)^(bump e)·c + bump r`.  Corresponds to
`WilliamAngus/Goodstein`'s `(HBase.f k · (k+1)).eval ∘ HBase.ofNat k`
(the structural base-replacement `f` on the `ofNat` representation);
checked concretely: `bumpN 2 4 = 3 ^ 3 ^ 3 ^ 0 = 27`, both here and
there (`4 = 2^2^2^0`).  Degenerate bases are the identity
(`bumpN 0 n = bumpN 1 n = n`), so no `2 ≤ k` side condition is ever
needed for soundness. -/
def bumpNAux (k : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | 0, _ + 1 => 0
  | fuel + 1, n + 1 =>
      (k + 1) ^ bumpNAux k fuel (hlog k (n + 1)) * ((n + 1) / k ^ hlog k (n + 1))
        + bumpNAux k fuel ((n + 1) % k ^ hlog k (n + 1))

/-- Hereditary base change at the adequate fuel (`Goodstein.lean`,
`hrep_eval_bump`, connects it to the syntactic representation read at
base `k + 1`). -/
def bumpN (k n : ℕ) : ℕ :=
  bumpNAux k n n

/-- **The Goodstein sequence, value level**: `goodN m 0 = m`, and one
step bumps the base `s + 2` hereditarily and subtracts one.  This is
`WilliamAngus/Goodstein`'s `goodsteinSequence start h n i` at
`start = 2`: their step `i → i + 1` applies the base-change `G` at base
`start + i = 2 + i`, exactly this `bumpN (s + 2)` at `i = s` (indexing
convention checked against their `g`/`G`; values checked:
`goodN 4 = 4, 26, 41, 60, …`, `goodN 3 = 3, 3, 3, 2, 1, 0, 0, …`). -/
def goodN (m : ℕ) : ℕ → ℕ
  | 0 => m
  | s + 1 => bumpN (s + 2) (goodN m s) - 1

/-! ## The fueled logarithm: the two facts used

`hlog` (`Syntax.lean`) is structural in its fuel so the kernel can
compute it; fuel `= n` is adequate.  Only two facts about it are ever
needed: the leading exponent is *small* (`hlog_lt`, which powers every
fuel-adequacy argument below) and *correct enough* (`pow_hlog_le`,
which bounds the digit remainder).  No further logarithm theory is
built. -/

/-- The fueled logarithm is strictly below its (positive) argument, at
every fuel. -/
theorem hlogAux_lt (b : ℕ) : ∀ (fuel m : ℕ), 1 ≤ m → hlogAux b fuel m < m
  | 0, _, hm => hm
  | fuel + 1, m, hm => by
    simp only [hlogAux]
    split
    · next h =>
      have hdiv : m / b < m := Nat.div_lt_self (by omega) h.1
      have hdiv1 : 1 ≤ m / b := (Nat.one_le_div_iff (by omega)).mpr h.2
      have := hlogAux_lt b fuel (m / b) hdiv1
      omega
    · omega

/-- `b ^ hlog b m ≤ m` for positive `m`, at every fuel: the leading
digit's power does not overshoot. -/
theorem pow_hlogAux_le (b : ℕ) : ∀ (fuel m : ℕ), 1 ≤ m →
    b ^ hlogAux b fuel m ≤ m
  | 0, _, hm => hm
  | fuel + 1, m, hm => by
    simp only [hlogAux]
    split
    · next h =>
      have hdiv1 : 1 ≤ m / b := (Nat.one_le_div_iff (by omega)).mpr h.2
      have ih := pow_hlogAux_le b fuel (m / b) hdiv1
      calc b ^ (hlogAux b fuel (m / b) + 1)
          = b ^ hlogAux b fuel (m / b) * b := Nat.pow_succ ..
        _ ≤ m / b * b := Nat.mul_le_mul_right b ih
        _ ≤ m := Nat.div_mul_le_self m b
    · exact hm

/-- The self-fueled logarithm is strictly below its positive argument. -/
theorem hlog_lt (b m : ℕ) (hm : 1 ≤ m) : hlog b m < m :=
  hlogAux_lt b m m hm

/-- `b ^ hlog b m ≤ m` for positive `m`. -/
theorem pow_hlog_le (b m : ℕ) (hm : 1 ≤ m) : b ^ hlog b m ≤ m :=
  pow_hlogAux_le b m m hm

/-- The leading power is never zero (degenerate bases give exponent
`0`, and `0 ^ 0 = 1`). -/
theorem pow_hlog_pos (b m : ℕ) : 0 < b ^ hlog b m := by
  cases b with
  | zero =>
    have h0 : hlog 0 m = 0 := by
      cases m with
      | zero => rfl
      | succ m => simp [hlog, hlogAux]
    rw [h0]
    exact Nat.one_pos
  | succ b => exact Nat.pow_pos (Nat.succ_pos b)


/-! ## Logarithm theory (Phase D1)

Phase B needed exactly two facts about `hlog` (`hlog_lt`, `pow_hlog_le`).
The digit bounds and the exponent ordering — the canonicity content Phase
B deferred — need the *maximality* half as well, so the theory is built
here.  Everything below assumes `2 ≤ k`; the degenerate bases are never
used by the Goodstein sequence (its bases are `s + 2`), and `hlog` is
identically `0` there anyway. -/

/-- Above the adequate fuel one more unit changes nothing. -/
theorem hlogAux_succ_eq (b : ℕ) : ∀ (fuel n : ℕ), n ≤ fuel →
    hlogAux b (fuel + 1) n = hlogAux b fuel n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    show (if 1 < b ∧ b ≤ 0 then hlogAux b 0 (0 / b) + 1 else 0) = hlogAux b 0 0
    rw [if_neg (by omega)]
    rfl
  | fuel + 1, n, h => by
    show (if 1 < b ∧ b ≤ n then hlogAux b (fuel + 1) (n / b) + 1 else 0)
      = (if 1 < b ∧ b ≤ n then hlogAux b fuel (n / b) + 1 else 0)
    rcases dec_em (1 < b ∧ b ≤ n) with hc | hc
    · have hdiv : n / b ≤ fuel := by
        have : n / b < n := Nat.div_lt_self (by omega) hc.1
        omega
      rw [if_pos hc, if_pos hc, hlogAux_succ_eq b fuel (n / b) hdiv]
    · rw [if_neg hc, if_neg hc]

theorem hlogAux_eq_of_le (b : ℕ) : ∀ (fuel n : ℕ), n ≤ fuel →
    hlogAux b fuel n = hlog b n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    rcases dec_em (n = fuel + 1) with he | he
    · rw [he]; rfl
    · have hf : n ≤ fuel := by omega
      rw [hlogAux_succ_eq b fuel n hf, hlogAux_eq_of_le b fuel n hf]

/-- The recursion for `hlog`, at the adequate fuel: one digit peeled. -/
theorem hlog_succ_eq {b n : ℕ} (hb : 2 ≤ b) (hn : b ≤ n) :
    hlog b n = hlog b (n / b) + 1 := by
  obtain ⟨f, hf⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega⟩
  subst hf
  have hdiv : (f + 1) / b ≤ f := by
    have : (f + 1) / b < f + 1 := Nat.div_lt_self (by omega) (by omega)
    omega
  show (if 1 < b ∧ b ≤ f + 1 then hlogAux b f ((f + 1) / b) + 1 else 0) = _
  rw [if_pos ⟨by omega, by omega⟩, hlogAux_eq_of_le b f _ hdiv]

/-- Below the base the logarithm is zero. -/
theorem hlog_eq_zero {b n : ℕ} (h : n < b) : hlog b n = 0 := by
  cases n with
  | zero => rfl
  | succ m =>
    show (if 1 < b ∧ b ≤ m + 1 then hlogAux b m ((m + 1) / b) + 1 else 0) = 0
    rw [if_neg (by omega)]

/-- **Maximality**: `n` is strictly below the next power. -/
theorem lt_pow_hlog_succ {b : ℕ} (hb : 2 ≤ b) :
    ∀ n : ℕ, n < b ^ (hlog b n + 1) := by
  refine nat_strong_ind (fun n ih ↦ ?_)
  rcases dec_em (n < b) with h | h
  · rw [hlog_eq_zero h, Nat.pow_one]
    exact h
  · have hn : b ≤ n := by omega
    have hpos : 0 < n := by omega
    have hdiv : n / b < n := Nat.div_lt_self hpos (by omega)
    have ihd := ih (n / b) hdiv
    rw [hlog_succ_eq hb hn]
    have hmul : n < (n / b + 1) * b := by
      have h1 := Nat.div_add_mod n b
      have h2 : n % b < b := Nat.mod_lt _ (by omega)
      have h3 : (n / b + 1) * b = b * (n / b) + b := by
        rw [Nat.succ_mul, Nat.mul_comm]
      omega
    calc n < (n / b + 1) * b := hmul
      _ ≤ b ^ (hlog b (n / b) + 1) * b :=
          Nat.mul_le_mul (by omega) (Nat.le_refl b)
      _ = b ^ (hlog b (n / b) + 1 + 1) := (Nat.pow_succ ..).symm

/-- The leading exponent is small enough: below any exponent whose power
overshoots. -/
theorem hlog_lt_of_lt_pow {b n e : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n)
    (h : n < b ^ e) : hlog b n < e := by
  by_contra hc
  have hle : b ^ e ≤ b ^ hlog b n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have := pow_hlog_le b n hn
  omega

/-- The logarithm is monotone. -/
theorem hlog_le_hlog {b a c : ℕ} (hb : 2 ≤ b) (hac : a ≤ c) :
    hlog b a ≤ hlog b c := by
  rcases dec_em (a = 0) with h0 | h0
  · subst h0
    show hlog b 0 ≤ _
    rw [hlog_eq_zero (by omega)]
    exact Nat.zero_le _
  · have h1 : b ^ hlog b a ≤ a := pow_hlog_le b a (by omega)
    have h2 : c < b ^ (hlog b c + 1) := lt_pow_hlog_succ hb c
    by_contra hc
    have : b ^ (hlog b c + 1) ≤ b ^ hlog b a :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-! ### The digits

For `2 ≤ k` and `1 ≤ n`, writing `e = hlog k n`, the leading digit
`n / k^e` is between `1` and `k - 1` and the remainder `n % k^e` is below
`k^e` — the facts that make the representation canonical. -/

theorem one_le_digit {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) :
    1 ≤ n / k ^ hlog k n :=
  (Nat.one_le_div_iff (Nat.pow_pos (by omega))).mpr (pow_hlog_le k n hn)

theorem digit_lt {k n : ℕ} (hk : 2 ≤ k) : n / k ^ hlog k n < k := by
  have h := lt_pow_hlog_succ hk n
  rw [Nat.pow_succ] at h
  exact Nat.div_lt_of_lt_mul h

theorem rem_lt_pow {k n : ℕ} : n % k ^ hlog k n < k ^ hlog k n :=
  Nat.mod_lt _ (pow_hlog_pos k n)

theorem rem_lt {k n : ℕ} (hn : 1 ≤ n) : n % k ^ hlog k n < n :=
  Nat.lt_of_lt_of_le rem_lt_pow (pow_hlog_le k n hn)

/-- The remainder's own leading exponent is strictly below the leading
exponent — the exponents of a normal form strictly decrease. -/
theorem hlog_rem_lt {k n : ℕ} (hk : 2 ≤ k) (hr : 1 ≤ n % k ^ hlog k n) :
    hlog k (n % k ^ hlog k n) < hlog k n :=
  hlog_lt_of_lt_pow hk hr rem_lt_pow

/-- The digit decomposition, as an equation. -/
theorem digit_decomp (k n : ℕ) :
    k ^ hlog k n * (n / k ^ hlog k n) + n % k ^ hlog k n = n :=
  Nat.div_add_mod n (k ^ hlog k n)

/-- **Reading the digits back off**: if `n = b^E·d + R` with `1 ≤ d < b`
and `R < b^E`, then `E`, `d`, `R` *are* `n`'s leading exponent, digit and
remainder.  The uniqueness half of the representation, in the form the
base-change theorem needs. -/
theorem hlog_of_digits {b E d R : ℕ} (hb : 2 ≤ b) (hd : 1 ≤ d) (hdb : d < b)
    (hR : R < b ^ E) : hlog b (b ^ E * d + R) = E := by
  have hpos : 0 < b ^ E := Nat.pow_pos (by omega)
  have hge : b ^ E ≤ b ^ E * d + R := by
    have : b ^ E * 1 ≤ b ^ E * d := Nat.mul_le_mul_left _ hd
    omega
  have hlt : b ^ E * d + R < b ^ (E + 1) := by
    have h1 : b ^ E * d + R < b ^ E * d + b ^ E := by omega
    have h2 : b ^ E * (d + 1) = b ^ E * d + b ^ E := by
      rw [Nat.mul_add, Nat.mul_one]
    have h3 : b ^ E * (d + 1) ≤ b ^ E * b := Nat.mul_le_mul_left _ (by omega)
    have h4 : b ^ E * b = b ^ (E + 1) := (Nat.pow_succ ..).symm
    omega
  have h1 : hlog b (b ^ E * d + R) < E + 1 :=
    hlog_lt_of_lt_pow hb (by omega) hlt
  have h2 : E ≤ hlog b (b ^ E * d + R) := by
    by_contra hc
    have hmax := lt_pow_hlog_succ hb (b ^ E * d + R)
    have hle : b ^ (hlog b (b ^ E * d + R) + 1) ≤ b ^ E :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  omega

theorem div_of_digits {b E d R : ℕ} (hR : R < b ^ E) :
    (b ^ E * d + R) / b ^ E = d := by
  have hpos : 0 < b ^ E := Nat.lt_of_le_of_lt (Nat.zero_le R) hR
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hR,
    Nat.zero_add]

theorem mod_of_digits {b E d R : ℕ} (hR : R < b ^ E) :
    (b ^ E * d + R) % b ^ E = R := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]

/-! ## Hereditary base change: fuel adequacy, monotonicity, and the bound

`bumpN` was only ever *computed* in Phase B (its correctness there is the
clause-for-clause mirror `hrepAux_eval_bump`, at equal fuels).  Phase D
needs it as a *function*: that it is strictly monotone, and that it
respects the digit bound — `r < k^e` implies `bump r < (k+1)^(bump e)`.
The two are proved together, by one strong induction, because each step
of either needs the other at smaller arguments. -/

theorem bumpNAux_succ_eq (k : ℕ) : ∀ (fuel n : ℕ), n ≤ fuel →
    bumpNAux k (fuel + 1) n = bumpNAux k fuel n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    cases n with
    | zero => rfl
    | succ m =>
      have hE : hlog k (m + 1) ≤ fuel := by
        have := hlog_lt k (m + 1) (by omega)
        omega
      have hR : (m + 1) % k ^ hlog k (m + 1) ≤ fuel := by
        have := rem_lt (k := k) (n := m + 1) (by omega)
        omega
      show (k + 1) ^ bumpNAux k (fuel + 1) (hlog k (m + 1)) * _
        + bumpNAux k (fuel + 1) _ = _
      rw [bumpNAux_succ_eq k fuel _ hE, bumpNAux_succ_eq k fuel _ hR]
      rfl

theorem bumpNAux_eq_of_le (k : ℕ) : ∀ (fuel n : ℕ), n ≤ fuel →
    bumpNAux k fuel n = bumpN k n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    rcases dec_em (n = fuel + 1) with he | he
    · rw [he]; rfl
    · have hf : n ≤ fuel := by omega
      rw [bumpNAux_succ_eq k fuel n hf, bumpNAux_eq_of_le k fuel n hf]

/-- The defining recursion of `bumpN`, at the adequate fuel. -/
theorem bumpN_pos_eq {k n : ℕ} (hn : 1 ≤ n) :
    bumpN k n = (k + 1) ^ bumpN k (hlog k n) * (n / k ^ hlog k n)
      + bumpN k (n % k ^ hlog k n) := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  have hE : hlog k (m + 1) ≤ m := by
    have := hlog_lt k (m + 1) (by omega)
    omega
  have hR : (m + 1) % k ^ hlog k (m + 1) ≤ m := by
    have := rem_lt (k := k) (n := m + 1) (by omega)
    omega
  show (k + 1) ^ bumpNAux k m (hlog k (m + 1)) * _ + bumpNAux k m _ = _
  rw [bumpNAux_eq_of_le k m _ hE, bumpNAux_eq_of_le k m _ hR]

@[simp] theorem bumpN_zero (k : ℕ) : bumpN k 0 = 0 := rfl

/-- **`bumpN` is strictly monotone, and respects the digit bound.**  One
strong induction proving both, since each case of either half consumes
the other at a smaller argument:

* the bound at `b` needs the bound at `b`'s remainder *and* monotonicity
  at `b`'s exponent, both smaller than `b`;
* monotonicity at `(a, b)` needs the bound at `a` (smaller than `b`) and
  monotonicity at `b`'s exponent and remainder.

The bound is stated in "own exponent" form — `bump b < (k+1)^(bump (hlog
b) + 1)` — which is what keeps every induction hypothesis at an argument
below `b`. -/
theorem bumpN_mono_bound {k : ℕ} (hk : 2 ≤ k) : ∀ b : ℕ,
    (∀ a, a < b → bumpN k a < bumpN k b) ∧
      bumpN k b < (k + 1) ^ (bumpN k (hlog k b) + 1) := by
  refine nat_strong_ind (fun b ih ↦ ?_)
  rcases dec_em (b = 0) with hb0 | hb0
  · subst hb0
    refine ⟨fun a ha ↦ absurd ha (by omega), ?_⟩
    have h1 : (1 : ℕ) ≤ (k + 1) ^ (bumpN k (hlog k 0) + 1) :=
      Nat.one_le_pow _ _ (by omega)
    rw [bumpN_zero]
    omega
  · have hb1 : 1 ≤ b := by omega
    have hEb : hlog k b < b := hlog_lt k b hb1
    have hd1 : 1 ≤ b / k ^ hlog k b := one_le_digit hk hb1
    have hdk : b / k ^ hlog k b < k := digit_lt hk
    have hRp : b % k ^ hlog k b < k ^ hlog k b := rem_lt_pow
    have hRb : b % k ^ hlog k b < b := rem_lt hb1
    have hBb := bumpN_pos_eq (k := k) hb1
    have hpow : (1 : ℕ) ≤ (k + 1) ^ bumpN k (hlog k b) :=
      Nat.one_le_pow _ _ (by omega)
    -- The sub-fact used three times: a number below `k ^ (leading exponent
    -- of b)` bumps to something below `(k+1) ^ (bump of that exponent)`.
    have hkey : ∀ r : ℕ, r < b → r < k ^ hlog k b →
        bumpN k r < (k + 1) ^ bumpN k (hlog k b) := by
      intro r hrb hrp
      rcases dec_em (r = 0) with h0 | h0
      · subst h0
        rw [bumpN_zero]
        exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.one_le_pow _ _ (by omega))
      · have hlt : hlog k r < hlog k b := hlog_lt_of_lt_pow hk (by omega) hrp
        have h1 := (ih r hrb).2
        have h2 : bumpN k (hlog k r) < bumpN k (hlog k b) :=
          (ih _ hEb).1 _ hlt
        have h3 : (k + 1) ^ (bumpN k (hlog k r) + 1)
            ≤ (k + 1) ^ bumpN k (hlog k b) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
    have hbound : bumpN k b < (k + 1) ^ (bumpN k (hlog k b) + 1) := by
      have hBR := hkey _ hRb hRp
      have h1 : (k + 1) ^ bumpN k (hlog k b) * (b / k ^ hlog k b + 1)
          = (k + 1) ^ bumpN k (hlog k b) * (b / k ^ hlog k b)
            + (k + 1) ^ bumpN k (hlog k b) := by
        rw [Nat.mul_add, Nat.mul_one]
      have h2 : (k + 1) ^ bumpN k (hlog k b) * (b / k ^ hlog k b + 1)
          ≤ (k + 1) ^ bumpN k (hlog k b) * (k + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h3 : (k + 1) ^ bumpN k (hlog k b) * (k + 1)
          = (k + 1) ^ (bumpN k (hlog k b) + 1) := (Nat.pow_succ ..).symm
      omega
    refine ⟨?_, hbound⟩
    intro a hab
    rcases dec_em (a = 0) with ha0 | ha0
    · subst ha0
      have h4 : (k + 1) ^ bumpN k (hlog k b) * 1
          ≤ (k + 1) ^ bumpN k (hlog k b) * (b / k ^ hlog k b) :=
        Nat.mul_le_mul_left _ hd1
      rw [bumpN_zero]
      omega
    · have ha1 : 1 ≤ a := by omega
      have hEa : hlog k a ≤ hlog k b := hlog_le_hlog hk (by omega)
      have hBa := bumpN_pos_eq (k := k) ha1
      rcases dec_em (hlog k a < hlog k b) with hlt | hnlt
      · have h1 := (ih a hab).2
        have h2 : bumpN k (hlog k a) < bumpN k (hlog k b) := (ih _ hEb).1 _ hlt
        have h3 : (k + 1) ^ (bumpN k (hlog k a) + 1)
            ≤ (k + 1) ^ bumpN k (hlog k b) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have h4 : (k + 1) ^ bumpN k (hlog k b) * 1
            ≤ (k + 1) ^ bumpN k (hlog k b) * (b / k ^ hlog k b) :=
          Nat.mul_le_mul_left _ hd1
        omega
      · have hEeq : hlog k a = hlog k b := by omega
        rw [hEeq] at hBa
        have hdiv : a / k ^ hlog k b ≤ b / k ^ hlog k b :=
          Nat.div_le_div_right (by omega)
        have hmodp : a % k ^ hlog k b < k ^ hlog k b :=
          Nat.mod_lt _ (pow_hlog_pos k b)
        have hdeca := Nat.div_add_mod a (k ^ hlog k b)
        have hdecb := Nat.div_add_mod b (k ^ hlog k b)
        rcases dec_em (a / k ^ hlog k b < b / k ^ hlog k b) with hdlt | hdnlt
        · have hBRa := hkey (a % k ^ hlog k b) (by omega) hmodp
          have h1 : (k + 1) ^ bumpN k (hlog k b) * (a / k ^ hlog k b + 1)
              = (k + 1) ^ bumpN k (hlog k b) * (a / k ^ hlog k b)
                + (k + 1) ^ bumpN k (hlog k b) := by
            rw [Nat.mul_add, Nat.mul_one]
          have h2 : (k + 1) ^ bumpN k (hlog k b) * (a / k ^ hlog k b + 1)
              ≤ (k + 1) ^ bumpN k (hlog k b) * (b / k ^ hlog k b) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        · have hdd : a / k ^ hlog k b = b / k ^ hlog k b := by omega
          have hRlt : a % k ^ hlog k b < b % k ^ hlog k b := by
            rw [hdd] at hdeca
            omega
          have h1 : bumpN k (a % k ^ hlog k b) < bumpN k (b % k ^ hlog k b) :=
            (ih _ hRb).1 _ hRlt
          rw [hdd] at hBa
          omega

/-- `bumpN` is strictly monotone. -/
theorem bumpN_lt_bumpN {k a b : ℕ} (hk : 2 ≤ k) (h : a < b) :
    bumpN k a < bumpN k b :=
  (bumpN_mono_bound hk b).1 a h

/-- Bumping a nonzero number gives a nonzero number. -/
theorem bumpN_ne_zero {k n : ℕ} (hk : 2 ≤ k) (hn : n ≠ 0) : bumpN k n ≠ 0 := by
  have hn1 : 1 ≤ n := by omega
  rw [bumpN_pos_eq hn1]
  have hpow_pos : 0 < k ^ hlog k n := pow_hlog_pos k n
  have hquot : 1 ≤ n / k ^ hlog k n :=
    (Nat.one_le_div_iff hpow_pos).mpr (pow_hlog_le k n hn1)
  have hbase_pos : 0 < (k + 1) ^ bumpN k (hlog k n) :=
    Nat.pow_pos (by omega)
  have hprod_pos : 0 < (k + 1) ^ bumpN k (hlog k n) * (n / k ^ hlog k n) :=
    Nat.mul_pos hbase_pos (by omega)
  omega

/-- The digit bound, in the form the base-change theorem uses. -/
theorem bumpN_lt_pow {k r e : ℕ} (hk : 2 ≤ k) (h : r < k ^ e) :
    bumpN k r < (k + 1) ^ bumpN k e := by
  rcases dec_em (r = 0) with h0 | h0
  · subst h0
    rw [bumpN_zero]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.one_le_pow _ _ (by omega))
  · have hlt : hlog k r < e := hlog_lt_of_lt_pow hk (by omega) h
    have h1 := (bumpN_mono_bound hk r).2
    have h2 : bumpN k (hlog k r) < bumpN k e := bumpN_lt_bumpN hk hlt
    have h3 : (k + 1) ^ (bumpN k (hlog k r) + 1) ≤ (k + 1) ^ bumpN k e :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-! ## The ordinal assignment

`ordOf k n` is the code of the ordinal of `n`'s hereditary base-`k`
representation, read at base `ω`.  Clause for clause the mirror of Phase
B's `hrepAux`, with `mkO` where that builds terms.  (Defined in Phase C
inside `TransfiniteInduction.lean`; moved here in Phase D, unchanged,
because `Term.eval` and `Soundness.lean` both need it.) -/

/-- The ordinal code of `n` in hereditary base `k` (fueled, mirroring
`hrepAux`). -/
def ordOfAux (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | f + 1, n + 1 =>
      mkO (ordOfAux k f (hlog k (n + 1)))
        ((n + 1) / k ^ hlog k (n + 1) - 1)
        (ordOfAux k f ((n + 1) % k ^ hlog k (n + 1)))

/-- The ordinal code of `n` in hereditary base `k`, at the adequate
fuel. -/
def ordOf (k n : ℕ) : ℕ := ordOfAux k n n

theorem ordOfAux_succ_eq (k : ℕ) : ∀ (fuel n : ℕ), n ≤ fuel →
    ordOfAux k (fuel + 1) n = ordOfAux k fuel n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    cases n with
    | zero => rfl
    | succ m =>
      have hE : hlog k (m + 1) ≤ fuel := by
        have := hlog_lt k (m + 1) (by omega)
        omega
      have hR : (m + 1) % k ^ hlog k (m + 1) ≤ fuel := by
        have := rem_lt (k := k) (n := m + 1) (by omega)
        omega
      show mkO (ordOfAux k (fuel + 1) (hlog k (m + 1))) _
        (ordOfAux k (fuel + 1) _) = _
      rw [ordOfAux_succ_eq k fuel _ hE, ordOfAux_succ_eq k fuel _ hR]
      rfl

theorem ordOfAux_eq_of_le (k : ℕ) : ∀ (fuel n : ℕ), n ≤ fuel →
    ordOfAux k fuel n = ordOf k n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    rcases dec_em (n = fuel + 1) with he | he
    · rw [he]; rfl
    · have hf : n ≤ fuel := by omega
      rw [ordOfAux_succ_eq k fuel n hf, ordOfAux_eq_of_le k fuel n hf]

@[simp] theorem ordOf_zero (k : ℕ) : ordOf k 0 = 0 := rfl

/-- **The defining equation of the assignment**, at the adequate fuel:
the ordinal of `n` is `ω^(ordinal of its leading exponent) · (its leading
digit) + (ordinal of its remainder)`. -/
theorem ordOf_pos {k n : ℕ} (hn : 1 ≤ n) :
    ordOf k n = mkO (ordOf k (hlog k n)) (n / k ^ hlog k n - 1)
      (ordOf k (n % k ^ hlog k n)) := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  have hE : hlog k (m + 1) ≤ m := by
    have := hlog_lt k (m + 1) (by omega)
    omega
  have hR : (m + 1) % k ^ hlog k (m + 1) ≤ m := by
    have := rem_lt (k := k) (n := m + 1) (by omega)
    omega
  show mkO (ordOfAux k m (hlog k (m + 1))) _ (ordOfAux k m _) = _
  rw [ordOfAux_eq_of_le k m _ hE, ordOfAux_eq_of_le k m _ hR]

/-! ### Obligation 1: the assignment is monotone and lands in normal form

Monotonicity comes first: normality needs it (a normal form's remainder
must have a *strictly smaller* head exponent, and "smaller" is `≺`), and
it is provable without normality because `precB` — the bare comparison —
does not mention `nfB`. -/

/-- **The assignment is strictly monotone**, in the bare comparison.  The
three cases of the digit comparison are the three constructors of the
order (`precB_mkO_exp`, `precB_mkO_coeff`, `precB_mkO_rem`). -/
theorem precB_ordOf_of_lt {k : ℕ} (hk : 2 ≤ k) :
    ∀ b a : ℕ, a < b → precB (ordOf k a) (ordOf k b) = true := by
  refine nat_strong_ind (fun b ih ↦ ?_)
  intro a hab
  have hb1 : 1 ≤ b := by omega
  have hEb : hlog k b < b := hlog_lt k b hb1
  have hRb : b % k ^ hlog k b < b := rem_lt hb1
  have hd1b : 1 ≤ b / k ^ hlog k b := one_le_digit hk hb1
  rw [ordOf_pos hb1]
  rcases dec_em (a = 0) with ha0 | ha0
  · subst ha0
    rw [ordOf_zero]
    exact precB_zero_mkO _ _ _
  · have ha1 : 1 ≤ a := by omega
    have hd1a : 1 ≤ a / k ^ hlog k a := one_le_digit hk ha1
    have hEa : hlog k a ≤ hlog k b := hlog_le_hlog hk (by omega)
    rw [ordOf_pos ha1]
    rcases dec_em (hlog k a < hlog k b) with hlt | hnlt
    · exact precB_mkO_exp _ _ _ _ (ih _ hEb _ hlt)
    · have hEeq : hlog k a = hlog k b := by omega
      rw [hEeq]
      have hdiv : a / k ^ hlog k b ≤ b / k ^ hlog k b :=
        Nat.div_le_div_right (by omega)
      have hdeca := Nat.div_add_mod a (k ^ hlog k b)
      have hdecb := Nat.div_add_mod b (k ^ hlog k b)
      have hd1a' : 1 ≤ a / k ^ hlog k b := by rw [← hEeq]; exact hd1a
      rcases dec_em (a / k ^ hlog k b < b / k ^ hlog k b) with hdlt | hdnlt
      · exact precB_mkO_coeff _ _ _ (by omega)
      · have hdd : a / k ^ hlog k b = b / k ^ hlog k b := by omega
        have hRlt : a % k ^ hlog k b < b % k ^ hlog k b := by
          rw [hdd] at hdeca
          omega
        rw [hdd]
        exact precB_mkO_rem _ _ (ih _ hRb _ hRlt)

/-- **Obligation 1**: the assignment lands in normal form.  The remainder
clause is where monotonicity is consumed: a normal form needs its
remainder's head exponent strictly below its own, and that is exactly
`hlog_rem_lt` transported along the assignment. -/
theorem nfB_ordOf {k : ℕ} (hk : 2 ≤ k) : ∀ n : ℕ, nfB (ordOf k n) = true := by
  refine nat_strong_ind (fun n ih ↦ ?_)
  rcases dec_em (n = 0) with h0 | h0
  · subst h0
    rw [ordOf_zero]
    exact nfB_zero
  · have hn1 : 1 ≤ n := by omega
    have hEn : hlog k n < n := hlog_lt k n hn1
    have hRn : n % k ^ hlog k n < n := rem_lt hn1
    rw [ordOf_pos hn1]
    refine nfB_mkO (ih _ hEn) (ih _ hRn) ?_
    rcases dec_em (n % k ^ hlog k n = 0) with hR0 | hR0
    · rw [hR0, ordOf_zero]
      exact Or.inl rfl
    · refine Or.inr ?_
      have hR1 : 1 ≤ n % k ^ hlog k n := Nat.pos_of_ne_zero hR0
      rw [ordOf_pos hR1, oE_mkO]
      exact precB_ordOf_of_lt hk _ _ (hlog_rem_lt hk hR1)

/-- Monotonicity in the order the rule uses (comparison *and* normality). -/
theorem olt_ordOf_of_lt {k a b : ℕ} (hk : 2 ≤ k) (h : a < b) :
    OLt (ordOf k a) (ordOf k b) :=
  olt_of (nfB_ordOf hk a) (nfB_ordOf hk b) (precB_ordOf_of_lt hk b a h)

/-! ### Obligation 2: base change preserves the ordinal -/

/-- **Obligation 2**: bumping the base does not change the ordinal.  The
proof is the digit calculation: the bumped number's base-`(k+1)` digits
are the bumped exponent, the *same* leading digit, and the bumped
remainder — which is exactly what `hlog_of_digits`/`div_of_digits`/
`mod_of_digits` certify, given `bumpN_lt_pow` for the remainder bound. -/
theorem ordOf_bumpN {k : ℕ} (hk : 2 ≤ k) :
    ∀ n : ℕ, ordOf (k + 1) (bumpN k n) = ordOf k n := by
  refine nat_strong_ind (fun n ih ↦ ?_)
  rcases dec_em (n = 0) with h0 | h0
  · subst h0
    rw [bumpN_zero, ordOf_zero, ordOf_zero]
  · have hn1 : 1 ≤ n := by omega
    have hEn : hlog k n < n := hlog_lt k n hn1
    have hRn : n % k ^ hlog k n < n := rem_lt hn1
    have hd1 : 1 ≤ n / k ^ hlog k n := one_le_digit hk hn1
    have hdk : n / k ^ hlog k n < k := digit_lt hk
    have hRp : n % k ^ hlog k n < k ^ hlog k n := rem_lt_pow
    have hBR : bumpN k (n % k ^ hlog k n) < (k + 1) ^ bumpN k (hlog k n) :=
      bumpN_lt_pow hk hRp
    have hBn := bumpN_pos_eq (k := k) hn1
    have hBpos : 1 ≤ bumpN k n := by
      have := bumpN_ne_zero (k := k) (n := n) hk (by omega)
      omega
    have hlogB : hlog (k + 1) (bumpN k n) = bumpN k (hlog k n) := by
      rw [hBn]
      exact hlog_of_digits (by omega) hd1 (by omega) hBR
    have hdivB : bumpN k n / (k + 1) ^ bumpN k (hlog k n) = n / k ^ hlog k n := by
      rw [hBn]
      exact div_of_digits hBR
    have hmodB : bumpN k n % (k + 1) ^ bumpN k (hlog k n)
        = bumpN k (n % k ^ hlog k n) := by
      rw [hBn]
      exact mod_of_digits hBR
    rw [ordOf_pos hBpos, hlogB, hdivB, hmodB, ih _ hEn, ih _ hRn,
      ordOf_pos hn1]

/-! ### Obligation 3: the Goodstein step descends -/

/-- **Obligation 3**: one Goodstein step — bump the base, subtract one —
strictly decreases the ordinal.  Given obligation 2 this *is*
monotonicity: the bump leaves the ordinal fixed, and the decrement drops
it.  Note what the proof does **not** use: `tiEps0`, or anything from the
derivation system.  All three obligations are value-level arithmetic; the
transfinite induction enters only where the theorem is proved
(`GoodsteinTheorem.lean`). -/
theorem ordOf_descent {k n : ℕ} (hk : 2 ≤ k) (hn : n ≠ 0) :
    OLt (ordOf (k + 1) (bumpN k n - 1)) (ordOf k n) := by
  have hB : bumpN k n ≠ 0 := bumpN_ne_zero hk hn
  have h1 : OLt (ordOf (k + 1) (bumpN k n - 1)) (ordOf (k + 1) (bumpN k n)) :=
    olt_ordOf_of_lt (by omega) (by omega)
  rw [ordOf_bumpN hk n] at h1
  exact h1

end Realizability
