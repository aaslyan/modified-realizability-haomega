/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Common.Arithmetic

/-!
# Phase B: hereditary base-`k` notation and the Goodstein sequence

This phase makes Goodstein's theorem *expressible* in the fragment.  It
does **not** prove it, and does not touch `TI(ε₀)` or ordinal notations
— those are Phases C/D.

## The encoding decision (the load-bearing choice; see docs/first-order/STATUS.md)

**A hereditary base-`k` representation is a term of the fragment's own
syntax, in one distinguished free variable — variable `0`, "the
base".**  `hrep k n` is the closed-except-for-the-base term

    x^(hrep k e) · c  +  hrep k r        (x := the base variable)

built from `zero`/`succ`/`plus`/`times`/`exp` by peeling leading
base-`k` digits, exponents hereditarily in the same form.  Under this
encoding:

* *existence* of the representation is the evaluation fact
  `(hrep k n).eval (base := k) = n` — meta-level `hrep_eval_self`, and
  *inside the fragment* the derivable equation `hrepSelfDeriv`;
* *bumping the base* is not an operation on the representation at all
  — it is evaluating the **same term** at base `k + 1`
  (`hrep_eval_bump`), which is the mathematical essence of a Goodstein
  step; the fragment's `bump` function symbol is tied to it by
  `bumpHrepDeriv`;
* *uniqueness* (canonicity of digit bounds and exponent ordering) is
  **deferred**: everything Phase D consumes factors through the
  deterministic function `hrep`, so no statement here ever quantifies
  over "some representation" — see docs/first-order/STATUS.md for the full argument.

## Correspondence with `WilliamAngus/Goodstein` (`Goodstein/HBase.lean`
and `Goodstein/Goodstein.lean` there; reference only, no code reuse)

* our `hrep` ↔ their `HBase.ofNat`, with our term shape
  `x^e·c + r` the image of their constructor
  `hadd i aᵢ rest ↦ base ^ i.eval * aᵢ + rest.eval`;
* our `HTerm` grammar ↔ their `HBase` inductive (their `NFBelow`/`NF`
  is the deferred canonicity layer);
* our `bumpN` ↔ their `fun n => ((f base n (base+1) _).eval)` composed
  with `ofNat` — their `f` replaces the base *index* leaving the tree
  untouched, our bump evaluates the unchanged term at the next base:
  the same operation, checked concretely at `n = 4, k = 2`
  (`4 = 2^2^2^0` both here and there; bump gives `3^3^3^0 = 27`);
* our `Term.gstep`/`pred (bump …)` ↔ their `G base n = (f …).pred`;
* our `goodN`/`good` ↔ their `goodsteinSequence start h n i` at
  `start = 2`: their step `i → i+1` applies `G` at base `start + i`,
  ours bumps base `s + 2` at step `s → s+1` — the same convention,
  with values `4, 26, 41, 60, …` from `m = 4` (checked below,
  `goodN_four`, kernel-verified by `rfl`).
-/

namespace Realizability

open ContinuousFunctionals

/-! ## The fueled logarithm

`hlog` and its basic facts (`hlog_lt`, `pow_hlog_le`, `pow_hlog_pos`)
moved to `OrdinalAssignment.lean` in Phase D1, which needed them — and
much more logarithm theory — before `Soundness.lean`.  Nothing about them
changed. -/

/-! ## The hereditary representation as a fragment term -/

/-- **Hereditary base-`k` representation** (fueled like `bumpNAux`,
which it mirrors clause for clause): the fragment term, in the base
variable `0`, obtained by peeling the leading base-`k` digit
`n = k^e·c + r` into `x^(hrep e)·c + (hrep r)`.

Corresponds to `WilliamAngus/Goodstein`'s `HBase.ofNat k n`: their
representation constructor `hadd i aᵢ rest` evaluates to
`base ^ i.eval * aᵢ + rest.eval`, which is precisely this term shape
with the base abstracted into a variable.  Checked concretely at
`n = 4, k = 2`: both give `2^(2^(2^0·1+0)·1+0)·1+0 = 2^2^1` (our
uniform shape keeps the trailing `·1`/`+0`; the *value* agrees, which
is what the cross-check demands). -/
def hrepAux (k : ℕ) : ℕ → ℕ → Term
  | _, 0 => .zero
  | 0, _ + 1 => .zero
  | fuel + 1, n + 1 =>
      .plus
        (.times (.exp (.var 0) (hrepAux k fuel (hlog k (n + 1))))
          (numeral ((n + 1) / k ^ hlog k (n + 1))))
        (hrepAux k fuel ((n + 1) % k ^ hlog k (n + 1)))

/-- The hereditary base-`k` representation of `n`, at the adequate
fuel. -/
def hrep (k n : ℕ) : Term :=
  hrepAux k n n

/-- **The bump-and-decrement step** as a term former: bump the base
hereditarily, then take the predecessor.  One Goodstein step;
`goodSucc`'s right-hand side is literally `gstep (succ (succ t))
(good s t)`.  Corresponds to `WilliamAngus/Goodstein`'s
`G base n = (f base n (base+1) _).pred` (their `f` = base
replacement, their `pred` = subtract one through `ofNat`); checked at
`k = 2, n = 4`: both give `3^3^3^0 - 1 = 26`. -/
def Term.gstep (s t : Term) : Term :=
  .pred (.bump s t)

/-! ## Well-formedness: the representation grammar -/

/-- **The hereditary-representation grammar**: terms built from the
base variable (variable `0`), `zero`, `succ`, `+`, `×`, and `exp` —
no `pred`/`bump`/`good`, and no variable other than the base.  This is
the fragment image of `WilliamAngus/Goodstein`'s `HBase` inductive
(their `NFBelow` normal-form predicate is the deferred canonicity
layer; see docs/first-order/STATUS.md).  `Prop`-valued: it certifies shape, while the
derivations below recurse on the fueled structure directly. -/
inductive HTerm : Term → Prop
  | var0 : HTerm (.var 0)
  | zero : HTerm .zero
  | succ {t : Term} : HTerm t → HTerm (.succ t)
  | plus {s t : Term} : HTerm s → HTerm t → HTerm (.plus s t)
  | times {s t : Term} : HTerm s → HTerm t → HTerm (.times s t)
  | exp {s t : Term} : HTerm s → HTerm t → HTerm (.exp s t)

/-- Numerals are hereditary-representation material. -/
theorem numeral_hterm : ∀ n : ℕ, HTerm (numeral n)
  | 0 => .zero
  | n + 1 => .succ (numeral_hterm n)

/-- The representation always lands in the grammar. -/
theorem hrepAux_hterm (k : ℕ) : ∀ fuel n : ℕ, HTerm (hrepAux k fuel n)
  | 0, 0 => .zero
  | 0, _ + 1 => .zero
  | _ + 1, 0 => .zero
  | fuel + 1, n + 1 =>
      .plus (.times (.exp .var0 (hrepAux_hterm k fuel _)) (numeral_hterm _))
        (hrepAux_hterm k fuel _)

/-- `hrep k n` is a grammar term. -/
theorem hrep_hterm (k n : ℕ) : HTerm (hrep k n) :=
  hrepAux_hterm k n n

/-- Grammar terms have no free variable besides the base. -/
theorem HTerm.vars_eq_zero {t : Term} (h : HTerm t) :
    ∀ y ∈ t.vars, y = 0 := by
  induction h with
  | var0 => intro y hy; simpa [Term.vars] using hy
  | zero => intro y hy; simp [Term.vars] at hy
  | succ _ ih => exact ih
  | plus _ _ ih₁ ih₂ | times _ _ ih₁ ih₂ | exp _ _ ih₁ ih₂ =>
    intro y hy
    rcases List.mem_append.mp hy with h' | h'
    · exact ih₁ y h'
    · exact ih₂ y h'

/-! ## Existence, and the meaning of bump (meta level) -/

/-- **Existence of the representation, meta level**: reading `hrep k n`
at base `k` recovers `n` — for *every* `k` and `n` (degenerate bases
`k ≤ 1` produce the one-digit term `x^0·n + 0`, still correct).  Only
`k^e·(n/k^e) + n%k^e = n` is needed: the digit-bound facts belong to
the deferred canonicity layer.  Counterpart of evaluation-correctness
of `WilliamAngus/Goodstein`'s `ofNat` (their `eval ∘ ofNat = id`). -/
theorem hrepAux_eval_self (k : ℕ) : ∀ (fuel n : ℕ), n ≤ fuel →
    (hrepAux k fuel n).eval (fun _ ↦ k) = n
  | 0, 0, _ => rfl
  | 0, n + 1, h => absurd h (by omega)
  | fuel + 1, 0, _ => rfl
  | fuel + 1, n + 1, h => by
    have he : hlog k (n + 1) ≤ fuel := by
      have := hlog_lt k (n + 1) (by omega)
      omega
    have hr : (n + 1) % k ^ hlog k (n + 1) ≤ fuel := by
      have h1 := Nat.mod_lt (n + 1) (pow_hlog_pos k (n + 1))
      have h2 := pow_hlog_le k (n + 1) (by omega)
      omega
    simp only [hrepAux, Term.eval, numeral_eval,
      hrepAux_eval_self k fuel _ he, hrepAux_eval_self k fuel _ hr]
    exact Nat.div_add_mod (n + 1) (k ^ hlog k (n + 1))

/-- Existence at the adequate fuel. -/
theorem hrep_eval_self (k n : ℕ) : (hrep k n).eval (fun _ ↦ k) = n :=
  hrepAux_eval_self k n n (Nat.le_refl n)

/-- **What bumping means, meta level**: the value-level `bumpN` of
`Syntax.lean` is the *same representation term* read at base `k + 1`.
The two fueled recursions mirror each other clause for clause, so no
fuel-adequacy hypothesis is needed.  This is the soundness content
behind `bumpHrepDeriv` below, and the exact counterpart of
`WilliamAngus/Goodstein`'s base-replacement `f` (which also leaves the
tree untouched and reinterprets the base). -/
theorem hrepAux_eval_bump (k : ℕ) : ∀ fuel n : ℕ,
    (hrepAux k fuel n).eval (fun _ ↦ k + 1) = bumpNAux k fuel n
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | fuel + 1, 0 => rfl
  | fuel + 1, n + 1 => by
    simp only [hrepAux, bumpNAux, Term.eval, numeral_eval,
      hrepAux_eval_bump k fuel]

/-- Bump at the adequate fuel. -/
theorem hrep_eval_bump (k n : ℕ) :
    (hrep k n).eval (fun _ ↦ k + 1) = bumpN k n :=
  hrepAux_eval_bump k n n

/-! ## Derivation-formers for the Phase-B congruence schemas -/

/-- Congruence of `×`, as a derivation-former (completing Phase A's
`congPlusE` family for the schema that already existed). -/
def Deriv.congTimesE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.times s₁ s₂) (.times t₁ t₂)) :=
  .impE (.impE (.eqCongTimes s₁ t₁ s₂ t₂) D₁) D₂

/-- Congruence of `×` in the left argument alone. -/
def Deriv.congTimesL {Γ : List Formula} {s t : Term} (u : Term)
    (D : Deriv Γ (.eq s t)) : Deriv Γ (.eq (.times s u) (.times t u)) :=
  D.congTimesE (.eqRefl u)

/-- Congruence of `pred`, as a derivation-former. -/
def Deriv.congPredE {Γ : List Formula} {s t : Term}
    (D : Deriv Γ (.eq s t)) : Deriv Γ (.eq (.pred s) (.pred t)) :=
  .impE (.eqCongPred s t) D

/-- Congruence of `exp`, as a derivation-former. -/
def Deriv.congExpE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.exp s₁ s₂) (.exp t₁ t₂)) :=
  .impE (.impE (.eqCongExp s₁ t₁ s₂ t₂) D₁) D₂

/-- Congruence of `bump`, as a derivation-former. -/
def Deriv.congBumpE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.bump s₁ s₂) (.bump t₁ t₂)) :=
  .impE (.impE (.eqCongBump s₁ t₁ s₂ t₂) D₁) D₂

/-- Congruence of `good`, as a derivation-former (kit completeness). -/
def Deriv.congGoodE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.good s₁ s₂) (.good t₁ t₂)) :=
  .impE (.impE (.eqCongGood s₁ t₁ s₂ t₂) D₁) D₂

/-! ## Numeral computation inside the fragment

The fragment proves every concrete instance of its recursion axioms on
numerals; these formers produce the derivations. -/

/-- Numerals are substitution-invariant (they are closed). -/
@[simp] theorem numeral_subst (x : ℕ) (u : Term) :
    ∀ n : ℕ, Term.subst x u (numeral n) = numeral n
  | 0 => rfl
  | n + 1 => by simp only [numeral, Term.subst, numeral_subst x u n]

/-- The fragment computes numeral addition: `⊢ m̂ + n̂ = (m+n)̂`. -/
def plusNumeralDeriv (m n : ℕ) :
    Deriv [] (.eq (.plus (numeral m) (numeral n)) (numeral (m + n))) := by
  induction m with
  | zero => rw [Nat.zero_add]; exact .zeroPlus (numeral n)
  | succ m ih =>
    rw [Nat.succ_add]
    exact (Deriv.succPlus (numeral m) (numeral n)).transE ih.congSuccE

/-- The fragment computes numeral multiplication: `⊢ m̂ × n̂ = (m·n)̂`. -/
def timesNumeralDeriv (m n : ℕ) :
    Deriv [] (.eq (.times (numeral m) (numeral n)) (numeral (m * n))) := by
  induction m with
  | zero => rw [Nat.zero_mul]; exact .zeroTimes (numeral n)
  | succ m ih =>
    rw [Nat.succ_mul]
    exact (Deriv.succTimes (numeral m) (numeral n)).transE
      ((ih.congPlusL (numeral n)).transE (plusNumeralDeriv (m * n) n))

/-- The fragment computes numeral exponentiation: `⊢ b̂ ^ n̂ = (b^n)̂`. -/
def expNumeralDeriv (b n : ℕ) :
    Deriv [] (.eq (.exp (numeral b) (numeral n)) (numeral (b ^ n))) := by
  induction n with
  | zero => exact .expZero (numeral b)
  | succ n ih =>
    rw [Nat.pow_succ]
    exact (Deriv.expSucc (numeral b) (numeral n)).transE
      ((ih.congTimesL (numeral b)).transE (timesNumeralDeriv (b ^ n) b))

/-- The fragment computes the numeral predecessor: `⊢ pred n̂ = (n-1)̂`. -/
def predNumeralDeriv : (n : ℕ) →
    Deriv [] (.eq (.pred (numeral n)) (numeral (n - 1)))
  | 0 => .predZero
  | n + 1 => .predSucc (numeral n)

/-! ## The representation, certified inside the fragment -/

/-- **The certifying evaluator for representation terms**: substituting
any base numeral `b̂` for the base variable of `hrepAux k fuel n`
yields a closed term the fragment proves equal to the numeral of its
value.  Recursion mirroring `hrepAux` itself; each layer is one
congruence step plus one numeral-computation derivation. -/
def hrepSubstDeriv (k b : ℕ) : (fuel n : ℕ) →
    Deriv [] (.eq (Term.subst 0 (numeral b) (hrepAux k fuel n))
      (numeral ((hrepAux k fuel n).eval fun _ ↦ b)))
  | 0, 0 => .eqRefl .zero
  | 0, _ + 1 => .eqRefl .zero
  | _ + 1, 0 => .eqRefl .zero
  | fuel + 1, n + 1 => by
    have de := hrepSubstDeriv k b fuel (hlog k (n + 1))
    have dr := hrepSubstDeriv k b fuel ((n + 1) % k ^ hlog k (n + 1))
    simp only [hrepAux, Term.subst, Term.eval, numeral_subst, numeral_eval,
      reduceIte]
    exact (Deriv.congPlusE
        ((Deriv.congTimesE
          ((Deriv.congExpE (.eqRefl (numeral b)) de).transE
            (expNumeralDeriv b _))
          (.eqRefl (numeral _))).transE
          (timesNumeralDeriv _ _))
        dr).transE
      (plusNumeralDeriv _ _)

/-- **Existence, inside the fragment**: for every `k` and `n`, the
fragment derives that `n`'s hereditary representation, read at base
`k`, is `n` — the equation `(hrep k n)[base := k̂] = n̂` as a closed
theorem of the fragment, produced by the certifying evaluator (no
axiom about `hrep` exists; this is proved from the recursion axioms of
`+`/`×`/`exp` alone). -/
def hrepSelfDeriv (k n : ℕ) :
    Deriv [] (.eq (Term.subst 0 (numeral k) (hrep k n)) (numeral n)) := by
  have h := hrepSubstDeriv k k n n
  rw [hrepAux_eval_self k n n (Nat.le_refl n)] at h
  exact h

/-- **The meaning of `bump`, inside the fragment**: `bump k̂ n̂` equals
the representation read at base `k + 1`.  Derived (not axiomatized)
from the numeral-graph axiom `bumpNum` and the certifying evaluator —
the fragment-internal form of "same tree, next base", their `f`. -/
def bumpHrepDeriv (k n : ℕ) :
    Deriv [] (.eq (.bump (numeral k) (numeral n))
      (Term.subst 0 (numeral (k + 1)) (hrep k n))) :=
  (Deriv.bumpNum k n).transE
    (Deriv.symmE (hrep_eval_bump k n ▸ hrepSubstDeriv k (k + 1) n n))

/-! ## The Goodstein sequence, certified inside the fragment -/

/-- **The fragment computes its own Goodstein sequence**: for every
start value `m` and step count `s`, a closed derivation of
`good m̂ ŝ = (goodN m s)̂`, by the recursion axioms `goodZero`/
`goodSucc`, the `bump` graph, and the predecessor axioms — one
congruence chain per step.  (Values cross-checked against
`WilliamAngus/Goodstein`'s `goodsteinSequence` at `start = 2`; see
`goodN_four`/`goodN_three` below.) -/
def goodComputeDeriv (m : ℕ) : (s : ℕ) →
    Deriv [] (.eq (.good (numeral m) (numeral s)) (numeral (goodN m s)))
  | 0 => .goodZero (numeral m)
  | s + 1 =>
      (Deriv.goodSucc (numeral m) (numeral s)).transE
        ((Deriv.congPredE
          ((Deriv.congBumpE (.eqRefl (numeral (s + 2)))
            (goodComputeDeriv m s)).transE
            (.bumpNum (s + 2) (goodN m s)))).transE
          (predNumeralDeriv (bumpN (s + 2) (goodN m s))))

/-- **Zero is absorbing, inside the fragment** (open-term form): from
`G(s, t) = 0` the fragment derives `G(s, t+1) = 0`, via `bumpZero` —
the well-formedness fact Phase D's termination reading will want
("once the sequence hits `0` it stays there"). -/
def Deriv.goodZeroStep {Γ : List Formula} (s t : Term)
    (D : Deriv Γ (.eq (.good s t) .zero)) :
    Deriv Γ (.eq (.good s (.succ t)) .zero) :=
  (Deriv.goodSucc s t).transE
    ((Deriv.congPredE ((Deriv.congBumpE (.eqRefl (.succ (.succ t))) D).transE
      (.bumpZero (.succ (.succ t))))).transE
      .predZero)

/-! ## Concrete cross-checks (kernel-verified)

The fueled definitions compute by kernel reduction, so these are
`rfl`.  The values are the classical ones, and agree with
`WilliamAngus/Goodstein`'s `goodsteinSequence 2 _ m s` convention:
`G(4) = 4, 26, 41, 60, …` and `G(3) = 3, 3, 3, 2, 1, 0, 0` (their
step `i` bumps base `2 + i`, exactly our `s + 2`). -/

/-- `4 = 2^2^2^0` bumps to `3^3^3^0 = 27`. -/
theorem bumpN_two_four : bumpN 2 4 = 27 := rfl

/-- The classical opening of `G(4)`. -/
theorem goodN_four :
    (goodN 4 0, goodN 4 1, goodN 4 2, goodN 4 3) = (4, 26, 41, 60) := rfl

/-- `G(3)` runs to `0` in five steps and stays there. -/
theorem goodN_three :
    (goodN 3 0, goodN 3 1, goodN 3 2, goodN 3 3, goodN 3 4, goodN 3 5,
      goodN 3 6) = (3, 3, 3, 2, 1, 0, 0) := rfl

/-- The fragment itself proves `G(4, 1) = 26`. -/
def goodFourOneDeriv : Deriv []
    (.eq (.good (numeral 4) (numeral 1)) (numeral 26)) :=
  goodComputeDeriv 4 1

/-! ## Extraction and certification

The usual discipline: the headline derivations' extracted realizers
realize their conclusions (`soundness` at the empty context), the
type-2 extracts are continuous (`extract_continuous`), and
`#print axioms` runs at every build. -/

/-- The extracted realizer of fragment-level existence realizes it. -/
theorem hrep_self_realized (k n' : ℕ) (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound (hrepSelfDeriv k n') ≤ n) :
    MR ρ (.eq (Term.subst 0 (numeral k) (hrep k n')) (numeral n')) n
      (extract (hrepSelfDeriv k n') ρ [] n) :=
  soundness (hrepSelfDeriv k n') ρ [] trivial n hn

/-- The extracted realizer of the fragment's Goodstein computation
realizes it. -/
theorem good_compute_realized (m s : ℕ) (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound (goodComputeDeriv m s) ≤ n) :
    MR ρ (.eq (.good (numeral m) (numeral s)) (numeral (goodN m s))) n
      (extract (goodComputeDeriv m s) ρ [] n) :=
  soundness (goodComputeDeriv m s) ρ [] trivial n hn

/-- Continuity of the type-2 extract of fragment-level existence. -/
theorem hrep_self_extract_continuous (k n' : ℕ) (ρ : ℕ → ℕ) :
    Continuous2 (extract (hrepSelfDeriv k n') ρ [] 1) :=
  extract_continuous (hrepSelfDeriv k n') ρ

/-- Continuity of the type-2 extract of the Goodstein computation. -/
theorem good_compute_extract_continuous (m s : ℕ) (ρ : ℕ → ℕ) :
    Continuous2 (extract (goodComputeDeriv m s) ρ [] 1) :=
  extract_continuous (goodComputeDeriv m s) ρ

#print axioms hrep_self_realized
#print axioms good_compute_realized
#print axioms hrep_self_extract_continuous
#print axioms good_compute_extract_continuous

end Realizability
