/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Ordinals.Epsilon0

/-!
# Phase H1: finite rooted trees as natural numbers

The Kirby–Paris Hydra game needs the fragment to quantify over *trees*,
and the fragment has one sort: `ℕ`.  So hydras are coded as naturals,
the same way Phase C coded ordinal notations — and, as there, the coding
is built from scratch rather than taken from Mathlib.

## Why from scratch again

Phase C's experience is the reason, and it is worth restating because it
is the constraint that shapes this file.  Mathlib's `Nat.pair`/
`Nat.unpair` were unusable there for two independent reasons: *every*
lemma about them depends on `Classical.choice` (measured, not assumed),
which would propagate into `extract` and break the continuity theorems'
`[propext, Quot.sound]` budget; and `Nat.unpair` goes through `Nat.sqrt`,
which does not reduce in the kernel, which would cost every `rfl`
cross-check.  `Epsilon0.lean` therefore has a hand-rolled triangular
pairing that is choice-free and kernel-computable, with `pr`/`pr1`/`pr2`
and the bijection lemmas.  **This file reuses that pairing**; it adds no
new coding primitive, only the list-of-children layer on top.

## The trees, and the coding

A hydra is a finite rooted tree: a node together with a finite, possibly
empty, list of child hydras.  Written as a mutual pair of inductives —
`Hydra` and `Forest` — rather than as `Hydra := List Hydra`, because
mutual structural recursion over the pair is what the encode/decode
proofs need, and nested inductives make those proofs fight the recursor.

Codes follow the standard list coding through the pairing:

    ⌜nil⌝            = 0
    ⌜cons h f⌝       = ⟪⌜h⌝, ⌜f⌝⟫ + 1
    ⌜node f⌝         = ⌜f⌝

A hydra's code *is* its forest's code, since a node carries no data
beyond its children.  Because `pr` is a bijection and the `+1` separates
the empty forest from the nonempty ones, the coding is a bijection
between `ℕ` and hydras — both round trips are proved below
(`decode_encode`, `encode_decode`), which is what makes "the fragment's
`∀x` ranges over exactly the hydras" true rather than approximate.

Decoding is fueled, like every other recursion in this development: the
components `pr1 n` and `pr2 n` are `≤ n` (`pr1_le`, `pr2_le`), so fuel
`= n` is adequate (`decodeF_eq_of_le`).

## Position in the import chain (since H4)

This module sits **before `Syntax.lean`**, next to `OrdinalAssignment.lean`
and for the same reason: `Term.eval` evaluates the Phase-H4 symbols by
`hydraStepN`/`hydraSeqN`/`ordOfHydraN` defined here, and `Soundness.lean`
needs `olt_ordOfHydraN_step` for the descent schema's case.  So the
definitions in this file are inside `extract`'s dependency graph, and
every one of them must stay `Classical`-free and kernel-computable — the
same constraint `Epsilon0.lean` carries, and for the same reason: a
`Classical.choice` here would break every continuity theorem's
`[propext, Quot.sound]` budget.  It currently holds: `#print axioms` on
all three reports *does not depend on any axioms*.  Proofs in this file
are unconstrained (they reach `soundness`, whose budget allows choice);
only the definitions are.
-/

namespace Realizability

/-! ## The trees -/

mutual

/-- A hydra: a rooted node with a finite list of child hydras. -/
inductive Hydra : Type where
  | node : Forest → Hydra

/-- A finite list of hydras — the children of a node. -/
inductive Forest : Type where
  | nil : Forest
  | cons : Hydra → Forest → Forest

end

/-- The one-node hydra (a bare head). -/
def Hydra.leaf : Hydra := .node .nil

/-! ## Encoding -/

mutual

/-- The code of a hydra: the code of its children. -/
def encodeH : Hydra → ℕ
  | .node f => encodeF f

/-- The code of a forest: the standard list coding through the pairing. -/
def encodeF : Forest → ℕ
  | .nil => 0
  | .cons h f => pr (encodeH h) (encodeF f) + 1

end

@[simp] theorem encodeH_node (f : Forest) : encodeH (.node f) = encodeF f := rfl

@[simp] theorem encodeF_nil : encodeF .nil = 0 := rfl

@[simp] theorem encodeF_cons (h : Hydra) (f : Forest) :
    encodeF (.cons h f) = pr (encodeH h) (encodeF f) + 1 := rfl

/-! ## Decoding -/

/-- Decode a code into a forest (fueled; `pr1`/`pr2` strictly decrease the
code, so fuel `= n` is adequate). -/
def decodeF : ℕ → ℕ → Forest
  | 0, _ => .nil
  | _ + 1, 0 => .nil
  | fuel + 1, n + 1 =>
      .cons (.node (decodeF fuel (pr1 n))) (decodeF fuel (pr2 n))

/-- Decode a code into a hydra. -/
def decodeH (fuel n : ℕ) : Hydra := .node (decodeF fuel n)

theorem decodeF_succ_eq : ∀ (fuel n : ℕ), n ≤ fuel →
    decodeF (fuel + 1) n = decodeF fuel n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    cases n with
    | zero => rfl
    | succ m =>
      have h1 : pr1 m ≤ fuel := by
        have := pr1_le m
        omega
      have h2 : pr2 m ≤ fuel := by
        have := pr2_le m
        omega
      show Forest.cons (.node (decodeF (fuel + 1) (pr1 m)))
          (decodeF (fuel + 1) (pr2 m)) = _
      rw [decodeF_succ_eq fuel _ h1, decodeF_succ_eq fuel _ h2]
      rfl

theorem decodeF_eq_of_le : ∀ (fuel n : ℕ), n ≤ fuel →
    decodeF fuel n = decodeF n n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    rcases dec_em (n = fuel + 1) with he | he
    · rw [he]
    · have hf : n ≤ fuel := by omega
      rw [decodeF_succ_eq fuel n hf, decodeF_eq_of_le fuel n hf]

/-- **The hydra with code `n`**, at the adequate fuel. -/
def hydraOf (n : ℕ) : Hydra := decodeH n n

/-- **The forest with code `n`**, at the adequate fuel. -/
def forestOf (n : ℕ) : Forest := decodeF n n

theorem forestOf_zero : forestOf 0 = .nil := rfl

/-- The decoding recursion, at the adequate fuel. -/
theorem forestOf_succ (n : ℕ) :
    forestOf (n + 1) = .cons (.node (forestOf (pr1 n))) (forestOf (pr2 n)) := by
  show decodeF (n + 1) (n + 1) = _
  show Forest.cons (.node (decodeF n (pr1 n))) (decodeF n (pr2 n)) = _
  rw [decodeF_eq_of_le n _ (pr1_le n), decodeF_eq_of_le n _ (pr2_le n)]
  rfl

/-! ## The coding is a bijection

Both round trips, as the brief requires: decoding a code and re-encoding
returns the code, and encoding a tree and decoding returns the tree. -/

/-- Round trip one: every natural number *is* a code. -/
theorem encodeF_decodeF : ∀ (fuel n : ℕ), n ≤ fuel →
    encodeF (decodeF fuel n) = n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    cases n with
    | zero => rfl
    | succ m =>
      have h1 : pr1 m ≤ fuel := by
        have := pr1_le m
        omega
      have h2 : pr2 m ≤ fuel := by
        have := pr2_le m
        omega
      show pr (encodeH (.node (decodeF fuel (pr1 m)))) (encodeF (decodeF fuel (pr2 m)))
        + 1 = m + 1
      rw [encodeH_node, encodeF_decodeF fuel _ h1, encodeF_decodeF fuel _ h2,
        pr_pr1_pr2]

/-- Round trip one, at the adequate fuel: `⌜forestOf n⌝ = n`. -/
theorem encodeF_forestOf (n : ℕ) : encodeF (forestOf n) = n :=
  encodeF_decodeF n n (Nat.le_refl n)

/-- Hence also for hydras. -/
theorem encodeH_hydraOf (n : ℕ) : encodeH (hydraOf n) = n :=
  encodeF_forestOf n

mutual

/-- Round trip two, hydras: decoding a tree's own code returns the tree. -/
theorem decodeH_encodeH : ∀ (h : Hydra) (fuel : ℕ), encodeH h ≤ fuel →
    decodeH fuel (encodeH h) = h
  | .node f, fuel, hf => by
    show Hydra.node (decodeF fuel (encodeF f)) = Hydra.node f
    rw [decodeF_encodeF f fuel hf]

/-- Round trip two, forests. -/
theorem decodeF_encodeF : ∀ (f : Forest) (fuel : ℕ), encodeF f ≤ fuel →
    decodeF fuel (encodeF f) = f
  | .nil, fuel, _ => by
    cases fuel with
    | zero => rfl
    | succ g => rfl
  | .cons h f, fuel, hf => by
    cases fuel with
    | zero =>
      exact absurd hf (by simp [encodeF])
    | succ g =>
      have hb : pr (encodeH h) (encodeF f) ≤ g := by
        simp only [encodeF] at hf
        omega
      have h1 : encodeH h ≤ g := by
        have := pr1_le (pr (encodeH h) (encodeF f))
        rw [pr1_pr] at this
        omega
      have h2 : encodeF f ≤ g := by
        have := pr2_le (pr (encodeH h) (encodeF f))
        rw [pr2_pr] at this
        omega
      show Forest.cons (.node (decodeF g (pr1 (pr (encodeH h) (encodeF f)))))
          (decodeF g (pr2 (pr (encodeH h) (encodeF f)))) = _
      rw [pr1_pr, pr2_pr, decodeF_encodeF f g h2]
      have hh : decodeH g (encodeH h) = h := decodeH_encodeH h g h1
      show Forest.cons (decodeH g (encodeH h)) f = _
      rw [hh]

end

/-- Round trip two, at the adequate fuel. -/
theorem hydraOf_encodeH (h : Hydra) : hydraOf (encodeH h) = h :=
  decodeH_encodeH h (encodeH h) (Nat.le_refl _)

theorem forestOf_encodeF (f : Forest) : forestOf (encodeF f) = f :=
  decodeF_encodeF f (encodeF f) (Nat.le_refl _)

/-! ## Small codes, kernel-checked

The coding is computable in the kernel (that is what the hand-rolled
pairing buys), so the smallest hydras can be read off by `rfl`. -/

/-- The empty forest — a bare root with no children — is code `0`. -/
theorem encodeH_leaf : encodeH Hydra.leaf = 0 := rfl

/-- A root with one leaf child is code `1`. -/
theorem encodeH_one : encodeH (.node (.cons Hydra.leaf .nil)) = 1 := rfl

/-- A root with one child which itself has one leaf child — a chain of
depth two — is code `2`. -/
theorem encodeH_two :
    encodeH (.node (.cons (.node (.cons Hydra.leaf .nil)) .nil)) = 2 := rfl

/-- A root with two leaf children is code `3`. -/
theorem encodeH_three :
    encodeH (.node (.cons Hydra.leaf (.cons Hydra.leaf .nil))) = 3 := rfl

/-- And the decoder inverts all of them, in the kernel. -/
theorem hydraOf_small :
    (hydraOf 0, hydraOf 1, hydraOf 2, hydraOf 3)
      = (Hydra.leaf,
         .node (.cons Hydra.leaf .nil),
         .node (.cons (.node (.cons Hydra.leaf .nil)) .nil),
         .node (.cons Hydra.leaf (.cons Hydra.leaf .nil))) := rfl

/-! ## Phase H2: the cutting-and-regrowth step

The rule implemented here (see docs/first-order/STATUS.md for the citation and for the
variants that exist in the literature):

* a **head** is a leaf — a node with no children;
* Hercules chops one head off.  Let `p` be the head's parent;
* if `p` is the **root**, the head is simply removed and nothing grows;
* otherwise let `g` be `p`'s parent.  After the head is removed from `p`,
  the hydra grows `n` extra copies of the resulting subtree at `p`, all
  attached to `g`.  The modified `p` itself stays where it was.

Two parameters are left open and fixed by the caller, deliberately:
**which** head is chopped (here: the leftmost, per H4's canonical-strategy
decision) and **how many** copies grow (`n`, so the theorems quantify over
it and cover both the "n at stage n" and the adversarial readings).

`cutH` returns the new subtree together with a flag saying "the head I
chopped was a *direct child* of me", which is exactly the information the
caller needs to decide whether it is the grandparent and must therefore
grow the copies.  At the root the flag is discarded — which is precisely
the "parent is the root, nothing grows" clause. -/

/-- Concatenation of forests. -/
def Forest.append : Forest → Forest → Forest
  | .nil, g => g
  | .cons h f, g => .cons h (Forest.append f g)

/-- `n` copies of a hydra, as a forest. -/
def Forest.replicate : ℕ → Hydra → Forest
  | 0, _ => .nil
  | n + 1, h => .cons h (Forest.replicate n h)

/-- Is this hydra a bare head (a node with no children)? -/
def Hydra.isLeaf : Hydra → Bool
  | .node .nil => true
  | .node (.cons _ _) => false

/-- **One Hydra move**: chop the leftmost head, growing `n` copies at the
grandparent.  The `Bool` reports whether the chopped head was a direct
child of this node, i.e. whether *this node's parent* is the grandparent
that must grow the copies. -/
def cutH (n : ℕ) : Hydra → Hydra × Bool
  | .node .nil => (.node .nil, false)
  | .node (.cons (.node .nil) rest) => (.node rest, true)
  | .node (.cons (.node (.cons c₀ cs)) rest) =>
      let child : Hydra := .node (.cons c₀ cs)
      let r := cutH n child
      if r.2 then
        -- the head was a child of `child`, so this node is the grandparent
        (.node (.cons r.1 (Forest.append (Forest.replicate n r.1) rest)), false)
      else
        (.node (.cons r.1 rest), false)

/-- The move, forgetting the flag: at the root there is no grandparent, so
a head chopped from the root simply disappears. -/
def hydraStep (n : ℕ) (h : Hydra) : Hydra := (cutH n h).1

/-- The move on **codes** — the value-level function the fragment's symbol
will evaluate by.  Decoding and re-encoding are both kernel-computable, so
this computes. -/
def hydraStepN (n code : ℕ) : ℕ := encodeH (hydraStep n (hydraOf code))

/-- The battle: `hydraSeq n s` is the state after `s` moves from the hydra
coded `n`, with the number of copies at step `s` taken to be `s + 1`. -/
def hydraSeqN (start : ℕ) : ℕ → ℕ
  | 0 => start
  | s + 1 => hydraStepN (s + 1) (hydraSeqN start s)

/-! ### Small battles, kernel-checked

Codes from the table above: `0` is a bare head, `1` a root with one head,
`2` the two-deep chain, `3` a root with two heads. -/

/-- A root with two heads loses them one at a time and nothing grows —
both heads hang off the root, so the regrowth clause never fires. -/
theorem hydraSeq_two_heads :
    (hydraSeqN 3 0, hydraSeqN 3 1, hydraSeqN 3 2) = (3, 1, 0) := rfl

/-- The two-deep chain, where regrowth actually fires. -/
theorem hydraSeq_chain :
    (hydraSeqN 2 0, hydraSeqN 2 1, hydraSeqN 2 2, hydraSeqN 2 3) = (2, 3, 1, 0) := rfl

/-- Worth reading off: the middle step **grew** the hydra.  Code `2` is a
root with one child carrying one head; chopping that head empties the
child, and the root — the grandparent — grows a copy of it, leaving code
`3`, a root with *two* heads.  The tree got wider before it died.  This is
the phenomenon in miniature, and the reason the assigned ordinal, not the
node count, is what decreases (Phase H3). -/
theorem hydraSeq_one : (hydraSeqN 1 0, hydraSeqN 1 1) = (1, 0) := rfl

/-! ### Path hydras and the published battle lengths

The discriminating cross-check.  A *path hydra* is a chain: `path k` has
`k + 1` nodes.  Under Kirby–Paris the battle lengths are `1, 3, 37, …`
(the fourth exceeds Graham's number); under the *other* game in
circulation — copies as bare leaves attached to the parent — they are
`1, 3, 11, …`.  Getting `37` therefore pins down both the grandparent
rule and the copy count.

`battleLen` counts moves to death with the stage-indexed replication this
file uses.  Paths 1 and 2 are checked by `rfl` at build time; path 3 takes
about ninety seconds, so it is verified out of band and recorded in
docs/first-order/STATUS.md rather than run on every build:

    #eval battleLen 200 1 (encodeH (path 3))   -- 37
-/

/-- The path hydra with `k + 1` nodes. -/
def path : ℕ → Hydra
  | 0 => Hydra.leaf
  | k + 1 => .node (.cons (path k) .nil)

/-- Moves to death, from stage `stage`, with `fuel` bounding the count. -/
def battleLen : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, stage, code =>
      if code = 0 then 0 else battleLen f (stage + 1) (hydraStepN stage code) + 1

/-- `Hydra(1) = 1` and `Hydra(2) = 3`, the published values. -/
theorem battleLen_small :
    (battleLen 20 1 (encodeH (path 1)), battleLen 20 1 (encodeH (path 2)))
      = (1, 3) := rfl

/-! ## Phase H3: the ordinal assignment

The measure that decreases even when the tree grows.  A hydra is sent to
a Cantor-normal-form notation of `Epsilon0.lean` — **no second ordinal
encoding**, the same principle Phase C's `ordTerm` followed:

    ord(node [c₁, …, cₖ])  =  ω^(ord c₁) ⊕ … ⊕ ω^(ord cₖ)

the natural (Hessenberg) sum, built by inserting one exponent at a time
into a normal form.  Insertion is where the ordinal arithmetic this
development did not previously have lives: given an exponent `e` and a
normal form `c`, produce the normal form of `ω^e ⊕ c` by comparing `e`
against `c`'s head exponent — equal exponents merge into the
coefficient, a larger one is prepended, a smaller one recurses into the
remainder.

`ordOfForest` is then a plain structural recursion over the tree, needing
no fuel; only `insertExp` is fueled, on `oR c < c`. -/

/-- `ω^e ⊕ c` in Cantor normal form (fueled on the remainder). -/
def insertExpAux : ℕ → ℕ → ℕ → ℕ
  | 0, e, _ => mkO e 0 0
  | _ + 1, e, 0 => mkO e 0 0
  | fuel + 1, e, c =>
      if e = oE c then mkO (oE c) (oC c + 1) (oR c)
      else if precB (oE c) e then mkO e 0 c
      else mkO (oE c) (oC c) (insertExpAux fuel e (oR c))

/-- `ω^e ⊕ c`, at the adequate fuel. -/
def insertExp (e c : ℕ) : ℕ := insertExpAux c e c

theorem insertExpAux_succ_eq (e : ℕ) : ∀ (fuel c : ℕ), c ≤ fuel →
    insertExpAux (fuel + 1) e c = insertExpAux fuel e c
  | 0, c, h => by
    have hc : c = 0 := by omega
    subst hc
    rfl
  | fuel + 1, c, h => by
    cases c with
    | zero => rfl
    | succ m =>
      have hr : oR (m + 1) ≤ fuel := by
        have := oR_lt (n := m + 1) (by omega)
        omega
      show (if e = oE (m + 1) then _ else if precB (oE (m + 1)) e then _
        else mkO (oE (m + 1)) (oC (m + 1)) (insertExpAux (fuel + 1) e (oR (m + 1)))) = _
      rw [insertExpAux_succ_eq e fuel _ hr]
      rfl

theorem insertExpAux_eq_of_le (e : ℕ) : ∀ (fuel c : ℕ), c ≤ fuel →
    insertExpAux fuel e c = insertExp e c
  | 0, c, h => by
    have hc : c = 0 := by omega
    subst hc
    rfl
  | fuel + 1, c, h => by
    rcases dec_em (c = fuel + 1) with he | he
    · rw [he]; rfl
    · have hf : c ≤ fuel := by omega
      rw [insertExpAux_succ_eq e fuel c hf, insertExpAux_eq_of_le e fuel c hf]

@[simp] theorem insertExp_zero (e : ℕ) : insertExp e 0 = mkO e 0 0 := rfl

/-- The defining equation of insertion at a nonzero normal form. -/
theorem insertExp_pos {e c : ℕ} (hc : c ≠ 0) :
    insertExp e c =
      if e = oE c then mkO (oE c) (oC c + 1) (oR c)
      else if precB (oE c) e then mkO e 0 c
      else mkO (oE c) (oC c) (insertExp e (oR c)) := by
  obtain ⟨m, hm⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  subst hm
  have hr : oR (m + 1) ≤ m := by
    have := oR_lt (n := m + 1) (by omega)
    omega
  show (if e = oE (m + 1) then _ else if precB (oE (m + 1)) e then _
    else mkO (oE (m + 1)) (oC (m + 1)) (insertExpAux m e (oR (m + 1)))) = _
  rw [insertExpAux_eq_of_le e m _ hr]

/-- The head exponent of an insertion is one of the two candidates: the
inserted exponent (when it is prepended, or when it merges with an equal
head) or the old head (when it recurses into the remainder).  Needed for
normality: the new remainder's head must still sit below the old head. -/
theorem oE_insertExp (e c : ℕ) :
    oE (insertExp e c) = e ∨ oE (insertExp e c) = oE c := by
  rcases dec_em (c = 0) with hc | hc
  · subst hc
    left
    rw [insertExp_zero, oE_mkO]
  · rw [insertExp_pos hc]
    rcases dec_em (e = oE c) with he | he
    · rw [if_pos he, oE_mkO]
      exact Or.inr rfl
    · rw [if_neg he]
      rcases dec_em (precB (oE c) e = true) with hp | hp
      · rw [if_pos hp, oE_mkO]
        exact Or.inl rfl
      · rw [if_neg hp, oE_mkO]
        exact Or.inr rfl

/-- An insertion is never zero: every branch builds an `mkO`. -/
theorem insertExp_ne_zero (e c : ℕ) : insertExp e c ≠ 0 := by
  rcases dec_em (c = 0) with hc | hc
  · subst hc
    rw [insertExp_zero]
    exact mkO_ne_zero _ _ _
  · rw [insertExp_pos hc]
    rcases dec_em (e = oE c) with he | he
    · rw [if_pos he]; exact mkO_ne_zero _ _ _
    · rw [if_neg he]
      rcases dec_em (precB (oE c) e = true) with hp | hp
      · rw [if_pos hp]; exact mkO_ne_zero _ _ _
      · rw [if_neg hp]; exact mkO_ne_zero _ _ _

/-- **Insertion preserves normal form.**  Three of the four cases are the
normal-form destructors read back; the fourth — recursing into the
remainder — is where totality of the comparison is consumed, to know that
an exponent neither equal to nor above the head sits below it, so the new
remainder still fits under the old head. -/
theorem nfB_insertExp {e : ℕ} (he : nfB e = true) :
    ∀ c : ℕ, nfB c = true → nfB (insertExp e c) = true := by
  refine nat_strong_ind (fun c ih ↦ ?_)
  intro hnc
  rcases dec_em (c = 0) with hc | hc
  · subst hc
    rw [insertExp_zero]
    exact nfB_mkO he nfB_zero (Or.inl rfl)
  · rw [insertExp_pos hc]
    rcases dec_em (e = oE c) with heq | heq
    · rw [if_pos heq]
      exact nfB_mkO (nfB_exp hc hnc) (nfB_rem hc hnc) (nfB_below hc hnc)
    · rw [if_neg heq]
      rcases dec_em (precB (oE c) e = true) with hp | hp
      · rw [if_pos hp]
        exact nfB_mkO he hnc (Or.inr hp)
      · rw [if_neg hp]
        have hpf : precB (oE c) e = false := by
          simpa using hp
        have hlt : precB e (oE c) = true :=
          precB_of_ne_of_not_precB he (nfB_exp hc hnc) heq hpf
        have hrec : nfB (insertExp e (oR c)) = true :=
          ih (oR c) (oR_lt hc) (nfB_rem hc hnc)
        refine nfB_mkO (nfB_exp hc hnc) hrec (Or.inr ?_)
        rcases dec_em (oR c = 0) with hr0 | hr0
        · rw [hr0, insertExp_zero, oE_mkO]
          exact hlt
        · rcases oE_insertExp e (oR c) with hoe | hoe
          · rw [hoe]; exact hlt
          · rw [hoe]
            rcases nfB_below hc hnc with h0 | h0
            · exact absurd h0 hr0
            · exact h0

/-- **Inserting strictly increases the ordinal**: `c ≺ ω^e ⊕ c`.

At `e = 0` this *is* the base case of the descent, read backwards:
`ord(node (leaf :: rest)) = ω^0 ⊕ ord(rest) ≻ ord(rest)`, i.e. chopping a
head whose parent is the root strictly lowers the ordinal.  The cases
follow the three order constructors — bigger coefficient, bigger head
exponent, bigger remainder — with the last recursing. -/
theorem precB_insertExp_self (e : ℕ) :
    ∀ c : ℕ, precB c (insertExp e c) = true := by
  refine nat_strong_ind (fun c ih ↦ ?_)
  rcases dec_em (c = 0) with hc | hc
  · subst hc
    rw [insertExp_zero]
    exact precB_zero_mkO _ _ _
  · have hA : mkO (oE c) (oC c) (oR c) = c := mkO_oE_oC_oR hc
    rw [insertExp_pos hc]
    rcases dec_em (e = oE c) with heq | heq
    · rw [if_pos heq]
      have h := precB_mkO_coeff (oE c) (oR c) (oR c)
        (show oC c < oC c + 1 by omega)
      rwa [hA] at h
    · rw [if_neg heq]
      rcases dec_em (precB (oE c) e = true) with hp | hp
      · rw [if_pos hp]
        have h := precB_mkO_exp (oC c) (oR c) 0 c hp
        rwa [hA] at h
      · rw [if_neg hp]
        have h := precB_mkO_rem (oE c) (oC c) (ih (oR c) (oR_lt hc))
        rwa [hA] at h

/-- **Monotonicity of insertion in the accumulator.**  See
`docs/internal/NOTES_insertExp_monotonicity.md` for the grid this follows: row `Z`
(`c₁ = 0`) settles with one constructor each; the equal-head rows collapse
to the diagonal, because both accumulators compare `e` against the same
head and so take the same branch, and only the both-recursed corner uses
the induction hypothesis; the smaller-head rows need transitivity to place
`c₁` from `c₂`'s branch condition. -/
theorem precB_insertExp_mono {e : ℕ} (he : nfB e = true) :
    ∀ c₂ c₁ : ℕ, nfB c₁ = true → nfB c₂ = true → precB c₁ c₂ = true →
      precB (insertExp e c₁) (insertExp e c₂) = true := by
  refine nat_strong_ind (fun c₂ ih ↦ ?_)
  intro c₁ hn₁ hn₂ h12
  have hc₂ : c₂ ≠ 0 := by
    intro h0
    rw [h0, precB_zero_right] at h12
    exact absurd h12 (by simp)
  rw [insertExp_pos hc₂]
  rcases dec_em (c₁ = 0) with hc₁ | hc₁
  · -- row Z
    subst hc₁
    rw [insertExp_zero]
    rcases dec_em (e = oE c₂) with hb | hb
    · rw [if_pos hb]
      conv => lhs; rw [hb]
      exact precB_mkO_coeff _ _ _ (by omega)
    · rw [if_neg hb]
      rcases dec_em (precB (oE c₂) e = true) with hp | hp
      · rw [if_pos hp]
        exact precB_mkO_rem _ _ (precB_zero_left hc₂)
      · rw [if_neg hp]
        exact precB_mkO_exp _ _ _ _
          (precB_of_ne_of_not_precB he (nfB_exp hc₂ hn₂) hb (by simpa using hp))
  · rw [insertExp_pos hc₁]
    rcases precB_cases hc₁ hc₂ h12 with hexp | ⟨heq, hrest⟩
    · -- smaller head exponent
      rcases dec_em (e = oE c₂) with hb | hb
      · rw [if_pos hb]
        have hp₁ : precB (oE c₁) e = true := by rw [hb]; exact hexp
        have hne₁ : ¬ (e = oE c₁) := by
          intro hEq
          rw [← hEq, precB_irrefl] at hp₁
          exact absurd hp₁ (by simp)
        rw [if_neg hne₁, if_pos hp₁]
        conv => lhs; rw [hb]
        exact precB_mkO_coeff _ _ _ (by omega)
      · rcases dec_em (precB (oE c₂) e = true) with hp | hp
        · rw [if_neg hb, if_pos hp]
          have hp₁ : precB (oE c₁) e = true := precB_trans hexp hp
          have hne₁ : ¬ (e = oE c₁) := by
            intro hEq
            rw [← hEq, precB_irrefl] at hp₁
            exact absurd hp₁ (by simp)
          rw [if_neg hne₁, if_pos hp₁]
          exact precB_mkO_rem _ _ h12
        · rw [if_neg hb, if_neg hp]
          have hlt : precB e (oE c₂) = true :=
            precB_of_ne_of_not_precB he (nfB_exp hc₂ hn₂) hb (by simpa using hp)
          rcases dec_em (e = oE c₁) with hb₁ | hb₁
          · rw [if_pos hb₁]
            exact precB_mkO_exp _ _ _ _ (hb₁ ▸ hlt)
          · rw [if_neg hb₁]
            rcases dec_em (precB (oE c₁) e = true) with hp₁ | hp₁
            · rw [if_pos hp₁]
              exact precB_mkO_exp _ _ _ _ hlt
            · rw [if_neg hp₁]
              exact precB_mkO_exp _ _ _ _ hexp
    · -- equal head exponents: both take the same branch
      rw [heq]
      rcases dec_em (e = oE c₂) with hb | hb
      · rw [if_pos hb, if_pos hb]
        rcases hrest with hcc | ⟨hcc, hrr⟩
        · exact precB_mkO_coeff _ _ _ (by omega)
        · rw [hcc]
          exact precB_mkO_rem _ _ hrr
      · rw [if_neg hb, if_neg hb]
        rcases dec_em (precB (oE c₂) e = true) with hp | hp
        · rw [if_pos hp, if_pos hp]
          exact precB_mkO_rem _ _ h12
        · rw [if_neg hp, if_neg hp]
          rcases hrest with hcc | ⟨hcc, hrr⟩
          · exact precB_mkO_coeff _ _ _ (by omega)
          · rw [hcc]
            exact precB_mkO_rem _ _
              (ih (oR c₂) (oR_lt hc₂) (oR c₁) (nfB_rem hc₁ hn₁) (nfB_rem hc₂ hn₂) hrr)

/-- **Monotonicity of insertion in the exponent**: inserting a smaller
exponent into the same normal form gives a smaller normal form.

Grid, per the notes: `b`'s branch drives the case analysis.  If `b` merges
(`b = oE X`) then `a ≺ oE X`, so `a` recurses, and the two sides differ by
one in the coefficient.  If `b` prepends then all three of `a`'s branches
give a head strictly below `b`, so each is one exponent comparison.  If
`b` recurses then `a ≺ b ≺ oE X` forces `a` to recurse too, and the
induction hypothesis finishes it. -/
theorem precB_insertExp_mono_exp {a b : ℕ} (ha : nfB a = true)
    (hb : nfB b = true) (hab : precB a b = true) :
    ∀ X : ℕ, nfB X = true → precB (insertExp a X) (insertExp b X) = true := by
  refine nat_strong_ind (fun X ih ↦ ?_)
  intro hnX
  rcases dec_em (X = 0) with hX | hX
  · subst hX
    rw [insertExp_zero, insertExp_zero]
    exact precB_mkO_exp _ _ _ _ hab
  · rw [insertExp_pos hX, insertExp_pos hX]
    rcases dec_em (b = oE X) with hbE | hbE
    · rw [if_pos hbE]
      have haX : precB a (oE X) = true := hbE ▸ hab
      have hane : ¬ (a = oE X) := by
        intro h
        rw [h, precB_irrefl] at haX
        exact absurd haX (by simp)
      have hnp : ¬ (precB (oE X) a = true) := by
        intro h
        rw [precB_asymm haX] at h
        exact absurd h (by simp)
      rw [if_neg hane, if_neg hnp]
      exact precB_mkO_coeff _ _ _ (by omega)
    · rw [if_neg hbE]
      rcases dec_em (precB (oE X) b = true) with hpb | hpb
      · rw [if_pos hpb]
        rcases dec_em (a = oE X) with haE | haE
        · rw [if_pos haE]
          exact precB_mkO_exp _ _ _ _ (haE ▸ hab)
        · rw [if_neg haE]
          rcases dec_em (precB (oE X) a = true) with hpa | hpa
          · rw [if_pos hpa]
            exact precB_mkO_exp _ _ _ _ hab
          · rw [if_neg hpa]
            exact precB_mkO_exp _ _ _ _ hpb
      · rw [if_neg hpb]
        have hbX : precB b (oE X) = true :=
          precB_of_ne_of_not_precB hb (nfB_exp hX hnX) hbE (by simpa using hpb)
        have haX : precB a (oE X) = true := precB_trans hab hbX
        have hane : ¬ (a = oE X) := by
          intro h
          rw [h, precB_irrefl] at haX
          exact absurd haX (by simp)
        have hnp : ¬ (precB (oE X) a = true) := by
          intro h
          rw [precB_asymm haX] at h
          exact absurd h (by simp)
        rw [if_neg hane, if_neg hnp]
        exact precB_mkO_rem _ _ (ih (oR X) (oR_lt hX) (nfB_rem hX hnX))

/-! ### Iterated insertion: the `n` regrown copies

`insertIter e n X` is the `n`-fold insertion of `ω^e` into `X` — the
ordinal of a node that grew `n` copies.  The bound below is what makes
arbitrarily many copies harmless, and note where `n` appears in its
proof: only as a coefficient, in the two places the order constructors
ignore coefficients.  The induction is on `X`, with `n` general. -/

/-- Insert `n` copies of `ω^e` into the CNF sum `X` (iterated `insertExp`). -/
def insertIter (e : ℕ) : ℕ → ℕ → ℕ
  | 0, X => X
  | n + 1, X => insertExp e (insertIter e n X)

@[simp] theorem insertIter_zero (e X : ℕ) : insertIter e 0 X = X := rfl

@[simp] theorem insertIter_succ (e n X : ℕ) :
    insertIter e (n + 1) X = insertExp e (insertIter e n X) := rfl

/-- The head of an iterate is the inserted exponent or the old head. -/
theorem oE_insertIter (e : ℕ) : ∀ (n X : ℕ),
    oE (insertIter e n X) = e ∨ oE (insertIter e n X) = oE X
  | 0, X => Or.inr rfl
  | n + 1, X => by
    rcases oE_insertExp e (insertIter e n X) with h | h
    · exact Or.inl (by rw [insertIter_succ, h])
    · rcases oE_insertIter e n X with h' | h'
      · exact Or.inl (by rw [insertIter_succ, h, h'])
      · exact Or.inr (by rw [insertIter_succ, h, h'])

/-- When the inserted exponent is below the head, every insertion is
pushed into the remainder. -/
theorem insertIter_push {e X : ℕ} (h : precB e (oE X) = true) : ∀ n : ℕ,
    insertIter e n X = mkO (oE X) (oC X) (insertIter e n (oR X))
  | 0 => by
    have hX : X ≠ 0 := by
      intro h0
      rw [h0] at h
      simp only [oE] at h
      rw [show pr1 (0 - 1) = 0 from rfl, precB_zero_right] at h
      exact absurd h (by simp)
    exact (mkO_oE_oC_oR hX).symm
  | n + 1 => by
    have hne : ¬ (e = oE X) := by
      intro hEq
      rw [hEq, precB_irrefl] at h
      exact absurd h (by simp)
    have hnp : ¬ (precB (oE X) e = true) := by
      intro hp
      rw [precB_asymm h] at hp
      exact absurd hp (by simp)
    rw [insertIter_succ, insertIter_push h n]
    rw [insertExp_pos (mkO_ne_zero _ _ _), oE_mkO, oC_mkO, oR_mkO,
      if_neg hne, if_neg hnp]
    rfl

/-- **The bound**: `n` copies of `ω^a` sit below one `ω^b`, for every `n`,
whenever `a ≺ b`.  Induction on `X`; `n` is untouched. -/
theorem precB_insertIter_lt {a b : ℕ} (ha : nfB a = true) (hb : nfB b = true)
    (hab : precB a b = true) :
    ∀ X : ℕ, nfB X = true → ∀ n : ℕ,
      precB (insertIter a n X) (insertExp b X) = true := by
  refine nat_strong_ind (fun X ih ↦ ?_)
  intro hnX n
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0, precB_zero_right] at hab
    exact absurd hab (by simp)
  rcases dec_em (precB (oE X) b = true) with hpb | hpb
  · -- `b` is above `X`'s head: the right side prepends, and the left
    -- side's head is `a` or `oE X`, both below `b`
    have hbE : ¬ (b = oE X) := by
      intro hEq
      rw [hEq, precB_irrefl] at hpb
      exact absurd hpb (by simp)
    have hRHS : insertExp b X = mkO b 0 X := by
      rcases dec_em (X = 0) with hX | hX
      · rw [hX, insertExp_zero]
      · rw [insertExp_pos hX, if_neg hbE, if_pos hpb]
    rw [hRHS]
    rcases dec_em (insertIter a n X = 0) with hz | hz
    · rw [hz]
      exact precB_zero_mkO _ _ _
    · have hd := mkO_oE_oC_oR hz
      have hlt : precB (oE (insertIter a n X)) b = true := by
        rcases oE_insertIter a n X with h | h
        · rw [h]; exact hab
        · rw [h]; exact hpb
      have hgoal := precB_mkO_exp (oC (insertIter a n X))
        (oR (insertIter a n X)) 0 X hlt
      rwa [hd] at hgoal
  · rcases dec_em (b = oE X) with hbE | hbE
    · -- `b` equals the head: coefficient comparison, `n` ignored
      have haX : precB a (oE X) = true := hbE ▸ hab
      have hX : X ≠ 0 := by
        intro h0
        rw [h0, show oE 0 = 0 from rfl, precB_zero_right] at haX
        exact absurd haX (by simp)
      rw [insertExp_pos hX, if_pos hbE, insertIter_push haX n]
      exact precB_mkO_coeff _ _ _ (by omega)
    · -- `b` is below the head: both sides push into the remainder
      have hX : X ≠ 0 := by
        intro h0
        rw [h0, show oE 0 = 0 from rfl] at hpb
        exact hpb (precB_zero_left hbne)
      have hbX : precB b (oE X) = true :=
        precB_of_ne_of_not_precB hb (nfB_exp hX hnX) hbE (by simpa using hpb)
      have haX : precB a (oE X) = true := precB_trans hab hbX
      rw [insertExp_pos hX, if_neg hbE, if_neg hpb, insertIter_push haX n]
      exact precB_mkO_rem _ _ (ih (oR X) (oR_lt hX) (nfB_rem hX hnX) n)

/-! ### The assignment -/

mutual

/-- **The ordinal of a hydra**, as a notation code. -/
def ordOfHydra : Hydra → ℕ
  | .node f => ordOfForest f

/-- The natural sum of `ω^(ord ·)` over a forest. -/
def ordOfForest : Forest → ℕ
  | .nil => 0
  | .cons h f => insertExp (ordOfHydra h) (ordOfForest f)

end

@[simp] theorem ordOfHydra_node (f : Forest) :
    ordOfHydra (.node f) = ordOfForest f := rfl

@[simp] theorem ordOfForest_nil : ordOfForest .nil = 0 := rfl

@[simp] theorem ordOfForest_cons (h : Hydra) (f : Forest) :
    ordOfForest (.cons h f) = insertExp (ordOfHydra h) (ordOfForest f) := rfl

mutual

/-- **The assignment lands in normal form**, so `≺` applies to it — the
precondition for any descent statement at all. -/
theorem nfB_ordOfHydra : ∀ h : Hydra, nfB (ordOfHydra h) = true
  | .node f => nfB_ordOfForest f

theorem nfB_ordOfForest : ∀ f : Forest, nfB (ordOfForest f) = true
  | .nil => nfB_zero
  | .cons h f => nfB_insertExp (nfB_ordOfHydra h) _ (nfB_ordOfForest f)

end

/-- **The base case of the descent**: a node loses a head that hangs off
it, and its ordinal strictly drops.  This is the "parent is the root"
clause of the Kirby–Paris rule, where nothing regrows. -/
theorem ordOfForest_cons_leaf_descends (f : Forest) :
    precB (ordOfForest f) (ordOfForest (.cons Hydra.leaf f)) = true :=
  precB_insertExp_self _ _

/-- The regrown copies, as an iterate: bookkeeping over `append`/
`replicate`, no ordinal reasoning. -/
theorem ordOfForest_append_replicate (c : Hydra) (f : Forest) : ∀ n : ℕ,
    ordOfForest (Forest.append (Forest.replicate n c) f)
      = insertIter (ordOfHydra c) n (ordOfForest f)
  | 0 => rfl
  | n + 1 => by
    show ordOfForest (Forest.cons c (Forest.append (Forest.replicate n c) f)) = _
    rw [ordOfForest_cons, ordOfForest_append_replicate c f n]
    rfl

/-- **The descent.**  Every legal move strictly decreases the assigned
ordinal.  A bare head is excluded: `cutH` leaves it alone, and a dead
hydra's ordinal does not drop.

The three cases are `cutH`'s own: a head hanging off this node
(`ordOfForest_cons_leaf_descends`); a deeper cut with no regrowth here
(exponent monotonicity); and a deeper cut where this node is the
grandparent and `n` copies grow (`precB_insertIter_lt`, which is
insensitive to `n`). -/
theorem cutH_descends (n : ℕ) : ∀ h : Hydra, h ≠ Hydra.leaf →
    precB (ordOfHydra (cutH n h).1) (ordOfHydra h) = true
  | .node .nil, hne => absurd rfl hne
  | .node (.cons (.node .nil) rest), _ =>
      ordOfForest_cons_leaf_descends rest
  | .node (.cons (.node (.cons c₀ cs)) rest), _ => by
    have hchild : (Hydra.node (.cons c₀ cs)) ≠ Hydra.leaf := by
      intro hEq
      exact absurd hEq (by simp [Hydra.leaf])
    have IH := cutH_descends n (.node (.cons c₀ cs)) hchild
    have hnf₁ := nfB_ordOfHydra (cutH n (Hydra.node (.cons c₀ cs))).1
    have hnf₂ := nfB_ordOfHydra (Hydra.node (.cons c₀ cs))
    have hnfR := nfB_ordOfForest rest
    rcases dec_em ((cutH n (Hydra.node (.cons c₀ cs))).2 = true) with hflag | hflag
    · simp only [cutH, hflag, if_true, ordOfHydra_node, ordOfForest_cons,
        ordOfForest_append_replicate]
      exact precB_insertIter_lt hnf₁ hnf₂ IH _ hnfR (n + 1)
    · simp only [Bool.not_eq_true] at hflag
      simp only [cutH, hflag, if_false, ordOfHydra_node, ordOfForest_cons]
      exact precB_insertExp_mono_exp hnf₁ hnf₂ IH _ hnfR

/-- The assignment on codes — the value-level function the fragment's
symbol will evaluate by in H4. -/
def ordOfHydraN (code : ℕ) : ℕ := ordOfHydra (hydraOf code)

/-- The descent on codes. -/
theorem hydraStepN_descends (n code : ℕ) (h : hydraOf code ≠ Hydra.leaf) :
    precB (ordOfHydraN (hydraStepN n code)) (ordOfHydraN code) = true := by
  show precB (ordOfHydra (hydraOf (encodeH (hydraStep n (hydraOf code)))))
    (ordOfHydra (hydraOf code)) = true
  rw [hydraOf_encodeH]
  exact cutH_descends n (hydraOf code) h

/-! ### The form the fragment imports (Phase H4)

The fragment has one sort and no predicate for "is a bare head", so the
side condition must be an equation on codes.  It is: the coding is a
bijection sending the dead hydra to `0`, so `code = 0` *is* "the hydra is
dead".  Everything below is stated that way. -/

/-- The dead hydra is exactly code `0` — one direction of the bijection,
read as the fragment's termination test. -/
theorem hydraOf_eq_leaf_iff {code : ℕ} : hydraOf code = Hydra.leaf ↔ code = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  have h2 : encodeH (hydraOf code) = encodeH Hydra.leaf := by rw [h]
  rw [encodeH_hydraOf, encodeH_leaf] at h2
  exact h2

/-- **The descent, with the fragment's own side condition**: as long as
the hydra is not already dead, one move strictly decreases its ordinal.
This is the single fact Phase H4 imports as an axiom schema
(`Deriv.hordCutLt`), and it is a property of the *move* symbol, not of the
battle — the analogue of `ordPredLt` in the Goodstein layer. -/
theorem olt_ordOfHydraN_step (n code : ℕ) (h : code ≠ 0) :
    OLt (ordOfHydraN (hydraStepN n code)) (ordOfHydraN code) :=
  olt_of (nfB_ordOfHydra _) (nfB_ordOfHydra _)
    (hydraStepN_descends n code fun hl ↦ h (hydraOf_eq_leaf_iff.mp hl))

/-- The battle's own recursion, in the two forms the fragment's schemas
`hydraZero`/`hydraSucc` assert.  Both hold by definition; they are named
so that the soundness cases read as citations rather than as `rfl`. -/
theorem hydraSeqN_zero (start : ℕ) : hydraSeqN start 0 = start := rfl

theorem hydraSeqN_succ (start s : ℕ) :
    hydraSeqN start (s + 1) = hydraStepN (s + 1) (hydraSeqN start s) := rfl

/-- The dead hydra stays dead: `0` is a fixed point of every move.  Not
needed for termination, but it is what makes "reaches `0`" the right
reading of the theorem. -/
theorem hydraStepN_zero (n : ℕ) : hydraStepN n 0 = 0 := rfl


/-! ### The first descent instances, kernel-checked

The smallest battle where the tree *grows* is `2 → 3` (one child with one
head becomes two heads).  Its ordinals are `ω` and `2`: the node count
went up, the ordinal came down.  That is the whole point of the
assignment, and here it is checked by computation. -/

/-- A bare head has ordinal `0`; a root with one head has ordinal `1`;
the two-deep chain has ordinal `ω` (code `2`); two heads has ordinal `2`
(code `3`). -/
theorem ordOfHydraN_small :
    (ordOfHydraN 0, ordOfHydraN 1, ordOfHydraN 2, ordOfHydraN 3)
      = (0, 1, omegaCode, 3) := rfl

/-- **The measure decreases where the tree grows.**  `ω ≻ 2`, along the
step `2 → 3` that made the hydra wider. -/
theorem ordOfHydraN_descends_two :
    OLt (ordOfHydraN (hydraSeqN 2 1)) (ordOfHydraN (hydraSeqN 2 0)) := by decide

/-- And along the rest of that battle. -/
theorem ordOfHydraN_descends_rest :
    OLt (ordOfHydraN (hydraSeqN 2 2)) (ordOfHydraN (hydraSeqN 2 1)) ∧
    OLt (ordOfHydraN (hydraSeqN 2 3)) (ordOfHydraN (hydraSeqN 2 2)) := by
  refine ⟨by decide, by decide⟩

#print axioms encodeF_decodeF
#print axioms decodeF_encodeF
#print axioms hydraOf_encodeH
#print axioms encodeF_forestOf

end Realizability
