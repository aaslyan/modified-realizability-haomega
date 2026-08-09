/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Signature.Hydra

/-!
# Phase H8: running the battle, and seeing it

Two things this module adds, both of which the earlier phases wanted and
neither of which needed new mathematics.

## 1. The battle, a hundred times faster — and certified to be the same one

`battleLen` (Phase H2) runs the battle **on codes**: every move decodes a
natural number into a tree, cuts, and re-encodes.  That is what made the
discriminating cross-check `Hydra(3) = 37` take ≈ 98 s and forced it out
of the build.

The cost was never the pairing — Phase H2 already made `tri` constant-time
and `unTri` logarithmic.  It is that hydra codes grow *doubly*
exponentially: `⟪a,b⟫ ≈ (a+b)²/2`, so nesting depth `d` squares the
magnitude `d` times, and the path-3 battle reaches 20-node trees.  Every
step was doing arithmetic on numbers with astronomically many digits, to
compute something the tree itself answers instantly.

`battleLenH` runs the same battle directly on `Hydra`, never encoding.
Same 37, in under a second — and `battleLen_eq_battleLenH` **proves the
two agree at every fuel, stage and code**, so the fast version is not a
different measurement, it is the same one without the arithmetic.

The three published Kirby–Paris lengths are therefore `#guard`ed at every
build now, `37` included.  That number is the discriminating one: the
*other* game in circulation (copies as bare leaves at the parent) gives
`1, 3, 11`, so landing on `37` pins down both the grandparent rule and the
copy count.  It used to be a claim in docs/first-order/STATUS.md checked by hand; it is now
checked by the build.

## 2. The trace: the tree grows, the ordinal falls

`battleTrace` prints each state in bracket notation with its ordinal
beside it.  On the 4-node path the first steps read

    (((o)))            [ω^ω]
    ((o o))            [ω^2]
    ((o) (o) (o))      [ω·3]
    (o o o o (o) (o))  [ω·2 + 4]

— the hydra gaining nodes at every step while the measure comes down.
`sizeTrace` is the same battle as node counts: `4, 4, 7, 9, 8, …, 20, 19,
…, 1`, peaking at five times its starting size before it dies.

`descendsAlong` checks the descent step by step along the real battle, and
is `#guard`ed too.  That is a *demonstration*, not a proof — the proof is
`cutH_descends` (H3), which covers every hydra and every replication
factor, and `hercules_wins` (H7), which covers every play.  What the
`#guard` adds is that the thing proved and the thing computed are visibly
the same thing.
-/

namespace Realizability

/-! ## The battle on trees -/

/-- Leaf-ness, as an equation. -/
theorem isLeaf_iff {h : Hydra} : h.isLeaf = true ↔ h = Hydra.leaf := by
  cases h with
  | node f =>
    cases f with
    | nil => simp [Hydra.isLeaf, Hydra.leaf]
    | cons c g => simp [Hydra.isLeaf, Hydra.leaf]

/-- Moves to death, run **on the tree** rather than on its code: same
recursion as `battleLen`, no encoding and no decoding. -/
def battleLenH : ℕ → ℕ → Hydra → ℕ
  | 0, _, _ => 0
  | f + 1, stage, h =>
      if h.isLeaf then 0 else battleLenH f (stage + 1) (hydraStep stage h) + 1

/-- Decoding commutes with the move — the fact that makes the tree-level
battle the same battle. -/
theorem hydraOf_hydraStepN (stage code : ℕ) :
    hydraOf (hydraStepN stage code) = hydraStep stage (hydraOf code) :=
  hydraOf_encodeH _

/-- **The fast battle is the same battle.**  At every fuel, stage and
code, running on trees agrees with running on codes. -/
theorem battleLen_eq_battleLenH : ∀ (fuel stage code : ℕ),
    battleLen fuel stage code = battleLenH fuel stage (hydraOf code)
  | 0, _, _ => rfl
  | fuel + 1, stage, code => by
    rcases dec_em (code = 0) with h0 | h0
    · subst h0
      rfl
    · have hne : ¬ (hydraOf code).isLeaf = true :=
        fun hl ↦ h0 (hydraOf_eq_leaf_iff.mp (isLeaf_iff.mp hl))
      show (if code = 0 then 0 else battleLen fuel (stage + 1) _ + 1)
        = if (hydraOf code).isLeaf then 0 else battleLenH fuel (stage + 1) _ + 1
      rw [if_neg h0, if_neg hne, battleLen_eq_battleLenH fuel (stage + 1)
        (hydraStepN stage code), hydraOf_hydraStepN]

/-! ### The published values, now checked at every build

`Hydra(k)` for the path hydra with `k + 1` nodes.  `37` is the
discriminating value: the other game in circulation gives `11` here. -/

#guard battleLenH 20 1 (path 1) == 1
#guard battleLenH 20 1 (path 2) == 3
#guard battleLenH 200 1 (path 3) == 37

/-- The same three, stated as a theorem about the *code-level* function —
which is the one Phase H2's `battleLen_small` and the citation discussion
are about.  Paths 1 and 2 reduce in the kernel; path 3 is left to the
`#guard` above, since kernel reduction does not use the compiled
closed forms for `tri`/`unTri`. -/
theorem battleLen_path_small :
    (battleLen 20 1 (encodeH (path 1)), battleLen 20 1 (encodeH (path 2)))
      = (1, 3) := rfl

/-! ## The descent, watched rather than proved -/

/-- Does the ordinal strictly drop at every step of the real battle? -/
def descendsAlong : ℕ → ℕ → Hydra → Bool
  | 0, _, _ => true
  | f + 1, stage, h =>
      if h.isLeaf then true
      else
        let h' := hydraStep stage h
        precB (ordOfHydra h') (ordOfHydra h) && descendsAlong f (stage + 1) h'

/-! Checked at every build: along the whole 37-move battle on the 4-node
path, every single move lowered the ordinal — while the tree grew from 4
nodes to 20.  (The *theorem* is `cutH_descends`; this is the picture of
it.) -/

#guard descendsAlong 200 1 (path 3)

/-! ## Rendering -/

mutual

/-- Node count. -/
def sizeH : Hydra → ℕ
  | .node f => sizeF f + 1

/-- The number of nodes in a forest (mutual with `sizeH`). -/
def sizeF : Forest → ℕ
  | .nil => 0
  | .cons h f => sizeH h + sizeF f

end

mutual

/-- Bracket notation: `o` is a head, `(…)` a node with its children. -/
def renderH : Hydra → String
  | .node .nil => "o"
  | .node f => "(" ++ renderF f ++ ")"

/-- Bracket notation for a forest (mutual with `renderH`). -/
def renderF : Forest → String
  | .nil => ""
  | .cons h .nil => renderH h
  | .cons h f => renderH h ++ " " ++ renderF f

end

/-- A notation code as Cantor normal form: `mkO e c r` is `ω^e·(c+1) + r`,
read back through the destructors.  Fueled on `oE n < n` and `oR n < n`. -/
def ordStr : ℕ → ℕ → String
  | 0, _ => "?"
  | _ + 1, 0 => "0"
  | fuel + 1, n + 1 =>
      let e := oE (n + 1)
      let c := oC (n + 1)
      let r := oR (n + 1)
      let power :=
        if e = 0 then toString (c + 1)
        else
          let es := ordStr fuel e
          let b := if e = 1 then "ω"
                   else if es.any (fun ch ↦ ch == ' ' || ch == '·') then "ω^(" ++ es ++ ")"
                   else "ω^" ++ es
          if c = 0 then b else b ++ "·" ++ toString (c + 1)
      if r = 0 then power else power ++ " + " ++ ordStr fuel r

/-- The ordinal of a hydra, printed. -/
def ordOfHydraStr (h : Hydra) : String :=
  let n := ordOfHydra h
  ordStr (n + 1) n

/-- One line per state: the tree, then its ordinal. -/
def battleTrace : ℕ → ℕ → Hydra → List String
  | 0, _, _ => []
  | f + 1, stage, h =>
      let line := renderH h ++ "   [" ++ ordOfHydraStr h ++ "]"
      if h.isLeaf then [line]
      else line :: battleTrace f (stage + 1) (hydraStep stage h)

/-- The same battle as node counts — the growth curve. -/
def sizeTrace : ℕ → ℕ → Hydra → List ℕ
  | 0, _, _ => []
  | f + 1, stage, h =>
      if h.isLeaf then [sizeH h]
      else sizeH h :: sizeTrace f (stage + 1) (hydraStep stage h)

/-! ## The pictures

The 3-node path in full: four states, `ω ≻ 2 ≻ 1 ≻ 0`, with the middle
step the one where the tree gets *wider* (one child with one head becomes
two heads). -/

#eval battleTrace 100 1 (path 2)

/-! The 4-node path, first ten of its thirty-eight states.  Read the two
columns against each other: the bracket string gets longer, the ordinal
gets smaller, at every line. -/

#eval (battleTrace 200 1 (path 3)).take 10

/-! And the whole 37-move battle as node counts.  It peaks at 20 — five
times the starting size — and the ordinal came down at all 37 steps
(`descendsAlong`, above). -/

#eval sizeTrace 200 1 (path 3)

#print axioms battleLen_eq_battleLenH
#print axioms isLeaf_iff

end Realizability
