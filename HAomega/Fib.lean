/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Extraction

/-!
# HA^ω, part 4b: Fibonacci — extracted, runnable, readable

The first end-to-end pass through the new pipeline.

## What is different from the first-order version, in one line

There, `fib` is a **symbol** with three axiom schemas (`fibZero`, `fibOne`,
`fibSucc`) added through ~16 sites of the development.  Here it is a
**term**, `fibT`, defined by a paired System T recursion — no new syntax, no
new axioms, no changes anywhere else.  That is the "all 21 symbols become
definable" claim, discharged for one of them.

## Reading the output

`extract` produces a `Tm`, so it can be printed.  `Tm.pretty` below renders it
with named variables.  Two views matter:

* the **raw** extract, which carries a `star` for every contentless
  subderivation — the `unit`-typed junk that equational reasoning leaves
  behind;
* the **collapsed** view, `Tm.pretty'`, which elides those.

That distinction is only possible because `tyOf` sends equations to `unit`,
so "carries no information" is visible in the type rather than by convention.
-/

namespace HAomega

/-! ## Fibonacci as a System T term -/

/-- The step of the paired iteration: `(a, b) ↦ (b, a + b)`. -/
def fibStep {Γ : List Ty} :
    Tm Γ (.arrow (.prod .nat .nat) (.prod .nat .nat)) :=
  .lam (.pair (.snd (.var .here))
    (.add (.fst (.var .here)) (.snd (.var .here))))

/-- **Fibonacci**, by iterating the paired step `n` times from `(0, 1)`.

Definable in System T because the recursor works at *every* type — here at
`nat × nat`.  The first-order fragment cannot do this: its recursion is on `ℕ`
alone, which is exactly why `fib` had to be a primitive symbol there. -/
def fibPairT {Γ : List Ty} : Tm Γ (.arrow .nat (.prod .nat .nat)) :=
  .lam (.recNat (.pair .zero (.succ .zero))
    (.lam (.lam (.app fibStep (.var .here)))) (.var .here))

/-- `fib n`. -/
def fibT {Γ : List Ty} : Tm Γ (.arrow .nat .nat) :=
  .lam (.fst (.app fibPairT (.var .here)))

-- The term computes.  (`#guard`, not `rfl`: kernel reduction of `recNat` at
-- these arguments exhausts the recursion depth, while compiled evaluation is
-- instant — the same distinction the first-order development records for its
-- fueled value functions.)
#guard (fibT (Γ := [])).eval Env.nil 10 == 55
#guard (fibT (Γ := [])).eval Env.nil 20 == 6765

/-! ## The theorem, and its extraction -/

/-- `∀n. ∃y. y = fib n`. -/
def fibSpec : Formula [] (.arrow .nat (.prod .nat .unit)) :=
  .all .nat (.ex .nat (.eq (.var .here) (.app fibT (.var (.there .here)))))

/-- The derivation: introduce `∀n`, then witness the existential with `fib n`
itself and close by reflexivity.

The proof is short *because* `fib` is definable — which is the point, but it
also means the extracted program is essentially `fibT`.  The genuinely
interesting extraction, where an induction with a paired invariant produces an
algorithm the specification did not name, is the next milestone; see
`HAOMEGA.md`. -/
def fibDeriv : Deriv Ctx.nil fibSpec := by
  refine Deriv.allI ?_
  exact Deriv.exI (.app fibT (.var .here)) (Deriv.eqRefl _)

/-- The extracted realizer, as a closed System T term. -/
def fibRealizer : Tm [] (.arrow .nat (.prod .nat .unit)) := extractClosed fibDeriv

/-- The extracted **program**: apply the realizer to `n` and read the witness
component of the existential. -/
def fibExtracted (n : Nat) : Nat := (fibRealizer.eval Env.nil n).1

/-! ## It runs -/

#guard (List.range 16).map fibExtracted
  == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610]
#guard fibExtracted 100 == 354224848179261915075
#guard fibExtracted 1000 % 1000000007 == 517691607
#guard (fibExtracted 1000).repr.length == 209

/-! ### The evaluation wall — historical note

An earlier version of `fibStep` used `Tm.addT` — addition *defined* by
primitive recursion on the second argument, costing `y` steps per `x + y` —
and `fibExtracted` then genuinely overflowed the stack near `n = 28`, since
`fib n` cost `Θ(fib n)` recursor frames.  That diagnosis motivated making `+`
a **primitive** term former (interpreted by `Nat.add`, defining equations as
the conversion rules `convAddZero`/`convAddSucc`), which is how HA^ω is
usually presented and what the first-order development also does.  `Tm.addT`
remains as the proof that addition is definable.

**Current behavior, verified by direct evaluation** (2026-08-08):
`fibExtracted` at `26 / 27 / 28` returns `121393 / 196418 / 317811`
instantly, and the `n = 100` and `n = 1000` guards above pass at every
build.  There is no wall in this range. -/

/-! ## It is readable

A pretty-printer for `Tm`.  Variables print as `x0`, `x1`, … by de Bruijn
level, so the output is ordinary lambda-calculus notation. -/

/-- Render a variable's de Bruijn *level* given the context depth. -/
def Var.lvl : {Γ : List Ty} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .here => 0
  | _, _, .there v => v.lvl + 1

/-- A type, as a string. -/
def Ty.str : Ty → String
  | .unit => "1"
  | .ord => "O"
  | .hyd => "H"
  | .nat => "N"
  | .arrow a b => "(" ++ a.str ++ "→" ++ b.str ++ ")"
  | .prod a b => "(" ++ a.str ++ "×" ++ b.str ++ ")"

/-- Render a term.  `d` is the current binder depth, so bound variables get
distinct names. -/
def Tm.pretty : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → (d : Nat) → String
  | _, _, .var v, d => "x" ++ toString (d - 1 - v.lvl)
  | _, _, .lam t, d => "(λx" ++ toString d ++ ". " ++ t.pretty (d + 1) ++ ")"
  | _, _, .app f a, d => "(" ++ f.pretty d ++ " " ++ a.pretty d ++ ")"
  | _, _, .star, _ => "★"
  | _, _, .pair a b, d => "⟨" ++ a.pretty d ++ ", " ++ b.pretty d ++ "⟩"
  | _, _, .fst t, d => "fst " ++ t.pretty d
  | _, _, .snd t, d => "snd " ++ t.pretty d
  | _, _, .zero, _ => "0"
  | _, _, .succ t, d => "S " ++ t.pretty d
  | _, _, .add a b, d => "(" ++ a.pretty d ++ " + " ++ b.pretty d ++ ")"
  | _, _, .prec a b, d => "(" ++ a.pretty d ++ " ≺ " ++ b.pretty d ++ ")"
  | _, _, .pred a, d => "pred " ++ a.pretty d
  | _, _, .bump a b, d => "bump(" ++ a.pretty d ++ ", " ++ b.pretty d ++ ")"
  | _, _, .good a b, d => "good(" ++ a.pretty d ++ ", " ++ b.pretty d ++ ")"
  | _, _, .ord a b, d => "ord(" ++ a.pretty d ++ ", " ++ b.pretty d ++ ")"
  | _, _, .hcut a b, d => "hcut(" ++ a.pretty d ++ ", " ++ b.pretty d ++ ")"
  | _, _, .hcutAt p a b, d =>
      "hcutAt(" ++ p.pretty d ++ ", " ++ a.pretty d ++ ", " ++ b.pretty d ++ ")"
  | _, _, .ezero, _ => "0ᵒ"
  | _, _, .orde a b, d => "ordᵒ(" ++ a.pretty d ++ ", " ++ b.pretty d ++ ")"
  | _, _, .olte a b, d => "(" ++ a.pretty d ++ " ≺ᵒ " ++ b.pretty d ++ ")"
  | _, _, .tiRecE s n, d =>
      "tiRecᵒ[" ++ s.pretty d ++ " | " ++ n.pretty d ++ "]"
  | _, _, .hleaf, _ => "leafᴴ"
  | _, _, .hcutH a b, d => "cutᴴ(" ++ a.pretty d ++ ", " ++ b.pretty d ++ ")"
  | _, _, .hleafQ a, d => "deadᴴ?" ++ a.pretty d
  | _, _, .hordH a, d => "hordᴴ " ++ a.pretty d
  | _, _, .hydra a b, d => "hydra(" ++ a.pretty d ++ ", " ++ b.pretty d ++ ")"
  | _, _, .hord a, d => "hord " ++ a.pretty d
  | _, _, .tiRec s n, d =>
      "tiRec[" ++ s.pretty d ++ " | " ++ n.pretty d ++ "]"
  | _, _, .recNat z s n, d =>
      "rec[" ++ z.pretty d ++ " | " ++ s.pretty d ++ " | " ++ n.pretty d ++ "]"

/-- The **collapsed** view: contentless components (`star`, and pairs whose
second component is contentless) are elided, so what prints is the part of the
realizer that carries information. -/
def Tm.pretty' : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → (d : Nat) → String
  | _, _, .var v, d => "x" ++ toString (d - 1 - v.lvl)
  | _, _, .lam t, d => "(λx" ++ toString d ++ ". " ++ t.pretty' (d + 1) ++ ")"
  | _, _, .app f a, d => "(" ++ f.pretty' d ++ " " ++ a.pretty' d ++ ")"
  | _, _, .star, _ => "·"
  | _, _, .pair a b, d =>
      -- elide a contentless second component (the equational certificate)
      let sb := b.pretty' d
      if sb == "·" then a.pretty' d
      else "⟨" ++ a.pretty' d ++ ", " ++ sb ++ "⟩"
  | _, _, .fst t, d => "fst " ++ t.pretty' d
  | _, _, .snd t, d => "snd " ++ t.pretty' d
  | _, _, .zero, _ => "0"
  | _, _, .succ t, d => "S " ++ t.pretty' d
  | _, _, .add a b, d => "(" ++ a.pretty' d ++ " + " ++ b.pretty' d ++ ")"
  | _, _, .prec a b, d => "(" ++ a.pretty' d ++ " ≺ " ++ b.pretty' d ++ ")"
  | _, _, .pred a, d => "pred " ++ a.pretty' d
  | _, _, .bump a b, d => "bump(" ++ a.pretty' d ++ ", " ++ b.pretty' d ++ ")"
  | _, _, .good a b, d => "good(" ++ a.pretty' d ++ ", " ++ b.pretty' d ++ ")"
  | _, _, .ord a b, d => "ord(" ++ a.pretty' d ++ ", " ++ b.pretty' d ++ ")"
  | _, _, .hcut a b, d => "hcut(" ++ a.pretty' d ++ ", " ++ b.pretty' d ++ ")"
  | _, _, .hcutAt p a b, d =>
      "hcutAt(" ++ p.pretty' d ++ ", " ++ a.pretty' d ++ ", " ++ b.pretty' d ++ ")"
  | _, _, .ezero, _ => "0ᵒ"
  | _, _, .orde a b, d => "ordᵒ(" ++ a.pretty' d ++ ", " ++ b.pretty' d ++ ")"
  | _, _, .olte a b, d => "(" ++ a.pretty' d ++ " ≺ᵒ " ++ b.pretty' d ++ ")"
  | _, _, .tiRecE s n, d =>
      "tiRecᵒ[" ++ s.pretty' d ++ " | " ++ n.pretty' d ++ "]"
  | _, _, .hleaf, _ => "leafᴴ"
  | _, _, .hcutH a b, d => "cutᴴ(" ++ a.pretty' d ++ ", " ++ b.pretty' d ++ ")"
  | _, _, .hleafQ a, d => "deadᴴ?" ++ a.pretty' d
  | _, _, .hordH a, d => "hordᴴ " ++ a.pretty' d
  | _, _, .hydra a b, d => "hydra(" ++ a.pretty' d ++ ", " ++ b.pretty' d ++ ")"
  | _, _, .hord a, d => "hord " ++ a.pretty' d
  | _, _, .tiRec s n, d =>
      "tiRec[" ++ s.pretty' d ++ " | " ++ n.pretty' d ++ "]"
  | _, _, .recNat z s n, d =>
      "rec[" ++ z.pretty' d ++ " | " ++ s.pretty' d ++ " | " ++ n.pretty' d ++ "]"

-- The realizer's type.
#eval (Ty.arrow .nat (.prod .nat .unit)).str

-- The raw extracted realizer.
#eval fibRealizer.pretty 0

-- The same realizer, contentless parts elided.
#eval fibRealizer.pretty' 0

#print axioms extract
#print axioms fibRealizer

end HAomega
