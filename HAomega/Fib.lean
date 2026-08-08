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

/-! ### The evaluation wall, diagnosed

`fibExtracted` runs to `n = 26` and overflows the stack at about `n = 28`.
That limit is **not** the extractor, and not the ambient-level problem this
whole branch exists to remove.  It is arithmetic:

`Tm.addT` is `λx y. rec x (λk. λih. succ ih) y` — addition by primitive
recursion on the second argument, so `x + y` costs **`y` steps**.  In
Fibonacci the second argument *is* a Fibonacci number, so `fib n` costs
`Θ(fib n)` recursor steps and the same depth of `Nat.rec` frames.  fib(26)
already needs ~121 393 of them.

So the object language's addition is unary, and that is a genuine property of
System T terms, not an artefact of this implementation.  The fix is a design
decision rather than a patch: add `+` as a **primitive** term former
interpreted by Lean's `Nat.add`, with its two defining equations as conversion
rules — which is how HA^ω is usually presented anyway, and which the
first-order development also does (`zeroPlus`/`succPlus`).  `addT` then stays
as the *proof* that addition is definable, while the primitive is what runs.

Recorded rather than silently fixed, because it changes the term language. -/

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
