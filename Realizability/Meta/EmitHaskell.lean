/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Meta.EmitLean

/-!
# A Haskell backend for the same walk

`Meta/EmitLean.lean` re-extracts a derivation into native Lean types.  This
module emits the *same* structure as Haskell source.  The two share their
shape deliberately: `hsTy` mirrors `tyOf` clause for clause, `hsDefault`
mirrors `defaultOf`, and `hsEmit` mirrors `emit` case for case, so a
discrepancy between them is visible by reading them side by side.

## Scope — weaker than `EmitLean`, and it matters

`EmitLean` is an unproved *translation*, but it is at least a total Lean
function that Lean type-checks.  This module is a **string generator**, so it
has two further gaps, and neither should be glossed:

1. **Nothing checks the output.**  Lean type-checks `emit`; nothing here
   type-checks what `hsEmit` prints except GHC, downstream, on the emitted
   file.  This is the same arrangement as Coq's extraction to OCaml/Haskell,
   which sits in the trusted base rather than being verified — the motivation
   for verified-extraction work such as CertiCoq.
2. **`tiEps0` loses its termination guarantee.**  The rule's realizer is
   well-founded recursion along `≺`, and Haskell cannot express that, so
   `tiRec` in the prelude is an ordinary recursive function.  A Goodstein
   program emitted here is one Haskell cannot certify halts — epistemically
   right back beside `GoodsteinSearch.lean`'s `partial def stopBySearch`,
   which is the exact distinction Phase P4 exists to draw.  Emitting to Agda,
   Idris, or Rocq would keep it; Haskell and OCaml cannot.

## The prelude is a second trusted boundary

The fragment's function symbols are interpreted by `Term.eval` through the
value layer (`goodN`, `bumpN`, `hydraStepN`, `lookN`, …).  Haskell needs its
own copies, and their fidelity to the Lean originals is an *assumption*, not a
theorem.  `hsPrelude` below therefore splits them in two, explicitly:

* **implemented** — the arithmetic, `fibN`, `pasN`, `xorN`.  These are short,
  structural, and independent of the ordinal-notation pairing.
* **stubbed** — everything that decodes Phase C's hand-rolled pairing
  (`bumpN`, `goodN`, `ordOf`, `oltN`, the Hydra and Hanoi coders, `lookN`).
  Each is emitted as an `error` naming the Lean source to port from, rather
  than as a plausible-looking re-implementation that might silently diverge.

Consequently the theorems that emit to **complete, runnable Haskell** are the
ones whose derivations use only `zero`/`succ`/`+`/`×` and the implemented
symbols: **gcd, Fibonacci, Pascal**.  Goodstein, Hydra, Hanoi, and Sperner emit
structurally complete programs whose prelude must be finished first.

That gcd is in the runnable group is the useful accident: it is the derivation
whose certified realizer evaluates at no input at all.
-/

namespace Realizability.Emit

open Realizability

/-! ## Types and defaults, mirroring `tyOf` / `defaultOf` -/

/-- The Haskell type of a realizer of `φ`.  Mirrors `tyOf` clause for clause. -/
def hsTy : Formula → String
  | .bot => "()"
  | .eq _ _ => "()"
  | .and a b => "(" ++ hsTy a ++ ", " ++ hsTy b ++ ")"
  | .or a b => "(Integer, (" ++ hsTy a ++ ", " ++ hsTy b ++ "))"
  | .imp a b => "(" ++ hsTy a ++ " -> " ++ hsTy b ++ ")"
  | .all _ a => "(Integer -> " ++ hsTy a ++ ")"
  | .ex _ a => "(Integer, " ++ hsTy a ++ ")"

/-- A canonical inhabitant of `hsTy φ`.  Mirrors `defaultOf`. -/
def hsDefault : Formula → String
  | .bot => "()"
  | .eq _ _ => "()"
  | .and a b => "(" ++ hsDefault a ++ ", " ++ hsDefault b ++ ")"
  | .or a b => "(0, (" ++ hsDefault a ++ ", " ++ hsDefault b ++ "))"
  | .imp _ b => "(\\_ -> " ++ hsDefault b ++ ")"
  | .all _ a => "(\\_ -> " ++ hsDefault a ++ ")"
  | .ex _ a => "(0, " ++ hsDefault a ++ ")"

/-- Recognise a numeral, so `succ^5 zero` prints as `5` and not as five
additions.  (Same device as `RealizerDisplay.numLit?`.) -/
partial def numLit? : Term → Option Nat
  | .zero => some 0
  | .succ t => (numLit? t).map (· + 1)
  | _ => none

/-- A fragment term as a Haskell expression.  Variables become `x<n>`, which is
also how the binder cases below name them, so the fragment's own variable
numbering carries over and its shadowing behaves the same way. -/
partial def hsTerm : Term → String
  | t =>
    match numLit? t with
    | some k => toString k
    | none =>
      match t with
      | .var i => "x" ++ toString i
      | .zero => "0"
      | .succ a => "(1 + " ++ hsTerm a ++ ")"
      | .plus a b => "(" ++ hsTerm a ++ " + " ++ hsTerm b ++ ")"
      | .times a b => "(" ++ hsTerm a ++ " * " ++ hsTerm b ++ ")"
      | .pred a => "(predN " ++ hsTerm a ++ ")"
      | .exp a b => "(expN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .bump a b => "(bumpN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .good a b => "(goodN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .prec a b => "(oltN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .ord a b => "(ordOf " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .hcut a b => "(hydraStepN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .hydra a b => "(hydraSeqN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .hord a => "(ordOfHydraN " ++ hsTerm a ++ ")"
      | .hcons a b => "(hconsN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .happ a b => "(happN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .mvcount a => "(hlenN " ++ hsTerm a ++ ")"
      | .solves a b c d e =>
          "(solvesN " ++ hsTerm a ++ " " ++ hsTerm b ++ " " ++ hsTerm c ++ " "
            ++ hsTerm d ++ " " ++ hsTerm e ++ ")"
      | .xor a b => "(xorN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .pas a b => "(pasN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .look a b => "(lookN " ++ hsTerm a ++ " " ++ hsTerm b ++ ")"
      | .fib a => "(fibN " ++ hsTerm a ++ ")"

/-- Conclusions whose realizer carries no information — the collapse rule, as
in `RealizerDisplay.toSkel`.  This is what keeps the emitted program small:
most of any derivation is equational reasoning, and all of it prints as `()`. -/
def isContentless : Formula → Bool
  | .eq _ _ => true
  | .bot => true
  | _ => false

/-! ## The emitter

`hsEmit D d` prints `D`'s realizer, with `d` the number of hypotheses currently
in scope; hypothesis `i` is the Haskell variable `h<i>`, and `ax` is the most
recent, `h<d-1>`.  ∀-bound values reuse the fragment's own variable numbering
as `x<n>`.

Every constructor has a case and there is no wildcard, for the reason given in
`EmitLean.lean`: a new content-bearing rule silently emitting a contentless
realizer would produce a program that compiles, runs, and is wrong. -/
partial def hsEmit {Γ : List Formula} {φ : Formula} (D : Deriv Γ φ) (d : ℕ) :
    String :=
  if isContentless φ then "()" else
  match D with
  | .ax => "h" ++ toString (d - 1)
  | .wk D => hsEmit D (d - 1)
  | .andI D₁ D₂ => "(" ++ hsEmit D₁ d ++ ", " ++ hsEmit D₂ d ++ ")"
  | .andE₁ D => "(fst " ++ hsEmit D d ++ ")"
  | .andE₂ D => "(snd " ++ hsEmit D d ++ ")"
  | @Deriv.orI₁ _ _ ψ D => "(0, (" ++ hsEmit D d ++ ", " ++ hsDefault ψ ++ "))"
  | @Deriv.orI₂ _ φ' _ D => "(1, (" ++ hsDefault φ' ++ ", " ++ hsEmit D d ++ "))"
  | .orE D D₁ D₂ =>
      let r := "r" ++ toString d
      "(let " ++ r ++ " = " ++ hsEmit D d ++ " in if fst " ++ r ++ " == 0 then (\\h"
        ++ toString d ++ " -> " ++ hsEmit D₁ (d + 1) ++ ") (fst (snd " ++ r
        ++ ")) else (\\h" ++ toString d ++ " -> " ++ hsEmit D₂ (d + 1)
        ++ ") (snd (snd " ++ r ++ ")))"
  | .impI D => "(\\h" ++ toString d ++ " -> " ++ hsEmit D (d + 1) ++ ")"
  | .impE D₁ D₂ => "(" ++ hsEmit D₁ d ++ " " ++ hsEmit D₂ d ++ ")"
  | @Deriv.botE _ φ' _ => hsDefault φ'
  | @Deriv.allI _ x _ D _ => "(\\x" ++ toString x ++ " -> " ++ hsEmit D d ++ ")"
  | @Deriv.allE _ _ _ u D _ => "(" ++ hsEmit D d ++ " " ++ hsTerm u ++ ")"
  | @Deriv.ind _ x _ D₁ D₂ _ =>
      "(\\x" ++ toString x ++ " -> natRec (" ++ hsEmit D₁ d ++ ") ("
        ++ hsEmit D₂ d ++ ") x" ++ toString x ++ ")"
  | @Deriv.tiEps0 _ x _ _ D _ _ _ =>
      "(\\x" ++ toString x ++ " -> tiRec (\\k rec -> " ++ hsEmit D d
        ++ " k (\\y _ -> rec y)) x" ++ toString x ++ ")"
  | @Deriv.exI _ _ _ u D _ => "(" ++ hsTerm u ++ ", " ++ hsEmit D d ++ ")"
  | @Deriv.exE _ x _ _ D₁ D₂ _ _ =>
      let p := "p" ++ toString d
      "(let " ++ p ++ " = " ++ hsEmit D₁ d ++ " in (\\x" ++ toString x
        ++ " -> (\\h" ++ toString d ++ " -> " ++ hsEmit D₂ (d + 1) ++ ") (snd "
        ++ p ++ ")) (fst " ++ p ++ "))"
  | .eqDec s t =>
      "(if " ++ hsTerm s ++ " == " ++ hsTerm t ++ " then 0 else 1, ((), ()))"
  -- contentless axiom / equation schemas.  Enumerated, never a wildcard.
  | .succNeZero .. => hsDefault φ
  | .succInj .. => hsDefault φ
  | .eqRefl .. => hsDefault φ
  | .eqSymm .. => hsDefault φ
  | .eqTrans .. => hsDefault φ
  | .eqCongSucc .. => hsDefault φ
  | .eqCongPlus .. => hsDefault φ
  | .eqCongTimes .. => hsDefault φ
  | .zeroPlus .. => hsDefault φ
  | .succPlus .. => hsDefault φ
  | .zeroTimes .. => hsDefault φ
  | .succTimes .. => hsDefault φ
  | .predZero => hsDefault φ
  | .predSucc .. => hsDefault φ
  | .expZero .. => hsDefault φ
  | .expSucc .. => hsDefault φ
  | .bumpZero .. => hsDefault φ
  | .bumpNum .. => hsDefault φ
  | .goodZero .. => hsDefault φ
  | .goodSucc .. => hsDefault φ
  | .eqCongPred .. => hsDefault φ
  | .eqCongExp .. => hsDefault φ
  | .eqCongBump .. => hsDefault φ
  | .eqCongGood .. => hsDefault φ
  | .precNum .. => hsDefault φ
  | .eqCongPrec .. => hsDefault φ
  | .ordBump .. => hsDefault φ
  | .ordPredLt .. => hsDefault φ
  | .bumpNeZero .. => hsDefault φ
  | .eqCongOrd .. => hsDefault φ
  | .hydraZero .. => hsDefault φ
  | .hydraSucc .. => hsDefault φ
  | .hordCutLt .. => hsDefault φ
  | .hcutNum .. => hsDefault φ
  | .eqCongHcut .. => hsDefault φ
  | .eqCongHydra .. => hsDefault φ
  | .eqCongHord .. => hsDefault φ
  | .solvesZero .. => hsDefault φ
  | .solvesSucc .. => hsDefault φ
  | .mvcountNil => hsDefault φ
  | .mvcountApp .. => hsDefault φ
  | .eqCongHcons .. => hsDefault φ
  | .eqCongHapp .. => hsDefault φ
  | .eqCongMvcount .. => hsDefault φ
  | .pasZeroZero => hsDefault φ
  | .pasZeroSucc .. => hsDefault φ
  | .pasSuccZero .. => hsDefault φ
  | .pasSuccSucc .. => hsDefault φ
  | .xorNum .. => hsDefault φ
  | .eqCongXor .. => hsDefault φ
  | .eqCongPas .. => hsDefault φ
  | .lookNum .. => hsDefault φ
  | .eqCongLook .. => hsDefault φ
  | .eqCongSolves .. => hsDefault φ
  | .fibZero => hsDefault φ
  | .fibOne => hsDefault φ
  | .fibSucc .. => hsDefault φ
  | .eqCongFib .. => hsDefault φ

/-! ## The prelude -/

/-- The Haskell prelude the emitted programs link against.

The two recursors, then the value symbols in two clearly separated groups —
see the module header on why the pairing-dependent ones are `error` stubs
rather than re-implementations. -/
def hsPrelude : String :=
"-- GENERATED by Realizability/Meta/EmitHaskell.lean -- NOT a certified artifact.
module Realizability.Prelude where

-- The two recursors the fragment's rules extract to.

-- `ind` / `indRecC`: primitive recursion on succ.
natRec :: a -> (Integer -> a -> a) -> Integer -> a
natRec z _ 0 = z
natRec z s k = s (k - 1) (natRec z s (k - 1))

-- `tiEps0` / `tiRecC`: recursion along the notation order.
--
-- WARNING.  In Lean this is `WellFounded.fix` on `oLt_wf`, and its totality is
-- a theorem.  Haskell cannot express that, so this is an ordinary recursive
-- function and its termination is NOT guaranteed by anything here.  The guard
-- mirrors `tiRecC`, which re-decides the order because the realizer of `y < x`
-- is contentless and carries no evidence.
tiRec :: (Integer -> (Integer -> a) -> a) -> Integer -> a
tiRec f k = f k (\\j -> if oltN j k == 1
                          then tiRec f j
                          else error \"tiEps0: non-descending recursive call\")

-- ---------------------------------------------------------------------------
-- IMPLEMENTED.  Short, structural, independent of the Phase-C pairing.
-- ---------------------------------------------------------------------------

predN :: Integer -> Integer
predN n = if n <= 0 then 0 else n - 1

expN :: Integer -> Integer -> Integer
expN b e = b ^ e

fibN :: Integer -> Integer
fibN n = go n 0 1 where
  go 0 a _ = a
  go k a b = go (k - 1) b (a + b)

xorN :: Integer -> Integer -> Integer
xorN a b = (a + b) `mod` 2

pasN :: Integer -> Integer -> Integer
pasN 0 0 = 1
pasN 0 _ = 0
pasN _ 0 = 1
pasN n k = xorN (pasN (n - 1) (k - 1)) (pasN (n - 1) k)

-- ---------------------------------------------------------------------------
-- STUBBED.  Every one of these decodes the hand-rolled triangular pairing of
-- Realizability/Ordinals/Epsilon0.lean.  Port them from the Lean source named
-- on each line; a plausible re-implementation that silently diverges would be
-- worse than this error.
-- ---------------------------------------------------------------------------

bumpN :: Integer -> Integer -> Integer
bumpN = error \"port from Realizability/Signature/OrdinalAssignment.lean: bumpN\"

goodN :: Integer -> Integer -> Integer
goodN = error \"port from Realizability/Signature/OrdinalAssignment.lean: goodN\"

ordOf :: Integer -> Integer -> Integer
ordOf = error \"port from Realizability/Signature/OrdinalAssignment.lean: ordOf\"

oltN :: Integer -> Integer -> Integer
oltN = error \"port from Realizability/Ordinals/Epsilon0.lean: oltN\"

hydraStepN :: Integer -> Integer -> Integer
hydraStepN = error \"port from Realizability/Signature/Hydra.lean: hydraStepN\"

hydraSeqN :: Integer -> Integer -> Integer
hydraSeqN = error \"port from Realizability/Signature/Hydra.lean: hydraSeqN\"

ordOfHydraN :: Integer -> Integer
ordOfHydraN = error \"port from Realizability/Signature/Hydra.lean: ordOfHydraN\"

hconsN :: Integer -> Integer -> Integer
hconsN = error \"port from Realizability/Signature/Hanoi.lean: hcons\"

happN :: Integer -> Integer -> Integer
happN = error \"port from Realizability/Signature/Hanoi.lean: happN\"

hlenN :: Integer -> Integer
hlenN = error \"port from Realizability/Signature/Hanoi.lean: hlen\"

solvesN :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
solvesN = error \"port from Realizability/Signature/Hanoi.lean: solvesN\"

lookN :: Integer -> Integer -> Integer
lookN = error \"port from Realizability/Signature/Coloring.lean: lookN\"
"

/-- A complete Haskell module for one closed derivation.

`mod` is the module name and must be capitalized (Haskell requires it); `fn` is
the emitted function's name and must not be.  The type signature is read off
the conclusion by `hsTy`, and the body by `hsEmit`. -/
def hsModule (mod fn : String) {φ : Formula} (D : Deriv [] φ) : String :=
  "-- GENERATED by Realizability/Meta/EmitHaskell.lean from a `Deriv [] _`.\n" ++
  "-- This is a translation, not the certified artifact.  See the module\n" ++
  "-- header of Realizability/Meta/EmitHaskell.lean before quoting it.\n" ++
  "module Extracted." ++ mod ++ " where\n\n" ++
  "import Realizability.Prelude\n\n" ++
  fn ++ " :: " ++ hsTy φ ++ "\n" ++
  fn ++ " = " ++ hsEmit D 0 ++ "\n"

end Realizability.Emit

/-- `#haskell "Mod" "fn" d` prints a complete Haskell module for the closed
derivation `d`: module `Extracted.Mod`, function `fn`.  A generated view, not
the certified artifact. -/
macro "#haskell " m:str f:str t:term : command =>
  `(command| #eval IO.println (Realizability.Emit.hsModule $m $f $t))

/-- `#haskellPrelude` prints the prelude the emitted modules link against. -/
macro "#haskellPrelude" : command =>
  `(command| #eval IO.println Realizability.Emit.hsPrelude)
