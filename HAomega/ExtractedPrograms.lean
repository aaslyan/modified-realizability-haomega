/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PascalTheorem
import HAomega.Fib
import HAomega.HigherType
import HAomega.EmitHaskell

/-!
# The extracted programs, printed

One place to *see* every extracted realizer.  Each is a closed System T term —
`Tm.pretty'` elides the contentless (`unit`-typed) parts, so what prints is
the computational content and nothing else.

The Fibonacci realizers are witness-style (the term the proof was handed).
**Pascal's is not**: its case structure — the nested `rec[…]` zero-tests — is
the extraction image of `eqDec`, `orE` and two `ind`s.  Nobody wrote that
program; the proof of `pasTotal` did.
-/

namespace HAomega

/-- Pascal's extracted decider, as a term. -/
def pasRealizer : Tm [] (.arrow .nat (.arrow .nat
    (.prod .nat (.prod .unit .unit)))) :=
  extractClosed (pasTotal (Γ := []) (Δ := Ctx.nil))

-- Fibonacci (witness-style; 109 chars collapsed):
#eval IO.println ("fib      : " ++ fibRealizer.pretty' 0)
-- Fibonacci at type 2 (witness-style):
#eval IO.println ("fib-hi   : " ++ hiRealizer.pretty' 0)
-- Pascal's decider (proof-computed; 792 chars collapsed):
#eval IO.println ("pascal   : " ++ pasRealizer.pretty' 0)

-- The three realizers' types.
#eval IO.println ("fib      : " ++ (Ty.arrow .nat (.prod .nat .unit)).str)
#eval IO.println ("fib-hi   : " ++ (Ty.arrow (.arrow .nat .nat) (.prod .nat .unit)).str)
#eval IO.println ("pascal   : " ++
  (Ty.arrow .nat (.arrow .nat (.prod .nat (.prod .unit .unit)))).str)

#print axioms pasRealizer

/-! ## Haskell views

These are host-language renderings of the closed System T terms above.  They
are useful for inspection and execution, but they are not certified compiler
correctness theorems. -/

#eval IO.println (EmitHaskell.moduleFor "FibExtracted" "fibExtracted" fibRealizer)
#eval IO.println (EmitHaskell.moduleFor "PascalExtracted" "pascalExtracted" pasRealizer)

end HAomega
