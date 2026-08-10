/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Kit

/-!
# The two numeric layers, in the object language

Groundwork for constructive analysis, exercised. `rat` and `dyad` are base
types now, so the object language can *carry* both representations and compute
with them; this file checks that it does, and shows the division of labour the
roadmap depends on.

## What is here

`dpow2` is the precision sequence `2⁻ⁿ`, written as an object term. It is
built by `recNat` from halving — not a primitive — which is the point: the
recursor works at every type, so `dyad` needs no special support to be
iterated over.

`dtoq` is the bridge. A statement of constructive analysis is naturally about
rationals; the program that witnesses it computes with dyadics; and the bridge
is what lets one derivation mention both.

## What is deliberately absent

**Reasoning rules.** `Deriv` has no conversion equations for the rational or
dyadic operations, so the object language can *state* facts about them (via
`Formula.eq` at either type, and branch on `qlt`/`dlt` with the existing
numeric `eqDec`) but cannot yet *prove* arithmetic identities like
`q + 0 = q`. Those rules should be designed together with the first analysis
theorem rather than guessed at in advance, since which ones are needed is
exactly what writing that theorem will reveal.
-/

namespace HAomega

/-- `2⁻ⁿ` as an object term: iterate halving from `1`. -/
def dpow2 {Γ : List Ty} : Tm Γ (.arrow .nat .dyad) :=
  .lam (.recNat (.dnat (.succ .zero)) (.lam (.lam (.dhalf (.var .here))))
    (.var .here))

/-- The same sequence read as rationals, through the bridge. -/
def qpow2 {Γ : List Ty} : Tm Γ (.arrow .nat .rat) :=
  .lam (.dtoq (.app dpow2 (.var .here)))

-- The object term computes the precision sequence.
#guard (List.range 6).map ((dpow2 (Γ := [])).eval Env.nil)
  == (List.range 6).map D.pow2neg
-- and the bridge sends it to the rationals it denotes.
#guard (List.range 5).map ((qpow2 (Γ := [])).eval Env.nil)
  == [Q.ofNat 1, Q.of 1 2, Q.of 1 4, Q.of 1 8, Q.of 1 16]

/-- A first approximation statement, as an object term: `|x·x − q| < 2⁻ⁿ`,
the shape a square-root theorem's conclusion takes.  Stating it needs `rat`;
computing a witness for it will use `dyad`. -/
def approxSq {Γ : List Ty} :
    Tm (.nat :: .rat :: .rat :: Γ) .nat :=
  .qlt (.qsub (.qmul (.var (.there .here)) (.var (.there .here)))
         (.var (.there (.there .here))))
    (.app qpow2 (.var .here))

-- It decides: `(3/2)² = 9/4` is within `2⁻¹` of `2`, and not within `2⁻³`.
#guard (approxSq (Γ := [])).eval
  (Env.cons 1 (Env.cons (Q.of 3 2) (Env.cons (Q.ofNat 2) Env.nil))) == 1
#guard (approxSq (Γ := [])).eval
  (Env.cons 3 (Env.cons (Q.of 3 2) (Env.cons (Q.ofNat 2) Env.nil))) == 0

#print axioms dpow2
#print axioms qpow2

end HAomega
