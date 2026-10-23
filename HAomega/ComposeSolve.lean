/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ShiftSolve

/-!
# Composition as an instance of the general solver

Closed-universe pillar 4, composition. If `f` solves `y' = F(y)`, then
`f ∘ G` (for `G` with `G(0) = 0`, or `G − G(0)` in general) solves
`Y' = G'·F(Y)`, i.e. `Y = f(0) + ∫(G'·F(Y))`. With `G'` a closed constant
jet, that is `genSolveD` at `F' = G'·F` — no new derivation. So the universe
is closed, proof-computed, under composing ODE-defined functions with any
jet.

`expComp G` is `exp ∘ (G − G(0))`. That it equals the metatheory's
`Jet.compZero Jet.exp G` coefficientwise needs a chain-rule theorem for
`compZero`, **not proved here**; the `#guard`s below check it at instances
(`G = sin`, `G = x + x²`) and are evidence, not proof.
-/

namespace HAomega

/-- `exp ∘ (G − G(0))`: the general solver at `A = 1`, `F = G'·Y`. -/
def expCompD (G : Tm [] JetTy) :=
  genSolveD tmConstOneJet (.mul (.const (.app tmJetDeriv G)) .var)

/-- The extracted jet of `exp ∘ (G − G(0))`, iterate `k`. -/
def expComp (G : Tm [] JetTy) (k : Nat) : Nat → Q :=
  (((extractClosed (expCompD G)).eval Env.nil) k).1

/-- The jet `x + x²`. -/
def tmXPlusXSq : Tm [] JetTy :=
  .app (.app tmJetAdd (.app tmJetShift tmConstOneJet))
    (.app tmJetShift (.app tmJetShift tmConstOneJet))

-- Evidence (not proof): agreement with `Jet.compZero` below degree 6.
#guard (List.range 6).all fun i =>
  decide ((expComp tmSinJet 6 i).val = ((Jet.compZero Jet.exp Jet.sin).coeff i).val)
#guard (List.range 6).all fun i =>
  decide ((expComp tmXPlusXSq 6 i).val =
    ((Jet.compZero Jet.exp ⟨(tmXPlusXSq.eval Env.nil)⟩).coeff i).val)

#print axioms expCompD

end HAomega
