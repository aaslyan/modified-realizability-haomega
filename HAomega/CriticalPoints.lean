/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.DefiniteIntegral

/-!
# Approximate critical points

Room 4 of the closed universe (`docs/CLOSED_UNIVERSE_PLAN.md` §0.1). The universe
is closed under `d/dx`, so a stationary point of `f` is a root of `f′`, found by
the root operator: `UExpr.critical e a b j m := (UExpr.deriv e).root a b j m`.

What is proved is the **constructive (approximate) Rolle statement**: if `f′`
changes sign on `[a, b]` (its end colours differ), the returned point is in
`[a, b]` and every partial sum of `f′` past the modulus is small there. It is not
claimed to be a maximum or a minimum — that needs more data (e.g. the sign of
`f″`) — and an exact critical point is not computable from `f` in general.
-/

namespace HAomega

/-- An approximate stationary point of `e` on `[a, b]`. -/
def UExpr.critical (e : UExpr) (a b : Q) (j m : Nat) : Q := (UExpr.deriv e).root a b j m

/-- **Approximate Rolle**: where `f′` changes sign, `critical` returns a point of
`[a, b]` at which `f′` is within `2⁻ᵐ + 2^{M+R+2}(b−a)/2ʲ` of `0`, with
`(M, R)` the radius data of `f′`. -/
theorem UExpr.critical_spec (e : UExpr) (h : e.Defined) (a b : Q) (j m : Nat)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((UExpr.deriv e).radiusParams.2 + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((UExpr.deriv e).radiusParams.2 + 2))
    (hab : a.val ≤ b.val)
    (hends : (UExpr.deriv e).rootColor a b j m 0 ≠ (UExpr.deriv e).rootColor a b j m (2 ^ j))
    (d : Nat) :
    a.val ≤ (e.critical a b j m).val ∧ (e.critical a b j m).val ≤ b.val ∧
    |(Jet.evalPoly ⟨(UExpr.deriv e).eval⟩ (m + ((UExpr.deriv e).radiusParams.1 + 3) + d)
        (e.critical a b j m)).val|
      < 1 / (2 : Rat) ^ m
        + (2 : Rat) ^ ((UExpr.deriv e).radiusParams.1 + (UExpr.deriv e).radiusParams.2 + 2)
          * ((b.val - a.val) / (2 : Rat) ^ j) :=
  (UExpr.deriv e).root_spec h a b j m ha hb hab hends d

/-! ## Example

`f(x) = ∫₀ˣ (eᵗ − 1 − 1/20) dt = eˣ − 1 − (21/20)x` has its minimum at
`ln(21/20) ≈ 0.0488`, inside the disk `|x| ≤ 1/8` of `f′`. -/

/-- `∫₀ˣ (eᵗ − 1 − 1/20) dt`. -/
def criticalExample : UExpr :=
  .integ (.sub (.sub .exp (.const (Q.ofNat 1))) (.const ⟨1, 19⟩))

#guard (UExpr.deriv criticalExample).radiusParams = (4, 1)
#guard (UExpr.deriv criticalExample).rootColor ⟨0, 0⟩ ⟨1, 7⟩ 40 40 0 = 1 ∧
       (UExpr.deriv criticalExample).rootColor ⟨0, 0⟩ ⟨1, 7⟩ 40 40 (2 ^ 40) = 0
#guard (let r := criticalExample.critical ⟨0, 0⟩ ⟨1, 7⟩ 40 40
        (Float.ofInt r.num / Float.ofNat r.den - Float.log 1.05).abs < 1e-10)

#print axioms UExpr.critical
#print axioms UExpr.critical_spec

end HAomega
