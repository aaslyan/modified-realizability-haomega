/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Kit

/-!
# The kit, used standalone

This file exists to check one thing, and its `import` line is the check: a new
derivation can be written against `HAomega.Kit` alone.

Before the kit was collected, the equational combinators lived in
`Pascal.lean` and `PascalTheorem.lean` and the tactics in `GcdDvd.lean`, so a
file like this one had to import the entire Pascal and greatest-common-divisor
developments in order to write `a = b → b = c → a = c`. Nothing here uses
Pascal or gcd, and nothing here imports them.
-/

namespace HAomega

/-- `∀x ∀y. y = x + 0 → y = x`.

Three moves, all from the kit: introduce the binders, then chain the
hypothesis with the conversion rule for `+ 0`.  `deriv_assumption` normalizes
and locates the hypothesis without being told its depth. -/
def demoAddZero {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all .nat (.imp
      (.eq (.var .here) (.add (.var (.there .here)) .zero))
      (.eq (.var .here) (.var (.there .here)))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  exact Deriv.transE (by deriv_assumption)
    (Deriv.convAddZero (.var (.there .here)))

/-- Symmetry and congruence, also from the kit: from `x = y` conclude
`f x = f y` for any `f`, then flip it. -/
def demoCong {Γ as : List Ty} {Δ : Ctx Γ as} (f : Tm Γ (.arrow .nat .nat)) :
    Deriv Δ (.all .nat (.all .nat (.imp
      (.eq (.var (.there .here)) (.var .here))
      (.eq (.app f.wk.wk (.var .here)) (.app f.wk.wk (.var (.there .here))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  exact (Deriv.congArg _ (by deriv_assumption)).symmE

-- Axiom-free, like every derivation in the development.
#print axioms demoAddZero
#print axioms demoCong

end HAomega
