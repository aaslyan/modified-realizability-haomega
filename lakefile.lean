import Lake
open Lake DSL

package «Realizability» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

/-
This project uses the Kleene–Kreisel continuous-functionals development
(`PureType`, `Assoc`, `Ct`, `CtPer`, `ctPer_iff_assoc`, `CtQ`).  The subset
it actually depends on — the transitive closure of
`ContinuousFunctionals.Hierarchy` and `ContinuousFunctionals.CtQ`, 12
files — is **vendored** into this repository under
`Realizability/Core/ContinuousFunctionals/`, copied verbatim from
`kleene-kreisel-lean`, and built as the in-tree library declared below.
There is no longer any dependency on a sibling `kleene-kreisel-lean`
checkout: this repository builds standalone.

Mathlib is pinned to the same version the vendored code was written
against (the continuous-functionals code reaches it through
`Sequences.lean`; the realizability engine reaches it through
`Epsilon0.lean`).
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

@[default_target]
lean_lib «Realizability» where

/-- **The HA^ω development** (the `haomega` branch's reason for existing).

A *parallel* core: Heyting arithmetic in all finite types, with an
intrinsically-typed System T term language.  It deliberately imports nothing
from `Realizability` — the first-order development stays in the tree as the
reference implementation to compare against, not as a dependency.  See
`HAOMEGA.md`. -/
@[default_target]
lean_lib «HAomega» where
  globs := #[.submodules `HAomega]

/-- The vendored Kleene–Kreisel continuous-functionals code — 12 files
under `Realizability/Core/ContinuousFunctionals/ContinuousFunctionals/`,
in the `ContinuousFunctionals` namespace, so
`import ContinuousFunctionals.Hierarchy` resolves in-tree with no external
package. -/
lean_lib «ContinuousFunctionals» where
  srcDir := "Realizability/Core/ContinuousFunctionals"
  globs := #[.submodules `ContinuousFunctionals]
