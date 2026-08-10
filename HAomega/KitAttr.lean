/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Continuity

/-!
# The `derivNorm` simp set

One line, in its own module for a mechanical reason: Lean requires a simp
attribute to be *declared* in a module earlier than any use of it, so
`Kit.lean` cannot both register the attribute and tag lemmas with it.

Everything that `deriv_norm` knows how to reduce is tagged `@[derivNorm]`,
wherever it is defined.  A layer that introduces new definitions extends the
normalizer by tagging them, without touching `Kit.lean`.
-/

register_simp_attr derivNorm
