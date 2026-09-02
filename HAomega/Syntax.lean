/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Signature.OrdinalAssignment
import Realizability.Signature.Hydra
import HAomega.HydraSurgery
import HAomega.OrdCnf
import HAomega.Dyadics
import HAomega.HydraTyped

/-!
# HA^ω, part 1: the finite types and System T

The first module of the `haomega` branch.  Where the first-order development
(`Realizability/Core/Syntax.lean`) has one sort — `ℕ` — and reaches everything
else by *coding* it into a number, this one has the full hierarchy of finite
types and a typed term language over them.

Three consequences drive the whole design, and they are why this rewrite is
worth doing at all:

* **No encoding.**  A hydra is an inductive type, a coloring is a function.
  The triangular pairing, the `look` symbol, and the doubly-exponential Hanoi
  codes all exist only because the first-order fragment cannot say `ℕ → ℕ`.
* **No numeral graphs.**  `bump`, `prec`, `hcut`, `xor`, `look` enter the old
  fragment through per-numeral axiom schemas, because their recursion is
  course-of-values through an encoding and so is not a first-order equation
  schema.  In System T course-of-values recursion is *definable*, so those
  schemas become theorems.
* **No ambient levels.**  A realizer's type will be computed from its formula
  (`tyOf`, part 3), so the `PureType` tower, `liftR`/`dropR`, `lvl` and
  `derivBound` have nothing to do.  That machinery is 330 lines of
  `Transport.lean` plus a level index threaded through every clause of `MR`.

## Design decisions taken here

**Intrinsically typed, de Bruijn.**  `Tm : List Ty → Ty → Type` — a term
*is* a typing derivation, so evaluation is total by construction and there is
no separate type-checker to prove sound.  The cost is that renaming and
substitution need the standard two-stage treatment (renaming first, so that
substitution can push under binders), which is most of this file.

**Retiring the naive-substitution dodges.**  The old development carries two
devices invented to route around capture: naming a term with a fresh `∀`
(Goodstein's `namedIHDeriv`) and α-renaming an induction hypothesis
(Hanoi's `ihRenamed`), composed in `gcdTheorem`.  De Bruijn indices make
capture impossible, so both disappear — a substantial share of `gcdTheorem`'s
531 lines was that bookkeeping.

**A `unit` type.**  Realizers of equations and `⊥` carry no information, and
in part 3 `tyOf` sends them to `unit`.  The alternative — using `nat` and
ignoring the value, as `axiomC` effectively does today — works, but makes
"contentless" invisible in the types.

**Function-valued environments.**  `Env Γ` is `(τ : Ty) → Var Γ τ → τ.interp`
rather than a nested product.  Both work; this one makes the substitution
lemmas at the foot of the file short, and those lemmas are what the soundness
proof will consume.
-/

namespace HAomega

/-! ## Finite types -/

/-- The finite types over `ℕ`.

Note this is *not* the pure-type tower `PureType` of the vendored
Kleene–Kreisel development, which is `ℕ`, `ℕ → ℕ`, `(ℕ → ℕ) → ℕ`, … — a
hierarchy indexed by a single number, with no products and no general arrows.
Bridging `Ty` to that tower is what the continuity theorem will need, and it
is the open problem of this branch. -/
inductive Ty where
  | unit : Ty
  | nat : Ty
  -- Ordinal notations below ε₀, as their own base type — the typed ordinal
  -- layer (`OrdCnf.lean`).  The first-order development had to code these
  -- into ℕ; here they are structural values.
  | ord : Ty
  -- Hydras as their own base type — the typed hydra layer (`HydraTyped.lean`).
  -- The battle state is a tree, not a doubly-exponential code.
  | hyd : Ty
  -- **Rationals, two representations.**  `rat` states — general fractions are
  -- the vocabulary of an analytic theorem — and `dyad` computes, because an
  -- approximation is always *at* a precision `2⁻ⁿ`.  Both are hand-rolled
  -- (`Rationals.lean`, `Dyadics.lean`): Mathlib's `Rat` arithmetic is
  -- choice-dependent and `Tm.eval` must stay choice-free.
  | rat : Ty
  | dyad : Ty
  | arrow : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- The Lean type a finite type denotes.  This is the *set-theoretic* model,
used for evaluation and for stating the substitution lemmas; the continuous
model is a later concern. -/
@[reducible] def Ty.interp : Ty → Type
  | .unit => Unit
  | .nat => Nat
  | .ord => Eps0
  | .hyd => Realizability.Hydra
  | .rat => Q
  | .dyad => D
  | .arrow a b => a.interp → b.interp
  | .prod a b => a.interp × b.interp

/-- A canonical value at every finite type.  `tiRec` needs it: the order
premise's realizer is contentless, so the recursor cannot *know* a recursive
call is legal and must re-decide `≺` and fall back when it is not — exactly
what the first-order `tiRecC` does, and for the same reason. -/
def Ty.dfltVal : (τ : Ty) → τ.interp
  | .unit => ()
  | .nat => 0
  | .ord => .zero
  | .hyd => Realizability.Hydra.leaf
  | .rat => Q.zero
  | .dyad => D.zero
  | .arrow _ b => fun _ ↦ b.dfltVal
  | .prod a b => (a.dfltVal, b.dfltVal)

/-! ## Variables and terms -/

/-- A de Bruijn index, carrying its type: `Var Γ τ` is a position in `Γ`
holding a `τ`. -/
inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {τ : Ty} : Var (τ :: Γ) τ
  | there {Γ : List Ty} {τ σ : Ty} : Var Γ τ → Var (σ :: Γ) τ

/-- **System T, intrinsically typed.**

The whole term language: lambda-calculus with products, the numerals, and a
recursor *at every type* `τ` (the feature the first-order fragment cannot
have, and the one that makes all 21 of its function symbols definable rather
than primitive). -/
inductive Tm : List Ty → Ty → Type where
  | var {Γ : List Ty} {τ : Ty} : Var Γ τ → Tm Γ τ
  | lam {Γ : List Ty} {a b : Ty} : Tm (a :: Γ) b → Tm Γ (.arrow a b)
  | app {Γ : List Ty} {a b : Ty} : Tm Γ (.arrow a b) → Tm Γ a → Tm Γ b
  | star {Γ : List Ty} : Tm Γ .unit
  | pair {Γ : List Ty} {a b : Ty} : Tm Γ a → Tm Γ b → Tm Γ (.prod a b)
  | fst {Γ : List Ty} {a b : Ty} : Tm Γ (.prod a b) → Tm Γ a
  | snd {Γ : List Ty} {a b : Ty} : Tm Γ (.prod a b) → Tm Γ b
  | zero {Γ : List Ty} : Tm Γ .nat
  | succ {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat
  -- Addition is **primitive**, not defined.  `addT = λx y. rec x (λk ih. S ih) y`
  -- is definable (and kept in `Extraction.lean` as the proof of that), but it
  -- costs `y` recursor steps, so Fibonacci through it walls at `n ≈ 27`.  A
  -- primitive interpreted by `Nat.add` is how HA^ω is normally presented, and
  -- matches the first-order development's `zeroPlus`/`succPlus`.
  | add {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat
  | recNat {Γ : List Ty} {τ : Ty} :
      Tm Γ τ → Tm Γ (.arrow .nat (.arrow τ τ)) → Tm Γ .nat → Tm Γ τ
  -- The order on ordinal notations below `ε₀`, as a primitive (like `add`):
  -- `oltN` is course-of-values through the CNF encoding, so defining it in
  -- System T would be a project of its own.
  | prec {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat
  -- The Goodstein layer's primitives, following `prec`'s precedent: their
  -- recursions are course-of-values through the hereditary base encoding, so
  -- they enter as primitives evaluated by the proven first-order value layer
  -- (`Realizability.Signature.OrdinalAssignment`, choice-free).
  | pred {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat
  | bump {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat
  | good {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat
  | ord  {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat
  -- The Hydra layer, same precedent: tree surgery through the coding is
  -- course-of-values, so the symbols are primitive, evaluated by the proven
  -- choice-free `Realizability.Signature.Hydra` layer.
  | hcut  {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat
  | hydra {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat
  | hord  {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat
  -- The **any-head** move (position, replication, hydra), evaluated by the
  -- surgery layer's `playAtN` — what lets the general Hercules theorem
  -- quantify the head choice, not just the replication.
  | hcutAt {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat → Tm Γ .nat
  -- **The typed ordinal layer** (`OrdCnf.lean`): the zero notation, the
  -- Goodstein assignment `ord(k, n)` landing in `.ord`, and the structural
  -- order test — no coding anywhere.
  | ezero {Γ : List Ty} : Tm Γ .ord
  | orde {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .ord
  | olte {Γ : List Ty} : Tm Γ .ord → Tm Γ .ord → Tm Γ .nat
  -- **The typed hydra layer**: the dead hydra, the move on trees, the
  -- `ℕ`-valued death test (so the case split reuses the numeric `eqDec`), and
  -- the ordinal of a tree — landing in `.ord`, so state *and* measure are
  -- structural and nothing is ever encoded.
  | hleaf {Γ : List Ty} : Tm Γ .hyd
  | hcutH {Γ : List Ty} : Tm Γ .nat → Tm Γ .hyd → Tm Γ .hyd
  | hleafQ {Γ : List Ty} : Tm Γ .hyd → Tm Γ .nat
  | hordH {Γ : List Ty} : Tm Γ .hyd → Tm Γ .ord
  -- The **any-head** move on trees (position, replication, hydra), evaluated
  -- by the surgery layer's `playAt` — already a tree function, so the typed
  -- general game needs no new value-level mathematics.
  | hcutAtH {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .hyd → Tm Γ .hyd
  -- The stating layer.  `qlt` returns a numeral, so a derivation branches on
  -- it with the existing numeric `eqDec` -- no new decision rule.
  | qnat {Γ : List Ty} : Tm Γ .nat → Tm Γ .rat
  | qadd {Γ : List Ty} : Tm Γ .rat → Tm Γ .rat → Tm Γ .rat
  | qsub {Γ : List Ty} : Tm Γ .rat → Tm Γ .rat → Tm Γ .rat
  | qmul {Γ : List Ty} : Tm Γ .rat → Tm Γ .rat → Tm Γ .rat
  | qdiv {Γ : List Ty} : Tm Γ .rat → Tm Γ .rat → Tm Γ .rat
  | qlt  {Γ : List Ty} : Tm Γ .rat → Tm Γ .rat → Tm Γ .nat
  -- The computing layer.  No division: dyadics are not closed under it, and
  -- `dhalf` is what `2⁻ⁿ` is built from.  `dtoq` is the bridge.
  | dnat {Γ : List Ty} : Tm Γ .nat → Tm Γ .dyad
  | dadd {Γ : List Ty} : Tm Γ .dyad → Tm Γ .dyad → Tm Γ .dyad
  | dsub {Γ : List Ty} : Tm Γ .dyad → Tm Γ .dyad → Tm Γ .dyad
  | dmul {Γ : List Ty} : Tm Γ .dyad → Tm Γ .dyad → Tm Γ .dyad
  | dhalf {Γ : List Ty} : Tm Γ .dyad → Tm Γ .dyad
  | dlt  {Γ : List Ty} : Tm Γ .dyad → Tm Γ .dyad → Tm Γ .nat
  | dtoq {Γ : List Ty} : Tm Γ .dyad → Tm Γ .rat
  -- **Recursion along `≺`** — the program construct matching the `tiEps0`
  -- rule.  Its step type is the rule's nested `∀→` pair read off exactly: at
  -- `x`, given the recursive values at every `y` together with the (`unit`)
  -- realizer of `y ≺ x`, produce the value at `x`.
  | tiRec {Γ : List Ty} {τ : Ty} :
      Tm Γ (.arrow .nat (.arrow (.arrow .nat (.arrow .unit τ)) τ)) →
      Tm Γ .nat → Tm Γ τ
  -- Recursion along `≺` **on the typed notations** — `tiRec`'s twin with the
  -- measure at `.ord` instead of coded ℕ, matching the `tiEps0O` rule.
  | tiRecE {Γ : List Ty} {τ : Ty} :
      Tm Γ (.arrow .ord (.arrow (.arrow .ord (.arrow .unit τ)) τ)) →
      Tm Γ .ord → Tm Γ τ

/-! ## Renaming

The first of the two stages.  A renaming maps variables to variables; it is
what lets substitution push under a binder without needing itself. -/

/-- A type-preserving renaming of variables. -/
def Ren (Γ Δ : List Ty) : Type := (τ : Ty) → Var Γ τ → Var Δ τ

/-- Weakening: every variable of `Γ` is a variable of `σ :: Γ`. -/
def Ren.wk {Γ : List Ty} (σ : Ty) : Ren Γ (σ :: Γ) := fun _ v ↦ .there v

/-- Push a renaming under a binder. -/
def Ren.ext {Γ Δ : List Ty} {σ : Ty} (ρ : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .here => .here
  | _, .there v => .there (ρ _ v)

/-- Apply a renaming to a term. -/
def Tm.rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) : {τ : Ty} → Tm Γ τ → Tm Δ τ
  | _, .var v => .var (ρ _ v)
  | _, .lam t => .lam (t.rename ρ.ext)
  | _, .app f a => .app (f.rename ρ) (a.rename ρ)
  | _, .star => .star
  | _, .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | _, .fst t => .fst (t.rename ρ)
  | _, .snd t => .snd (t.rename ρ)
  | _, .zero => .zero
  | _, .succ t => .succ (t.rename ρ)
  | _, .add a b => .add (a.rename ρ) (b.rename ρ)
  | _, .recNat z s n => .recNat (z.rename ρ) (s.rename ρ) (n.rename ρ)
  | _, .prec a b => .prec (a.rename ρ) (b.rename ρ)
  | _, .pred a => .pred (a.rename ρ)
  | _, .bump a b => .bump (a.rename ρ) (b.rename ρ)
  | _, .good a b => .good (a.rename ρ) (b.rename ρ)
  | _, .ord a b => .ord (a.rename ρ) (b.rename ρ)
  | _, .hcut a b => .hcut (a.rename ρ) (b.rename ρ)
  | _, .hcutAt p a b => .hcutAt (p.rename ρ) (a.rename ρ) (b.rename ρ)
  | _, .ezero => .ezero
  | _, .orde a b => .orde (a.rename ρ) (b.rename ρ)
  | _, .olte a b => .olte (a.rename ρ) (b.rename ρ)
  | _, .tiRecE s n => .tiRecE (s.rename ρ) (n.rename ρ)
  | _, .hleaf => .hleaf
  | _, .hcutH a b => .hcutH (a.rename ρ) (b.rename ρ)
  | _, .hleafQ a => .hleafQ (a.rename ρ)
  | _, .hordH a => .hordH (a.rename ρ)
  | _, .hcutAtH p a b => .hcutAtH (p.rename ρ) (a.rename ρ) (b.rename ρ)
  | _, .qnat a => .qnat (a.rename ρ)
  | _, .dnat a => .dnat (a.rename ρ)
  | _, .dhalf a => .dhalf (a.rename ρ)
  | _, .dtoq a => .dtoq (a.rename ρ)
  | _, .qadd a b => .qadd (a.rename ρ) (b.rename ρ)
  | _, .qsub a b => .qsub (a.rename ρ) (b.rename ρ)
  | _, .qmul a b => .qmul (a.rename ρ) (b.rename ρ)
  | _, .qdiv a b => .qdiv (a.rename ρ) (b.rename ρ)
  | _, .qlt a b => .qlt (a.rename ρ) (b.rename ρ)
  | _, .dadd a b => .dadd (a.rename ρ) (b.rename ρ)
  | _, .dsub a b => .dsub (a.rename ρ) (b.rename ρ)
  | _, .dmul a b => .dmul (a.rename ρ) (b.rename ρ)
  | _, .dlt a b => .dlt (a.rename ρ) (b.rename ρ)
  | _, .hydra a b => .hydra (a.rename ρ) (b.rename ρ)
  | _, .hord a => .hord (a.rename ρ)
  | _, .tiRec s n => .tiRec (s.rename ρ) (n.rename ρ)

/-! ## Substitution -/

/-- A type-preserving substitution: variables to terms. -/
def Sub (Γ Δ : List Ty) : Type := (τ : Ty) → Var Γ τ → Tm Δ τ

/-- Push a substitution under a binder.  This is the clause that needs
renaming to exist first — the substituted terms must be weakened into the
extended context. -/
def Sub.ext {Γ Δ : List Ty} {σ : Ty} (s : Sub Γ Δ) : Sub (σ :: Γ) (σ :: Δ)
  | _, .here => .var .here
  | _, .there v => (s _ v).rename (Ren.wk σ)

/-- Apply a substitution to a term. -/
def Tm.subst {Γ Δ : List Ty} (s : Sub Γ Δ) : {τ : Ty} → Tm Γ τ → Tm Δ τ
  | _, .var v => s _ v
  | _, .lam t => .lam (t.subst s.ext)
  | _, .app f a => .app (f.subst s) (a.subst s)
  | _, .star => .star
  | _, .pair a b => .pair (a.subst s) (b.subst s)
  | _, .fst t => .fst (t.subst s)
  | _, .snd t => .snd (t.subst s)
  | _, .zero => .zero
  | _, .succ t => .succ (t.subst s)
  | _, .add a b => .add (a.subst s) (b.subst s)
  | _, .recNat z sc n => .recNat (z.subst s) (sc.subst s) (n.subst s)
  | _, .prec a b => .prec (a.subst s) (b.subst s)
  | _, .pred a => .pred (a.subst s)
  | _, .bump a b => .bump (a.subst s) (b.subst s)
  | _, .good a b => .good (a.subst s) (b.subst s)
  | _, .ord a b => .ord (a.subst s) (b.subst s)
  | _, .hcut a b => .hcut (a.subst s) (b.subst s)
  | _, .hcutAt p a b => .hcutAt (p.subst s) (a.subst s) (b.subst s)
  | _, .ezero => .ezero
  | _, .orde a b => .orde (a.subst s) (b.subst s)
  | _, .olte a b => .olte (a.subst s) (b.subst s)
  | _, .tiRecE sc n => .tiRecE (sc.subst s) (n.subst s)
  | _, .hleaf => .hleaf
  | _, .hcutH a b => .hcutH (a.subst s) (b.subst s)
  | _, .hleafQ a => .hleafQ (a.subst s)
  | _, .hordH a => .hordH (a.subst s)
  | _, .hcutAtH p a b => .hcutAtH (p.subst s) (a.subst s) (b.subst s)
  | _, .qnat a => .qnat (a.subst s)
  | _, .dnat a => .dnat (a.subst s)
  | _, .dhalf a => .dhalf (a.subst s)
  | _, .dtoq a => .dtoq (a.subst s)
  | _, .qadd a b => .qadd (a.subst s) (b.subst s)
  | _, .qsub a b => .qsub (a.subst s) (b.subst s)
  | _, .qmul a b => .qmul (a.subst s) (b.subst s)
  | _, .qdiv a b => .qdiv (a.subst s) (b.subst s)
  | _, .qlt a b => .qlt (a.subst s) (b.subst s)
  | _, .dadd a b => .dadd (a.subst s) (b.subst s)
  | _, .dsub a b => .dsub (a.subst s) (b.subst s)
  | _, .dmul a b => .dmul (a.subst s) (b.subst s)
  | _, .dlt a b => .dlt (a.subst s) (b.subst s)
  | _, .hydra a b => .hydra (a.subst s) (b.subst s)
  | _, .hord a => .hord (a.subst s)
  | _, .tiRec sc n => .tiRec (sc.subst s) (n.subst s)

/-- Weakening a term into a context with one more variable.  Named because
part 2's extensional equality at arrow types uses it constantly. -/
def Tm.wk {Γ : List Ty} {τ σ : Ty} (t : Tm Γ τ) : Tm (σ :: Γ) τ :=
  t.rename (Ren.wk σ)

/-- The identity substitution extended by one term: `here ↦ u`, `there v ↦ v`.
This is what a `β`-step and a `∀`-elimination both use. -/
def Sub.one {Γ : List Ty} {a : Ty} (u : Tm Γ a) : Sub (a :: Γ) Γ
  | _, .here => u
  | _, .there v => .var v

/-- Substitute a single term for the outermost variable. -/
def Tm.subst1 {Γ : List Ty} {a τ : Ty} (t : Tm (a :: Γ) τ) (u : Tm Γ a) :
    Tm Γ τ :=
  t.subst (Sub.one u)

/-- Ordinal-notation codes, wrapped so that `≺` — and not `ℕ`'s `<` — is the
well-founded relation Lean's termination checker uses.  A bare type synonym
does not work: it unfolds, and the default `Nat` instance wins. -/
structure OrdCode where
  code : ℕ

instance : WellFoundedRelation OrdCode :=
  ⟨InvImage Realizability.OLt OrdCode.code,
   InvImage.wf OrdCode.code Realizability.oLt_wf⟩

/-- **Recursion along `≺`**, at the value level — the semantics of `tiRec`,
and the exact analogue of the first-order `tiRecC`.

Given a step that, at `x`, may consult the values at every `y`, this produces
the value at `x` by well-founded recursion on `oLt_wf`.  The `dite` is
load-bearing: the order premise's realizer is contentless, so the step cannot
carry evidence that its recursive call is legal, and the recursor must
**re-decide** `≺` and fall back otherwise.  `OLt` is decidable and `oLt_wf` is
`Classical`-free, so nothing is smuggled in.

Declared by `termination_by`/`decreasing_by` over `OrdCode` rather than by
calling `WellFounded.fix` directly, because a direct call does not compile —
and every `#eval` in the development depends on `Tm.eval` staying
computable. -/
def tiRecVal {τ : Ty} (step : ℕ → (ℕ → Unit → τ.interp) → τ.interp)
    (x : ℕ) : τ.interp :=
  step x fun y _ ↦
    if _h : Realizability.OLt y x then tiRecVal step y else τ.dfltVal
termination_by OrdCode.mk x
decreasing_by exact _h

/-- Wrapper for the typed notations, same device as `OrdCode`: makes `OLtE`
the well-founded relation the termination checker uses. -/
structure EpsW where
  o : Eps0

instance : WellFoundedRelation EpsW :=
  ⟨InvImage Eps0.OLtE EpsW.o, InvImage.wf EpsW.o Eps0.oLtE_wf⟩

/-- Recursion along `≺` on the **typed** notations — `tiRecVal`'s twin, with
the re-decision structural (`oltE`: pattern matching, no decoding).  The
`dite` is load-bearing for the same reason as there. -/
def tiRecEVal {τ : Ty} (step : Eps0 → (Eps0 → Unit → τ.interp) → τ.interp)
    (x : Eps0) : τ.interp :=
  step x fun y _ ↦
    if _h : Eps0.OLtE y x then tiRecEVal step y else τ.dfltVal
termination_by EpsW.mk x
decreasing_by exact _h

/-! ## Evaluation -/

/-- An environment: a value for every variable in scope. -/
def Env (Γ : List Ty) : Type := (τ : Ty) → Var Γ τ → τ.interp

/-- The empty environment. -/
def Env.nil : Env [] := fun _ v ↦ nomatch v

/-- Extend an environment with a value for the outermost variable. -/
def Env.cons {Γ : List Ty} {σ : Ty} (x : σ.interp) (e : Env Γ) :
    Env (σ :: Γ)
  | _, .here => x
  | _, .there v => e _ v

/-- **Evaluation.**  Total by construction, because a term is its own typing
derivation — contrast the first-order `Term.eval`, which is total only
because every symbol was given a fueled interpretation. -/
def Tm.eval {Γ : List Ty} : {τ : Ty} → Tm Γ τ → Env Γ → τ.interp
  | _, .var v, e => e _ v
  | _, .lam t, e => fun x ↦ t.eval (Env.cons x e)
  | _, .app f a, e => (f.eval e) (a.eval e)
  | _, .star, _ => ()
  | _, .pair a b, e => (a.eval e, b.eval e)
  | _, .fst t, e => (t.eval e).1
  | _, .snd t, e => (t.eval e).2
  | _, .zero, _ => 0
  | _, .succ t, e => (t.eval e) + 1
  | _, .add a b, e => a.eval e + b.eval e
  | _, .recNat z s n, e =>
      Nat.rec (motive := fun _ ↦ _) (z.eval e) (fun k ih ↦ s.eval e k ih)
        (n.eval e)
  | _, .prec a b, e => Realizability.oltN (a.eval e) (b.eval e)
  | _, .pred a, e => Nat.pred (a.eval e)
  | _, .bump a b, e => Realizability.bumpN (a.eval e) (b.eval e)
  | _, .good a b, e => Realizability.goodN (a.eval e) (b.eval e)
  | _, .ord a b, e => Realizability.ordOf (a.eval e) (b.eval e)
  | _, .hcut a b, e => Realizability.hydraStepN (a.eval e) (b.eval e)
  | _, .hcutAt p a b, e => playAtN (p.eval e) (a.eval e) (b.eval e)
  | _, .ezero, _ => .zero
  | _, .orde a b, e => ordE (a.eval e) (b.eval e)
  | _, .olte a b, e => Eps0.oltNE (a.eval e) (b.eval e)
  | _, .hleaf, _ => Realizability.Hydra.leaf
  | _, .hcutH a b, e => Realizability.hydraStep (a.eval e) (b.eval e)
  | _, .hleafQ a, e => isLeafN (a.eval e)
  | _, .hordH a, e => ordEOfHydra (a.eval e)
  | _, .hcutAtH p a b, e => playAt (p.eval e) (a.eval e) (b.eval e)
  | _, .qnat a, e => Q.ofNat (a.eval e)
  | _, .dnat a, e => D.ofNat (a.eval e)
  | _, .dhalf a, e => D.half (a.eval e)
  | _, .dtoq a, e => D.toQ (a.eval e)
  | _, .qadd a b, e => Q.add (a.eval e) (b.eval e)
  | _, .qsub a b, e => Q.sub (a.eval e) (b.eval e)
  | _, .qmul a b, e => Q.mul (a.eval e) (b.eval e)
  | _, .qdiv a b, e => Q.div (a.eval e) (b.eval e)
  | _, .qlt a b, e => Q.ltN (a.eval e) (b.eval e)
  | _, .dadd a b, e => D.add (a.eval e) (b.eval e)
  | _, .dsub a b, e => D.sub (a.eval e) (b.eval e)
  | _, .dmul a b, e => D.mul (a.eval e) (b.eval e)
  | _, .dlt a b, e => D.ltN (a.eval e) (b.eval e)
  | _, .hydra a b, e => Realizability.hydraSeqN (a.eval e) (b.eval e)
  | _, .hord a, e => Realizability.ordOfHydraN (a.eval e)
  | _, .tiRec s n, e => tiRecVal (s.eval e) (n.eval e)
  | _, .tiRecE s n, e => tiRecEVal (s.eval e) (n.eval e)

/-! ## The substitution lemmas

These are what the soundness proof of part 4 will consume, and they are the
reason the two-stage renaming/substitution treatment is worth its length.
The first-order development needed the analogous `eval_subst`; here they must
be proved for a language with binders, which is strictly more work but pays
for itself by making capture impossible. -/

/-- Renaming commutes with evaluation. -/
theorem Tm.eval_rename {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ : List Ty} (ρ : Ren Γ Δ) (e : Env Δ),
      (t.rename ρ).eval e = t.eval (fun _ v ↦ e _ (ρ _ v)) := by
  induction t with
  | var v => intros; rfl
  | lam t ih =>
      intro Δ ρ e
      funext x
      simp only [Tm.rename, Tm.eval]
      rw [ih ρ.ext (Env.cons x e)]
      congr 1
      funext σ v
      cases v <;> rfl
  | app f a ihf iha => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ihf, iha]
  | star => intros; rfl
  | pair a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | fst t ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | snd t ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | zero => intros; rfl
  | succ t ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | add a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | recNat z sc n ihz ihs ihn =>
      intro Δ ρ e; simp only [Tm.rename, Tm.eval, ihz, ihs, ihn]
  | prec a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | pred a ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | bump a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | good a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | ord a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | hcut a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | hcutAt p a b ihp iha ihb =>
      intro Δ ρ e; simp only [Tm.rename, Tm.eval, ihp, iha, ihb]
  | ezero => intros; rfl
  | orde a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | olte a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | tiRecE s n ihs ihn => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ihs, ihn]
  | hleaf => intros; rfl
  | hcutH a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | hleafQ a ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | hordH a ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | hcutAtH p a b ihp iha ihb =>
      intro Δ ρ e; simp only [Tm.rename, Tm.eval, ihp, iha, ihb]
  | qnat a ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | dnat a ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | dhalf a ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | dtoq a ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | qadd a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | qsub a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | qmul a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | qdiv a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | qlt a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | dadd a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | dsub a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | dmul a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | dlt a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | hydra a b iha ihb => intro Δ ρ e; simp only [Tm.rename, Tm.eval, iha, ihb]
  | hord a ih => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ih]
  | tiRec sc n ihs ihn => intro Δ ρ e; simp only [Tm.rename, Tm.eval, ihs, ihn]

/-- Weakening a term and then evaluating in an extended environment is the
same as evaluating in the original.  The corollary of `eval_rename` that the
`Sub.ext` clause needs. -/
theorem Tm.eval_wk {Γ : List Ty} {σ τ : Ty} (t : Tm Γ τ) (x : σ.interp)
    (e : Env Γ) : (t.rename (Ren.wk σ)).eval (Env.cons x e) = t.eval e := by
  have h : (fun (τ' : Ty) (v : Var Γ τ') ↦ Env.cons x e τ' (Ren.wk σ τ' v)) = e := by
    funext τ' v; rfl
  rw [Tm.eval_rename, h]

/-- **Substitution commutes with evaluation.**  The workhorse. -/
theorem Tm.eval_subst {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ : List Ty} (s : Sub Γ Δ) (e : Env Δ),
      (t.subst s).eval e = t.eval (fun _ v ↦ (s _ v).eval e) := by
  induction t with
  | var v => intros; rfl
  | lam t ih =>
      intro Δ s e
      funext x
      simp only [Tm.subst, Tm.eval]
      rw [ih s.ext (Env.cons x e)]
      congr 1
      funext σ v
      cases v with
      | here => rfl
      | there v => exact Tm.eval_wk (s _ v) x e
  | app f a ihf iha => intro Δ s e; simp only [Tm.subst, Tm.eval, ihf, iha]
  | star => intros; rfl
  | pair a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | fst t ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | snd t ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | zero => intros; rfl
  | succ t ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | add a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | recNat z sc n ihz ihs ihn =>
      intro Δ s e; simp only [Tm.subst, Tm.eval, ihz, ihs, ihn]
  | prec a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | pred a ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | bump a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | good a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | ord a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | hcut a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | hcutAt p a b ihp iha ihb =>
      intro Δ s e; simp only [Tm.subst, Tm.eval, ihp, iha, ihb]
  | ezero => intros; rfl
  | orde a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | olte a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | tiRecE sc n ihs ihn => intro Δ s e; simp only [Tm.subst, Tm.eval, ihs, ihn]
  | hleaf => intros; rfl
  | hcutH a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | hleafQ a ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | hordH a ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | hcutAtH p a b ihp iha ihb =>
      intro Δ s e; simp only [Tm.subst, Tm.eval, ihp, iha, ihb]
  | qnat a ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | dnat a ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | dhalf a ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | dtoq a ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | qadd a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | qsub a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | qmul a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | qdiv a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | qlt a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | dadd a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | dsub a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | dmul a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | dlt a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | hydra a b iha ihb => intro Δ s e; simp only [Tm.subst, Tm.eval, iha, ihb]
  | hord a ih => intro Δ s e; simp only [Tm.subst, Tm.eval, ih]
  | tiRec sc n ihs ihn => intro Δ s e; simp only [Tm.subst, Tm.eval, ihs, ihn]

/-- **Single substitution commutes with evaluation.**  This is the exact shape
`∀`-elimination and `∃`-introduction will need in part 4, and the analogue of
the first-order development's `eval_subst`. -/
theorem Tm.eval_subst1 {Γ : List Ty} {a τ : Ty} (t : Tm (a :: Γ) τ)
    (u : Tm Γ a) (e : Env Γ) :
    (t.subst1 u).eval e = t.eval (Env.cons (u.eval e) e) := by
  rw [Tm.subst1, Tm.eval_subst]
  congr 1
  funext σ v
  cases v <;> rfl

/-! ## Sanity checks

The point of these is that they are `rfl`: evaluation computes in the kernel,
which the first-order development had to engineer for (fueled recursions, no
`WellFounded.fix` in the value layer) and which comes free here. -/

/-- Addition is *definable*, not primitive — the headline difference from the
21-symbol first-order signature. -/
def add {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.lam (.recNat (.var .here) (.lam (.lam (.succ (.var .here))))
    (.var (.there .here))))

example : add.eval Env.nil 2 3 = 5 := rfl
example : add.eval Env.nil 0 7 = 7 := rfl

/-- Doubling, to exercise `lam`/`app`/`subst1` together. -/
def double {Γ : List Ty} : Tm Γ (.arrow .nat .nat) :=
  .lam (.app (.app add (.var .here)) (.var .here))

example : double.eval Env.nil 21 = 42 := rfl

/-- A higher-type term: twice-iteration, `(τ→τ) → τ → τ`.  Nothing of this
shape is expressible in the first-order fragment at all. -/
def twice {Γ : List Ty} (τ : Ty) : Tm Γ (.arrow (.arrow τ τ) (.arrow τ τ)) :=
  .lam (.lam (.app (.var (.there .here)) (.app (.var (.there .here))
    (.var .here))))

/-- `2⁻ⁿ` as an object term: iterate halving from `1`. -/
def dpow2 {Γ : List Ty} : Tm Γ (.arrow .nat .dyad) :=
  .lam (.recNat (.dnat (.succ .zero)) (.lam (.lam (.dhalf (.var .here))))
    (.var .here))

/-- `2⁻ⁿ` read as rationals through the bridge. -/
def qpow2 {Γ : List Ty} : Tm Γ (.arrow .nat .rat) :=
  .lam (.dtoq (.app dpow2 (.var .here)))

/-- `2ⁿ` as an object term: iterate doubling from `1`. -/
def qpow2pos {Γ : List Ty} : Tm Γ (.arrow .nat .rat) :=
  .lam (.recNat (.qnat (.succ .zero)) (.lam (.lam (.qadd (.var .here) (.var .here))))
    (.var .here))

/-- `|z|` as an object term. -/
def qabsT {Γ : List Ty} : Tm Γ (.arrow .rat .rat) :=
  .lam (.recNat (.var .here)
    (.lam (.lam (.qsub (.qnat .zero) (.var (.there (.there .here))))))
    (.qlt (.var .here) (.qnat .zero)))

/-- `close k x y` — the test `|x − y| < 2⁻ᵏ`, as a `0`/`1` numeral. -/
def qclose {Γ : List Ty} :
    Tm Γ (.arrow .nat (.arrow .rat (.arrow .rat .nat))) :=
  .lam (.lam (.lam
    (.qlt (.app qabsT (.qsub (.var (.there .here)) (.var .here)))
      (.app qpow2 (.var (.there (.there .here)))))))

#print axioms Tm.eval
#print axioms Tm.eval_subst1

end HAomega
