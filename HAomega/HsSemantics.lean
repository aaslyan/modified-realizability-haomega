/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Fib

/-!
# Certified semantics for the emitted Haskell

`EmitHaskell.lean` renders a realizer as Haskell source, and every document in
this repository has had to add the same disclaimer: *uncertified translation;
the certified artifact is the `Tm`.*  This file removes most of that
disclaimer, and states precisely what is left of it.

## What can and cannot be proved

Certifying "the emitted program is correct Haskell" against **GHC** is not
possible here: it would need a formal semantics of Haskell plus a proof that
GHC implements it.  What *is* possible, and is what a verified compiler
actually proves, is correctness against a **formal semantics of the target**:

1. a syntax `HsTm` for the fragment the emitter produces — untyped, as the
   target is (all of `Ty`'s distinctions are erased);
2. a big-step evaluation relation `HsEval` for it, with closures;
3. a translation `hsOf : Tm Γ τ → HsTm`;
4. **`hsOf_correct`** — the emitted program evaluates, and its value agrees
   with the realizer's, at every type.

Agreement across a type erasure cannot be an equation, so it is a *logical
relation* `Rel τ x v` — the same device the continuity proof uses, here
relating a Lean value to a target value.  At base types it is an equation; at
arrow types it is "applying the target closure to related arguments yields
related results".

## The trusted base, stated exactly

* **The prelude.**  The emitted source calls hand-written Haskell for the
  arithmetic, ordinal and hydra primitives (`goodN`, `hydraStep`,
  `ordEOfHydra`, …).  Those cannot be verified here, so the model *defines*
  the target's meaning for them to be the corresponding Lean function
  (`prim1Sem`/`prim2Sem`/`prim3Sem`).  The theorem is therefore relative to
  the prelude implementing them correctly — exactly the runtime-correctness
  assumption a verified compiler makes.
* **The printer.**  `hsOf` produces an abstract syntax tree; turning it into a
  string, and GHC's parsing of that string back, are outside the theorem.
* **Transfinite recursion is covered, and its termination is not GHC's to
  check.**  The target has `tiRecT`/`tiRecET` and a guarded caller that
  recurses when the order test succeeds and returns a carried default when it
  does not — the source recursor's `dite`, transcribed.  The correctness case
  goes by well-founded induction on the ordinal, exactly as `soundness` and
  `eval_tracked` do.  What that means precisely: the emitted Haskell is an
  ordinary recursive function, GHC does not verify that it terminates, and the
  theorem is relative to the ε₀-descent proved on the Lean side.  That is the
  usual shape of a compiler correctness statement for a language whose type
  system is weaker than the source's.  `hsSupported` is now true on the whole
  language, and `ShowAll.lean` guards that all **13 of 13** extracted programs
  are covered.
-/

namespace HAomega

/-! ## The target syntax -/

/-- Runtime primitives of arity 1, 2 and 3 — the hand-written prelude. -/
inductive Prim1 where
  | pred | hord | hleafQ | hordH | qnat | dnat | dhalf | dtoq
  deriving DecidableEq, Repr

inductive Prim2 where
  | prec | bump | good | ord | hcut | hydra | orde | olte | hcutH
  | qadd | qsub | qmul | qdiv | qlt | dadd | dsub | dmul | dlt
  deriving DecidableEq, Repr

inductive Prim3 where
  | hcutAt | hcutAtH
  deriving DecidableEq, Repr

/-- The target language: untyped lambda calculus with pairs, numerals, a
numeric recursor, and calls into the prelude.  `oops` is the image of a
construct the emitter cannot translate; it has no evaluation rule, which is
how a Haskell `error` behaves. -/
inductive HsTm where
  | var : Nat → HsTm
  | lam : HsTm → HsTm
  | app : HsTm → HsTm → HsTm
  | unit : HsTm
  | pair : HsTm → HsTm → HsTm
  | fst : HsTm → HsTm
  | snd : HsTm → HsTm
  | lit : Nat → HsTm
  | succ : HsTm → HsTm
  | add : HsTm → HsTm → HsTm
  | natRec : HsTm → HsTm → HsTm → HsTm
  | ezero : HsTm
  -- an ordinal literal, as `lit` is a numeral literal
  | eord : Eps0 → HsTm
  | hleaf : HsTm
  | p1 : Prim1 → HsTm → HsTm
  | p2 : Prim2 → HsTm → HsTm → HsTm
  | p3 : Prim3 → HsTm → HsTm → HsTm → HsTm
  -- **Transfinite recursion.**  `tiRecT step n dflt` and its `Eps0`-indexed
  -- twin.  The third argument is the translation of `Ty.dflt`: the source
  -- recursor re-decides the order and falls back when the test fails, and the
  -- untyped target cannot reconstruct a type-indexed default, so it is
  -- carried.  `recFun` is the guarded caller the step is applied to; it is an
  -- internal form, emitted as a prelude call.
  | tiRecT : HsTm → HsTm → HsTm → HsTm
  | tiRecET : HsTm → HsTm → HsTm → HsTm
  | recFun : HsTm → HsTm → Nat → HsTm
  | recFunE : HsTm → HsTm → Eps0 → HsTm
  | oops : String → HsTm → HsTm → HsTm
  deriving Repr

/-- Target values.  Functions are **closures** (code plus environment) rather
than Lean functions, since `(HsVal → HsVal) → HsVal` is not a legal
inductive. -/
inductive HsVal where
  | vNat : Nat → HsVal
  | vOrd : Eps0 → HsVal
  | vHyd : Realizability.Hydra → HsVal
  | vUnit : HsVal
  | vPair : HsVal → HsVal → HsVal
  | vRat : Q → HsVal
  | vDyad : D → HsVal
  | vClos : HsTm → List HsVal → HsVal
  -- the guarded recursive caller, awaiting the index and then the (unit)
  -- realizer of the order premise
  | vRec : HsTm → HsTm → List HsVal → Nat → HsVal
  | vRec2 : HsTm → HsTm → List HsVal → Nat → Nat → HsVal
  | vRecE : HsTm → HsTm → List HsVal → Eps0 → HsVal
  | vRecE2 : HsTm → HsTm → List HsVal → Eps0 → Eps0 → HsVal

/-! ## The prelude's meaning

This is the trusted base, written out: the target's semantics for each
primitive *is* the Lean function the realizer evaluates by. -/

def prim1Sem : Prim1 → HsVal → Option HsVal
  | .pred,   .vNat n => some (.vNat (Nat.pred n))
  | .hord,   .vNat n => some (.vNat (Realizability.ordOfHydraN n))
  | .hleafQ, .vHyd h => some (.vNat (isLeafN h))
  | .hordH,  .vHyd h => some (.vOrd (ordEOfHydra h))
  | .qnat,   .vNat n => some (.vRat (Q.ofNat n))
  | .dnat,   .vNat n => some (.vDyad (D.ofNat n))
  | .dhalf,  .vDyad a => some (.vDyad (D.half a))
  | .dtoq,   .vDyad a => some (.vRat (D.toQ a))
  | _, _ => none

def prim2Sem : Prim2 → HsVal → HsVal → Option HsVal
  | .prec,  .vNat a, .vNat b => some (.vNat (Realizability.oltN a b))
  | .bump,  .vNat a, .vNat b => some (.vNat (Realizability.bumpN a b))
  | .good,  .vNat a, .vNat b => some (.vNat (Realizability.goodN a b))
  | .ord,   .vNat a, .vNat b => some (.vNat (Realizability.ordOf a b))
  | .hcut,  .vNat a, .vNat b => some (.vNat (Realizability.hydraStepN a b))
  | .hydra, .vNat a, .vNat b => some (.vNat (Realizability.hydraSeqN a b))
  | .orde,  .vNat a, .vNat b => some (.vOrd (ordE a b))
  | .olte,  .vOrd a, .vOrd b => some (.vNat (Eps0.oltNE a b))
  | .hcutH, .vNat a, .vHyd h => some (.vHyd (Realizability.hydraStep a h))
  | .qadd, .vRat a, .vRat b => some (.vRat (Q.add a b))
  | .qsub, .vRat a, .vRat b => some (.vRat (Q.sub a b))
  | .qmul, .vRat a, .vRat b => some (.vRat (Q.mul a b))
  | .qdiv, .vRat a, .vRat b => some (.vRat (Q.div a b))
  | .qlt,  .vRat a, .vRat b => some (.vNat (Q.ltN a b))
  | .dadd, .vDyad a, .vDyad b => some (.vDyad (D.add a b))
  | .dsub, .vDyad a, .vDyad b => some (.vDyad (D.sub a b))
  | .dmul, .vDyad a, .vDyad b => some (.vDyad (D.mul a b))
  | .dlt,  .vDyad a, .vDyad b => some (.vNat (D.ltN a b))
  | _, _, _ => none

def prim3Sem : Prim3 → HsVal → HsVal → HsVal → Option HsVal
  | .hcutAt,  .vNat p, .vNat n, .vNat c => some (.vNat (playAtN p n c))
  | .hcutAtH, .vNat p, .vNat n, .vHyd h => some (.vHyd (playAt p n h))
  | _, _, _, _ => none

/-! ## Big-step evaluation

Relational rather than fuel-indexed: recursion is unfolded by the relation, so
no fuel bookkeeping enters the correctness proof.  `oops` has no rule. -/

inductive HsEval : HsTm → List HsVal → HsVal → Prop where
  | var {i : Nat} {ρ : List HsVal} {v : HsVal} :
      ρ[i]? = some v → HsEval (.var i) ρ v
  | lam {b : HsTm} {ρ : List HsVal} : HsEval (.lam b) ρ (.vClos b ρ)
  | app {f a : HsTm} {ρ : List HsVal} {b : HsTm} {ρ' : List HsVal}
      {w v : HsVal} :
      HsEval f ρ (.vClos b ρ') → HsEval a ρ w → HsEval b (w :: ρ') v →
      HsEval (.app f a) ρ v
  | unit {ρ : List HsVal} : HsEval .unit ρ .vUnit
  | pair {a b : HsTm} {ρ : List HsVal} {x y : HsVal} :
      HsEval a ρ x → HsEval b ρ y → HsEval (.pair a b) ρ (.vPair x y)
  | fst {t : HsTm} {ρ : List HsVal} {x y : HsVal} :
      HsEval t ρ (.vPair x y) → HsEval (.fst t) ρ x
  | snd {t : HsTm} {ρ : List HsVal} {x y : HsVal} :
      HsEval t ρ (.vPair x y) → HsEval (.snd t) ρ y
  | lit {n : Nat} {ρ : List HsVal} : HsEval (.lit n) ρ (.vNat n)
  | succ {t : HsTm} {ρ : List HsVal} {n : Nat} :
      HsEval t ρ (.vNat n) → HsEval (.succ t) ρ (.vNat (n + 1))
  | add {a b : HsTm} {ρ : List HsVal} {x y : Nat} :
      HsEval a ρ (.vNat x) → HsEval b ρ (.vNat y) →
      HsEval (.add a b) ρ (.vNat (x + y))
  | recZero {z s n : HsTm} {ρ : List HsVal} {v : HsVal} :
      HsEval n ρ (.vNat 0) → HsEval z ρ v → HsEval (.natRec z s n) ρ v
  | recSucc {z s n : HsTm} {ρ : List HsVal} {k : Nat} {v : HsVal} :
      HsEval n ρ (.vNat (k + 1)) →
      HsEval (.app (.app s (.lit k)) (.natRec z s (.lit k))) ρ v →
      HsEval (.natRec z s n) ρ v
  | ezero {ρ : List HsVal} : HsEval .ezero ρ (.vOrd .zero)
  | eord {o : Eps0} {ρ : List HsVal} : HsEval (.eord o) ρ (.vOrd o)
  | hleaf {ρ : List HsVal} :
      HsEval .hleaf ρ (.vHyd Realizability.Hydra.leaf)
  | p1 {op : Prim1} {t : HsTm} {ρ : List HsVal} {x v : HsVal} :
      HsEval t ρ x → prim1Sem op x = some v → HsEval (.p1 op t) ρ v
  | p2 {op : Prim2} {a b : HsTm} {ρ : List HsVal} {x y v : HsVal} :
      HsEval a ρ x → HsEval b ρ y → prim2Sem op x y = some v →
      HsEval (.p2 op a b) ρ v
  | p3 {op : Prim3} {a b c : HsTm} {ρ : List HsVal} {x y z v : HsVal} :
      HsEval a ρ x → HsEval b ρ y → HsEval c ρ z →
      prim3Sem op x y z = some v → HsEval (.p3 op a b c) ρ v
  -- **Transfinite recursion.**  The step is applied to the index and then to
  -- the guarded caller; the caller recurses when the order test succeeds and
  -- returns the carried default when it does not — the source recursor's
  -- `dite`, transcribed.
  | recFun {s d : HsTm} {x : Nat} {ρ : List HsVal} :
      HsEval (.recFun s d x) ρ (.vRec s d ρ x)
  | recFunE {s d : HsTm} {o : Eps0} {ρ : List HsVal} :
      HsEval (.recFunE s d o) ρ (.vRecE s d ρ o)
  | appRec {f a : HsTm} {ρ : List HsVal} {s d : HsTm} {ρ' : List HsVal}
      {x y : Nat} :
      HsEval f ρ (.vRec s d ρ' x) → HsEval a ρ (.vNat y) →
      HsEval (.app f a) ρ (.vRec2 s d ρ' x y)
  | appRecE {f a : HsTm} {ρ : List HsVal} {s d : HsTm} {ρ' : List HsVal}
      {x y : Eps0} :
      HsEval f ρ (.vRecE s d ρ' x) → HsEval a ρ (.vOrd y) →
      HsEval (.app f a) ρ (.vRecE2 s d ρ' x y)
  | appRec2 {f a : HsTm} {ρ : List HsVal} {s d : HsTm} {ρ' : List HsVal}
      {x y : Nat} {w r : HsVal} :
      HsEval f ρ (.vRec2 s d ρ' x y) → HsEval a ρ w →
      HsEval (.tiRecT s (.lit y) d) ρ' r → Realizability.OLt y x →
      HsEval (.app f a) ρ r
  | appRec2dflt {f a : HsTm} {ρ : List HsVal} {s d : HsTm} {ρ' : List HsVal}
      {x y : Nat} {w r : HsVal} :
      HsEval f ρ (.vRec2 s d ρ' x y) → HsEval a ρ w →
      HsEval d ρ' r → ¬ Realizability.OLt y x →
      HsEval (.app f a) ρ r
  | appRecE2 {f a : HsTm} {ρ : List HsVal} {s d : HsTm} {ρ' : List HsVal}
      {x y : Eps0} {w r : HsVal} :
      HsEval f ρ (.vRecE2 s d ρ' x y) → HsEval a ρ w →
      HsEval (.tiRecET s (.eord y) d) ρ' r → Eps0.OLtE y x →
      HsEval (.app f a) ρ r
  | appRecE2dflt {f a : HsTm} {ρ : List HsVal} {s d : HsTm} {ρ' : List HsVal}
      {x y : Eps0} {w r : HsVal} :
      HsEval f ρ (.vRecE2 s d ρ' x y) → HsEval a ρ w →
      HsEval d ρ' r → ¬ Eps0.OLtE y x →
      HsEval (.app f a) ρ r
  | tiRec {s n d : HsTm} {ρ : List HsVal} {x : Nat} {v : HsVal} :
      HsEval n ρ (.vNat x) →
      HsEval (.app (.app s (.lit x)) (.recFun s d x)) ρ v →
      HsEval (.tiRecT s n d) ρ v
  | tiRecE {s n d : HsTm} {ρ : List HsVal} {o : Eps0} {v : HsVal} :
      HsEval n ρ (.vOrd o) →
      HsEval (.app (.app s (.eord o)) (.recFunE s d o)) ρ v →
      HsEval (.tiRecET s n d) ρ v

/-- **Applying a target value to an argument.**  A closure application, or one
of the guarded-recursion steps.  This is a definition rather than a second
inductive: `HsEval` is already fixed, so no mutual induction is needed. -/
def HsApp (v w r : HsVal) : Prop :=
  (∃ (b : HsTm) (ρ' : List HsVal), v = .vClos b ρ' ∧ HsEval b (w :: ρ') r)
  ∨ (∃ (s d : HsTm) (ρ' : List HsVal) (x y : Nat),
      v = .vRec s d ρ' x ∧ w = .vNat y ∧ r = .vRec2 s d ρ' x y)
  ∨ (∃ (s d : HsTm) (ρ' : List HsVal) (x y : Nat),
      v = .vRec2 s d ρ' x y ∧
        ((Realizability.OLt y x ∧ HsEval (.tiRecT s (.lit y) d) ρ' r)
          ∨ (¬ Realizability.OLt y x ∧ HsEval d ρ' r)))
  ∨ (∃ (s d : HsTm) (ρ' : List HsVal) (x y : Eps0),
      v = .vRecE s d ρ' x ∧ w = .vOrd y ∧ r = .vRecE2 s d ρ' x y)
  ∨ (∃ (s d : HsTm) (ρ' : List HsVal) (x y : Eps0),
      v = .vRecE2 s d ρ' x y ∧
        ((Eps0.OLtE y x ∧ HsEval (.tiRecET s (.eord y) d) ρ' r)
          ∨ (¬ Eps0.OLtE y x ∧ HsEval d ρ' r)))

theorem HsEval.appOf {F A : HsTm} {ρ : List HsVal} {v w r : HsVal}
    (hF : HsEval F ρ v) (hA : HsEval A ρ w) (hr : HsApp v w r) :
    HsEval (.app F A) ρ r := by
  rcases hr with ⟨b, ρ', rfl, hb⟩ | ⟨s, d, ρ', x, y, rfl, rfl, rfl⟩
    | ⟨s, d, ρ', x, y, rfl, hcase⟩ | ⟨s, d, ρ', x, y, rfl, rfl, rfl⟩
    | ⟨s, d, ρ', x, y, rfl, hcase⟩
  · exact HsEval.app hF hA hb
  · exact HsEval.appRec hF hA
  · rcases hcase with ⟨hlt, hr⟩ | ⟨hlt, hr⟩
    · exact HsEval.appRec2 hF hA hr hlt
    · exact HsEval.appRec2dflt hF hA hr hlt
  · exact HsEval.appRecE hF hA
  · rcases hcase with ⟨hlt, hr⟩ | ⟨hlt, hr⟩
    · exact HsEval.appRecE2 hF hA hr hlt
    · exact HsEval.appRecE2dflt hF hA hr hlt

/-- The translation of `Ty.dflt`, by recursion on the type.  The source
recursor falls back on it when its re-decided order test fails, and the untyped
target cannot rebuild a type-indexed default, so `hsOf` carries it. -/
def hsDflt : Ty → HsTm
  | .unit => .unit
  | .nat => .lit 0
  | .ord => .ezero
  | .hyd => .hleaf
  | .rat => .p1 .qnat (.lit 0)
  | .dyad => .p1 .dnat (.lit 0)
  | .arrow _ b => .lam (hsDflt b)
  | .prod a b => .pair (hsDflt a) (hsDflt b)

/-! ## The translation -/

/-- The certified fragment: everything except transfinite recursion, for which
the emitter has never produced running code. -/
def hsSupported : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → Bool
  | _, _, .var _ => true
  | _, _, .lam t => hsSupported t
  | _, _, .app f a => hsSupported f && hsSupported a
  | _, _, .star => true
  | _, _, .pair a b => hsSupported a && hsSupported b
  | _, _, .fst t => hsSupported t
  | _, _, .snd t => hsSupported t
  | _, _, .zero => true
  | _, _, .succ t => hsSupported t
  | _, _, .add a b => hsSupported a && hsSupported b
  | _, _, .recNat z s n => hsSupported z && hsSupported s && hsSupported n
  | _, _, .prec a b => hsSupported a && hsSupported b
  | _, _, .pred t => hsSupported t
  | _, _, .bump a b => hsSupported a && hsSupported b
  | _, _, .good a b => hsSupported a && hsSupported b
  | _, _, .ord a b => hsSupported a && hsSupported b
  | _, _, .hcut a b => hsSupported a && hsSupported b
  | _, _, .hcutAt p a b => hsSupported p && hsSupported a && hsSupported b
  | _, _, .hydra a b => hsSupported a && hsSupported b
  | _, _, .hord t => hsSupported t
  | _, _, .ezero => true
  | _, _, .orde a b => hsSupported a && hsSupported b
  | _, _, .olte a b => hsSupported a && hsSupported b
  | _, _, .hleaf => true
  | _, _, .hcutH a b => hsSupported a && hsSupported b
  | _, _, .hleafQ t => hsSupported t
  | _, _, .hordH t => hsSupported t
  | _, _, .hcutAtH p a b => hsSupported p && hsSupported a && hsSupported b
  | _, _, .qnat a => hsSupported a
  | _, _, .dnat a => hsSupported a
  | _, _, .dhalf a => hsSupported a
  | _, _, .dtoq a => hsSupported a
  | _, _, .qadd a b => hsSupported a && hsSupported b
  | _, _, .qsub a b => hsSupported a && hsSupported b
  | _, _, .qmul a b => hsSupported a && hsSupported b
  | _, _, .qdiv a b => hsSupported a && hsSupported b
  | _, _, .qlt a b => hsSupported a && hsSupported b
  | _, _, .dadd a b => hsSupported a && hsSupported b
  | _, _, .dsub a b => hsSupported a && hsSupported b
  | _, _, .dmul a b => hsSupported a && hsSupported b
  | _, _, .dlt a b => hsSupported a && hsSupported b
  | _, _, .tiRec s n => hsSupported s && hsSupported n
  | _, _, .tiRecE s n => hsSupported s && hsSupported n

/-- **The translation.**  Types are erased; variables become de Bruijn indices;
primitives become prelude calls.  `tiRec`/`tiRecE` become `oops`. -/
def hsOf : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → HsTm
  | _, _, .var v => .var v.lvl
  | _, _, .lam t => .lam (hsOf t)
  | _, _, .app f a => .app (hsOf f) (hsOf a)
  | _, _, .star => .unit
  | _, _, .pair a b => .pair (hsOf a) (hsOf b)
  | _, _, .fst t => .fst (hsOf t)
  | _, _, .snd t => .snd (hsOf t)
  | _, _, .zero => .lit 0
  | _, _, .succ t => .succ (hsOf t)
  | _, _, .add a b => .add (hsOf a) (hsOf b)
  | _, _, .recNat z s n => .natRec (hsOf z) (hsOf s) (hsOf n)
  | _, _, .prec a b => .p2 .prec (hsOf a) (hsOf b)
  | _, _, .pred t => .p1 .pred (hsOf t)
  | _, _, .bump a b => .p2 .bump (hsOf a) (hsOf b)
  | _, _, .good a b => .p2 .good (hsOf a) (hsOf b)
  | _, _, .ord a b => .p2 .ord (hsOf a) (hsOf b)
  | _, _, .hcut a b => .p2 .hcut (hsOf a) (hsOf b)
  | _, _, .hcutAt p a b => .p3 .hcutAt (hsOf p) (hsOf a) (hsOf b)
  | _, _, .hydra a b => .p2 .hydra (hsOf a) (hsOf b)
  | _, _, .hord t => .p1 .hord (hsOf t)
  | _, _, .ezero => .ezero
  | _, _, .orde a b => .p2 .orde (hsOf a) (hsOf b)
  | _, _, .olte a b => .p2 .olte (hsOf a) (hsOf b)
  | _, _, .hleaf => .hleaf
  | _, _, .hcutH a b => .p2 .hcutH (hsOf a) (hsOf b)
  | _, _, .hleafQ t => .p1 .hleafQ (hsOf t)
  | _, _, .hordH t => .p1 .hordH (hsOf t)
  | _, _, .hcutAtH p a b => .p3 .hcutAtH (hsOf p) (hsOf a) (hsOf b)
  | _, _, .qnat a => .p1 .qnat (hsOf a)
  | _, _, .dnat a => .p1 .dnat (hsOf a)
  | _, _, .dhalf a => .p1 .dhalf (hsOf a)
  | _, _, .dtoq a => .p1 .dtoq (hsOf a)
  | _, _, .qadd a b => .p2 .qadd (hsOf a) (hsOf b)
  | _, _, .qsub a b => .p2 .qsub (hsOf a) (hsOf b)
  | _, _, .qmul a b => .p2 .qmul (hsOf a) (hsOf b)
  | _, _, .qdiv a b => .p2 .qdiv (hsOf a) (hsOf b)
  | _, _, .qlt a b => .p2 .qlt (hsOf a) (hsOf b)
  | _, _, .dadd a b => .p2 .dadd (hsOf a) (hsOf b)
  | _, _, .dsub a b => .p2 .dsub (hsOf a) (hsOf b)
  | _, _, .dmul a b => .p2 .dmul (hsOf a) (hsOf b)
  | _, _, .dlt a b => .p2 .dlt (hsOf a) (hsOf b)
  | _, τ, .tiRec s n => .tiRecT (hsOf s) (hsOf n) (hsDflt τ)
  | _, τ, .tiRecE s n => .tiRecET (hsOf s) (hsOf n) (hsDflt τ)

/-! ## The printer

Rendering the AST as Haskell source.  This is deliberately **outside** the
correctness theorem — a string is not a semantic object, and GHC's parse of it
is not modelled — which is also why the numeral-collapsing optimisation lives
here rather than in `hsOf`: it is a presentation choice with no semantic
content. -/

/-- Recognise a numeral spine, so `S (S 0)` prints as `2`. -/
def hsNumLit? : HsTm → Option Nat
  | .lit n => some n
  | .succ t => (hsNumLit? t).map (· + 1)
  | _ => none

def Prim1.name : Prim1 → String
  | .pred => "predN" | .hord => "ordOfHydraN"
  | .hleafQ => "isLeafN" | .hordH => "ordEOfHydra"
  | .qnat => "qOfNat" | .dnat => "dOfNat" | .dhalf => "dHalf" | .dtoq => "dToQ"

def Prim2.name : Prim2 → String
  | .prec => "oltN" | .bump => "bumpN" | .good => "goodN" | .ord => "ordOfN"
  | .hcut => "hydraStepN" | .hydra => "hydraSeqN" | .orde => "ordE"
  | .olte => "oltNE" | .hcutH => "hydraStep"
  | .qadd => "qAdd" | .qsub => "qSub" | .qmul => "qMul" | .qdiv => "qDiv"
  | .qlt => "qLtN"
  | .dadd => "dAdd" | .dsub => "dSub" | .dmul => "dMul" | .dlt => "dLtN"

def Prim3.name : Prim3 → String
  | .hcutAt => "playAtN" | .hcutAtH => "playAt"

/-- Ordinal notations print structurally — no coding, matching the source. -/
def hsOrd : Eps0 → String
  | .zero => "EZero"
  | .node e c r => "(ENode " ++ hsOrd e ++ " " ++ toString c ++ " " ++ hsOrd r ++ ")"

/-- Render the target AST as Haskell source. -/
def hsPrint : HsTm → Nat → String
  | .var i, d => "x" ++ toString (d - 1 - i)
  | .lam b, d => "(\\x" ++ toString d ++ " -> " ++ hsPrint b (d + 1) ++ ")"
  | .app f a, d => "(" ++ hsPrint f d ++ " " ++ hsPrint a d ++ ")"
  | .unit, _ => "()"
  | .pair a b, d => "(" ++ hsPrint a d ++ ", " ++ hsPrint b d ++ ")"
  | .fst t, d => "(fst " ++ hsPrint t d ++ ")"
  | .snd t, d => "(snd " ++ hsPrint t d ++ ")"
  | .lit n, _ => toString n
  | .succ t, d =>
      match hsNumLit? (.succ t) with
      | some n => toString n
      | none => "(1 + " ++ hsPrint t d ++ ")"
  | .add a b, d => "(" ++ hsPrint a d ++ " + " ++ hsPrint b d ++ ")"
  | .natRec z s n, d =>
      "(natRec " ++ hsPrint z d ++ " " ++ hsPrint s d ++ " " ++ hsPrint n d ++ ")"
  | .ezero, _ => "EZero"
  | .eord o, _ => hsOrd o
  | .tiRecT s n d, dep =>
      "(tiRec " ++ hsPrint s dep ++ " " ++ hsPrint n dep ++ " "
        ++ hsPrint d dep ++ ")"
  | .tiRecET s n d, dep =>
      "(tiRecE " ++ hsPrint s dep ++ " " ++ hsPrint n dep ++ " "
        ++ hsPrint d dep ++ ")"
  | .recFun s d x, dep =>
      "(recFun " ++ hsPrint s dep ++ " " ++ hsPrint d dep ++ " "
        ++ toString x ++ ")"
  | .recFunE s d o, dep =>
      "(recFunE " ++ hsPrint s dep ++ " " ++ hsPrint d dep ++ " "
        ++ hsOrd o ++ ")"
  | .hleaf, _ => "hLeaf"
  | .p1 op t, d => "(" ++ op.name ++ " " ++ hsPrint t d ++ ")"
  | .p2 op a b, d =>
      "(" ++ op.name ++ " " ++ hsPrint a d ++ " " ++ hsPrint b d ++ ")"
  | .p3 op a b c, d =>
      "(" ++ op.name ++ " " ++ hsPrint a d ++ " " ++ hsPrint b d ++ " "
        ++ hsPrint c d ++ ")"
  | .oops nm a b, d =>
      "(" ++ nm ++ " " ++ hsPrint a d ++ " " ++ hsPrint b d ++ ")"

/-! ## Agreement across the erasure

`Rel τ x v` — the Lean value `x` of type `τ` and the target value `v` denote
the same thing.  An equation at base types; at arrow types, closure under
application.  This is the continuity proof's device, reused: type structure
carried by a relation rather than by the target's (absent) types. -/

def Rel : (τ : Ty) → τ.interp → HsVal → Prop
  | .nat, n, v => v = .vNat n
  | .ord, o, v => v = .vOrd o
  | .hyd, h, v => v = .vHyd h
  | .rat, q, v => v = .vRat q
  | .dyad, d, v => v = .vDyad d
  | .unit, _, v => v = .vUnit
  | .prod a b, p, v => ∃ x y, v = .vPair x y ∧ Rel a p.1 x ∧ Rel b p.2 y
  | .arrow a b, f, v => ∀ x w, Rel a x w → ∃ r, HsApp v w r ∧ Rel b (f x) r

/-- Related environments: every variable's value is related, at the de Bruijn
index the translation uses. -/
def RelEnv {Γ : List Ty} (e : Env Γ) (ρ : List HsVal) : Prop :=
  ∀ (τ : Ty) (v : Var Γ τ), ∃ w, ρ[v.lvl]? = some w ∧ Rel τ (e τ v) w

theorem RelEnv.cons {Γ : List Ty} {σ : Ty} {e : Env Γ} {ρ : List HsVal}
    (hρ : RelEnv e ρ) {x : σ.interp} {w : HsVal} (hx : Rel σ x w) :
    RelEnv (Env.cons x e) (w :: ρ) := by
  intro τ v
  cases v with
  | here => exact ⟨w, by simp [Var.lvl], hx⟩
  | there v =>
      obtain ⟨u, hu, hru⟩ := hρ τ v
      exact ⟨u, by simpa [Var.lvl] using hu, hru⟩

/-- The carried default really denotes `Ty.dfltVal`. -/
theorem hsDflt_rel : ∀ (τ : Ty) (ρ : List HsVal),
    ∃ v, HsEval (hsDflt τ) ρ v ∧ Rel τ (Ty.dfltVal τ) v
  | .unit, _ => ⟨.vUnit, HsEval.unit, rfl⟩
  | .nat, _ => ⟨.vNat 0, HsEval.lit, rfl⟩
  | .ord, _ => ⟨.vOrd .zero, HsEval.ezero, rfl⟩
  | .hyd, _ => ⟨.vHyd Realizability.Hydra.leaf, HsEval.hleaf, rfl⟩
  | .rat, _ => ⟨.vRat (Q.ofNat 0), HsEval.p1 HsEval.lit rfl, rfl⟩
  | .dyad, _ => ⟨.vDyad (D.ofNat 0), HsEval.p1 HsEval.lit rfl, rfl⟩
  | .prod a b, ρ => by
      obtain ⟨x, hx, hrx⟩ := hsDflt_rel a ρ
      obtain ⟨y, hy, hry⟩ := hsDflt_rel b ρ
      exact ⟨.vPair x y, HsEval.pair hx hy, ⟨x, y, rfl, hrx, hry⟩⟩
  | .arrow a b, ρ => by
      refine ⟨.vClos (hsDflt b) ρ, HsEval.lam, ?_⟩
      intro x w _
      obtain ⟨r, hr, hrr⟩ := hsDflt_rel b (w :: ρ)
      exact ⟨r, Or.inl ⟨_, _, rfl, hr⟩, hrr⟩

/-! ## The correctness theorem -/

/-- **The emitted program computes what the realizer computes.**

For every term of the certified fragment, in related environments, the
translation evaluates in the target semantics, and its value is related to the
realizer's value at the term's type.

Relative to: the prelude implementing `prim1Sem`/`prim2Sem`/`prim3Sem`, and
the printer/parser round trip. -/
theorem hsOf_correct : {Γ : List Ty} → {τ : Ty} → (t : Tm Γ τ) →
    hsSupported t = true → (e : Env Γ) → (ρ : List HsVal) → RelEnv e ρ →
    ∃ v, HsEval (hsOf t) ρ v ∧ Rel τ (t.eval e) v := by
  intro Γ τ t
  induction t with
  | var v =>
      intro _ e ρ hρ
      obtain ⟨w, hw, hrw⟩ := hρ _ v
      exact ⟨w, HsEval.var hw, hrw⟩
  | lam b ih =>
      intro hs e ρ hρ
      refine ⟨.vClos (hsOf b) ρ, HsEval.lam, ?_⟩
      intro x w hx
      obtain ⟨r, hr, hrr⟩ := ih hs (Env.cons x e) (w :: ρ) (hρ.cons hx)
      exact ⟨r, Or.inl ⟨_, _, rfl, hr⟩, hrr⟩
  | app f a ihf iha =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨vf, hvf, hrf⟩ := ihf hs.1 e ρ hρ
      obtain ⟨va, hva, hra⟩ := iha hs.2 e ρ hρ
      obtain ⟨r, hap, hrr⟩ := hrf _ _ hra
      exact ⟨r, HsEval.appOf hvf hva hap, hrr⟩
  | star => intro _ e ρ _; exact ⟨.vUnit, HsEval.unit, rfl⟩
  | pair a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      exact ⟨.vPair x y, HsEval.pair hx hy, ⟨x, y, rfl, hrx, hry⟩⟩
  | fst t ih =>
      intro hs e ρ hρ
      obtain ⟨v, hv, x, y, rfl, hrx, _⟩ := ih hs e ρ hρ
      exact ⟨x, HsEval.fst hv, hrx⟩
  | snd t ih =>
      intro hs e ρ hρ
      obtain ⟨v, hv, x, y, rfl, _, hry⟩ := ih hs e ρ hρ
      exact ⟨y, HsEval.snd hv, hry⟩
  | zero => intro _ e ρ _; exact ⟨.vNat 0, HsEval.lit, rfl⟩
  | succ t ih =>
      intro hs e ρ hρ
      obtain ⟨v, hv, hrv⟩ := ih hs e ρ hρ
      subst hrv
      exact ⟨.vNat (t.eval e + 1), HsEval.succ hv, rfl⟩
  | add a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vNat _, HsEval.add hx hy, rfl⟩
  | recNat z s n ihz ihs ihn =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨vn, hvn, hrn⟩ := ihn hs.2 e ρ hρ
      subst hrn
      -- the recursion, at every fixed depth
      have key : ∀ k : Nat, ∃ v,
          (∀ N, HsEval N ρ (.vNat k) →
            HsEval (.natRec (hsOf z) (hsOf s) N) ρ v) ∧
          Rel _ (Nat.rec (motive := fun _ ↦ _) (z.eval e)
            (fun j ih ↦ s.eval e j ih) k) v := by
        intro k
        induction k with
        | zero =>
            obtain ⟨v0, hv0, hr0⟩ := ihz hs.1.1 e ρ hρ
            exact ⟨v0, fun N hN ↦ HsEval.recZero hN hv0, hr0⟩
        | succ k ihk =>
            obtain ⟨vk, hvk, hrk⟩ := ihk
            obtain ⟨vs, hvs, hrs⟩ := ihs hs.1.2 e ρ hρ
            obtain ⟨r1, hap1, hr1⟩ := hrs k (.vNat k) rfl
            obtain ⟨r2, hap2, hr2⟩ := hr1 _ vk hrk
            refine ⟨r2, fun N hN ↦ HsEval.recSucc hN ?_, hr2⟩
            exact HsEval.appOf
              (HsEval.appOf hvs HsEval.lit hap1)
              (hvk _ HsEval.lit) hap2
      obtain ⟨v, hv, hrv⟩ := key (n.eval e)
      exact ⟨v, hv _ hvn, hrv⟩
  | prec a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vNat _, HsEval.p2 hx hy rfl, rfl⟩
  | pred t ih =>
      intro hs e ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih hs e ρ hρ
      subst hrx
      exact ⟨.vNat _, HsEval.p1 hx rfl, rfl⟩
  | bump a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vNat _, HsEval.p2 hx hy rfl, rfl⟩
  | good a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vNat _, HsEval.p2 hx hy rfl, rfl⟩
  | ord a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vNat _, HsEval.p2 hx hy rfl, rfl⟩
  | hcut a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vNat _, HsEval.p2 hx hy rfl, rfl⟩
  | hcutAt p a b ihp iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨u, hu, hru⟩ := ihp hs.1.1 e ρ hρ
      obtain ⟨x, hx, hrx⟩ := iha hs.1.2 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hru; subst hrx; subst hry
      exact ⟨.vNat _, HsEval.p3 hu hx hy rfl, rfl⟩
  | hydra a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vNat _, HsEval.p2 hx hy rfl, rfl⟩
  | hord t ih =>
      intro hs e ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih hs e ρ hρ
      subst hrx
      exact ⟨.vNat _, HsEval.p1 hx rfl, rfl⟩
  | ezero => intro _ e ρ _; exact ⟨.vOrd .zero, HsEval.ezero, rfl⟩
  | orde a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vOrd _, HsEval.p2 hx hy rfl, rfl⟩
  | olte a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vNat _, HsEval.p2 hx hy rfl, rfl⟩
  | hleaf =>
      intro _ e ρ _; exact ⟨.vHyd Realizability.Hydra.leaf, HsEval.hleaf, rfl⟩
  | hcutH a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨.vHyd _, HsEval.p2 hx hy rfl, rfl⟩
  | hleafQ t ih =>
      intro hs e ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih hs e ρ hρ
      subst hrx
      exact ⟨.vNat _, HsEval.p1 hx rfl, rfl⟩
  | hordH t ih =>
      intro hs e ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih hs e ρ hρ
      subst hrx
      exact ⟨.vOrd _, HsEval.p1 hx rfl, rfl⟩
  | hcutAtH p a b ihp iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨u, hu, hru⟩ := ihp hs.1.1 e ρ hρ
      obtain ⟨x, hx, hrx⟩ := iha hs.1.2 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hru; subst hrx; subst hry
      exact ⟨.vHyd _, HsEval.p3 hu hx hy rfl, rfl⟩
  | qnat a ih =>
      intro hs e ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih hs e ρ hρ
      subst hrx
      exact ⟨_, HsEval.p1 hx rfl, rfl⟩
  | dnat a ih =>
      intro hs e ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih hs e ρ hρ
      subst hrx
      exact ⟨_, HsEval.p1 hx rfl, rfl⟩
  | dhalf a ih =>
      intro hs e ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih hs e ρ hρ
      subst hrx
      exact ⟨_, HsEval.p1 hx rfl, rfl⟩
  | dtoq a ih =>
      intro hs e ρ hρ
      obtain ⟨x, hx, hrx⟩ := ih hs e ρ hρ
      subst hrx
      exact ⟨_, HsEval.p1 hx rfl, rfl⟩
  | qadd a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨_, HsEval.p2 hx hy rfl, rfl⟩
  | qsub a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨_, HsEval.p2 hx hy rfl, rfl⟩
  | qmul a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨_, HsEval.p2 hx hy rfl, rfl⟩
  | qdiv a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨_, HsEval.p2 hx hy rfl, rfl⟩
  | qlt a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨_, HsEval.p2 hx hy rfl, rfl⟩
  | dadd a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨_, HsEval.p2 hx hy rfl, rfl⟩
  | dsub a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨_, HsEval.p2 hx hy rfl, rfl⟩
  | dmul a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨_, HsEval.p2 hx hy rfl, rfl⟩
  | dlt a b iha ihb =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨x, hx, hrx⟩ := iha hs.1 e ρ hρ
      obtain ⟨y, hy, hry⟩ := ihb hs.2 e ρ hρ
      subst hrx; subst hry
      exact ⟨_, HsEval.p2 hx hy rfl, rfl⟩
  | @tiRec _ τ' s n ihs ihn =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨vs, hvs, hrs⟩ := ihs hs.1 e ρ hρ
      obtain ⟨vn, hvn, hrn⟩ := ihn hs.2 e ρ hρ
      have hvn' : HsEval (hsOf n) ρ (.vNat (n.eval e)) := hrn ▸ hvn
      -- the recursion at every ordinal, for any index term denoting it
      have key : ∀ x : Nat, ∀ N : HsTm, HsEval N ρ (.vNat x) →
          ∃ v, HsEval (.tiRecT (hsOf s) N (hsDflt τ')) ρ v
            ∧ Rel τ' (tiRecVal (s.eval e) x) v := by
        intro x
        induction x using Realizability.oLt_wf.induction with
        | _ x ihx =>
            intro N hN
            obtain ⟨r1, hap1, hr1⟩ := hrs x (.vNat x) rfl
            have hguard : Rel (.arrow .nat (.arrow .unit τ'))
                (fun y (_ : Unit) ↦
                  if _h : Realizability.OLt y x then tiRecVal (s.eval e) y
                  else Ty.dfltVal τ')
                (.vRec (hsOf s) (hsDflt τ') ρ x) := by
              intro y w hw
              have hw' : w = .vNat y := hw
              subst hw'
              refine ⟨.vRec2 (hsOf s) (hsDflt τ') ρ x y,
                Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl⟩), ?_⟩
              intro u wu _
              by_cases hlt : Realizability.OLt y x
              · obtain ⟨v', hv', hrv'⟩ := ihx y hlt (.lit y) HsEval.lit
                exact ⟨v', Or.inr (Or.inr (Or.inl
                  ⟨_, _, _, _, _, rfl, Or.inl ⟨hlt, hv'⟩⟩)), by
                    simpa only [dif_pos hlt] using hrv'⟩
              · obtain ⟨v', hv', hrv'⟩ := hsDflt_rel τ' ρ
                exact ⟨v', Or.inr (Or.inr (Or.inl
                  ⟨_, _, _, _, _, rfl, Or.inr ⟨hlt, hv'⟩⟩)), by
                    simpa only [dif_neg hlt] using hrv'⟩
            obtain ⟨r2, hap2, hr2⟩ := hr1 _ _ hguard
            refine ⟨r2, HsEval.tiRec hN
              (HsEval.appOf (HsEval.appOf hvs HsEval.lit hap1)
                HsEval.recFun hap2), ?_⟩
            rw [tiRecVal]
            exact hr2
      exact key (n.eval e) (hsOf n) hvn'
  | @tiRecE _ τ' s n ihs ihn =>
      intro hs e ρ hρ
      simp only [hsSupported, Bool.and_eq_true] at hs
      obtain ⟨vs, hvs, hrs⟩ := ihs hs.1 e ρ hρ
      obtain ⟨vn, hvn, hrn⟩ := ihn hs.2 e ρ hρ
      have hvn' : HsEval (hsOf n) ρ (.vOrd (n.eval e)) := hrn ▸ hvn
      have key : ∀ x : Eps0, ∀ N : HsTm, HsEval N ρ (.vOrd x) →
          ∃ v, HsEval (.tiRecET (hsOf s) N (hsDflt τ')) ρ v
            ∧ Rel τ' (tiRecEVal (s.eval e) x) v := by
        intro x
        induction x using Eps0.oLtE_wf.induction with
        | _ x ihx =>
            intro N hN
            obtain ⟨r1, hap1, hr1⟩ := hrs x (.vOrd x) rfl
            have hguard : Rel (.arrow .ord (.arrow .unit τ'))
                (fun y (_ : Unit) ↦
                  if _h : Eps0.OLtE y x then tiRecEVal (s.eval e) y
                  else Ty.dfltVal τ')
                (.vRecE (hsOf s) (hsDflt τ') ρ x) := by
              intro y w hw
              have hw' : w = .vOrd y := hw
              subst hw'
              refine ⟨.vRecE2 (hsOf s) (hsDflt τ') ρ x y,
                Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl⟩))), ?_⟩
              intro u wu _
              by_cases hlt : Eps0.OLtE y x
              · obtain ⟨v', hv', hrv'⟩ := ihx y hlt (.eord y) HsEval.eord
                exact ⟨v', Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨_, _, _, _, _, rfl, Or.inl ⟨hlt, hv'⟩⟩))), by
                    simpa only [dif_pos hlt] using hrv'⟩
              · obtain ⟨v', hv', hrv'⟩ := hsDflt_rel τ' ρ
                exact ⟨v', Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨_, _, _, _, _, rfl, Or.inr ⟨hlt, hv'⟩⟩))), by
                    simpa only [dif_neg hlt] using hrv'⟩
            obtain ⟨r2, hap2, hr2⟩ := hr1 _ _ hguard
            refine ⟨r2, HsEval.tiRecE hN
              (HsEval.appOf (HsEval.appOf hvs HsEval.eord hap1)
                HsEval.recFunE hap2), ?_⟩
            rw [tiRecEVal]
            exact hr2
      exact key (n.eval e) (hsOf n) hvn'

/-- **The headline, at a closed program of numeric type**: the emitted program
evaluates to exactly the number the realizer computes. -/
theorem hsOf_closed_nat (t : Tm [] .nat) (hs : hsSupported t = true) :
    HsEval (hsOf t) [] (.vNat (t.eval Env.nil)) := by
  obtain ⟨v, hv, hrv⟩ := hsOf_correct t hs Env.nil [] (fun _ v ↦ nomatch v)
  exact hrv ▸ hv

/-- And for a closed first-order function: at every input, the emitted program
applied to that numeral evaluates to the realizer's output. -/
theorem hsOf_closed_fun (t : Tm [] (.arrow .nat .nat)) (hs : hsSupported t = true)
    (n : Nat) :
    ∃ v, HsEval (.app (hsOf t) (.lit n)) [] v ∧ v = .vNat (t.eval Env.nil n) := by
  obtain ⟨f, hf, hrf⟩ := hsOf_correct t hs Env.nil [] (fun _ v ↦ nomatch v)
  obtain ⟨r, hap, hrr⟩ := hrf n (.vNat n) rfl
  exact ⟨r, HsEval.appOf hf HsEval.lit hap, hrr⟩

/-- **A concrete instance**: the emitted Haskell for Fibonacci provably
computes Fibonacci.  Applied to any numeral, the emitted program evaluates to
a pair whose informative component is exactly `fibExtracted n`. -/
theorem fib_emitted_correct (n : Nat) :
    ∃ w, HsEval (.app (hsOf fibRealizer) (.lit n)) []
      (.vPair (.vNat (fibExtracted n)) w) := by
  obtain ⟨vf, hvf, hrf⟩ :=
    hsOf_correct fibRealizer (by decide) Env.nil [] (fun _ v ↦ nomatch v)
  obtain ⟨r, hap, hrr⟩ := hrf n (.vNat n) rfl
  obtain ⟨x, y, rfl, hx, _⟩ := hrr
  exact ⟨y, hx ▸ HsEval.appOf hvf HsEval.lit hap⟩

-- The certified fragment covers the case studies that do not use `TI(ε₀)`.
#guard hsSupported fibRealizer == true

#print axioms hsOf_correct
#print axioms hsOf_closed_nat

end HAomega
