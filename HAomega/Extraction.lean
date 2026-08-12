/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Realizability

/-!
# HA^ω, part 4: extraction

    extract : Deriv Δ φ → Tm (as ++ Γ) a

for `Δ : Ctx Γ as` and `φ : Formula Γ a`.

**The realizer is a term of the object language.**  In the first-order
development `extract` produces an element of `PureType (n+1)` — a Lean
function, opaque, printable only by walking the derivation instead, and
evaluable only through the ambient tower that made `gcdWitness` unrunnable at
every input.  Here the output is a `Tm`: it prints, it normalises, it runs.

**And there is not a single cast.**  The previous version of this module had
six, one for each rule whose conclusion is a substitution instance
(`allI`, `allE`, `exI`, `exE`, `ind`, `eqSubst`).  Indexing `Formula` by its
realizer type removed all of them: `φ.subst1 u` has the same index as `φ` by
construction, so `.app (extract D) u` already has the type the conclusion
demands.  That is also what made `MR_subst` provable, hence soundness
reachable.

## The context of the extracted term

The realizer needs a variable per hypothesis and per object variable, so it
lives in `as ++ Γ` — hypothesis realizers innermost.  With that ordering `ax`
is `var here` and `impI`, `orE` and the hypothesis half of `exE` are direct
`lam`s.  The cost is paid once, in `allI`, which moves a freshly bound object
variable past the hypothesis block: `Ren.exch`.

## Case analysis without a case-analysis primitive

`orE` and `eqDec` must branch on a number and System T has no `if`.
`recNat z (λk. λih. b) n` gives `z` at `0` and `b` at a successor, and when `b`
mentions neither `k` nor `ih` that is exactly a zero-test.  Both use it, which
is why the extracted programs show `recNat` where one expects a conditional.
-/

namespace HAomega

/-! ## Context plumbing -/

/-- Weaken a term into a context with a whole block prepended. -/
def Ren.wkList : {Γ : List Ty} → (D : List Ty) → Ren Γ (D ++ Γ)
  | _, [] => fun _ v ↦ v
  | _, _ :: D => fun σ v ↦ .there (Ren.wkList D σ v)

/-- **The exchange renaming**: move the variable bound just after the block `D`
to the front.  What `allI` needs, and the only place the context ordering costs
anything. -/
def Ren.exch {Γ : List Ty} {τ : Ty} :
    (D : List Ty) → Ren (D ++ τ :: Γ) (τ :: (D ++ Γ))
  | [] => fun _ v ↦ v
  | a :: D => fun σ v ↦
      match v with
      | .here => .there .here
      | .there w => (Ren.wk a).ext σ (Ren.exch D σ w)

/-! ## Numeric equality, as a System T term

`eqDec` is the one axiom with computational content, so extraction has to
produce an actual decision procedure. -/

/-- Truncated predecessor. -/
def Tm.predT {Γ : List Ty} : Tm Γ (.arrow .nat .nat) :=
  .lam (.recNat .zero (.lam (.lam (.var (.there .here)))) (.var .here))

/-- Truncated subtraction, `x ∸ y`. -/
def Tm.subT {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.lam (.recNat (.var (.there .here))
    (.lam (.lam (.app Tm.predT (.var .here)))) (.var .here)))

/-- `isPos x` is `0` when `x = 0` and `1` otherwise. -/
def Tm.isPos {Γ : List Ty} : Tm Γ (.arrow .nat .nat) :=
  .lam (.recNat .zero (.lam (.lam (.succ .zero))) (.var .here))

/-- Addition **as a defined term**, kept as the proof that `+` is definable
even though the language now has it as a primitive.  Its cost is `y` recursor
steps, which is why the primitive exists. -/
def Tm.addT {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat .nat)) :=
  .lam (.lam (.recNat (.var (.there .here))
    (.lam (.lam (.succ (.var .here)))) (.var .here)))

/-- `eqTest s t` is `0` when `s = t` and `1` otherwise, as `isPos ((s∸t)+(t∸s))`. -/
def Tm.eqTest {Γ : List Ty} (s t : Tm Γ .nat) : Tm Γ .nat :=
  .app Tm.isPos (.add (.app (.app Tm.subT s) t) (.app (.app Tm.subT t) s))

/-! ## The extractor -/

/-- **Extraction.**  Every rule maps to a term former.  Every constructor has a
case and there is no wildcard — the per-rule discipline of the first-order
development, carried over. -/
def extract : {Γ : List Ty} → {as : List Ty} → {Δ : Ctx Γ as} → {a : Ty} →
    {φ : Formula Γ a} → Deriv Δ φ → Tm (as ++ Γ) a
  | _, _, _, _, _, .ax => .var .here
  | _, _, _, _, _, .wk D => (extract D).wk
  | _, _, _, _, _, .andI D₁ D₂ => .pair (extract D₁) (extract D₂)
  | _, _, _, _, _, .andE₁ D => .fst (extract D)
  | _, _, _, _, _, .andE₂ D => .snd (extract D)
  | _, _, _, _, _, @Deriv.orI₁ _ _ _ b _ _ _ D =>
      .pair .zero (.pair (extract D) (Tm.dflt b))
  | _, _, _, _, _, @Deriv.orI₂ _ _ a _ _ _ _ D =>
      .pair (.succ .zero) (.pair (Tm.dflt a) (extract D))
  | _, _, _, _, _, .orE D D₁ D₂ =>
      let r := extract D
      .recNat ((extract D₁).subst1 (.fst (.snd r)))
        (.lam (.lam (((extract D₂).subst1 (.snd (.snd r))).wk.wk)))
        (.fst r)
  | _, _, _, _, _, .impI D => .lam (extract D)
  | _, _, _, _, _, .impE D₁ D₂ => .app (extract D₁) (extract D₂)
  | _, _, _, a, _, .botE _ => Tm.dflt a
  | _, as, _, _, _, .allI D => .lam ((extract D).rename (Ren.exch as))
  | _, as, _, _, _, .allE u D =>
      .app (extract D) (u.rename (Ren.wkList as))
  | _, as, _, _, _, .exI u D =>
      .pair (u.rename (Ren.wkList as)) (extract D)
  | _, as, _, _, _, @Deriv.exE _ _ a _ _ _ _ _ D₁ D₂ =>
      let p := extract D₁
      .app (.app (.lam (.lam ((extract D₂).rename (Ren.exch (a :: as)))))
        (.snd p)) (.fst p)
  | _, _, _, _, _, .ind D₁ D₂ =>
      .lam (.recNat (extract D₁).wk (extract D₂).wk (.var .here))
  | _, _, _, _, _, .tiEps0 D => .lam (.tiRec (extract D).wk (.var .here))
  | _, _, _, _, _, .tiEps0O D => .lam (.tiRecE (extract D).wk (.var .here))
  | _, _, _, _, _, .convQPosRecip _ => .star
  | _, _, _, _, _, .convQSubSelf _ => .star
  | _, _, _, _, _, .convPredZero => .star
  | _, _, _, _, _, .convPredSucc _ => .star
  | _, _, _, _, _, .convGoodZero _ => .star
  | _, _, _, _, _, .convGoodSucc _ _ => .star
  | _, _, _, _, _, .ordEBump _ _ => .star
  | _, _, _, _, _, .ordEPredLt _ _ => Tm.dflt _
  | _, _, _, _, _, .ordBump _ _ => .star
  | _, _, _, _, _, .ordPredLt _ _ => Tm.dflt _
  | _, _, _, _, _, .bumpNeZero _ _ => Tm.dflt _
  | _, _, _, _, _, .convHydraZero _ => .star
  | _, _, _, _, _, .convHydraSucc _ _ => .star
  | _, _, _, _, _, .hordCutLt _ _ => Tm.dflt _
  | _, _, _, _, _, .hordCutLtH _ _ => Tm.dflt _
  | _, _, _, _, _, .hordCutAtLtH _ _ _ => Tm.dflt _
  | _, _, _, _, _, .hordCutAtLt _ _ _ => Tm.dflt _
  | _, _, _, _, _, .eqRefl _ => .star
  | _, _, _, _, _, .eqSubst _ _ D₂ => extract D₂
  | _, _, _, _, _, .convBeta _ _ => .star
  | _, _, _, _, _, .convRecZero _ _ => .star
  | _, _, _, _, _, .convRecSucc _ _ _ => .star
  | _, _, _, _, _, .convAddZero _ => .star
  | _, _, _, _, _, .convAddSucc _ _ => .star
  | _, _, _, _, _, .convFst _ _ => .star
  | _, _, _, _, _, .convSnd _ _ => .star
  | _, _, _, _, _, .succNeZero _ => Tm.dflt _
  | _, _, _, _, _, .succInj _ _ => Tm.dflt _
  | _, as, _, _, _, .eqDec s t =>
      .pair (Tm.eqTest (s.rename (Ren.wkList as)) (t.rename (Ren.wkList as)))
        (.pair .star (Tm.dflt _))

/-- The realizer of a closed derivation: a closed System T term. -/
def extractClosed {a : Ty} {φ : Formula [] a} (D : Deriv .nil φ) : Tm [] a :=
  extract D

end HAomega
