/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.PolyODESystemN

/-!
# Derivation trees: `#dtree`

Display tooling, not part of the certified pipeline. `#dtree d` prints the
natural-deduction tree of a closed `Deriv` term `d` the way a logician draws it,
one rule per line:

    rule   ⊢ conclusion

with each rule's premises indented below it. The printer `whnf`-unfolds every
helper derivation (`Deriv.symmE`, `genSolveNStepD`, …) down to the primitive
`Deriv` constructors, so the tree contains only the 60 rules of
`Realizability.lean`. A rule whose conclusion has a contentless realizer type
(an equation, `⊥`, or a `∀`/`→`/`∧` built from them) is marked `·`: extraction
erases it. The unmarked nodes are exactly the ones the extracted program is made of.

* `#dtree d` prints the whole tree; `#dtree d depth k` stops at depth `k`.
* `#dtreeStats d` prints the node count and the number of uses of each rule.

Notation: bound variables are de Bruijn indices `#k` (`#0` the innermost binder);
`P` is `genStepN`, `W₀` is `initN`, `sel` is `selectStep`, `1̂`/`0̂` the constant
jets; `…` marks a subterm cut off by the printing depth.

Only closed instances unfold fully: a derivation parametric in a system (like
`genSolveND sys`) recurses on `sys`, so it is printed at a concrete system.
Meta code only (`partial def`s and commands): no theorems, no axiom-budget impact.
-/

namespace HAomega.DerivTree

open Lean Meta Elab Command

/-- Closed terms printed by name instead of being unfolded. -/
def abbrevs : List (Name × String) :=
  [(``genStepN, "P"), (``initN, "W₀"), (``tmJetAdd, "add"), (``tmJetInteg, "∫"),
   (``tmJetSub, "sub"), (``tmJetMul, "mul"), (``tmConstOneJet, "1̂"), (``tmZeroJet, "0̂"),
   (``selectStep, "sel"), (``selectInit, "selInit")]

/-- The index of a `Var` as a number. -/
partial def varIdx (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOf ``HAomega.Var.there then return (← varIdx e.appArg!) + 1
  return 0

/-- Pretty-print a `Tm`. -/
partial def ppT (e : Expr) (fuel : Nat) : MetaM String := do
  if fuel = 0 then return "…"
  let e ← whnfR e
  if let .const n _ := e.getAppFn then
    if let some (_, s) := abbrevs.find? (·.1 == n) then return s
  let e ← whnf e
  let args := e.getAppArgs
  let a (i : Nat) := args[args.size - i]!
  let p := fun x => ppT x (fuel - 1)
  match e.getAppFn with
  | .const n _ =>
    match n.componentsRev.head!.toString with
    | "var" => return s!"#{← varIdx (a 1)}"
    | "zero" => return "0"
    | "succ" => return s!"S({← p (a 1)})"
    | "add" => return s!"({← p (a 2)} + {← p (a 1)})"
    | "app" => return s!"{← p (a 2)}({← p (a 1)})"
    | "lam" => return s!"λ.{← p (a 1)}"
    | "recNat" => return s!"rec[{← p (a 3)} | {← p (a 2)} | {← p (a 1)}]"
    | "qnat" => return s!"q({← p (a 1)})"
    | "qadd" => return s!"({← p (a 2)} +q {← p (a 1)})"
    | "qsub" => return s!"({← p (a 2)} −q {← p (a 1)})"
    | "qmul" => return s!"({← p (a 2)} ·q {← p (a 1)})"
    | "qdiv" => return s!"({← p (a 2)} /q {← p (a 1)})"
    | "pair" => return s!"⟨{← p (a 2)}, {← p (a 1)}⟩"
    | "fst" => return s!"fst {← p (a 1)}"
    | "snd" => return s!"snd {← p (a 1)}"
    | "star" => return "∗"
    | "pred" => return s!"pred({← p (a 1)})"
    | s => return s
  | _ => return "?"

/-- Pretty-print a `Formula`. -/
partial def ppF (e : Expr) (fuel : Nat) : MetaM String := do
  if fuel = 0 then return "…"
  let e ← whnf e
  let args := e.getAppArgs
  let a (i : Nat) := args[args.size - i]!
  let p := fun x => ppF x (fuel - 1)
  match e.getAppFn with
  | .const n _ =>
    match n.componentsRev.head!.toString with
    | "bot" => return "⊥"
    | "eq" => return s!"{← ppT (a 2) 12} = {← ppT (a 1) 12}"
    | "and" => return s!"({← p (a 2)} ∧ {← p (a 1)})"
    | "or" => return s!"({← p (a 2)} ∨ {← p (a 1)})"
    | "imp" =>
      let r ← p (a 1)
      if r == "⊥" then return s!"¬({← p (a 2)})" else return s!"({← p (a 2)} → {r})"
    | "all" => return s!"∀{← p (a 1)}"
    | "ex" => return s!"∃{← p (a 1)}"
    | s => return s
  | _ => return "?"

/-- Whether a realizer type carries no information (`unit`, and `→`/`×` into it):
the extracted program erases a node whose conclusion has such a type. -/
partial def trivialTy (e : Expr) : MetaM Bool := do
  let e ← whnf e
  match e.getAppFn with
  | .const n _ =>
    if n == ``HAomega.Ty.unit then return true
    if n == ``HAomega.Ty.arrow then return ← trivialTy e.appArg!
    if n == ``HAomega.Ty.prod then
      return (← trivialTy e.appFn!.appArg!) && (← trivialTy e.appArg!)
    return false
  | _ => return false

/-- One node of the tree: rule name, conclusion, whether it is erased, premises. -/
partial def walk (e : Expr) (depth : Nat) (maxDepth : Option Nat)
    (out : IO.Ref (Array String)) (stats : IO.Ref (Std.HashMap String Nat)) : MetaM Unit := do
  let e ← whnf e
  let ty ← whnf (← inferType e)
  let fn := e.getAppFn
  let name := match fn with
    | .const n _ => (n.replacePrefix `HAomega.Deriv .anonymous).toString
    | _ => "?"
  stats.modify fun m => m.insert name (m.getD name 0 + 1)
  if maxDepth.all (depth ≤ ·) then
    let tyArgs := ty.getAppArgs
    let mark := if ← trivialTy tyArgs[tyArgs.size - 2]! then "· " else ""
    let line := String.ofList (List.replicate (2 * depth) ' ') ++
      s!"{mark}{name}   ⊢ {← ppF ty.appArg! 40}"
    out.modify (·.push line)
  if let .const n _ := fn then
    if (← getEnv).isConstructor n then
      for x in e.getAppArgs do
        let t ← whnf (← inferType x)
        if t.getAppFn.isConstOf ``HAomega.Deriv then walk x (depth + 1) maxDepth out stats

/-- Walk the derivation named `id`, returning the printed lines and the rule counts. -/
def run (id : Name) (maxDepth : Option Nat) :
    MetaM (Array String × Std.HashMap String Nat) := do
  let out ← IO.mkRef #[]
  let stats ← IO.mkRef {}
  let c ← realizeGlobalConstNoOverload (mkIdent id)
  -- unfolding a large derivation exceeds the default heartbeat budget
  withTheReader Core.Context ({ · with maxHeartbeats := 0 }) <|
    walk (mkConst c) 0 maxDepth out stats
  return (← out.get, ← stats.get)

/-- `#dtree d` / `#dtree d depth k`: print the derivation tree of `d`. -/
elab "#dtree " id:ident : command => liftTermElabM do
  let (lines, _) ← run id.getId none
  logInfo (String.intercalate "\n" lines.toList)

@[inherit_doc «command#dtree_»]
elab "#dtree " id:ident " depth " k:num : command => liftTermElabM do
  let (lines, _) ← run id.getId (some k.getNat)
  logInfo (String.intercalate "\n" lines.toList)

/-- `#dtreeStats d`: node count and per-rule counts, most used first. -/
elab "#dtreeStats " id:ident : command => liftTermElabM do
  let (_, stats) ← run id.getId (some 0)
  let rows := stats.toArray.qsort fun x y => x.2 > y.2 || (x.2 == y.2 && x.1 < y.1)
  let total := rows.foldl (· + ·.2) 0
  logInfo (s!"{total} rule applications\n" ++
    String.intercalate "\n" (rows.toList.map fun (n, c) => s!"{n} {c}"))

end HAomega.DerivTree

namespace HAomega

/-! ## The proof-computed solver, printed: `genSolveND` at `exp` (`y = 1 + ∫y`) -/

/-- The one-variable system of `exp`. -/
def dtreeExpSys : List (Tm [] JetTy × JExprN) := [(tmConstOneJet, .var 0)]

theorem dtreeExpSys_wf : ∀ p ∈ dtreeExpSys, p.2.WF dtreeExpSys.length := by
  intro p hp
  simp only [dtreeExpSys, List.mem_singleton] at hp
  subst hp
  show (0 : Nat) < 1
  omega

/-- `genSolveND` at the `exp` system: the derivation `#dtree` prints in full. -/
def dtreeExpSolve := genSolveND dtreeExpSys dtreeExpSys_wf

/-! ## Small trees, pinned -/

/-- `∀x. 0 + x = x`, by induction (`+` recurses on its second argument, so this
is not a conversion). Every node is an equation: extraction erases all of it. -/
def dtreeZeroAdd :
    Deriv (Ctx.nil (Γ := [])) (.all .nat (.eq (.add .zero (.var .here)) (.var .here))) :=
  Deriv.ind (Deriv.convAddZero .zero)
    (Deriv.allI (Deriv.impI
      (Deriv.transE (Deriv.convAddSucc .zero (.var .here))
        (Deriv.eqSubst (Formula.eq (.succ (Tm.add .zero (.var .here)).wk) (.succ (.var .here)))
          Deriv.ax (Deriv.eqRefl _)))))

/-- `∀x ∃y. y = S x`: the `exI` node carries the witness, so it is the one node kept. -/
def dtreeSuccEx :
    Deriv (Ctx.nil (Γ := [])) (.all .nat (.ex .nat (.eq (.var .here) (.succ (.var (.there .here)))))) :=
  Deriv.allI (Deriv.exI (.succ (.var .here)) (Deriv.eqRefl _))

/--
info: · ind   ⊢ ∀(0 + #0) = #0
  · convAddZero   ⊢ (0 + 0) = 0
  · allI   ⊢ ∀((0 + #0) = #0 → (0 + S(#0)) = S(#0))
    · impI   ⊢ ((0 + #0) = #0 → (0 + S(#0)) = S(#0))
      · eqSubst   ⊢ (0 + S(#0)) = S(#0)
        · eqSubst   ⊢ S((0 + #0)) = S(#0)
          · ax   ⊢ (0 + #0) = #0
          · eqRefl   ⊢ S((0 + #0)) = S((0 + #0))
        · convAddSucc   ⊢ (0 + S(#0)) = S((0 + #0))
-/
#guard_msgs in #dtree dtreeZeroAdd

/--
info: allI   ⊢ ∀∃#0 = S(#1)
  exI   ⊢ ∃#0 = S(#1)
    · eqRefl   ⊢ S(#0) = S(#0)
-/
#guard_msgs in #dtree dtreeSuccEx

/-! The full proof-computed solver at `exp`: 500 primitive rules. The induction
skeleton (`ind`, `exI`/`exE`, the quantifier and implication rules) is a few dozen;
the rest is equational computation — every β-step and recursor step of the Picard
operator is an explicit rule. Only the two `exI` witnesses (`W₀` and `P(W)`) and
the outer `ind` survive extraction. -/

/--
info: 500 rule applications
eqSubst 196
eqRefl 131
convBeta 40
allI 23
allE 17
impI 17
wk 13
ax 12
convAddSucc 11
impE 10
convAddZero 6
convRecSucc 6
convRecZero 6
ind 6
exI 2
botE 1
exE 1
succInj 1
succNeZero 1
-/
#guard_msgs in #dtreeStats dtreeExpSolve

end HAomega
