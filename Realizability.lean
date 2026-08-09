/-
# Modified realizability for a minimal fragment

Root module.  See docs/first-order/STATUS.md for scope; since the Phase-2 extension the
fragment includes the arithmetic induction rule, realized by the
type-indexed primitive-recursion combinator (`indRecC`/`indC`).
-/
import Realizability.Signature.OrdinalAssignment
import Realizability.Signature.Hydra
import Realizability.Signature.Hanoi
import Realizability.Signature.Pascal
import Realizability.Core.Syntax
import Realizability.Core.ModifiedRealizes
import Realizability.Core.Transport
import Realizability.Core.Extraction
import Realizability.Core.Soundness
import Realizability.Core.GenericContinuity
import Realizability.Core.CollapseDemo
import Realizability.Common.Arithmetic
import Realizability.Theorems.Goodstein.Goodstein
import Realizability.Theorems.Goodstein.TransfiniteInduction
import Realizability.Common.Exists
import Realizability.Theorems.Goodstein.OrdinalDescent
import Realizability.Theorems.Goodstein.GoodsteinTheorem
import Realizability.Theorems.Goodstein.GoodsteinExtraction
import Realizability.Theorems.Goodstein.GoodsteinSearch
import Realizability.Theorems.Hydra.HydraFragment
import Realizability.Theorems.Hydra.HydraTheorem
import Realizability.Theorems.Hydra.HydraExtraction
import Realizability.Theorems.Hydra.HydraGeneral
import Realizability.Theorems.Hydra.HydraDisplay
import Realizability.Theorems.Hydra.HydraStrategies
import Realizability.Theorems.Hanoi.HanoiTheorem
import Realizability.Theorems.Hanoi.HanoiExtraction
import Realizability.Theorems.Pascal.PascalTheorem
import Realizability.Theorems.Pascal.PascalExtraction
import Realizability.Theorems.Pascal.Lucas
import Realizability.Theorems.Pascal.PascalBinary
import Realizability.Common.StrongInduction
import Realizability.Theorems.Euclid.Euclid
import Realizability.Theorems.Euclid.GcdTheorem
import Realizability.Theorems.Euclid.GcdExtraction
import Realizability.Signature.Coloring
import Realizability.Theorems.Sperner.SpernerTheorem
import Realizability.Theorems.Sperner.SpernerExtraction
import Realizability.Signature.Fibonacci
import Realizability.Theorems.Fibonacci.FibonacciTheorem
import Realizability.Theorems.Fibonacci.FibonacciExtraction
import Realizability.Meta.ProgramExtraction
import Realizability.Meta.RealizerDisplay
import Realizability.Meta.EmitLean
import Realizability.Meta.EmitHaskell
import Realizability.Meta.EmitDemo
