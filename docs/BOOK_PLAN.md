# Practical Logic: From Proofs to Programs in Arithmetic and Analysis

*A Mechanized Course in Modified Realizability, Gödel's System T, and Constructive Analysis in Lean 4*

---

## Book Premise & Positioning

Most logic and proof-theory textbooks present modified realizability, Gödel's System T, ordinal recursion below $\varepsilon_0$, and constructive analysis as *paper metatheory*: the reader proves that a program exists in principle, but never watches a formal derivation compile into a running term or measures what happens when a proof changes. Conversely, interactive theorem proving textbooks teach how to prove theorems in a host language, treating program extraction as an opaque external command.

**This book bridges the two.** Every logical system in the book is *deeply embedded* in Lean 4: formulas, natural-deduction derivations (`Deriv`), System T programs (`Tm`), and representations (`Rep`) are first-class data structures. The extraction compiler (`extract`) is a 40-line total function whose soundness (`soundness`) and continuity (`extract_continuous2`) are machine-checked theorems. Every philosophical claim of constructive logic becomes a reproducible experiment verified by `#guard` and calibrated by `#print axioms`.

---

## Pedagogical Architecture: The "Heartbeat" Rhythm (Theory $\leftrightarrow$ Example)

A book on mathematical logic loses readers if it spends 80 pages building syntax, de Bruijn indices, associates, and soundness before running a single program — and it loses depth if it shows examples as magic tricks without explaining the theory underneath.

To keep genuine curiosity high from page 1, the book uses an **interleaved 4-beat rhythm in every chapter**:

1. **The Provocation (A Concrete Puzzle):** Start with a short, surprising question or a 5-line theorem whose computational behavior is not obvious (e.g., *"How can a terminating program take an infinite function $f : \mathbb{N} \to \mathbb{N}$ as input?"* or *"Why do two proofs of the same lemma extract to two different algorithms?"*).
2. **The Live Example (Run It First):** Show the concrete statement and run its extracted realizer in Lean (`#guard` / `#eval`) so the reader sees the phenomenon *before* the general machinery.
3. **The Theory (Just Enough to Explain Why):** Introduce the exact theoretical mechanism that explains what just happened (e.g., Kleene 1945 vs. Kreisel 1959, or Kleene–Kreisel associates `Assoc` and extensional collapse `CtQ`, or the conversion rules `convQLipScale` / `convQCloseMono`).
4. **The Boundary / Refutation Experiment:** End every chapter by pushing the mechanism until it hits a wall — mutating a witness so compilation fails, exhibiting a discontinuous functional (`zeroTest`) that *no* proof can extract to, or watching `#print axioms` light up with `Classical.choice` (`A0.toA1`, `canonicalAssociate`).

---

## Five-Part Architecture

| Part | Theme | Formal System | Central Question |
|---|---|---|---|
| **Prologue** | **The Three Mysteries** | Tour of the Pipeline | *How can a proof run, how can it eat an infinite function, and what can it never compute?* |
| **Part I** | **The Machine (Kleene to Kreisel)** | First-Order $\text{HA}$ | *Why did Kreisel modify Kleene's realizability, and how does a 40-line compiler extract programs?* |
| **Part II** | **Kleene–Kreisel & Continuity** | Continuous Functionals (`Ct`, `Assoc`, `CtQ`) | *Why is every computable higher-type functional continuous, and how do type-1 associates represent higher types?* |
| **Part III** | **Varying the Knobs in $\text{HA}^\omega$** | System T + $\text{TI}(\varepsilon_0)$ | *How do proof structure, logical strength ($\varepsilon_0$), and data representation change the extracted program?* |
| **Part IV** | **From Existence to Algorithm in Analysis** | $\text{HA}^\omega$ over $\mathbb{Q}$ and $\mathbb{D}$ | *How do classical existence theorems in analysis become certified algorithms and moduli?* |
| **Part V** | **Representations as Data Budgets** | Represented Spaces ($\mathbf{Rep}$, $A_0, A_1, E_0, E_1$) | *What quantitative data must a mathematical object carry before a theorem can compute?* |

---

## Detailed Chapter-by-Chapter Blueprint

### Prologue: Three Mysteries in Ten Pages (The Hook)
- **Goal**: Hook the reader in Chapter 0 with three live experiments before any heavy definitions:
  1. *Mystery 1 (Proofs as Programs)*: Run two proofs of 1D Sperner's Lemma on the same coloring and watch them return *different* crossings.
  2. *Mystery 2 (The Infinite Input)*: Pass an infinite function $f : \mathbb{N} \to \mathbb{N}$ into the extracted type-2 Fibonacci realizer $\text{fib}(f(f(0)))$ (`HigherType.lean`) — how did a finite program consume an infinite object? Because it only probed $f$ at two points ($0$ and $f(0)$) — **continuity**!
  3. *Mystery 3 (The Forbidden Functional)*: Exhibit `zeroTest : (ℕ → ℕ) → ℕ` (which returns $1$ iff $f$ is everywhere zero) and state the theorem that **no derivation in $\text{HA}^\omega$ can ever extract to it**.
- **Lean Modules**: [`HAomega/HigherType.lean`](../HAomega/HigherType.lean), [`HAomega/Sperner.lean`](../HAomega/Sperner.lean), [`HAomega/Continuity.lean`](../HAomega/Continuity.lean)

---

### Part I: The Machine — From Kleene (1945) to Kreisel (1959)

#### Chapter 1: Statements as Specifications & The Falsifiability Test
- **Beat 1 (Provocation)**: When does an existence proof $\forall x\,\exists y.\; \varphi(x, y)$ actually discover an algorithm, and when is it theater?
- **Beat 2 (Example)**: Compare $\forall n\,\exists y.\; y = \text{fib}(n)$ (closed by `rfl`) with Euclid's full GCD specification $\forall a\,\forall b\,\exists g.\; g \mid a \wedge g \mid b \wedge \forall d\,(d \mid a \to d \mid b \to d \mid g)$.
- **Beat 3 (Theory)**: Deeply embedding syntax, formulas, and natural deduction in Lean 4; the falsifiability test (*"Is there a term that would make this statement false?"*); Patterns P1, P2, and P3.
- **Beat 4 (Experiment)**: Mutate a witness in a genuine derivation and watch the Lean kernel reject the proof.
- **Lean Modules**: [`Realizability/Core/Syntax.lean`](../Realizability/Core/Syntax.lean), [`HAomega/GcdFull.lean`](../HAomega/GcdFull.lean), [`AUDIT_P1P2P3.md`](../AUDIT_P1P2P3.md)

#### Chapter 2: Kleene's Number Realizability (1945) vs. Kreisel's Modified Realizability (1959)
- **Beat 1 (Provocation)**: Why is Kreisel's interpretation called *modified* realizability? What was in Kleene's original 1945 definition that had to change?
- **Beat 2 (Example)**: Trace what happens on a false premise ($\bot \to \varphi$) and on an unbounded search ($\neg\neg \exists k\, P(k) \to \exists k\, P(k)$, Markov's Principle).
- **Beat 3 (Theory)**:
  - **Kleene (1945)**: Realizers are untyped numbers $e \in \mathbb{N}$ (Gödel indices of partial recursive functions $\{e\}$); if $\psi$ is unrealized, $\{e\}(a)$ may diverge; validates Markov's Principle via unbounded `while` search.
  - **Kreisel (1959)**: Realizers are *typed total functionals* in System T (`tyOf φ`); a realizer of $\psi \to \chi$ must be total on *all* inputs of type $\text{tyOf}(\psi)$, even non-realizers!
  - Why Kreisel's modification explains two concrete features of our codebase: why [`Ty.dfltVal`](../HAomega/Syntax.lean) is needed in `botE` / `tiRec`, and why root-finding (`sqrtApproxD`) requires an explicit Archimedean bound $K$ instead of unbounded search.
- **Beat 4 (Experiment)**: Inspect the 40-line `extract` function and prove `soundness`.
- **Lean Modules**: [`Realizability/Core/Realizability.lean`](../Realizability/Core/Realizability.lean), [`Realizability/Core/Extraction.lean`](../Realizability/Core/Extraction.lean), [`Realizability/Core/Soundness.lean`](../Realizability/Core/Soundness.lean), [`HAomega/Extraction.lean`](../HAomega/Extraction.lean)

---

### Part II: The Kleene–Kreisel Continuous Functionals & Continuity of Extraction

*(Placed right after Part I so the reader understands what "higher types" and "continuity" mean before climbing the $\text{HA}^\omega$ and Analysis ladders.)*

#### Chapter 3: The Kleene–Kreisel Hierarchy — Associates, Continuity, and Extensional Collapse
- **Beat 1 (Provocation)**: A type-2 functional $F : (\mathbb{N} \to \mathbb{N}) \to \mathbb{N}$ takes an uncountable space as input, and a type-3 functional $\Phi : ((\mathbb{N} \to \mathbb{N}) \to \mathbb{N}) \to \mathbb{N}$ is one level higher still. How can a finite machine represent and compute with objects at all finite types using only type-1 sequences $a : \mathbb{N} \to \mathbb{N}$?
- **Beat 2 (Example)**: Build a concrete **associate** (`IsAssociate` / `Assoc`) for a constant functional, for evaluation `evalAssociate`, and for type-2 composition `compAssociate`. Watch the "first-fire" protocol in action: along any prefix $\langle \alpha(0), \dots, \alpha(m-1) \rangle$, the associate outputs $0$ ("need more input") until stage $m$, where it fires with $F(\alpha) + 1$.
- **Beat 3 (Theory — The Vendored Kleene–Kreisel Development)**:
  - The pure finite type tower `PureType n` ($C_0 = \mathbb{N}$, $C_{n+1} = C_n \to \mathbb{N}$).
  - Kleene's inductive associate relation `Assoc n a x` and the countable functionals `Ct n`.
  - **The Main Theorem (`continuous_iff_hasAssociate` & `mem_ct_two_iff_continuous2`)**: At type 2, having a type-1 associate is *equivalent* to Baire/topological continuity (`Continuous2 F`)!
    - *Constructive direction (`continuous_of_hasAssociate`)*: The firing stage of the associate gives the modulus of continuity (`[propext, Quot.sound]`).
    - *Classical direction (`hasAssociate_of_continuous`)*: Building `canonicalAssociate F` via `Determines F σ` and `Nat.find` requires `Classical.choice`!
  - **The Extensional Collapse (`CtPer` and `CtQ`)**: Why different associates can represent the same functional; quotienting hereditarily total-extensional associates (`CtDom n`) by partial equivalence (`CtPer n`) to get the honest type `CtQ n`, culminating in the capstone equivalence `ctQTwoEquiv : CtQ 2 ≃ {F // Continuous2 F}`.
- **Beat 4 (Experiment)**: Audit `#print axioms` on `continuous_of_hasAssociate` vs. `hasAssociate_of_continuous` and `ctQTwoEquiv` — our first live demonstration of how Lean's kernel detects where classical choice enters metatheory!
- **Lean Modules**:
  - [`ContinuousFunctionals/Associate.lean`](../Realizability/Core/ContinuousFunctionals/ContinuousFunctionals/Associate.lean)
  - [`ContinuousFunctionals/Continuity.lean`](../Realizability/Core/ContinuousFunctionals/ContinuousFunctionals/Continuity.lean)
  - [`ContinuousFunctionals/MainTheorem.lean`](../Realizability/Core/ContinuousFunctionals/ContinuousFunctionals/MainTheorem.lean)
  - [`ContinuousFunctionals/Hierarchy.lean`](../Realizability/Core/ContinuousFunctionals/ContinuousFunctionals/Hierarchy.lean)
  - [`ContinuousFunctionals/Collapse.lean`](../Realizability/Core/ContinuousFunctionals/ContinuousFunctionals/Collapse.lean)
  - [`ContinuousFunctionals/CtQ.lean`](../Realizability/Core/ContinuousFunctionals/ContinuousFunctionals/CtQ.lean)

#### Chapter 4: Every Extracted Program Is Continuous (`Tracked` and Moduli)
- **Beat 1 (Provocation)**: Our $\text{HA}^\omega$ realizers have product types, general arrows, rationals, and trees (`Ty`), whereas `PureType n` only has pure arrows over $\mathbb{N}$. How do we prove that *every* extracted $\text{HA}^\omega$ realizer is continuous without drowning in associate coding?
- **Beat 2 (Example)**: Take `hiProgram f = fib(f(f 0))` in `HigherType.lean`. Automatically compute its oracle-dependent modulus `hiModulusAuto f = max 1 (f 0 + 1)` using the modulus algebra in `Modulus.lean`.
- **Beat 3 (Theory)**:
  - The logical-relation bridge `Tracked τ X` in `HAomega/Continuity.lean`: using `Continuous2` at the base and lifting across products and arrows by structural induction on `Tm` (`eval_tracked` $\implies$ `extract_continuous2`), completely choice-free (`[propext, Quot.sound]`).
  - Why the modulus must depend on the oracle: proving `no_constant_modulus` for `hiProgram`.
  - Why `tiRec` (transfinite recursion) is continuous (`extract_tracked`) even though it has no compositional formula for its modulus.
- **Beat 4 (Experiment)**: Define the discontinuous zero-test functional (`zeroTest`), prove it is not `Continuous2`, and conclude by `extract_continuous2` that **no formal derivation in $\text{HA}^\omega$ can ever extract to it**.
- **Lean Modules**: [`HAomega/Continuity.lean`](../HAomega/Continuity.lean), [`HAomega/HigherType.lean`](../HAomega/HigherType.lean), [`HAomega/Modulus.lean`](../HAomega/Modulus.lean), [`Realizability/Core/Transport.lean`](../Realizability/Core/Transport.lean)

---

### Part III: Varying the Knobs — Finite-Type Arithmetic ($\text{HA}^\omega$)

#### Chapter 5: Intrinsically Typed System T & Verified Code Emission
- **Beat 1 (Provocation)**: How do we eliminate variable capture, Gödel coding of pairs/functions, and unverified pretty-printers all at once?
- **Beat 2 (Example)**: Run the same extracted realizer three ways in [`EXTRACTED_HAOMEGA.md`](../EXTRACTED_HAOMEGA.md): raw realizer term, collapsed program (`Collapse.lean`), and certified Haskell (`EmitHaskell.lean`).
- **Beat 3 (Theory)**: Intrinsically typed de Bruijn System T (`Tm Γ τ`); simultaneous renaming/substitution (`Ren`, `Sub`); formal operational semantics of the target (`HsSemantics.lean`) and semantic preservation theorems for all extracted programs.
- **Beat 4 (Experiment)**: Inspect the trusted computing base boundary (why GHC cannot check termination of emitted `tiRec` even though Lean proved it via $\varepsilon_0$).
- **Lean Modules**: [`HAomega/Syntax.lean`](../HAomega/Syntax.lean), [`HAomega/Formulas.lean`](../HAomega/Formulas.lean), [`HAomega/Realizability.lean`](../HAomega/Realizability.lean), [`HAomega/Collapse.lean`](../HAomega/Collapse.lean), [`HAomega/EmitHaskell.lean`](../HAomega/EmitHaskell.lean), [`HAomega/HsSemantics.lean`](../HAomega/HsSemantics.lean)

#### Chapter 6: Knob 1 — Varying the Proof (Sperner's Lemma, Pascal, & Hanoi)
- **Beat 1 (Provocation)**: If a theorem has multiple valid proofs, how does the choice of proof alter the algorithm that falls out?
- **Beat 2 (Example)**: Two proofs of 1D Sperner's Lemma with the same inductive invariant extract to two different algorithms (returning the *first* vs. the *last* crossing).
- **Beat 3 (Theory)**: How induction direction and case-split ordering in `Deriv` control recursion order in `Tm`; function-valued witnesses in the Towers of Hanoi (`Hanoi.lean`) and proof-computed deciders in Pascal's triangle mod 2 (`PascalTheorem.lean`).
- **Beat 4 (Experiment)**: Compare the extracted terms side-by-side and run Pascal mod 2 to render the Sierpiński gasket in the kernel.
- **Lean Modules**: [`HAomega/Sperner.lean`](../HAomega/Sperner.lean), [`HAomega/Pascal.lean`](../HAomega/Pascal.lean), [`HAomega/PascalTheorem.lean`](../HAomega/PascalTheorem.lean), [`HAomega/Hanoi.lean`](../HAomega/Hanoi.lean)

#### Chapter 7: Knob 2 — Varying Logical Strength ($\text{TI}(\varepsilon_0)$: Goodstein & Kirby–Paris)
- **Beat 1 (Provocation)**: Goodstein's theorem and the Kirby–Paris Hydra battle are famous for being unprovable in Peano Arithmetic. What happens when you extract a program from a proof that uses transfinite induction up to $\varepsilon_0$?
- **Beat 2 (Example)**: Extract and run `goodsteinD` and `herculesAnyD` (where the adversary's head-choice and replication strategies are universally quantified function variables $f, g : \mathbb{N} \to \mathbb{N}$).
- **Beat 3 (Theory)**: Cantor Normal Form ordinals below $\varepsilon_0$ (`Epsilon0.lean`); pairing a proof rule (`tiEps0`) with a computational recursor (`tiRec`); proving ordinal descent on every Hydra move (`cutH_descends`).
- **Beat 4 (Experiment)**: Inspect the extracted term to see the ordinal measure `hord` / `ord` sitting explicitly inside `tiRec`.
- **Lean Modules**: [`HAomega/Goodstein.lean`](../HAomega/Goodstein.lean), [`HAomega/Hydra.lean`](../HAomega/Hydra.lean), [`HAomega/Hercules.lean`](../HAomega/Hercules.lean), [`HAomega/HerculesAny.lean`](../HAomega/HerculesAny.lean), [`Realizability/Signature/Hydra.lean`](../Realizability/Signature/Hydra.lean)

#### Chapter 8: Knob 3 — Varying Representation (Gödel Codes vs. Structural Trees)
- **Beat 1 (Provocation)**: Proof theory textbooks say Gödel numbering lets $\mathbb{N}$ represent any finite object. Why does that textbook promise fail catastrophically when you actually run extracted programs?
- **Beat 2 (Example)**: A 37-step Kirby–Paris hydra battle overflows when hydras are coded as natural numbers (`Hydra.lean`), yet finishes instantaneously when hydras and ordinals are structural base types (`HydraTree.lean`).
- **Beat 3 (Theory)**: Comparing term size, recursion depth, and representation overhead between coded arithmetic (`tiEps0` on `.nat`) and typed structural arithmetic (`tiEps0O` on `.ord` and `.hyd`).
- **Beat 4 (Experiment)**: Measure the exact representation size and evaluation wall between `Goodstein.lean` / `Hydra.lean` and `GoodsteinTyped.lean` / `HydraTree.lean` / `HerculesTree.lean`.
- **Lean Modules**: [`HAomega/OrdCnf.lean`](../HAomega/OrdCnf.lean), [`HAomega/GoodsteinTyped.lean`](../HAomega/GoodsteinTyped.lean), [`HAomega/HydraTyped.lean`](../HAomega/HydraTyped.lean), [`HAomega/HydraTree.lean`](../HAomega/HydraTree.lean), [`HAomega/HerculesTree.lean`](../HAomega/HerculesTree.lean)

---

### Part IV: From Existence to Algorithm — Constructive Analysis in $\text{HA}^\omega$

#### Chapter 9: Real Numbers as Programs ($\sqrt{2}$ and Certified Brackets)
- **Concepts**: Why constructive analysis replaces completed reals with $\forall n\,\exists k$ approximation processes; choice-free rationals (`Q`) and dyadics (`D`); instantiating 1D Sperner to bracket $\sqrt{q}$ and $\sqrt[3]{q}$; discharging the Archimedean bound in `QAnalysis`.
- **Lean Modules**: [`HAomega/Rationals.lean`](../HAomega/Rationals.lean), [`HAomega/Dyadics.lean`](../HAomega/Dyadics.lean), [`HAomega/SquareRoot.lean`](../HAomega/SquareRoot.lean) (`sqrtApproxD`, `cubeApproxD`), [`HAomega/QAnalysis.lean`](../HAomega/QAnalysis.lean) (`sqrt_premises`)
- **Lab / Experiment**: Extract `sqrtApproxX`, compute $\sqrt{2}$ at precision $2^{-8}$ ($k = 362 \implies 181/128$), and verify the certified interval bracket.

#### Chapter 10: The Solver That Never Met Its Function (Discrete IVT & Inversion)
- **Concepts**: Quantifying over function variables $\forall F : \mathbb{Q} \to \mathbb{Q}$; why 1D Sperner *is* the discrete Intermediate Value Theorem; pointwise function inversion and implicit curve plotting from a single extracted term.
- **Lean Modules**: [`HAomega/SquareRoot.lean`](../HAomega/SquareRoot.lean) (`fnCrossingD`, `fnCrossingX`), [`HAomega/InverseFunction.lean`](../HAomega/InverseFunction.lean) (`invOp`), [`HAomega/CertifiedPlotter.lean`](../HAomega/CertifiedPlotter.lean)
- **Lab / Experiment**: Apply the single extracted term `fnCrossingX` to solve $2x+1=5$, $x^3+x=10$, $x^5+x=1$ (no closed-form radical), $x^2=2$, and $x^4=2$.

#### Chapter 11: A Function Is a Rule Plus a Modulus (Uniform Continuity)
- **Concepts**: Kohlenbach-style proof mining; why classical $\forall \varepsilon\,\exists \delta$ discards the $\delta$; extracting the modulus $M(n) = n + j$ from an algebraic Lipschitz premise $|f(x) - f(y)| \le 2^j |x - y|$ via `convQLipScale`; applications to inverse functions and smoothing filters.
- **Lean Modules**: [`HAomega/UniformContinuity.lean`](../HAomega/UniformContinuity.lean) (`uniContLipD`, `uniModulus`), [`HAomega/Mollification.lean`](../HAomega/Mollification.lean), [`HAomega/QArith.lean`](../HAomega/QArith.lean)
- **Lab / Experiment**: Perform the mutation test on `uniContLipD` (changing witness $M := n + j$ to $M := n$ fails to compile) and inspect the two-layer axiom split between `uniContLipD` (`[propext, Quot.sound]`) and `Q_lip_scale`.

#### Chapter 12: When to Stop (Banach Contraction & Convergence Moduli)
- **Concepts**: Turning the modulus 90 degrees from space (input precision) to time (iteration count); formalizing orbit invariants by induction (`Deriv.ind`); scale monotonicity (`convQCloseMono`); proving the stopping rule $N(n) = n$ certifying an infinite future $\forall d,\; |x_{N+d} - x_{N+d+1}| < 2^{-n}$.
- **Lean Modules**: [`HAomega/BanachModulus.lean`](../HAomega/BanachModulus.lean) (`banachContractionD`, `banachStoppingN`)
- **Lab / Experiment**: Verify boundary sharpness on $T(y) = 1 + y/2$ at $n = 4$ (where step $N - 1 = 3$ sits at $1/16$, failing strict inequality $< 1/16$, while step $N = 4$ hits $1/32 < 1/16$).

#### Chapter 13: Witnesses at Arrow Type (Riemann Integration, Weierstrass, and ODE Composition)
- **Concepts**: Existential quantification at function type ($\exists G : \mathbb{Q} \to \mathbb{Q}$); packaging a System T operator with its continuity modulus; the closed System T Riemann upper-sum operator (`riemannUpperSumClosed` in `riemannIntegralD`) and Bernstein polynomial operator (`tmBernsteinClosed` in `weierstrassApproxD`); composing `fnCrossingD` and `banachContractionD` to locate and price the steady state of an ODE.
- **Lean Modules**: [`HAomega/IntegralModulus.lean`](../HAomega/IntegralModulus.lean) (`riemannIntegralD`), [`HAomega/Weierstrass.lean`](../HAomega/Weierstrass.lean) (`weierstrassApproxD`), [`HAomega/DerivFTC.lean`](../HAomega/DerivFTC.lean)
- **Lab / Experiment**: Run the extracted Riemann integrator and Bernstein polynomial approximator in the kernel, and compose `fnCrossingX` + `banachStoppingN` on $\dot{y} = 1 + y/2 - y$.

---

### Part V: Representations as Data Budgets — Calibration, Adequacy, and Axiom Footprints

#### Chapter 14: The Smoothness Ladder ($A_0, A_1, E_0, E_1$) and the Fundamental Theorem of Calculus
- **Concepts**: Why a bare evaluator $f : \mathbb{Q} \to \mathbb{Q}$ cannot support analysis; exact evaluators (`A0`, `A1`) vs. approximating evaluators (`E0`, `E1`); why EFTC1 (integration) succeeds on `A0` (`eftc1`) whereas EFTC2 (Newton–Leibniz differentiation) requires `A1` (`eftc2_thm`); how `A0.toA1` exhibits the Myhill differentiability gap via its `Classical.choice` axiom footprint.
- **Lean Modules**: [`HAomega/EFTC.lean`](../HAomega/EFTC.lean), [`HAomega/QAnalysis.lean`](../HAomega/QAnalysis.lean), [`HAomega/SmoothnessHierarchy.lean`](../HAomega/SmoothnessHierarchy.lean)
- **Lab / Experiment**: Audit `#print axioms` across `eftc1`, `eftc2_thm`, and `A0.toA1` to see how Lean's kernel detects missing constructive moduli.

#### Chapter 15: Represented Spaces, Galois Adequacy, and the Central Adequacy Bridge
- **Concepts**: The category of represented spaces (`Rep`, `RepMorphism`), retract preorders (`RepLe`), and Galois connections between operational requirements and representation theories (`GaloisAdjunction`); the Central Adequacy Theorem (`central_adequacy_theorem`) connecting `extractClosed D` on $\mathrm{HA}^\omega$ proofs to Galois-adequate morphisms.
- **Lean Modules**: [`HAomega/GaloisAdequacy.lean`](../HAomega/GaloisAdequacy.lean), [`HAomega/GaloisAdjunction.lean`](../HAomega/GaloisAdjunction.lean), [`HAomega/CentralAdequacy.lean`](../HAomega/CentralAdequacy.lean), [`HAomega/CategoryRep.lean`](../HAomega/CategoryRep.lean)
- **Lab / Experiment**: Trace `doubling_central_adequacy` and `exp_doubling_central_adequacy` from `Deriv` to `RepMorphism`.

#### Chapter 16: From Pointwise Evaluators to Exponential-Type and Cauchy–Hadamard Jet Algebras
- **Concepts**: Why System T handles coefficient streams $c : \mathbb{N} \to \mathbb{Q}$ (`JetTy`) structurally via 1-query differentiation (`tmJetDeriv`) and causal integration (`tmJetInteg`); the fundamental trade-off between **exponential-type entire jets** (`AnalyticJet`, $|c_n|\cdot n! \le 2^M(2^R)^n$, radius-preserving differentiation $(M, R) \mapsto (M+R, R)$, global evaluation `AnalyticJet.toE0` / `truncToE1` on $[-1, 1]$) and **Cauchy–Hadamard analytic germs** (`RadiusJet`, $|c_n| \le 2^M(2^R)^n$, admitting $\frac{1}{1-x}$, $-\ln(1-x)$, unit inversion, and local nonlinear ODEs at the price of radius-shrinking differentiation $(M, R) \mapsto (M+R+1, R+1)$); Kleene–Kreisel prefix causality (`JetAgree`, `picard_jetAgree_lock`) and object-language FTC1 in `Deriv` (`jetFTC1_cancel_norm_D`, `jetFTC1_sub_zero_D`).
- **Lean Modules**: [`HAomega/ClosedCalculus.lean`](../HAomega/ClosedCalculus.lean), [`HAomega/HolonomicCS.lean`](../HAomega/HolonomicCS.lean), [`HAomega/MajorantDom.lean`](../HAomega/MajorantDom.lean), [`HAomega/ClosedFourierODE.lean`](../HAomega/ClosedFourierODE.lean)
- **Lab / Experiment**: Compare `AnalyticJet.deriv` vs. `RadiusJet.deriv`, prove `geom_not_analyticJet`, run the extracted System T combinators (`extractedJetInteg`, `extractedJetMul`, `extractedJetEvalPoly`, `extractedNewtonJetInv`, `extractedRiccatiJet`) in the kernel, and inspect why bare `= c n` fails on unnormalized `Q` (`Q.mul_div_not_id`) while `jetFTC1_sub_zero_D` succeeds inside `Deriv`.

#### Appendix: Exact Rational Numerics & Dynamical Systems Lab
- **Purpose**: A self-contained computational showcase demonstrating exact rational algorithms and algebraic invariants in Lean 4 (explicitly separated from `Deriv` program extraction).
- **Lean Modules**:
  - *Root-Finding & Series*: [`HAomega/NewtonRaphson.lean`](../HAomega/NewtonRaphson.lean), [`HAomega/Taylor.lean`](../HAomega/Taylor.lean), [`HAomega/Chebyshev.lean`](../HAomega/Chebyshev.lean), [`HAomega/PadeApproximants.lean`](../HAomega/PadeApproximants.lean), [`HAomega/EulerMaclaurin.lean`](../HAomega/EulerMaclaurin.lean)
  - *Picard Iteration & ODE Invariants*: [`HAomega/Picard.lean`](../HAomega/Picard.lean), [`HAomega/HarmonicODE.lean`](../HAomega/HarmonicODE.lean), [`HAomega/SymplecticKepler.lean`](../HAomega/SymplecticKepler.lean), [`HAomega/DynamicalSystems/`](../HAomega/DynamicalSystems/) (`VanDerPol`, `Duffing`, `LotkaVolterra`, `Lorenz`, `Kepler`)
  - *Discrete Spectral & Grid Calculus*: [`HAomega/Fourier.lean`](../HAomega/Fourier.lean), [`HAomega/FFT.lean`](../HAomega/FFT.lean), [`HAomega/ConstructiveFFT.lean`](../HAomega/ConstructiveFFT.lean), [`HAomega/GreenDivergence.lean`](../HAomega/GreenDivergence.lean), [`HAomega/CauchyIntegral.lean`](../HAomega/CauchyIntegral.lean), [`HAomega/Isoperimetric.lean`](../HAomega/Isoperimetric.lean), [`HAomega/HeatEquation.lean`](../HAomega/HeatEquation.lean), [`HAomega/CauchyKowalevski.lean`](../HAomega/CauchyKowalevski.lean)
