# Showcase Post 1: The Van der Pol Oscillator & Limit Cycles

**Image Asset**: `docs/media/vanderpol_limit_cycle.jpg`
**Lean 4 Source**: `HAomega/DynamicalSystems/VanDerPol.lean`

---

### LinkedIn Post Text:

What happens when an electrical circuit or heart cell pumps energy when amplitude is low, but dissipates energy when amplitude is high?

You get the **Van der Pol Oscillator** — the quintessential model of self-sustained relaxation oscillations and stable limit cycles:

$$x'' - \mu (1 - x^2) x' + x = 0 \iff \begin{cases} \dot{x}_1 = x_2 \\ \dot{x}_2 = \mu (1 - x_1^2) x_2 - x_1 \end{cases}$$

No matter whether a trajectory starts far outside or deep inside near the origin, the non-linear velocity field pulls every path into a single, closed **stable limit cycle** (the glowing boundary in the phase portrait below).

In our constructive formalization in Lean 4 (`HAomega/DynamicalSystems/VanDerPol.lean`):
1. **Constructive Picard Solver**: Iterates polynomial Picard operators over $\mathbb{Q}[t]$ directly inside the theorem prover, computing higher-order non-linear trajectory expansions without floating-point approximations.
2. **Phase Divergence & Contraction**: Formalized and proved the exact trace identity $\nabla \cdot \mathbf{F} = \mu(1 - x_1^2)$, governing the transition between negative resistance and dissipation.
3. **Kernel-Checked Evaluation**: Every trajectory step is verified at compile time with `#guard`!

Mathematics meets executable code, verified from the axioms up.

#Lean4 #Mathematics #DynamicalSystems #Physics #DifferentialEquations #OpenSource #FormallyVerified
