# Showcase Post 4: The 3D Lorenz Butterfly & Strange Attractors

**Image Asset**: `docs/media/lorenz_butterfly_attractor.jpg`
**Lean 4 Source**: `HAomega/DynamicalSystems/Lorenz.lean`

---

### LinkedIn Post Text:

In 1963, Edward Lorenz discovered that three simple coupled differential equations could produce deterministic chaos — the famous **Butterfly Effect**:

$$\begin{cases} \dot{x} = \sigma (y - x) \\ \dot{y} = x (\rho - z) - y \\ \dot{z} = x y - \beta z \end{cases}$$

In 3D phase space, trajectories loop infinitely between two spiral lobes without ever intersecting themselves or repeating a cycle.

In our Lean 4 formalization (`HAomega/DynamicalSystems/Lorenz.lean`):
1. **Exponential Volume Contraction**: Proved `lorenz_volume_contraction_rate`:
   $$\nabla \cdot \mathbf{F} = \frac{\partial \dot{x}}{\partial x} + \frac{\partial \dot{y}}{\partial y} + \frac{\partial \dot{z}}{\partial z} = -(\sigma + 1 + \beta) < 0$$
   proving that any volume of initial states in phase space contracts exponentially into a zero-volume fractal strange attractor!
2. **3D Coupled Picard Solver**: Formalized 3D polynomial vector field integration in $\mathbb{Q}[t]^3$ generating exact rational initial trajectory segments.
3. **Verified Kernel Guards**: Fully checked with `#guard` at compile time in Lean 4.

Chaos theory and strange attractors brought to life in formal mathematics.

#Lean4 #ChaosTheory #Mathematics #ScientificComputing #Physics #DifferentialEquations #FormalVerification
