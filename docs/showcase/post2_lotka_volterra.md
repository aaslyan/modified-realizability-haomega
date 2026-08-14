# Showcase Post 2: Lotka–Volterra Predator–Prey Cycles

**Image Asset**: `docs/media/lotka_volterra_orbits.jpg`
**Lean 4 Source**: `HAomega/DynamicalSystems/LotkaVolterra.lean`

---

### LinkedIn Post Text:

Why do predator and prey populations naturally oscillate in eternal, out-of-phase cycles?

The iconic **Lotka–Volterra Predator–Prey System** models the ecological dance between prey $x$ and predators $y$:

$$\begin{cases} \frac{dx}{dt} = \alpha x - \beta x y \\ \frac{dy}{dt} = \delta x y - \gamma y \end{cases}$$

In the phase plane, this interaction generates concentric, closed periodic orbits surrounding a stable center equilibrium. The ecosystem never collapses or blows up — it loops forever along constant-energy invariant curves defined by:

$$H(x, y) = (\delta x - \gamma \ln x) + (\beta y - \alpha \ln y) = \text{constant}$$

In our Lean 4 formalization (`HAomega/DynamicalSystems/LotkaVolterra.lean`):
1. **Flow Invariant Conservation**: Proved `lotka_volterra_invariant_cancel` ($\frac{dH}{dt} = 0$), establishing the exact algebraic cancellation of predator-prey rate terms along any flow line.
2. **Coupled Quadratic Picard Step**: Extracted exact rational polynomial series in $\mathbb{Q}[t]^2$ generating deterministic population curves over time.
3. **Compile-Time Kernel Proofs**: Verified with `#guard` checks in the Lean 4 kernel with zero sorrys.

Differential equations and ecological dynamics formalized in modern interactive theorem proving.

#Lean4 #Ecology #DifferentialEquations #Mathematics #InteractiveTheoremProving #DynamicalSystems
