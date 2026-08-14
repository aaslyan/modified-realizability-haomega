# Showcase Post 3: The Duffing Oscillator & Double-Well Separatrix

**Image Asset**: `docs/media/duffing_double_well.jpg`
**Lean 4 Source**: `HAomega/DynamicalSystems/Duffing.lean`

---

### LinkedIn Post Text:

A particle rolling inside a double-well potential with a central hill at $x = 0$ and two stable valleys at $x = \pm 1$:

$$\ddot{x} + \delta \dot{x} - x + x^3 = 0 \iff \begin{cases} \dot{x}_1 = x_2 \\ \dot{x}_2 = x_1 - x_1^3 - \delta x_2 \end{cases}$$

This is the **Duffing Oscillator**. In phase space, it exhibits a golden **figure-eight separatrix** connecting the unstable saddle point at the origin to the boundaries of two distinct basins of attraction. Depending on initial energy and damping, trajectories spiral into either the left or right potential well.

In our Lean 4 formalization (`HAomega/DynamicalSystems/Duffing.lean`):
1. **Hamiltonian Energy Dissipation**: Proved `duffing_energy_dissipation_id`:
   $$\frac{dE}{dt} = -\delta x_2^2 \le 0$$
   proving that mechanical energy monotonically decreases under damping $\delta > 0$ until the system settles into one of the twin minima.
2. **Cubic Picard Step**: Implemented non-linear polynomial integration on $\mathbb{Q}[t]$ tracking cubic restoring terms.
3. **Machine-Checked Dynamics**: Verified compile-time `#guard` calculations verifying displacement and velocity trajectories.

Nonlinear mechanics and separatrix dynamics verified in Lean 4.

#Lean4 #Physics #ClassicalMechanics #NonlinearDynamics #TheoremProving #FormalMethods
