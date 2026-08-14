# Showcase Post 5: Keplerian Orbital Mechanics & Conservation of Angular Momentum

**Image Asset**: `docs/media/kepler_orbit_mechanics.jpg`
**Lean 4 Source**: `HAomega/DynamicalSystems/Kepler.lean`

---

### LinkedIn Post Text:

Why do planets sweep out equal areas in equal times as they orbit the Sun?

Under Isaac Newton's central inverse-square gravitational force:

$$\ddot{\mathbf{r}} = -\frac{G M}{\|\mathbf{r}\|^3} \mathbf{r}$$

planetary motion is governed by an exact geometric conservation law: **conservation of angular momentum** ($L = x v_y - y v_x$).

In our Lean 4 formalization (`HAomega/DynamicalSystems/Kepler.lean`):
1. **Kepler's Second Law**: Proved `kepler_angular_momentum_conserved`:
   $$\frac{dL}{dt} = \mathbf{r} \times \mathbf{F}_{\text{gravity}} = 0$$
   showing that the gravitational force produces zero torque about the central star.
2. **Planetary Picard Integrator**: Computes 2D gravitational orbital trajectories $(x(t), y(t), u(t), v(t)) \in \mathbb{Q}[t]^4$ over rational time steps.
3. **Kernel-Verified Mechanics**: Validated circular orbit velocity and position vectors with compile-time `#guard`s.

From celestial mechanics to verified interactive proofs in Lean 4.

#Lean4 #Astronomy #Physics #OrbitalMechanics #Kepler #Math #FormalMethods
