# Agent Execution Specification: Dynamical Selection and Stability of the Coherent Branch

**Priority: 3 of 6.** Measured budget on this Pi 5: 69 ms/step at 500x1000 ensembles;
~30 min for three regimes plus the growth-rate sweep. RAM is single-digit MB.
See `simulation_shared_notes.md`.

*(Renamed from `dynamic_sleep_inertia.md`, which described its contents
incorrectly - the sleep-inertia ramp was the follow-on offer, not this spec.)*

## Status of the output

Heuristic numerical evidence for the supplement. This closes no Lean gap. In
particular it does not establish dynamical selection; it exhibits it in
simulation at specific parameter values. `main.tex:340` must continue to say the
coherent branch is not proved to be dynamically selected.

## Objective

Implement a vectorized Python simulation showing that the supercritical coherent
branch (r > 0) is the dynamically selected attractor above threshold, resolving
the degeneracy in which the incoherent state (r = 0) remains a valid analytical
solution.

**Gap targeted.** `main.tex:340` states verbatim: *"Of the coherent branch we
prove existence, uniqueness, continuous emergence at threshold and strict growth
in K, but not that it is dynamically selected."* Also recorded at
`tasks/todo.md:2092`. This is the cleanest gap-to-figure mapping of the five, and
it complements `simulations/bifurcation.py` (which draws the static
self-consistency curve) rather than duplicating it.

## Mathematical Formulation

* **System dynamics.** Integrate the stochastic Kuramoto SDE
  `dtheta_i/dt = omega_i + (K/N) sum_j sin(theta_j - theta_i) + eta_i(t)`
  with thermodynamic noise D.
* **Natural frequencies.** Set `omega_i = 0` (identical oscillators). The
  self-consistency curve `r = I_1(a)/I_0(a)` that this simulation is validated
  against is derived for identical frequencies; a frequency spread changes the
  stationary density and the comparison stops being apples-to-apples.
* **The theoretical gap.** At `K > K_c = 2D` both `r = 0` and `r = R(K, r)` solve
  the self-consistency equation. The simulation must show that any infinitesimal
  perturbation drives the system irreversibly away from r = 0 and towards the
  coherent branch.

### REQUIRED CORRECTION - the growth rate is quantitative, not just proportional

Linearizing the mean-field Fokker-Planck operator around the uniform density
gives, for the first harmonic,

```
lambda = (K - 2D)/2 = (K - K_c)/2
```

Fit against this exact expression - slope 1/2 and intercept at K_c = 2D - not
merely against `lambda ∝ K - K_c`. The proportionality version passes on any
curve through the origin and so tests almost nothing; the slope is the part that
can actually fail.

### REQUIRED CORRECTION - the finite-N floor

Uniform initialization over `[-pi, pi]` does **not** "perfectly enforce" r(0) = 0.
It gives `r(0) ~ 1/sqrt(N)` (= 0.032 at N = 1000), and that fluctuation is
precisely the seed perturbation the escape dynamics needs - without it the system
sits exactly on the unstable fixed point and never leaves. Two consequences the
original spec got wrong:

* Describe the initialization as *seeding* the instability at the `1/sqrt(N)`
  fluctuation scale, not as enforcing r = 0.
* The subcritical trace plateaus at `~1/sqrt(N)`, **not** at zero. Draw
  `1/sqrt(N)` as a horizontal reference line on every r(t) panel, or the
  subcritical run will be misread as weakly ordered.

## Hardware-Specific Implementation (Pi 5)

* **Initialization & vectorization.** A 2D array of shape `(n_ensembles, N)`,
  e.g. 500 x 1000, phases uniform on `[-pi, pi]`.
* **Mean-field reduction.** Bypass the O(N^2) coupling: compute
  `Z = r exp(i psi) = (1/N) sum_j exp(i theta_j)` per ensemble row and use the
  drift `K r sin(psi - theta_i)`, giving O(N) per step.
* **Measured cost.** 69 ms/step at 500x1000, 138 ms/step at 1000x1000. Three
  regimes at ~5,000 steps each is ~17 min; the growth-rate sweep needs only the
  early exponential phase, so ~1,000 steps per K value, ~12 min for ten values.
* **Memory footprint.** Never append per-oscillator phases to a list. Store only
  the ensemble-averaged `r(t)` per step - kilobytes.

## Required Outputs & Visualizations

1. **Escape trajectories.** Ensemble-averaged `r(t)` for subcritical (K < K_c),
   critical (K = K_c) and supercritical (K > K_c). The supercritical trace should
   depart exponentially from the `1/sqrt(N)` floor before saturating into the
   non-equilibrium steady state. Use a log y-axis so the exponential phase is a
   straight line and the floor is visible.
2. **Empirical stability check.** Scatter the final steady-state r on top of the
   theoretical self-consistency curve `r = I_1(a)/I_0(a)` from the Lean
   formalization. Reuse the quadrature helpers in `simulations/bifurcation.py`
   rather than re-deriving the curve, so both figures plot the identical object.
3. **Growth rate extraction.** Log-linear regression on the exponential phase of
   `r(t)` for varying K > K_c. Fit window: after the initial transient and
   strictly before saturation (cap at r < 0.3 to stay linear). Plot the extracted
   lambda against K and overlay the predicted line `(K - 2D)/2`; report the
   fitted slope and intercept numerically.
