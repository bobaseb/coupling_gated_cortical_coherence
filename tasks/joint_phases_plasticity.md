# Agent Execution Specification: Joint Fast-Slow Co-Evolution of (theta, K)

**Priority: 6 of 6 - lowest value of the set, and blocked on a conceptual fix.**
Measured budget on this Pi 5: 0.5 ms/step at N = 100; the whole run is minutes.
See `simulation_shared_notes.md`.

## Read first: two reasons this ranks last

### 1. It overlaps heavily with existing code

`simulations/structural_resonance.py` already co-evolves theta and K jointly in a
single loop, with the same `sigma = sum(dtheta^2)` gradient, the same
non-negativity clip, the same hollow diagonal, and the same Frobenius distance to
an environmental covariance. The objective's premise - that this "fills the
theoretical gap left by the frozen-phase proofs" - does not match what is already
in the repo. **Before writing anything new, read that file and decide whether
this is a new simulation or a revision of it.** If it is a revision, revise it in
place rather than adding a near-duplicate.

What is genuinely absent from the existing script and worth adding: explicit
timescale separation (K updated every 10-100 fast steps rather than every step),
the total-coupling renormalization constraint, the `v_j` term in the gradient,
and an `r(t)` trace alongside `sigma(t)`.

### 2. BLOCKING - "entropy production" is mislabelled

With symmetric K and zero-mean natural frequencies, the Kuramoto system is a
gradient flow on the coupling potential. A gradient flow with additive noise
satisfies detailed balance, so its **true entropy production rate is exactly
zero**. The quantity `sigma = (1/D) sum_i v_i^2` is positive in that state, but
it is a dissipation function, not entropy production - it stays positive at
equilibrium precisely because thermal fluctuations keep `v_i` non-zero. So the
headline deliverable, "a strictly positive plateau proving a non-equilibrium
steady state", would be measuring an equilibrium system and calling it a NESS.

This matters beyond pedantry: the E45 edge in `Chain.lean` is a modelling
assumption that *dissipation constrains coupling*, and `main.tex` is careful about
what is and is not established. Publishing a figure whose axis label overstates
its own content hands a referee a free objection.

**Fix one of the two before running:**

* **(a) Make it a genuine NESS.** Introduce a non-zero mean drive - heterogeneous
  `omega_i` with non-zero mean, or asymmetric coupling `K_ij != K_ji` - so the
  system carries a steady probability current. Then `sum v_i^2 / D` is a
  legitimate proxy for entropy production and the positive plateau means what the
  spec says it means. **This is the preferred fix**, since the paper's claim is
  about a driven system.
* **(b) Relabel.** Keep symmetric K and zero-mean omega, and label the axis
  "dissipation function `sum v_i^2 / D`", stating in the caption that the true
  EPR vanishes here by detailed balance and that this quantity is the descent
  objective, not a thermodynamic rate.

Note the interaction with the zero-noise case: with identical frequencies and
D = 0, a perfectly locked state has `v_i = Omega` for all i, so
`sigma = N Omega^2`, which is zero when the mean frequency is zero. The positive
plateau under (a) comes from the drive; under (b) it comes from the noise. Say
which.

## Status of the output

Heuristic numerical evidence for the supplement. It does not discharge E45, which
is recorded as a modelling assumption in `Chain.lean` and stays that way.

## Objective

Demonstrate joint two-timescale dynamics of fast Kuramoto phases (theta) and slow
coupling plasticity (K), showing that gradient descent on the dissipation
functional proceeds without destabilizing the phase-locked state.

## Mathematical Formulation

* **Fast dynamics.** `dtheta_i/dt = omega_i + sum_j K_ij sin(theta_j - theta_i)
  + eta_i(t)` with noise D.
* **Local drift.** `v_i = omega_i + sum_j K_ij sin(theta_j - theta_i)`.
* **Slow dynamics.** With `sigma ∝ sum_i v_i^2` and K treated as symmetric (so
  `K_ij` and `K_ji` are one parameter),
  `grad_{K_ij} sigma = v_i sin(theta_j - theta_i) + v_j sin(theta_i - theta_j)`.
  Update `dK_ij/dt = -eta_K grad_{K_ij} sigma` with `eta_K << 1`. *(The factor of
  2 from differentiating the square is absorbed into eta_K; this is correct as
  written.)*
* **Resource constraints.** After each plasticity step: clip `K_ij < 0` to 0,
  set `K_ii = 0`, and renormalize so `sum_ij K_ij` is constant. Note that the
  clip-and-renormalize step makes this a *projected* descent, so `sigma` need not
  decrease monotonically; do not present non-monotonicity as a bug.

## Hardware-Specific Implementation (Pi 5)

* **State.** N = 100; theta a 1D array, K a 100x100 array.
* **Vectorized gradients.** `theta[None, :] - theta[:, None]`; drift via matrix
  product with the sine-difference matrix; gradient matrix with no Python loops.
* **Measured cost.** 0.5 ms/step at N = 100 - the cheapest of the five by an
  order of magnitude. There is headroom to raise N to 300-500 or to average over
  many seeds if that makes the result more convincing.
* **Timescale separation.** Euler-Maruyama at `dt = 0.01` for theta; update K
  once every 10-100 fast steps.

## Required Outputs & Visualizations

1. **Dissipation plateau.** Smoothed `sigma(t)`, axis-labelled per the fix chosen
   above, showing joint descent reaching a stable plateau.
2. **Order parameter maintenance.** `r(t)` on shared time axes with `sigma(t)`,
   showing that deformation of K does not break the synchronized state.
3. **Structural drift.** Frobenius distance between `K(t)` and the environmental
   drive covariance. Include a shuffled-covariance control: without it, a
   decreasing distance is not evidence of resonance, since renormalized K drifts
   toward a generic dense matrix regardless of what the environment looks like.

## Resolved specification question

* **Environmental drive.** Define an explicit clustered `omega_i` (e.g. three
  frequency clusters with a non-zero grand mean) rather than a random stationary
  drive. It satisfies fix (a) above, makes the structural-resonance claim
  testable against a known ground-truth block structure, and gives the Frobenius
  panel something specific to converge to.
