# Agent Execution Specification: Stochastic Kuramoto Mean-Field Limit

**Priority: 4 of 6.** Measured budget on this Pi 5: 138 ms/step at 1000x1000;
~30-40 min for the whole N sweep, *provided* the Wasserstein correction below is
applied. RAM is single-digit MB. See `simulation_shared_notes.md`.

## Status of the output

Heuristic numerical evidence for the supplement, and nothing more. Propagation of
chaos is a research programme (Lacker 2016, Sznitman 1991), recorded as O14(B)
and named as an open problem at `main.tex:223`, `main.tex:338` and
`tasks/todo.md:1098`. A simulation on a finite N sweep cannot close it and must
not be described as closing it. The manuscript's "no theorem in this development
closes it" stands unchanged.

## Objective

Implement a vectorized Python simulation of the stochastic Kuramoto SDE to
heuristically demonstrate propagation of chaos: asymptotic independence as
N -> infinity, and convergence to the theoretical stationary density.

## Mathematical Formulation

* **System dynamics.** N coupled oscillators subject to thermodynamic noise D.
* **Natural frequencies.** **Set `omega_i = 0`.** The specification originally
  left omega undefined, which is a substantive omission: the validation target
  `rho(theta) ∝ exp((Kr/D) cos theta)` is the stationary density of the
  mean-field equation *for identical frequencies*. With a frequency spread the
  stationary density is not von Mises and the density-validation panel would be
  comparing against the wrong curve.
* **Mean-field reduction.** Collapse the O(N^2) all-to-all coupling to O(N) via
  the complex order parameter:
  `(K/N) sum_j sin(theta_j - theta_i) = K r sin(psi - theta_i)`.
* **Theoretical target.** Above `K_c = 2D`, the empirical distribution should
  match the von Mises stationary density at concentration `a = Kr/D`.

### REQUIRED CORRECTION - circular statistics

`np.cov` on phases wrapped into `[-pi, pi]` is meaningless: two oscillators at
`+3.13` and `-3.13` rad are 0.02 rad apart but contribute as though they were
6.26 rad apart, so the "covariance" is an artifact of where the branch cut falls.

Use a circular correlation coefficient instead - the Fisher-Lee / Jammalamadaka
form:

```
rho_c = sum_k sin(t1_k - mu1) sin(t2_k - mu2)
        / sqrt( sum_k sin^2(t1_k - mu1) * sum_k sin^2(t2_k - mu2) )
```

with `mu1`, `mu2` the circular means over ensembles. This is branch-cut invariant
and is the quantity that should decay as 1/N.

Note what drives the residual correlation: with `omega = 0` and no pinning the
whole cluster's mean phase diffuses, and that common-mode diffusion has variance
O(1/N). That is exactly the 1/N signal being measured - it is not a bug, but the
decay should be plotted on log-log axes against N with a `1/N` reference slope so
the claim is checkable rather than asserted.

### REQUIRED CORRECTION - Wasserstein cost (this will otherwise hang the Pi)

`scipy.stats.wasserstein_distance_nd` solves an exact optimal-transport LP and
scales roughly as n^3.4 on this hardware. Measured here:

| n samples | wall time |
|---|---|
| 50 | 0.07 s |
| 100 | 0.41 s |
| 200 | 4.2 s |
| 400 | 48 s |

Extrapolating, the specified n = 1000 is **15-20 minutes per call**, once per N
value - longer than the entire rest of the sweep, and it dominated a 2-minute
timeout in testing. Do one of:

* subsample to n = 250 per call and bootstrap ~30 resamples, reporting mean and
  spread (~2 min total, and the spread is more informative than a single exact
  number); or
* use sliced Wasserstein (project onto random directions, 1D
  `wasserstein_distance` per slice, average), which is O(n log n) per slice; or
* use `scipy.stats.energy_distance` on the 1D marginals as a cheap screen.

Whichever is chosen, the joint-vs-product-of-marginals comparison must use the
same n for both sides, since this estimator is biased upward at small n and the
bias only cancels when it is matched.

## Hardware-Specific Implementation (Pi 5)

* **Tensor initialization.** A 2D array of shape `(n_ensembles, N)`, e.g.
  1000 x N. Sweep `N in {10, 50, 100, 500, 1000}`.
* **Measured cost.** 138 ms/step at 1000x1000 (the largest N); smaller N are
  proportionally cheaper. ~5,000-10,000 steps to reach steady state at dt = 0.01
  puts the N = 1000 leg at 12-23 min and the full sweep at ~30-40 min.
* **Memory management.** Overwrite the state matrix each step; extract metrics
  only from the final steady-state snapshot. 1000x1000 float64 is 8 MB.
* **Integration step.** Euler-Maruyama. Order parameter via
  `np.mean(np.exp(1j*phases), axis=1)`. Noise via
  `rng.normal(scale=np.sqrt(2*D*dt), size=(n_ensembles, N))`.

## Required Statistical Outputs

1. **Cross-correlation decay.** Circular correlation (formula above) between two
   fixed oscillators across all ensembles at the final time step, plotted
   log-log against N with a 1/N reference line.
2. **Asymptotic independence.** Wasserstein distance between the joint empirical
   distribution of `(theta_1, theta_2)` and the product of its marginals, under
   the cost-controlled scheme above, with error bars.
3. **Density validation.** Histogram of `theta_1` across ensembles at N = 1000,
   overlaid with the theoretical von Mises density at the *measured* `a = Kr/D`
   (not a nominal a), so the panel tests the self-consistency loop and not just
   the functional form.

## Resolved specification questions

* **Coupling and noise constants.** Fix `D = 1.0` so `K_c = 2.0`, and run the
  sweep at `K = 3.0` (clearly supercritical, `a` large enough that the von Mises
  is visibly peaked) with `K = 1.0` as a subcritical control. Report both.
