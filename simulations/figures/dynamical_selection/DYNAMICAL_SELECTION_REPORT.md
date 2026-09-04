# Dynamical selection simulation report

## Scope

This finite-N stochastic simulation supplies heuristic numerical evidence at the
sampled parameters. It does not prove dynamical selection, propagation of chaos,
or any trajectory theorem, and it discharges no Lean obligation. Natural
frequencies are identically zero so that comparison with the repository's
von Mises self-consistency curve is valid.

## Configuration

- Seed: 20260904
- Oscillators per replica: 1000
- Independent replicas: 500
- Diffusion: D = 1.0
- Euler--Maruyama step: dt = 0.01
- Long regimes: K = 1.6, 2.0, 2.8; 5,000 steps each
- Growth sweep: K = 2.2 through 3.1 in increments of 0.1; 1,000 steps each
- Growth window: t >= 1 and r < 0.3
- Finite-size reference: 1/sqrt(N) = 0.03162
- Saved integration runtime: 1,383.97 s

The implementation uses the O(N) complex mean-field reduction. Saved NPZ files
contain only decimated ensemble means and standard deviations, never oscillator
phases or per-replica histories.

## Results

The steady ensemble-mean orders were 0.06266 below threshold (K = 1.6), 0.16049
at threshold (K = 2.0), and 0.67735 above threshold (K = 2.8). The static
self-consistency value at K = 2.8 is 0.68270, giving a residual of -0.00535.
The nonzero subcritical and critical values are finite-N fluctuations, not
coherent fixed points; critical fluctuations are visibly enhanced relative to
the simple 1/sqrt(N) reference.

All ten log-linear growth fits had R-squared between 0.9738 and 0.9968. The
extracted rates rose from 0.14398 at K = 2.2 to 0.52282 at K = 3.1. Regressing
those rates on K gave

```text
lambda_fit = 0.43240 K - 0.82318
lambda_theory = 0.50000 K - 1.00000
```

Thus the sampled finite system reproduces the predicted positive, nearly linear
growth above threshold, but the fitted slope is 13.5% below the infinite-N
linearization and its inferred zero crossing is K = 1.904 rather than 2.0. This
quantitative discrepancy is retained as a finite-size/time-window result rather
than tuned away.

## Artifacts

- `selection_escape_trajectories.png`: subcritical, critical, and supercritical
  ensemble trajectories on log axes, each with the finite-size reference.
- `selection_static_comparison.png`: steady simulation points over the existing
  quadrature-based coherent branch.
- `selection_growth_rates.png`: extracted rates and the exact `(K - 2D)/2` line.
- `selection_{subcritical,critical,supercritical}.npz`: compact trajectory
  summaries.
- `dynamical_selection_summary.json`: parameters, rates, fit quality, static
  comparison, runtime, and scope statement.

The run is one finite N, one seed, one discretization, and a fixed set of
couplings. Agreement with the static branch and the observed escape do not show
that every perturbation, initial distribution, or continuum trajectory selects
the coherent branch.
