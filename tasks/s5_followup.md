# S5 follow-up specification — 2026-09-05

Intent: separate amplified finite-size noise from macroscopic coherence and make
S5 a reproducible sensitivity study. Preserve the failed strength-4 run.

Before running diagnostics, fix edge probability 0.2, omega=0, D=1, dt=0.01,
10,000 steps, burn-in half the run, and three topology/noise seeds 20261905,
20262905, 20263905. Sweep N={250,500,1000}, positive row sum g={0,1,2,4};
negative row sum is -g. Compare mean r and N*mean(r^2), whose independent-phase
expectation is exactly 1. Do not interpret decimated time samples as independent
replicas. Report individual seed results and their range, not a spurious CI.

Use g=1 as a separately declared weak-synapse rescue regime, with g=4 retained
as the original failed strong-synapse control. Require each seed's N=500 baseline
to pass the original mean-r <= 2/sqrt(N) gate. This tests parameter dependence;
it does not fix the g=4 failure. Sweep uniform K from 0.4 to max(4D,g), plus
zero, at 19 log-spaced nonzero points. Extending past g is necessary when g<2D:
stopping when the two terms match would fail to bracket the analytic threshold.
Run a reduced g=1 sweep first. Compare the three production seeds and a dt/2
control near the transition at the same physical duration. Retain compact NPZ
summaries/final states. Measure the operational r=0.2 crossing, with sampled
brackets and seed range, not an infinite-N critical point.

Make the missing calibration explicit as a rate gamma:
E_req = K_eff / (gamma * N_cortex * shift * f).
The requested arithmetic is the conditional gamma=1 numerical convention.
Report its values and inverse-gamma sensitivity; do not infer gamma from a
simulation or call this independent physical-unit validation.

Success: tested controls, saved complete sensitivity and rescue sweeps (or honest
failed gates), figures and a source-based report. Publish computed results only
through generated TeX macros and a drift test. No new citations or Lean changes.


## Reproduction

Run with `OPENBLAS_NUM_THREADS=1` and `uv run --directory simulations python`:

- `geometric_frustration.py --smoke --strength 1 --seed 20261905 --output figures/geometric_frustration/weak_smoke`
- `frustration_diagnostics.py baseline`
- `frustration_diagnostics.py rescue`
- `frustration_diagnostics.py timestep`

Then `frustration_summary.py` regenerates comparison figures/report and the
compact aggregate summary; `simulation_tex.py` regenerates manuscript macros.
These last two commands read saved outputs only. Per-leg metadata rejects
incompatible cached configurations. The original default strength-4 command
continues to fail its baseline gate intentionally and preserves that control.
