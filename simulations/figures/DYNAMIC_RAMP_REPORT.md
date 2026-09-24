# Dynamic-ramp numerical report

Finite-N heuristic evidence only; these runs prove no trajectory theorem and do
not discharge the adiabatic assumption. Seed 20260903, 32 replicas, N=2000,
D=1, dt=0.01. Escape is the first of three consecutive decimated samples with
r >= 0.2; pre-critical crossings are excluded.

| v | escaped | mean delay | replica SD | collapse Dev | beta_eff |
|---:|---:|---:|---:|---:|---:|
| 0.1 | 5/32 | 0.4160 | 0.0619 | 0.00245 | 0.964 |
| 0.02 | 31/32 | 0.2213 | 0.0786 | 0.00509 | 0.966 |
| 0.01 | 32/32 | 0.1947 | 0.0768 | 0.00599 | 0.898 |
| 0.005 | 32/32 | 0.1266 | 0.0645 | 0.00658 | 0.648 |
| 0.002 | 32/32 | 0.0875 | 0.0383 | 0.00672 | 0.646 |
| 0.001 | 32/32 | 0.0684 | 0.0313 | 0.00689 | 0.471 |
| 0.0002 | 32/32 | 0.0297 | 0.0201 | 0.00696 | 0.423 |
| 0.0001 | 32/32 | 0.0253 | 0.0168 | 0.00705 | 0.417 |

The delay fit uses the 6 uncensored legs of 8, excluding
v=0.1, v=0.02, and gives exponent 0.444 [0.394, 0.494] against the predicted 0.5,
which the interval excludes.

Split at the median speed, the faster half returns 0.492 [-0.289, 1.273] and the
slower half 0.447 [-0.406, 1.299]. The point estimates
agree to within 0.05, but each half is
three legs over one decade and its own interval is far wider than the shortfall
being tested, so the split is a consistency check and not a second measurement:
it does not resolve drift across the span, and neither half
resolves the shortfall by itself.

Bootstrapping the 10000 resamples over replicas within each of the 6
uncensored legs gives a 95% CI of [0.398, 0.496] for the exponent. The
fraction of bootstrap samples with an exponent at or above 0.5 is 0.019.

Collapse deviations and onset exponents are read on the decade-spaced legs
v=0.1, 0.01, 0.001, 0.0001. The slowest-ramp deviation floor is Dev_0=0.00705;
2 Dev_0=0.01410. The critical-speed crossing is
not bracketed by the sweep.

## Follow-up controls

Only completed checkpoints enter these fits. Pending rows are provisional. Zero-delay resamples cannot enter a log fit; the reported bootstrap intervals condition on a positive mean delay at every speed.

| condition | status | artifacts | fit legs | OLS exponent | bootstrap 95% CI | zero draws | missing speeds |
|:--|:--|--:|--:|--:|:--|--:|:--|
| N2000_r0.20 | complete | 8 | 6 | 0.444 | [0.398, 0.496] | 0 | — |
| N2000_r0.05 | complete | 8 | 8 | 0.637 | [0.525, 0.788] | 68 | — |
| N8000_r0.05 | complete | 8 | 7 | 0.720 | [0.631, 0.827] | 0 | — |
| 0.5 | complete | 4 | 3 | 0.241 | [0.179, 0.306] | 0 | — |
| 1.0 | complete | 4 | 3 | 0.178 | [0.107, 0.255] | 0 | — |
| 1.5 | fit censored | 4 | 2 | — | — | — | — |

The three delay exponents are 0.444, 0.637, and 0.720 in table order on all eligible legs. Over the matched six-leg subset v=0.01--0.0001, the exponents are 0.444, 0.634, and 0.710. On the matched subset, the sequence does not show convergence toward 0.5. In table order, log-residual RMS is 0.059, 0.091, 0.240; leave-one-speed-out slopes span [0.429, 0.466], [0.631, 0.642], [0.679, 0.759]. The N=8000 low-threshold fit has material log scatter, so a single power law is not established across these settings. In table order, maximum precritical order is 0.303, 0.303, 0.214; maximum initial order is 0.041, 0.041, 0.019; largest saved coupling step is 0.010; censored replica legs total 28, 0, 9. A postcritical threshold crossing can therefore be immediate when the trace is already above the absolute criterion before Kc. The tighter criterion produces zero-delay crossings. These finite-sweep estimates do not establish an asymptotic exponent. Do not assume tightening the criterion restores one-half.

At Lorentzian half-width 1.5, the completed sweep has too few uncensored speed legs for an exponent interval. The control therefore cannot decide whether heterogeneity changes only the prefactor or the exponent. A lower, predeclared escape criterion or wider coupling window is needed.

Using D_phys=1.5 rad/s, v_phys=v D_phys^2. A 100--1000 s crossing of a coupling
window of width 1.5 rad/s corresponds to v=0.000667--0.00667 in simulation
units, inside the tested range. This conversion compares scales; it is not a
measurement of astrocytic coupling dynamics.
