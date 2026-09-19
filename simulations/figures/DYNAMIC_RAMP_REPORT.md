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
it shows the apparent exponent does not drift across the span, and neither half
resolves the shortfall by itself.

Collapse deviations and onset exponents are read on the decade-spaced legs
v=0.1, 0.01, 0.001, 0.0001. The slowest-ramp deviation floor is Dev_0=0.00705;
2 Dev_0=0.01410. The critical-speed crossing is
not bracketed by the sweep.

Using D_phys=1.5 rad/s, v_phys=v D_phys^2. A 100--1000 s crossing of a coupling
window of width 1.5 rad/s corresponds to v=0.000667--0.00667 in simulation
units, inside the tested range. This conversion compares scales; it is not a
measurement of astrocytic coupling dynamics.
