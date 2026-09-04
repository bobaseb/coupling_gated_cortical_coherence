# Dynamic-ramp numerical report

Finite-N heuristic evidence only; these runs prove no trajectory theorem and do
not discharge the adiabatic assumption. Seed 20260903, 32 replicas, N=2000,
D=1, dt=0.01. Escape is the first of three consecutive decimated samples with
r >= 0.2; pre-critical crossings are excluded.

| v | escaped | mean delay | replica SD | collapse Dev | beta_eff |
|---:|---:|---:|---:|---:|---:|
| 0.1 | 5/32 | 0.4160 | 0.0619 | 0.00245 | 0.964 |
| 0.01 | 32/32 | 0.1947 | 0.0768 | 0.00599 | 0.898 |
| 0.001 | 32/32 | 0.0684 | 0.0313 | 0.00689 | 0.471 |
| 0.0001 | 32/32 | 0.0253 | 0.0168 | 0.00705 | 0.417 |

The delay fit excludes the right-censored v=0.1 leg and gives exponent
0.443 against the predicted 0.5. The slowest-ramp deviation
floor is Dev_0=0.00705; 2 Dev_0=0.01410. The critical-speed crossing
is not bracketed by the four-speed sweep.

Using D_phys=1.5 rad/s, v_phys=v D_phys^2. A 100--1000 s crossing of a coupling
window of width 1.5 rad/s corresponds to v=0.000667--0.00667 in simulation
units, inside the tested range. This conversion compares scales; it is not a
measurement of astrocytic coupling dynamics.
