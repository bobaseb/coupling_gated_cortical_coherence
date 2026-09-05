# S5: finite-N frustration rescue

Configuration: `{'n': 100, 'diffusion': 1.0, 'dt': 0.01, 'steps': 2000, 'sample_every': 10, 'seed': 20261905, 'probability': 0.5, 'positive_sum': 1.0}`; omega=0.
Saved integration runtime: 1.58 seconds.
Row sums (min, mean, max): [-1.6653345369377348e-16, -1.1934897514720433e-17, 1.6653345369377348e-16].
Zero-field steady r=0.17073.

Threshold: second-half mean r crosses 0.2 and stays above it at all larger sampled couplings.
epsilon_c=0.0132858; sampled bracket=[0.012649110640673518, 0.01437525465521851].
K_eff=1.32858; K_eff/D=1.32858 (reference 2).

| Decay (mm) | Conditional field (mV/mm) |
|---|---|
| 0.1 | 0.39647 |
| 0.2 | 0.04956 |
| 0.3 | 0.01468 |

Compare these conditional values with the 1–5 mV/mm band.
Conversion: K_eff=N_sim epsilon_c; E=K_eff/(N_cortex shift f), with constants imported from fermi_estimate_check.py and rate gamma=1. For other gamma, divide every reported field by gamma.
Dimensional limitation: N*shift*f is dimensionless; identifying it with inverse-time K requires an unspecified rate calibration.
Thus this is conditional arithmetic, not an independent physical-unit validation or a measured cortical threshold.
One fixed ER network (no self-edges), 80/20 Dale columns; signed row sums, probability and seeds are saved above and in each NPZ.
Row normalization preserves signs, but not equal per-synapse magnitudes. Row balance alone does not prove frustration; the zero-field trajectory is the empirical control.
The operational bracket is sweep resolution, not a confidence interval. Seed, network, finite-N, timestep and threshold-definition dependence remain unquantified.
No propagation-of-chaos, dynamical-selection or gluing theorem is established; no Lean obligation is discharged.
