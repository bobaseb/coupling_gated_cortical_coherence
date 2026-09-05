# S5: baseline gate failed

Configuration: `{'n': 500, 'diffusion': 1.0, 'dt': 0.01, 'steps': 10000, 'sample_every': 10, 'seed': 20260905, 'probability': 0.2, 'positive_sum': 4.0}`; omega=0; trajectory seed=config seed+1.
Second-half mean order: 0.13214.
Matched independent-noise control: 0.04207.
Finite-size reference: 0.04472.
Row sums (min, mean, max): [-8.881784197001252e-16, 6.439293542825907e-17, 1.3322676295501878e-15].
Saved integration runtime (baseline + control): 5.68 s.

The baseline exceeds the declared generous gate of twice 1/sqrt(N).
The modulatory sweep was not run; epsilon_c, K_eff and E_req are unavailable.
Exact row balance and Dale signs do not ensure an incoherent finite-N baseline.
This single network and seed do not establish persistent macroscopic order.

## Open questions

What synaptic strength and topology define the intended baseline? The specification
leaves both unspecified; this attempt fixed positive row sum 4 and probability 0.2
(0.5 in the N=100 smoke). Reducing strength to obtain a pass changes that regime.
Also, N_cortex*shift*f is dimensionless, whereas the SDE coupling is inverse time.
An independently justified rate calibration is required before the requested
conversion can establish physical-unit consistency. No measured field is inferred.

Artifacts retain only decimated order and final phases, with seeded metadata.
No Lean obligation, gluing claim or dynamical-selection theorem is discharged.
