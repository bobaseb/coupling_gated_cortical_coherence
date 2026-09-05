# S5: strength, finite-size and rescue controls

Design fixed in tasks/s5_followup.md before these sweeps. All three seeds retained.
N=500 rescue: g=1, p=0.2, D=1, omega=0, dt=0.01, T=100; 20 epsilon values.
Each row has positive sum g and negative sum -g, with 80/20 Dale columns.
The original g=4 failed baseline is retained; g=1 is a different regime.
At g=1 the positive-only mean-field reference is also subcritical. Thus this
regime does not establish that inhibition causes disorder; it tests added uniform coupling.

| N | g | mean r (seed range) | N mean(r²) (seed range) |
|---|---|---|---|
| 250 | 0 | 0.0531–0.0562 | 0.903–0.948 |
| 250 | 1 | 0.0711–0.0833 | 1.619–2.099 |
| 250 | 2 | 0.0916–0.1171 | 2.610–4.127 |
| 250 | 4 | 0.1415–0.1829 | 6.391–10.264 |
| 500 | 0 | 0.0394–0.0409 | 0.963–1.090 |
| 500 | 1 | 0.0508–0.0574 | 1.667–2.098 |
| 500 | 2 | 0.0770–0.0964 | 3.554–5.472 |
| 500 | 4 | 0.1311–0.1591 | 10.382–14.994 |
| 1000 | 0 | 0.0271–0.0280 | 0.946–1.023 |
| 1000 | 1 | 0.0355–0.0390 | 1.673–1.909 |
| 1000 | 2 | 0.0535–0.0602 | 3.689–4.362 |
| 1000 | 4 | 0.0759–0.0999 | 6.929–12.262 |

Mean order decreases with size in both g=1 and g=4 controls, while N mean(r²)
stays above the independent-noise value. This is consistent with amplified
finite-size fluctuations; these sizes cannot establish an asymptotic scaling law.

Rescue baseline seed range: [0.050814782477856826, 0.057425290064178895] (floor 1/sqrt(500)).
epsilon crossing seed range: [0.003798775036041554, 0.0038773837435049337].
K_eff/D crossing seed range: [1.899387518020777, 1.9386918717524668] (reference 2).
Union of sampled epsilon brackets: [0.0037132710668902227, 0.004219997650962095].
Crossing means second-half r=0.2 with all larger samples above it.
Ranges across three seeds and sampled brackets are not confidence intervals.

| Decay (mm) | Conditional E range (mV/mm), gamma=1 |
|---|---|
| 0.1 | 0.56681–0.57854 |
| 0.2 | 0.07085–0.07232 |
| 0.3 | 0.02099–0.02143 |

E_req=K_eff/(gamma N_cortex shift f); all field values scale as 1/gamma.
The gamma=1 numerical convention reproduces the requested Fermi arithmetic.
Gamma must carry the missing inverse-time calibration; this model does not measure it.
The values are below 1–5 mV/mm conditionally, not an independent physical validation.

| K | dt=0.01 mean r (seed range) | dt=0.005 mean r (seed range) |
|---|---|---|
| 1.6 | 0.0906–0.1387 | 0.1121–0.1393 |
| 2.0 | 0.2379–0.2916 | 0.1950–0.2500 |
| 2.4 | 0.5214–0.5513 | 0.5107–0.5524 |

Saved integration runtime for diagnostics, rescue and dt controls: 1166.97 s.
Timestep controls use equal duration and sampling cadence; their noise paths differ.
Three sizes, three seeds and two timesteps do not establish a limiting law.
No Lean, gluing, propagation-of-chaos or dynamical-selection theorem is discharged.
