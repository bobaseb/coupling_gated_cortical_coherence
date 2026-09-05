# S6 execution contract — 2026-09-05

Revise structural_resonance.py in place. No Lean changes. First test the
symmetric half-square gradient by finite differences, resource projection,
cluster/control construction, seeded storage and fast/slow cadence.

Production: N=100, D=0.1, dt=0.01, 40000 steps (400 time units),
K total=400 (mean row coupling 4), eta_K=0.001; update every 50 fast
steps with slow increment eta_K * 50 * dt. Three equal-as-possible clusters
at frequencies 0.5, 1, 1.5 rad/time; no additional frequency jitter.
Seeds 20260906, 20261906, 20262906. Start with narrow normal phases (SD 0.1)
and random symmetric nonnegative hollow K rescaled to the resource budget.
Compare each adaptive trajectory to frozen K with identical initial state and
noise. Smoke: N=24, 2000 steps, seed 20260906 before production.

The environmental covariance is the Gram matrix of one-hot cluster features
(shared unit-variance latent input per cluster), not a measured covariance of
constant frequencies. Hollow and rescale this template to the same budget as K
for distances. Shuffle node labels once per seed, retaining block sizes and
matrix norm. Store both templates and permutation. No covariance of wrapped
phases. The template is diagnostic only, never part of the update.

Measure decimated r, sum(v^2)/D, mean drift, and Frobenius distances to true and
shuffled templates every 50 steps, plus initial/final K and final phases.
Report second-half means, first/last-quarter dissipation and distance changes.
Order maintenance criterion: every sampled r after t=10 exceeds 0.5.
Structural specificity requires the true-template distance reduction to exceed
the shuffled reduction; report each seed without selecting successful seeds.
A stable plateau is operationally a last-quarter mean within 5% of the preceding
quarter; failure is recorded, never remedied by extending/tuning this run.

Symmetric interactions cancel in the mean drift, leaving the nonzero grand
mean. This establishes a driven collective coordinate, not stationarity of the
adaptive process. Squared drift is a dissipation objective, not thermodynamic
entropy production: the latter needs probability current, including density
gradients. Zero-mean heterogeneous torus frequencies need not satisfy detailed
balance either. The conceptual claims in the original spec are corrected by
this contract. No general descent, NESS convergence, resonance or E45 theorem
is claimed. Generate publication macros from saved JSON only, with drift test;
compile the supplement and compare warnings to HEAD; run repository gates.
