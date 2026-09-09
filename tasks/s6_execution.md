# S6 execution contract — 2026-09-09

Revise structural_resonance.py in place. No Lean changes. First test the
symmetric half-square gradient by finite differences, resource projection,
cluster/control construction, seeded storage, fast/slow cadence, the
matched-norm random arm, the rescaling invariance of the alignment statistics
and the permutation percentile at its two extremes.

Production: N=100, D=0.1, dt=0.01, 40000 steps (400 time units),
K total=400 (mean row coupling 4), eta_K=0.2; update every 50 fast
steps with slow increment eta_K * 50 * dt. Three equal-as-possible clusters
at frequencies 0.5, 1, 1.5 rad/time; no additional frequency jitter.
Seeds 20260906, 20261906, 20262906. Start with narrow normal phases (SD 0.1)
and random symmetric nonnegative hollow K rescaled to the resource budget.
Smoke: N=24, 2000 steps, seed 20260906 before production.

Three arms per seed on one phase-noise stream, the update direction drawn from
a separate stream so the arms differ only in that direction: the gradient step;
a symmetric hollow random matrix rescaled to the gradient's Frobenius norm; and
a frozen kernel. The random arm is what distinguishes the gradient's effect
from the effect of moving a kernel of that step size at fixed total resource,
and at zero learning rate all three arms must reproduce one trajectory.

Denying that dissipation minimization implies representational learning
requires the antecedent to hold in the run, so the descent is measured and not
assumed. Symmetric coupling cancels in the mean drift, fixing sum_i v_i and a
floor N*mean(omega)^2/D on the objective. Report the descent fraction: the
share of the frozen arm's headroom above that floor which an arm removes. The
gradient arm must remove a substantial share of it and the random arm must not.
eta_K is selected by a sweep on one seed over rates 0.001 to 0.4, taking the
rate at which the objective descends furthest subject to the plateau criterion.
The sweep is committed alongside the run. Rates past the minimum lose descent
while still passing the plateau criterion, so the criterion does not select a
rate; this is a declared selection, not a convergence claim.

The environmental covariance is the Gram matrix of one-hot cluster features
(shared unit-variance latent input per cluster), not a measured covariance of
constant frequencies. Hollow and rescale this template to the same budget as K
for distances. Shuffle node labels once per seed, retaining block sizes and
matrix norm. Store both templates and permutation. No covariance of wrapped
phases. The template is diagnostic only, never part of the update.

Frobenius distance to a template confounds alignment with kernel norm, and a
fixed total resource constrains the sum of the entries rather than the norm, so
distance is reported and not relied on. The alignment statistics are the ratio
of mean within-cluster to mean between-cluster coupling and the off-diagonal
correlation with the template, both invariant under rescaling K, together with
a permutation percentile over 2000 relabellings drawn per run. A single shuffle
is one draw from a null whose spread is comparable to the effect and does not
support a chance-baseline claim. Read the gradient arm's percentile against the
frozen arm's, not against the null median: the initial kernel need not sit at
the median. Report the kernel norm growth so the distance readout can be
decomposed.

Measure decimated r, sum(v^2)/D, mean drift, Frobenius distances to true and
shuffled templates, the within-over-between ratio and the template correlation
every 50 steps, plus initial/final K and final phases.
Report second-half means, first/last-quarter dissipation, distance changes,
descent fraction and permutation percentile.
Order maintenance criterion: every sampled r after t=10 exceeds 0.5.
Report each seed without selecting successful seeds.
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
