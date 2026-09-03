# Agent Execution Specification: Spatially Decaying 2D Ephaptic Kernel

**Priority: 2 of 6.** Measured budget on this Pi 5: 4.5 ms/step at
128x128, 19.5 ms/step at 256x256; ~20 min for a 15-value lambda sweep at 128x128.
RAM is single-digit MB. See `simulation_shared_notes.md`.

## Status of the output

Heuristic numerical evidence for the supplement. This closes no Lean gap and
proves nothing. Label the figures accordingly (follow the framing discipline of
`simulations/bifurcation.py`, whose docstring states its figure is "an
illustration of proved statements, not evidence for them"). Do not let the result
move `main.tex:340` or `main.tex:223` from "not established" to "established".

## Objective

Implement a vectorized Python simulation of the stochastic Kuramoto model on a 2D
sheet to test whether macroscopic unity survives realistic spatial decay. Evaluate
whether an exponentially decaying ephaptic coupling kernel
`A_ij = K_0 exp(-||x_i - x_j||/lambda)` still forces a global phase transition, or
whether it fragments into the phase singularities and spiral waves observed in
primate LFP maps.

**Why this one matters most.** It is the only simulation of the five that can go
against the paper. Two live claims depend on it: the Fermi estimate at
`main.tex:266` is explicitly parametric in lambda (empirically 0.1-0.3 mm), and
`main.tex:270` invokes the Townsend/Xu spiral centres as a falsifiable content
test. A fragmented steady state at the empirical lambda ~ 0.2 mm is a real
finding about the framework's own commitment and must be reported as such.

## Mathematical Formulation

* **Spatial substrate.** A 2D discrete grid of size L x L (N = L^2) with periodic
  boundary conditions (flat torus) to prevent edge artifacts. Fix the physical
  extent of the sheet so that lambda can be quoted in mm and compared against the
  0.1-0.3 mm empirical range of `\fermiLamMin`-`\fermiLamMax`.
* **The decaying kernel.** Replace the all-to-all mean-field coupling with a
  kernel decaying exponentially over toroidal distance.
* **System dynamics.** Integrate
  `dtheta_i/dt = omega_i + sum_j A_ij sin(theta_j - theta_i) + eta_i(t)`
  subject to thermodynamic noise D.

### REQUIRED CORRECTION - kernel normalization

**Normalize the kernel so that total per-node coupling is constant across the
sweep:**

```
W_ij  = exp(-d_torus(x_i, x_j) / lambda)          # unnormalized, W_ii = 0
A_ij  = K_0 * W_ij / sum_j W_ij                    # row sums identically K_0
```

Without this, shrinking lambda shrinks the total coupling each node receives, so
the "critical lambda" recovered is nothing but K dropping below K_c = 2D. That
would restate the threshold theorem already proved in
`Phase8_SelfConsistency.lean` rather than say anything about spatial structure.
With row-sum normalization, `lambda -> infinity` reproduces the mean-field limit
(`A_ij -> K_0/N`, giving `K_0 r sin(psi - theta_i)`) and any breakdown at finite
lambda is attributable to geometry alone. This is the single most important fix
in the specification.

Because the grid is shift-invariant, the row sum is the same for every node, so
the normalizer is one scalar: compute `sum_j W_ij` once per lambda.

## Hardware-Specific Implementation (Pi 5)

* **FFT convolution.** Do not build the dense O(N^2) matrix. Express the coupling
  as `Im( exp(-i theta_i) * sum_j A_ij exp(i theta_j) )`; the second factor is a
  2D circular convolution on the torus. Use `scipy.fft.fft2`/`ifft2` for O(N log N)
  per step. **Precompute `fft2(A)` once per lambda outside the time loop** - it is
  lambda-dependent but time-independent, and recomputing it per step roughly
  doubles the cost.
* **Measured cost.** 128x128 (N = 16,384) runs at 4.5 ms/step on this Pi;
  256x256 at 19.5 ms/step. A 20,000-step run is ~90 s at 128x128. A 15-value
  lambda sweep is ~20 min. Prefer 128x128 for the sweep and reserve 256x256 for
  the final publication-quality phase maps if the defect structure looks
  grid-limited.
* **Parameter sweep.** Sweep lambda in grid units from `lambda >> L` (mean-field
  limit) down to `lambda < 1` (disconnected patches), with the sweep points
  logarithmically spaced and at least three points inside the empirical
  0.1-0.3 mm band once converted to physical units. Choose K_0 comfortably above
  K_c = 2D so that the mean-field limit is unambiguously ordered - otherwise a
  null result is confounded with being subcritical.
* **RNG.** `rng.standard_normal(size=(L, L)) * sqrt(2*D*dt)`, drawn fresh each
  step; do not preallocate the whole noise history.

## Required Outputs & Visualizations

1. **Macroscopic order parameter trace.** `r(t)` for each lambda. Identify the
   critical lambda at which global synchronization breaks down. **Mark the finite-N
   floor `r ~ 1/sqrt(N)` (= 0.008 at N = 16,384) as a horizontal line** so that a
   disordered state is not misread as partially ordered.
2. **2D phase map snapshots.** Steady-state `theta(x, y)` under a cyclic colormap
   (`hsv` or `twilight`), one panel per lambda.
3. **Defect tracking.** Locate phase singularities by summing wrapped phase
   differences around each closed 2x2 plaquette and testing for a non-zero
   integer winding number. Wrap each difference into `(-pi, pi]` before summing.
   Plot defect density against lambda alongside `r(t)`; the interesting regime is
   where defect density rises while r falls.
4. **Physical-units readout.** State the critical lambda in mm and place it
   against the measured 0.1-0.3 mm LFP decay range. This is the sentence the
   supplement will actually quote.

## Resolved specification questions

* **Natural frequencies.** Use a non-zero spread (Lorentzian half-width matched to
  `\fermiD` = 1.5 rad/s, or a Gaussian of comparable width). A spatially decaying
  kernel with identical frequencies is an unrealistically easy test - detuning is
  what spiral waves need in order to form.
