# Agent Execution Specification: Overcoming Geometric Frustration via a Modulatory Spatial Kernel

**Priority: 5 of 6.** Measured budget on this Pi 5: 9.7 ms/step for a dense
500x500 step; ~30 min for a 20-value epsilon sweep. RAM ~2 MB. See `simulation_shared_notes.md`.

## Status of the output

Heuristic numerical evidence for the supplement. It closes no Lean gap, and in
particular does not touch the frustration gluing item (F2, the H^1 obstruction),
which is Lean proof work.

## REQUIRED REFRAMING - read before implementing

**As originally specified, the answer is analytically near-certain and the
simulation would be an illustration rather than a test.** A uniform all-to-all
term `E_ij = epsilon` contributes `epsilon * sum_j sin(theta_j - theta_i)
= epsilon N r sin(psi - theta_i)`, i.e. a mean-field coupling of strength
`epsilon N`. So the critical epsilon is simply `~ 2D/N`, and a positive uniform
kernel always wins for large N against a roughly zero-mean random matrix. Running
this to discover "the field rescues synchronization" recovers the threshold
theorem with extra steps.

**What makes it worth running is the number it produces.** Convert the measured
critical epsilon into a field magnitude in mV/mm and check it against the
1-5 mV/mm range the Fermi estimate already relies on (`\fermiFieldMin`,
`\fermiFieldMax` in `simulations/fermi_params.tex`). That turns the run into an
independent consistency check on the paper's own stated falsification condition -
the **Magnitude gap** clause at `main.tex:264`: *"if the spatial integration
required demands field effects an order of magnitude above the 1-5 mV/mm measured
in cortex, the commitment fails on arithmetic."* Frame the objective, the sweep
and the figures around that conversion.

### The conversion to state explicitly

Using the same arithmetic as `main.tex:266` and
`simulations/fermi_estimate_check.py`:

```
K_eff   = N_sim * epsilon_c                       # effective mean-field coupling at threshold
E_req   = K_eff / (N_cortex * shift * f)          # required field, mV/mm
```

with `shift = 0.4e-3` s per mV/mm, `f = 40` Hz (gamma), and
`N_cortex = (4/3) pi lambda^3 rho ≈ 1675` at `lambda = 0.2` mm,
`rho = 5e4` mm^-3. Report `epsilon_c`, `K_eff`, `K_eff/D` against `K_c/D = 2`,
and `E_req` against 1-5 mV/mm. Repeat at the lambda endpoints 0.1 and 0.3 mm,
since the estimate is parametric in lambda.

## Objective

Demonstrate that a weak, continuous, all-to-all positive coupling kernel
(representing the endogenous electromagnetic field) rescues macroscopic
phase-locking in a synaptic network frustrated by inhibitory interneurons, and
**bound the required modulatory field strength in physical units**.

## Mathematical Formulation

* **Synaptic matrix S.** Sparse Erdos-Renyi topology conforming to Dale's
  principle: 80% excitatory presynaptic columns (`S_ij > 0`), 20% inhibitory
  (`S_ij < 0`).
* **Ephaptic kernel E.** Uniform all-to-all positive `E_ij = epsilon > 0`,
  representing the spatially continuous endogenous field.
* **System dynamics.** Integrate the stochastic Kuramoto system with the
  composite coupling `A = S + E`:
  `dtheta_i/dt = omega_i + sum_j A_ij sin(theta_j - theta_i) + eta_i(t)`.

### REQUIRED CORRECTION - the baseline must actually be frustrated

A random E/I matrix with a non-zero row mean synchronizes on its own, and the
`epsilon = 0` panel would then show partial order for reasons having nothing to
do with frustration - making the "rescue" a rescue of nothing. **Enforce
excitatory/inhibitory balance so that `sum_j S_ij ≈ 0` for every i**, i.e. scale
the inhibitory weights by the E:I count ratio (with 80/20 sparsity and equal
per-synapse magnitude, inhibitory weights carry 4x the magnitude of excitatory
ones). Verify numerically before the sweep: print the row-sum distribution and
confirm it is centred on zero, and confirm the `epsilon = 0` run sits at the
finite-N floor `r ~ 1/sqrt(N)` = 0.045 at N = 500. If it does not, the baseline
is not frustrated and the sweep is not measuring what it claims.

This resolves the question the original spec left open at its foot: yes, the
inhibitory magnitude scaling must be specified, and balance is the criterion.

## Hardware-Specific Implementation (Pi 5)

* **Matrix dimensions.** N = 500. A dense 500x500 float64 matrix is 2 MB, so
  O(N^2) broadcasting is fine and `scipy.sparse` overhead is not worth it on ARM.
* **Vectorization.** `theta[:, None] - theta[None, :]`, then
  `np.sum(A * np.sin(phase_diffs), axis=1)`.
* **Measured cost.** 9.7 ms/step at N = 500. A 10,000-step run is ~96 s per
  epsilon; a 20-value sweep is ~32 min.
* **Parameter sweep.** Sweep epsilon from 0 up to where E's total strength
  matches S's positive sum. Since the expected threshold is `~2D/N`, space the
  sweep logarithmically around that value rather than linearly, or most points
  will land far above threshold and the transition will be resolved by one or two
  samples. Reuse preallocated state arrays across the sweep.

## Required Outputs & Visualizations

1. **Frustration baseline.** `r(t)` at `epsilon = 0`, with the `1/sqrt(N)` floor
   drawn as a horizontal line, showing that balanced 20% inhibition prevents
   global synchronization.
2. **Rescue transition.** Steady-state r against epsilon on a log-x axis, with
   the analytically expected threshold `epsilon = 2D/N` marked. A second x-axis
   (top) in mV/mm via the conversion above, with the 1-5 mV/mm measured band
   shaded. **This is the figure the supplement will use.**
3. **Phase distributions.** Two polar histograms of final phases - the scattered
   frustrated state and the phase-locked rescued state.
4. **Numerical readout.** A printed table of `epsilon_c`, `K_eff`, `K_eff/D`, and
   `E_req` at lambda = 0.1, 0.2, 0.3 mm, stated against the 1-5 mV/mm band.
