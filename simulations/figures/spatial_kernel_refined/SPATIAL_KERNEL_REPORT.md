# Grid-refinement control for the spatially decaying kernel

This is heuristic evidence from sampled finite systems, not a proof of a phase
transition, a cortical measurement, or evidence discharging a Lean obligation.

The production sweep in `../spatial_kernel/` places its operational coherence
boundary at 0.0140 mm, which on its own 128 x 128 grid is 0.90 lattice
spacings — below one cell, and so below the resolution of the sheet that
measured it. Two things could produce that number: a physical length set by the
coupling, the diffusion and the frequency spread, or an artifact of the
discretisation. They are separated by halving the spacing and asking whether the
boundary in millimetres halves with it.

- Grid: periodic 256 x 256 sheet, 2.0 mm extent (0.0078125 mm spacing)
- Dynamics, seed and criterion: identical to the production sweep — K0 = 8
  rad/s, diffusion = 0.5 rad2/s, Gaussian frequency sigma = 1.5 rad/s, dt =
  0.01, 20,000 steps, seed 20260904, steady r > 0.2
- Sweep: 22 lengths. The production sweep's transition band and the two lengths
  above its crossing, sampled twice — once at the same millimetre values, and
  once at the millimetre values carrying the same lattice-spacing counts, which
  on this sheet are half as long. A boundary fixed in millimetres falls in the
  first set and one fixed in cells falls in the second.

**Result: the boundary does not move with the spacing.** It sits at 0.014126
mm, 1.01 times its value on the coarse sheet, which is 1.81 spacings here
against 0.90 there. Every length in the fixed-cell-count set — 0.0039 to
0.0073 mm, 0.50 to 0.94 spacings — is incoherent on this sheet, so the coarse
sheet's boundary is not reproduced by reproducing its cell counts. The boundary
is a property of the dynamics at these parameters, and the finer sheet resolves
it.

The coherent side is sustained rather than asserted from one sample: steady r is
0.269 at 0.0147 mm and 0.899, 0.909 and 0.940 at 0.0259, 0.0276 and 0.0517 mm.

The transition-local trajectories are metastable and non-monotone on this sheet
as on the coarse one: steady r moves 0.130, 0.242, 0.030, 0.079, 0.257, 0.127,
0.187, 0.171, 0.184 across 0.0078 to 0.0140 mm. The boundary is therefore an
operational crossing under a declared criterion, not a critical-point estimate
with statistical precision.

The control does not resolve seed dependence — both sheets run one seed —
exclude longer-lived metastability, validate the Fermi estimate, or establish
that cortex follows this model.
