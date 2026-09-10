# Spatially decaying kernel report

This is heuristic evidence from sampled finite systems, not a proof of a phase
transition, a cortical measurement, or evidence discharging a Lean obligation.

- Grid: periodic 128 x 128 sheet, 2.0 mm extent (0.015625 mm spacing)
- Dynamics: K0 = 8 rad/s, diffusion = 0.5 rad2/s, Gaussian frequency sigma =
  1.5 rad/s, dt = 0.01, 20,000 steps
- Seed: 20260904, reused across independently initialized decay-length controls
- Sweep: 22 lengths from 0.0078125 to 8.0 mm, including exact 0.1, 0.2 and
  0.3 mm controls and seven transition-local refinement points
- Stored integration runtime: 1,151.8 seconds
- Operational criterion: steady r > 0.2, with the boundary defined as the
  interpolated crossing above which every larger sampled length remains ordered
- Operational boundary: 0.0140 mm

The near-boundary result is metastable and non-monotone: steady r ranges from
0.040 to 0.238 between 0.0085 and 0.0140 mm, then reaches 0.618 at 0.01467 mm.
The empirical controls are coherent in this parameter regime: r = 0.9424,
0.9427 and 0.9427 at 0.1, 0.2 and 0.3 mm, with defect density no larger than
2.5e-6. Thus fragmentation was not observed in the empirical band; the sampled
operational boundary is about sevenfold below its lower edge.

The operational boundary is below this grid's own spacing, so this sweep alone
does not say whether it is a physical length or an artifact of the
discretisation. The refinement control in `../spatial_kernel_refined/` reruns
the transition band and the lengths above it at half the spacing and finds the
boundary unmoved in millimetres (0.014126 mm, 1.81 spacings there), so it is
physical.

The result does not resolve seed dependence, infer a statistically sharp
critical point, exclude longer-lived metastability, validate the Fermi estimate,
or establish that cortex follows this model.
