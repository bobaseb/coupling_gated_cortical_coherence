# Finite-N propagation-of-chaos diagnostics

## Scope and protocol

This is heuristic numerical evidence at sampled finite sizes, not a proof of
propagation of chaos and not a discharged Lean obligation. The run used 1,000
ensembles, `D=1`, `dt=0.01`, 5,000 Euler--Maruyama steps, seed 20260904 (with a
declared deterministic offset per sweep point), and `N` in 10, 50, 100, 500 and
1,000. Identical natural frequencies were used. `K=1` is the subcritical control
and `K=3` the supercritical case.

Replicas began with their circular sample mean aligned to zero. Pair dependence
was evaluated in the lab frame at the final time. The density comparison instead
uses each oscillator's phase relative to its replica's final mean phase, because
mixing over the unpinned collective angle would make the one-particle lab-frame
density uniform. Joint-versus-product distance uses a four-dimensional
`(cos theta_1, sin theta_1, cos theta_2, sin theta_2)` torus embedding, 64 seeded
random projections, and 30 bootstrap resamples of 250 observations on both sides.
It never calls the cubic exact multidimensional transport solver.

## Results

The subcritical control exhibited the expected finite-size decline. Mean order
fell from 0.3726 at `N=10` to 0.0402 at `N=1000`; absolute circular pair
correlation fell from 0.0458 to 0.0010. The sliced joint-product distance changed
only from 0.0468 to 0.0419, showing that it had reached its matched-sample
estimator floor. Co-rotating density L1 error fell from 0.2640 to 0.1286.

The supercritical run did **not** exhibit the specified unconditional `1/N`
correlation decay. Mean order stabilized near 0.72, but lab-frame circular pair
correlation was 0.5245, 0.4807, 0.5100, 0.4593 and 0.4600 as `N` increased. The
sliced distance decreased modestly from 0.1042 to 0.0812 but remained about twice
the subcritical estimator floor. Thus the unconditional stationary ensemble
retains dependence through its random collective orientation. This is compatible
with conditional or symmetry-quotiented propagation of chaos, but this run did
not measure or establish that different statement.

The co-rotating stationary-density check was positive. At `K=3, N=1000`, measured
`r=0.7208` gave `a=Kr/D=2.1624`; the histogram's L1 error from the corresponding
von Mises density was 0.1291. The Bessel self-consistency residual was 0.00191.
For comparison, at `K=1, N=1000` the finite-size residual from the incoherent
solution was 0.0201.

Saved integration time was 1,622.35 seconds. Ten compact NPZ snapshots, one JSON
summary and one three-panel PNG are stored in this directory. Each snapshot holds
only the two fixed-oscillator samples, the aligned first-oscillator sample and
scalar summaries, never a full phase history.

## Limits

The experiment uses one seed family, one final time and only two coupling values.
The density L1 metric includes histogram and ensemble sampling error, and the
sliced distance has a visible finite-sample floor. Most importantly, spontaneous
rotational symmetry makes unconditional lab-frame independence and conditional
independence modulo collective phase different claims. These finite runs prove
neither form of propagation of chaos and close no theorem or manuscript gap.
