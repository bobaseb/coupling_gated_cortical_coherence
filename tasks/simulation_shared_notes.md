# Shared notes for the six planned Kuramoto simulations

Applies to `dynamic_ramp.md`, `spatially_decaying_kernel.md`,
`dynamical_selection.md`, `propagation_of_chaos.md`,
`overcoming_geometric_frustration.md`, `joint_phases_plasticity.md`. Read this
before implementing any of them.

## What these simulations are for

**None of them closes a gap in the Lean development, and none should be described
as doing so.** They produce heuristic numerical evidence for the supplement.

The repo already holds the right framing discipline: the docstring of
`simulations/bifurcation.py` states that its figure is *"an illustration of proved
statements, not evidence for them."* Keep that standard. Concretely, the following
manuscript sentences must survive these runs unchanged:

* `main.tex:223` - propagation of chaos is *"the missing link"*; *"No theorem in
  this development closes it."*
* `main.tex:340` - *"Of the coherent branch we prove existence, uniqueness,
  continuous emergence at threshold and strict growth in K, but not that it is
  dynamically selected."*
* `Chain.lean` - E45 remains a modelling assumption; E56 and E67 remain physical
  commitments.

A simulation at particular parameter values on a finite N exhibits a phenomenon;
it does not establish it. Figure captions should say which.

## Priority order

Revised after `dynamic_ramp.md` was added - it displaces the decaying kernel from
first place, because it defends the manuscript's sole unique empirical prediction
against an assumption the manuscript itself flags as unquantified
(`supplementary.tex:242`).

| # | Spec | Why |
|---|---|---|
| 1 | `dynamic_ramp.md` | Defends the paper's only unique prediction; `supplementary.tex:242` concedes the time course rests on an unquantified adiabatic assumption. Outcome not foregone |
| 2 | `spatially_decaying_kernel.md` | Can go against the paper; bears on the lambda-parametric Fermi estimate (`main.tex:266`) and the Townsend/Xu spiral test (`main.tex:270`) |
| 3 | `dynamical_selection.md` | Cleanest gap-to-figure mapping; targets `main.tex:340` directly |
| 4 | `propagation_of_chaos.md` | Targets the most-cited open gap (O14(B)), but cannot close it |
| 5 | `overcoming_geometric_frustration.md` | Result is analytically near-certain; value is the mV/mm conversion, not the rescue |
| 6 | `joint_phases_plasticity.md` | Overlaps existing `structural_resonance.py`; blocked on the entropy-production labelling fix |

**Where this differs from Gemini's matrix.** Gemini ranks the frustration rescue
first ("Critical - biological plausibility") and the decaying kernel fourth. The
frustration result is analytically foregone - a uniform positive all-to-all term
is a mean-field coupling of strength `epsilon N`, so it always wins for large N -
and a foregone result does not become critical because reviewers care about
biology. Its value is the mV/mm conversion against the 1-5 mV/mm band, which is
how it has been rewritten. Gemini's placement of the ramp as critical is right and
is adopted here, promoted to first.

## Measured hardware budget (this Pi 5)

Benchmarked directly, numpy 2.4.6 / scipy 1.17.1, 4 cores, 15 GB RAM:

| Kernel | Used by | Measured | Full run |
|---|---|---|---|
| mean-field 500x1000 | dynamical selection | 69 ms/step | ~30 min |
| mean-field 1000x1000 | propagation of chaos | 138 ms/step | ~30-40 min |
| dense 500x500 outer-sine | frustration | 9.7 ms/step | ~30 min |
| FFT conv 128x128 | decaying kernel | 4.5 ms/step | ~20 min |
| FFT conv 256x256 | decaying kernel (optional) | 19.5 ms/step | ~90 min |
| joint (theta, K) N=100 | plasticity | 0.5 ms/step | minutes |
| mean-field 32x2000 | dynamic ramp | 9.4 ms/step | ~2.6 h (slowest ramp leg) |
| mean-field single N=5000 | dynamic ramp (no error bars) | 0.79 ms/step | ~13 min |

Peak RAM is single-digit MB for every one of them; the 16 GB is not a constraint
and no spec needs to economize on memory beyond avoiding time-series
accumulation. The five non-ramp specs total ~2 h sequential, less across the 4
cores; the ramp roughly doubles that, and its four speeds should be run as four
processes, one per core, so its wall clock is the slowest leg alone.

**Two measured traps:**

* `scipy.stats.wasserstein_distance_nd` scales ~n^3.4 here (0.07 s at n=50,
  0.41 s at n=100, 4.2 s at n=200, 48 s at n=400). At n=1000 it is effectively a
  hang. See the correction in `propagation_of_chaos.md`.
* The ramp's step count is set by `1/(v·dt)`. Ramping from deep subcritical
  rather than from `K_c - 0.5` multiplies every leg by 4 for no information. See
  the window correction in `dynamic_ramp.md`.

## Conventions that apply to all five

* **The finite-N floor.** A disordered finite system sits at `r ~ 1/sqrt(N)`, not
  at 0 (0.032 at N=1000, 0.045 at N=500, 0.008 at N=16,384). Draw it as a
  horizontal reference line on every `r(t)` panel. Several of the original specs
  described uniform initialization as enforcing `r = 0`; it does not, and that
  residual fluctuation is what seeds the escape dynamics.
* **Identical vs. spread frequencies.** The von Mises stationary density and the
  `r = I_1(a)/I_0(a)` self-consistency curve are derived for identical
  frequencies. Any run validated against those objects must set `omega = 0`; any
  run that needs realistic detuning (spatial kernel, plasticity) cannot be
  validated against them. State which regime each run is in.
* **Circular quantities.** Never apply `np.cov`, `np.mean` or `np.var` to wrapped
  phases. Use `np.angle(np.mean(np.exp(1j*theta)))` for circular means and the
  Fisher-Lee coefficient for correlations.
* **Estimating the concentration `a` (applies to every run that plots an (a, r)
  collapse).** Use the log-density-slope regression of `main.tex:433`, never the
  von Mises MLE and never the Banerjee approximation. Both are functions of `r`
  alone - the MLE concentration solves `I_1(k)/I_0(k) = r` by definition - so an
  (a, r) trace built from either lies on `I_1(a)/I_0(a)` identically, for any data
  including pure noise. `main.tex:433` calls this out explicitly as a tautology to
  avoid. See `dynamic_ramp.md` Correction 1, and the cross-cutting issue below.
* **Toolchain.** Run under `uv run --directory simulations python ...`, matching
  the existing scripts. The repo lints with ruff (line-length 100, `E,F,W,S`) and
  type-checks with mypy in strict mode (`disallow_untyped_defs`), so annotate
  every function. Seed all RNGs explicitly; prefer
  `np.random.default_rng(seed)` over the legacy global functions.
* **Reuse.** Take the von Mises quadrature helpers from
  `simulations/bifurcation.py` rather than re-deriving `I_1/I_0`, so every figure
  plots the identical object the Lean file proves things about. Take the Fermi
  constants from `simulations/fermi_params.tex` /
  `simulations/fermi_estimate_check.py` rather than retyping them.

## Two bugs found and fixed in `empirical_collapse.py` (2026-09-03)

Found while amending these specs; both are fixed, and the propofol analysis and
the supplement have been re-run and revised.

**1. The concentration estimator made the collapse test vacuous.**
`concentration_a` used `scipy.stats.vonmises.fit` (MLE) with a Banerjee fallback.
The von Mises family is a one-parameter exponential family whose sufficient
statistic is `sum cos(theta)` = r, so every ML estimator solves
`I_1(a)/I_0(a) = r` and the (a, r) pair lies on the curve identically - for any
data, including pure noise. This is not specific to scipy: a Poisson GLM of binned
counts on `cos(theta)` has the same score equation, and the Banerjee closed form
approximates the same inverse. `main.tex:433` already forbade the MLE for exactly
this reason. Replaced with the unweighted log-density OLS regression it specifies;
the MLE survives as `concentration_a_mle` for diagnostics.

**2. The bandpass filter was numerically broken.** `design_bandpass` returned
transfer-function (`b, a`) coefficients and the extractors used `filtfilt`. At the
dataset's 5 kHz sampling rate an EEG passband sits at a very low normalised
frequency and the `ba` form loses catastrophic precision. Measured on white noise:

| band | `ba` + filtfilt | SOS + sosfiltfilt |
|---|---|---|
| 4-8 Hz | NaN | 0.27 |
| 8-12 Hz | NaN | 0.13 |
| 12-30 Hz | finite | finite |
| 4-40 Hz (production band) | **max abs = 4e+37** | 0.44 |

So the band the pipeline actually ran was filtered by a blown-up filter and the
Hilbert phase of that output was not the phase of the signal. Switched to
`butter(..., output="sos")` + `sosfiltfilt`. The supplement's Preprocessing
section already *claimed* `sosfiltfilt`, so this brought the code in line with the
stated method rather than changing the method.

This also explains the supplement's old note that theta and alpha were "near the
noise floor for 20 s of data at 5 kHz; longer recordings or a higher-order filter
would resolve this." They were returning NaN, and a higher order makes `ba`
instability worse. All five bands now collapse.

**Outcome: the collapse holds, and now non-tautologically.** Mean per-chunk
residual `r - I_1(a)/I_0(a)`, bipolar montage, against an estimator noise floor of
0.0024: between -0.0025 and +0.0033 (4-40 Hz), -0.0046 to +0.0046 (alpha),
-0.0016 to +0.0043 (beta) across sub-1016's seven blocks; cross-subject (n=8)
-0.0002 +/- 0.0002 SEM, RMSE 0.0005. The common-reference montage is
systematically negative (-0.041 to -0.003), consistent with volume conduction
adding a common-mode component that lifts r without sharpening the distribution.

**But the test lost most of its discriminating power.** The broken filter was
manufacturing dynamic range. The corrected pipeline gives a in [0.302, 0.542]
across subjects, not the 15-fold span previously reported. Over that short arc
`I_1(a)/I_0(a)` departs from the straight line `a/2` by at most 0.0094 and from
`tanh(a/2)` by at most 0.0030, while per-bin residual scatter is 0.02-0.03. The
data confirm the relation but cannot distinguish the Bessel curve from its own
tangent. Separating them needs a >~ 1.5, where the gap exceeds 0.17 - which is
what a sleep-inertia recovery sweeping through threshold would deliver, and is an
independent argument for `dynamic_ramp.md`.

**Manuscript updated accordingly**: `supplementary.tex` sections "(a, r)
estimation", "Narrowband analysis", "Results" and "Interpretation"; and the
closing sentence of `main.tex:433`. `check_prose`, `check_tableS1` and
`check_leaves` pass; both documents compile.

### A methodological tension still open

`main.tex:433` specifies the phase distribution *across recording sites*
(instantaneous), but `compute_ar_trace` pools 62 channels x 500 time samples
(100 ms). A single instant across 62 sites falls below `MIN_SAMPLES_FOR_A = 100`,
so the specified estimator cannot be run on the specified object with this
montage. Window length turns out not to matter empirically (residual is flat from
5 ms to 100 ms), so nothing is wrong with the numbers - but either the protocol
should ask for more sites or the supplement should say it pools over a window.
