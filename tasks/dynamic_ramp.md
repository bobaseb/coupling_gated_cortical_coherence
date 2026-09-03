# Agent Execution Specification: Dynamic Sleep-Inertia Ramp and Critical Slowing Down

**Priority: 1 of 6 - run this before any of the others.** Measured budget on this
Pi 5: 9.4 ms/step at 32 replicas x 2000 oscillators; ~2.6 h for the slowest ramp
over the narrowed window below, or the same wall clock for all four speeds if the
sweep is run one-process-per-core. See `simulation_shared_notes.md`.

*(This is the spec that `dynamic_sleep_inertia.md` was named for but did not
contain - that file held the dynamical-selection body and has been renamed
`dynamical_selection.md`.)*

## Why this ranks first

The paper stakes its falsifiability on this one prediction. `main.tex:48` and
`main.tex:63` present sleep-inertia recovery as *"one of its predictions is its
own rather than a rival's"*, and `main.tex:264` makes **Timescale mismatch** one
of the four stated failure conditions.

And the manuscript already concedes, in `supplementary.tex:242`, that the time
course rests on an assumption it never quantifies:

> *"The square-root cusp needs the slow variable to cross threshold at non-zero
> speed (`K̇(t₀) ≠ 0`) ... And the exponent theorem proves no stability or
> dynamical selection - `r = 0` remains a solution above threshold - so the time
> course `r(t)` is carried by the adiabatic assumption, not a trajectory theorem."*

`supplementary.tex:89` says the same: reading the exponent theorem *"as a
square-root foot on a recovery curve requires the adiabatic separation and a
threshold crossing at non-zero speed, both of which the main text states as
assumptions."*

So the paper's sole unique empirical prediction hangs on an adiabaticity
assumption with no stated validity range. This simulation supplies that range.
It is the most exposed load-bearing gap in the manuscript, and unlike the
frustration rescue, its outcome is not foregone: if `v*` lands below the
astrocytic clearance rate, the predicted collapse is smeared and the paper's
discriminator weakens.

## Status of the output

Heuristic numerical evidence for the supplement. It establishes no trajectory
theorem and does not discharge the adiabatic assumption - it bounds the regime in
which that assumption is safe. `supplementary.tex:242` stands unchanged.

## Objective

Quantify dynamic bifurcation delay when the effective coupling `K(t)` ramps
across `K_c = 2D`, and determine the maximum ramp speed `v = K̇` at which the
adiabatic collapse `r = I_1(a)/I_0(a)` survives undistorted.

## Mathematical Formulation

* **Time-dependent system.** `dtheta_i/dt = omega_i + (K(t)/N) sum_j
  sin(theta_j - theta_i) + eta_i(t)` with thermodynamic noise D.
* **Natural frequencies.** Set `omega_i = 0`. The target curve
  `r = I_1(a)/I_0(a)` is the identical-frequency stationary result; with a spread
  neither it nor `K_c = 2D` applies, and the collapse test loses its referent.
* **The linear ramp.** `K(t) = K_start + v t`, crossing `K_c`.

### REQUIRED CORRECTION 1 - the concentration estimator (this one is fatal)

**The spec says "compute the empirical concentration `a(t)` by fitting the
instantaneous phase distribution to a von Mises density." Do not do this.** The
von Mises MLE for the concentration solves

```
I_1(kappa_hat) / I_0(kappa_hat) = r        i.e.   kappa_hat = A^{-1}(r)
```

so `kappa_hat` is by construction the inverse Bessel ratio of the observed
resultant length. Plotting `(kappa_hat, r)` against `r = I_1(a)/I_0(a)` is then
an algebraic identity: the trace lies on the curve exactly, at every ramp speed,
for any data whatsoever - including pure noise. The simulation would report a
perfect collapse at all `v` and establish nothing, and `v*` would be
unmeasurable.

`main.tex:433` states the correct estimator and the reason, in as many words:

> *"The concentration `a` is the slope of the log-density of the same phase
> distribution regressed on `cos θ`, **not the maximum-likelihood estimate**:
> fitting `a` to the resultant length would make the predicted collapse a
> tautology."*

**Use the log-density-slope regression:** histogram the phases into bins, take
`log` of the binned density (with a pseudocount), and regress on `cos(theta -
psi)`; the fitted slope is `a`. It uses the *shape* of the distribution, so
agreement with `I_1/I_0` is a real test of the von Mises form rather than a
restatement of the definition of `r`.

*(See "Cross-cutting issue" below - the existing `empirical_collapse.py` uses the
MLE, so this correction is not only about the new simulation.)*

### REQUIRED CORRECTION 2 - predict the delay, do not merely display it

"Visually demonstrate the rightward shift" is not a test. For a mean-field
pitchfork with linear growth rate `lambda = (K - K_c)/2` ramped as
`K = K_c + v t`, the order parameter escapes the `1/sqrt(N)` fluctuation floor
when `∫ lambda dt ~ ln(1/r_0)`, giving

```
Delta_K(v) = K*(v) - K_c  ≈  sqrt(2 v ln N)
```

i.e. `Delta_K ∝ v^{1/2}` with a `sqrt(ln N)` prefactor. Fit the measured
`Delta_K(v)` on log-log axes and report the exponent against the predicted 1/2,
and vary N over `{500, 2000, 8000}` at fixed `v` to test the `sqrt(ln N)`
dependence. A fitted exponent is checkable; a rightward shift is not.

This also validates the sweep window below: at `v = 1e-2, N = 2000` the predicted
delay is `Delta_K ≈ 0.39`, and at `v = 1e-4` it is `≈ 0.039`.

### REQUIRED CORRECTION 3 - `v*` needs a quantitative criterion and a noise floor

At finite N the trace never lies exactly on the curve, so "definitively tears
away" has to be made numerical. Define the deviation over the crossing window as

```
Dev(v) = RMS over the window of [ r_emp(t) - I_1(a_emp(t))/I_0(a_emp(t)) ]
```

and measure the **finite-N floor** `Dev_0` by running the same pipeline in the
adiabatic limit (`v` at the smallest swept value, or a static run at fixed K).
Define `v*` as the speed at which `Dev(v) = 2 * Dev_0`. Report `Dev_0` explicitly;
without it `v*` is an artifact of the eyeball.

### REQUIRED ADDITION - the onset exponent is the decision-relevant number

`supplementary.tex:250` lists *"an onset preferring exponent 1 over 1/2"* as a
falsifier, and `main.tex:435` specifies the test as *"an onset exponent favouring
1/2 over 1 over the first 30-60 s of recovery."* So the quantity a referee will
actually check is the fitted `beta_eff` in `r(t) ∝ (t - t_0)^{beta_eff}` just
after crossing.

Add this output: fit `beta_eff` on the early foot for each `v`, and plot
`beta_eff` against `v`. Show that `beta_eff -> 1/2` as `v -> 0` and report how
fast it degrades - a ramp fast enough to push `beta_eff` toward 1 would make the
paper's own discriminator fail on its own terms. The spec as pitched omits this
entirely, and it is more directly tied to the manuscript's stated falsifier than
the collapse trace is.

## Hardware-Specific Implementation (Pi 5)

* **Ensemble, not a single trajectory.** The pitched `N = 5000` single run is
  cheap (0.79 ms/step) but `Delta_K` is a *random variable* - the escape time
  depends on the realized fluctuation that seeds it - so one trajectory gives no
  error bar on the very quantity being measured. Use replicas:
  `(M, N) = (32, 2000)` at a measured 9.4 ms/step is the right trade.
* **Narrow the ramp window.** Nothing happens deep in the subcritical regime, and
  the spec's implied full sweep is what makes the step count painful. Start at
  `K_start = K_c - 0.5` and stop once `r` saturates, i.e. a window of
  `Delta_K_total ≈ 1.0` rather than 4. This cuts every leg by 4x and still
  contains the predicted delay at all four speeds (see Correction 2).
* **Measured wall clock** (window `Delta_K = 1.0`, `dt = 0.01`, steps
  `= 1.0/(v·dt)`):

| v | steps | single N=5000 | M=32 x N=2000 | M=64 x N=2000 |
|---|---|---|---|---|
| 1e-1 | 1e3 | <1 min | <1 min | <1 min |
| 1e-2 | 1e4 | <1 min | 1.6 min | 2.9 min |
| 1e-3 | 1e5 | 1.3 min | 16 min | 29 min |
| 1e-4 | 1e6 | 13 min | **156 min** | 289 min |

  Sequential total at `(32, 2000)` is ~3 h. **Run the four speeds as four
  processes, one per core** - wall clock then collapses to the slowest leg,
  ~2.6 h. Without the narrowed window, multiply all of this by 4.
* **Data decimation.** As pitched, and it is right: compute `r(t)` and `a(t)`
  on the fly, append only every ~1000 steps. Output arrays stay in the kilobyte
  range; never store phase history. Note the `a(t)` regression only runs at
  decimated points, so its cost is negligible.
* **Sweep parameterization.** `v in {1e-1, 1e-2, 1e-3, 1e-4}` as pitched. Add
  `v = 1e-5` only if `v*` has not been bracketed by 1e-4 - at 26 h it is an
  overnight-and-then-some run and should not be launched speculatively.

## Required Outputs & Visualizations

1. **Bifurcation delay plot.** `r(t)` against `K(t)` for each `v`, overlaid on
   the static branch `r = R(K, r)` from `simulations/bifurcation.py`. Mark the
   `1/sqrt(N)` floor (0.022 at N = 2000).
2. **Delay scaling.** `Delta_K(v)` on log-log axes with the predicted
   `sqrt(2 v ln N)` overlaid, fitted exponent reported against 1/2, plus the
   N-dependence check.
3. **The (a, r) collapse trace.** Empirical `a(t)` vs `r(t)` per speed,
   superimposed on `r = I_1(a)/I_0(a)` - with `a` from the log-density regression
   (Correction 1), reusing the quadrature helpers in `bifurcation.py` for the
   curve.
4. **Onset exponent.** `beta_eff(v)` with the 1/2 and 1 reference lines.
5. **Critical speed bound, in biological units.** Convert `v*` from
   (coupling / time unit) to physical rate using `D = 1.5` rad/s from
   `simulations/fermi_params.tex`, and state it against the sleep-inertia window
   of `10^2`-`10^3` s (`main.tex:435`) and the seconds-to-minutes astrocytic
   constriction timescale (`main.tex:423`, Xie et al. 2013). **This is the
   sentence the supplement will quote:** either the biological ramp is slower
   than `v*`, and the parameter-free prediction is safe, or it is not, and the
   collapse is smeared by dynamic lag.

## Placement

Gemini's matrix puts this in Main Text §12. That is right if it survives - the
result belongs next to the prediction it defends. If `v*` turns out marginal
against the biological rate, it belongs in the supplement with the assumption
restated more narrowly in the main text. Decide after the run, not before.
