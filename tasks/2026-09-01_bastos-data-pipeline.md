# Bastos-Style Propofol (a, r) Collapse Pipeline — Plan

> **Goal:** Extract instantaneous phase statistics from a publicly available propofol/anesthesia LFP/EEG dataset during recovery, plot the (a, r) trace against the theoretical curve `r = I₁(a)/I₀(a)`, and test whether the collapse holds.

**Prediction being tested:** At every instant during recovery from propofol-induced unconsciousness, the concentration `a` (log-density slope of the phase distribution) and the coherence `r` (circular resultant length) must lie on the parameter-free curve `r = I₁(a)/I₀(a)`. This is the joint prediction of the von Mises stationary density and the mean-field closure; it is independent of the sleep-inertia timescale prediction.

**Falsification conditions (shared with the main text):** An (a, r) trace departing from I₁/I₀ terminates the framework's claim about the phase distribution. A trace that hugs the curve, even without the full recovery dynamics, supports it.

**Current context:** `simulations/bifurcation.py` already computes I₁/I₀ and the self-consistent `r(K, D)` by quadrature. What we lack is an empirical (a, r) trace to overlay.

---

## Open Question: Which dataset?

The Bastos et al. (2021) eLife paper's data availability statement: *"All data generated or analysed during this study are included in the manuscript and supporting files. Source data files have been provided for all figures and tables."* — the raw multisite LFP recordings may **not** be downloadable as a bulk electrophysiology archive.

**Three candidate data sources, ranked by feasibility:**

| Candidate | Format | Channels | State | Effort to ingest |
|---|---|---|---|---|
| **EEGDash ds005620** (HuggingFace) — repeated propofol awakening, human scalp EEG, 21 subjects | BIDS EEG (.edf/.set) | 32–64 | Anesthesia + recovery | Low (BIDS tools exist) |
| **Allen Neuropixels** — awake/sleep mice, Neuropixels LFP | NWB | 384 | Sleep (not propofol) | Medium |
| **Bastos source data** — if raw LFP `.mat` files were supplemental | Unknown | 64-ch Utah arrays × 4 areas | Propofol + recovery | Unknown availability |

**Recommended first pass:** ds005620 (human scalp EEG during propofol). It's immediate, public, and the prediction is about *any* anesthesia recovery, not specifically macaque LFP. If the collapse holds on human scalp EEG, that's stronger; if it fails, the framework loses before we reach the cortical-depth question.

**If ds005620's scalp EEG lacks sufficient phase resolution:** fall back to a simulation-based figure showing that synthetic data drawn from the von Mises model produces the predicted collapse, while a non-von-Mises alternative (uniform or bimodal) does not. This is still a figure, still testable, and honestly labeled.

---

## Pipeline steps

### Step 1: Verify dataset availability and structure

Download ds005620 metadata and one subject's data. Confirm:
- EEG sampling rate (≥250 Hz needed for Hilbert-based phase)
- Event markers for loss of consciousness (LOC) and recovery of consciousness (ROC)
- Number of channels, reference scheme

**Output:** One-paragraph summary plus notebook that loads and plots a few seconds of data.

### Step 2: Extract instantaneous phase per channel

For each channel:
1. Bandpass filter in a physiologically relevant band (e.g., 8–40 Hz — theta through gamma; the prediction is agnostic to the band insofar as the phase distribution matters)
2. Hilbert transform → analytic signal → instantaneous phase `θ_j(t)`
3. Collect the cross-channel phase vector `θ(t) = (θ_1(t), ..., θ_N(t))` at each time point

### Step 3: Compute (a, r) per time point

For each time `t`:
- **Order parameter r:** `r(t) = |(1/N) Σ exp(i θ_j(t))|` — exactly the Lean definition `order_parameter`
- **Concentration a:** The von Mises log-density is `log p(θ) ∝ a cos(θ - μ) + const`. Regress the histogram bin log-counts on `cos(θ)` across all channels at time `t`. The slope is `a`. (This avoids computing the MLE, which requires iterative solution of `R(a) = r`.)

**Critical methodological note:** `a` via log-density regression and `a` via `R⁻¹(r)` are not the same — the former is a nonparametric estimate, the latter assumes the von Mises ansatz. We use regression-based `a` for the trace and check consistency with the inverse-Bessel route as a cross-validation.

### Step 4: Compute the theoretical curve and overlay

Use `simulations/bifurcation.py`'s `bessel_ratio(a)` function (already battle-tested against the Lean definitions). Over the sampled `a(t)` values:
- Theoretical `r_theory = bessel_ratio(a(t))`
- Plot `(a(t), r(t))` as a scatter trace, color-coded by time (pre-LOC, unconscious, recovery)
- Overlay `r = I₁(a)/I₀(a)` as a solid curve
- Plot `r(t) - bessel_ratio(a(t))` as a residual

### Step 5: Quantitative test

Three criteria:
1. **RMSE** of `r(t)` vs `bessel_ratio(a(t))` — compared to a shuffled-phase null (same marginal distributions, scrambled temporal structure)
2. **Onset detection:** Does the (a, r) trace enter the `1-σ` band of the theoretical curve at the same time as ROC? (The biological hypothesis says yes; a delay of >5 s is problematic.)
3. **Band robustness:** Does the collapse hold across frequency bands (theta, alpha, beta, low-gamma), or is it band-specific? (The framework expects it to hold in any band where phase coherence is measurable.)

### Step 6: Produce figure for manuscript

Output: `figures/empirical_collapse.png` — 2-panel figure:
- **(A)** The (a, r) trace against theoretical curve, color-coded by state
- **(B)** Residual time series around ROC

---

## Files that would change

- `simulations/` — new directory `empirical/` or new file `empirical_collapse.py`
- `requirements.txt` or `pyproject.toml` — add `mne` (for BIDS EEG), `scipy.signal` (already in deps)
- `main.tex` — new subsection in `§5` (The sleep-inertia prediction) reporting the empirical test
- `supplementary.tex` — methods section describing the extraction pipeline

---

## Risks and open questions

| Risk | Mitigation |
|---|---|
| ds005620 scalp EEG has too few channels for reliable cross-channel phase stats | Use channel-wise phase clustering; r computed over available channels (≥8 is meaningful) |
| No clear ROC marker in the dataset | Use the last propofol infusion time + published PK/PD model to estimate recovery window |
| The prediction fails (trace departs from curve) | This is a valid outcome — falsification is the paper's strength. Report honestly. |
| Computational cost of per-time-point Hilbert on 21 subjects × 30 min × 64 ch | Batched processing, one-time cost, under 1 hour on a laptop. |

---

## When this is done

A two-panel figure showing that human propofol recovery EEG phase statistics converge to the theoretical `r = I₁(a)/I₀(a)` curve, with quantitative residuals. This turns the falsifiability-in-principle claim of the current manuscript into an actual data-backed result. The prediction then has *two* empirical handles: the sleep-inertia timescale mismatch (untested, requires a new experiment) and the collapse (tested here, on public data).