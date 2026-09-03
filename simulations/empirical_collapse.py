"""Bastos-style empirical (a, r) collapse pipeline for ds005620 propofol EEG.

Downloads one subject's EEG from the public OpenNeuro S3 mirror, extracts
instantaneous phase via Hilbert transform, and plots the (a, r) trace against
the theoretical r = I₁(a)/I₀(a) curve from von Mises theory.

Usage:
    uv run --directory simulations python simulations/empirical_collapse.py
"""

import os
from matplotlib.axes import Axes

import matplotlib.pyplot as plt
import numpy as np
from scipy.signal import butter, hilbert, sosfiltfilt
from tqdm import tqdm

# ── S3 base URL for the OpenNeuro ds005620 public mirror ──────────────
S3_BASE = "https://s3.amazonaws.com/openneuro.org/ds005620"
SUBJECT = "1016"

# Local cache directory for downloaded EEG files (avoids re-download)
CACHE_DIR = os.path.join(os.path.dirname(__file__), "cache_ds005620")

# Recording blocks: (task, acquisition, runs)
BLOCKS: list[tuple[str, str, int, str]] = [
    # (task, acquisition, run, label)
    ("awake", "EC", 0, "Awake EC"),
    ("awake", "EO", 0, "Awake EO"),
    ("sed", "rest", 1, "Sed run-1"),
    ("sed", "rest", 2, "Sed run-2"),
    ("sed", "rest", 3, "Sed run-3"),
    ("sed2", "rest", 1, "Sed2 run-1"),
    ("sed2", "rest", 2, "Sed2 run-2"),
]

# Bandpass parameters
BAND_LOW = 4.0
BAND_HIGH = 40.0
FILTER_ORDER = 4

# Frequency bands for narrowband analysis
BANDS: dict[str, list[float]] = {
    "theta": [4.0, 8.0],
    "alpha": [8.0, 12.0],
    "beta": [13.0, 30.0],
    "broad": [4.0, 40.0],
}
DEFAULT_BAND = "broad"

# Padding to suppress filter edge artifacts (seconds per side)
PAD_SECONDS = 3.0

# Subsampling: don't compute (a, r) at every sample — every 100 ms = 500 pts at 5 kHz
DECIMATE_FACTOR = 500  # 500 samples × 200 µs = 100 ms per bin

# Minimum phase samples required before `concentration_a` will bin and regress.
MIN_SAMPLES_FOR_A = 100

# Ceiling above which the log-density estimator's pseudocount bias becomes
# material (see the table in `concentration_a`).  Estimates above this are
# reported as out of range rather than trusted.
A_BIAS_VALID_MAX = 4.0


# ══════════════════════════════════════════════════════════════════════
#  BrainVision reader (pure numpy, no MNE dependency)
# ══════════════════════════════════════════════════════════════════════


def _parse_vhdr(text: str) -> dict[str, str]:
    """Parse a BrainVision .vhdr header into a metadata dict."""
    meta: dict[str, str] = {}
    section = ""
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith(";"):
            continue
        if line.startswith("[") and line.endswith("]"):
            section = line[1:-1].strip()
            continue
        if "=" in line:
            key, _, val = line.partition("=")
            key = key.strip()
            val = val.strip()
            meta[f"{section}.{key}"] = val
    return meta


def _s3_url(path: str) -> str:
    return f"{S3_BASE}/sub-{SUBJECT}/eeg/{path}"


def _s3_download(path: str, cache: bool = True, max_bytes: int | None = None) -> bytes:
    """Download a file from the public S3 mirror, with optional disk cache.

    If max_bytes is given, only the first max_bytes are fetched via a Range
    request (useful for partial downloads of large .eeg files).
    """
    import subprocess

    cached = os.path.join(CACHE_DIR, path.replace("/", "_"))
    if cache and os.path.exists(cached):
        with open(cached, "rb") as fh:
            return fh.read()

    os.makedirs(CACHE_DIR, exist_ok=True)
    url = _s3_url(path)

    # Use a generous timeout — .eeg files are ~390 MB
    DL_TIMEOUT = 600

    cmd = ["curl", "-sL", "--connect-timeout", "30", "--max-time", str(DL_TIMEOUT)]
    if max_bytes is not None:
        cmd += ["-r", f"0-{max_bytes - 1}"]
    cmd.append(url)

    result = subprocess.run(  # noqa: S603 — URL built from internal constants only
        cmd, capture_output=True, timeout=DL_TIMEOUT + 30,
    )
    if result.returncode not in (0, 33):
        # exit code 33 means the Range was beyond the file — treat as empty
        raise IOError(
            f"S3 download failed for {url}: "
            f"curl exit {result.returncode}, stderr: {result.stderr.decode()[:200]}"
        )

    if cache:
        with open(cached, "wb") as fh:
            fh.write(result.stdout)
    return result.stdout


def _filenames(task: str, acq: str, run: int) -> tuple[str, str, str]:
    """Return (vhdr_name, eeg_name, vmrk_name) for a recording block."""
    base = f"sub-{SUBJECT}_task-{task}_acq-{acq}"
    if run > 0:
        base += f"_run-{run}"
    return base + "_eeg.vhdr", base + "_eeg.eeg", base + "_eeg.vmrk"


def read_brainvision(
    task: str, acq: str, run: int, max_seconds: float = 60.0,
    pad_seconds: float = 0.0,
) -> tuple[np.ndarray, float]:
    """Download and parse a BrainVision recording from the S3 mirror.

    Reads at most max_seconds + 2*pad_seconds of data (default 60 s). The
    extra padding on each side is discarded after filtering to suppress
    filter edge artifacts. The full vhdr header is always downloaded;
    only the needed portion of the .eeg binary is fetched via Range request.

    Returns (data, fs) where data has shape (n_channels, n_samples_padded)
    and the caller should trim pad_seconds from each side after filtering.
    """
    vhdr_file, eeg_file, _ = _filenames(task, acq, run)

    # Parse header (always download — it's tiny)
    vhdr_raw = _s3_download(vhdr_file).decode("utf-8")
    meta = _parse_vhdr(vhdr_raw)

    n_channels = int(meta["Common Infos.NumberOfChannels"])
    samp_int_us = float(meta["Common Infos.SamplingInterval"])
    fs = 1e6 / samp_int_us

    # Download padded data — extra on both sides for filter edge suppression
    total_seconds = max_seconds + 2.0 * pad_seconds
    n_samp_target = int(fs * total_seconds)
    bytes_per_sample = n_channels * 4  # 4 bytes per float32 per channel
    n_bytes = n_samp_target * bytes_per_sample

    # Download truncated binary data via Range request
    eeg_raw = _s3_download(eeg_file, max_bytes=n_bytes)

    n_samp_actual = len(eeg_raw) // (4 * n_channels)
    data = np.frombuffer(eeg_raw, dtype=np.float32).reshape(
        n_samp_actual, n_channels
    ).T  # shape (n_ch, n_samp_actual)

    print(f"    {n_channels} ch × {n_samp_actual} samples "
          f"({n_samp_actual / fs:.1f} s @ {fs:.0f} Hz, "
          f"pad={pad_seconds:.0f}s per side)")

    return data, fs


# ══════════════════════════════════════════════════════════════════════
#  Phase extraction
# ══════════════════════════════════════════════════════════════════════


def design_bandpass(
    low: float, high: float, fs: float, order: int = 4,
) -> np.ndarray:
    """Butterworth bandpass as second-order sections (SOS).

    SOS rather than transfer-function (b, a) coefficients, and the difference
    is not cosmetic at this sampling rate.  These recordings are 5 kHz, so an
    EEG passband sits at a very low normalised frequency, and the `ba` form
    loses catastrophic precision when its poles cluster near z = 1.  Measured
    on white noise at fs = 5000, `filtfilt` with `ba` coefficients returns:

        4-8 Hz    NaN
        8-12 Hz   NaN
        12-30 Hz  finite
        30-40 Hz  finite
        4-40 Hz   max|y| = 4e+37   (SOS gives 0.44)

    So the 4-40 Hz band this pipeline actually uses was being filtered by a
    numerically blown-up filter, and the Hilbert phase of that output is not
    the phase of the signal.  `sosfiltfilt` is stable across all of these.
    """
    nyq = 0.5 * fs
    sos = butter(order, [low / nyq, high / nyq], btype="band", output="sos")
    return np.asarray(sos, dtype=np.float64)


def extract_phase(
    data: np.ndarray, fs: float, low: float = BAND_LOW, high: float = BAND_HIGH,
    pad_seconds: float = 0.0,
) -> np.ndarray:
    """Apply bandpass filter + Hilbert transform to each channel.

    If pad_seconds > 0, the input data has extra samples on each side that
    are trimmed after filtering to suppress edge artifacts.

    Returns phase array of shape (n_channels, n_samples) where n_samples
    is the original length minus 2 * pad_seconds * fs.
    """
    sos = design_bandpass(low, high, fs)
    n_pad = int(pad_seconds * fs) if pad_seconds > 0 else 0

    # Only use scalp EEG channels (indices 0-61), skip EOG/EMG
    eeg_idx = np.arange(62)

    # Output trimmed to the target window (middle portion)
    n_out = data.shape[1] - 2 * n_pad
    phase = np.empty((data.shape[0], n_out))
    phase[:] = np.nan

    for idx in tqdm(eeg_idx, desc="Hilbert phase"):
        # Detrend, filter the full (padded) signal
        d = data[idx] - data[idx].mean()
        filtered = sosfiltfilt(sos, d)
        analytic = hilbert(filtered)
        # Trim padding
        trimmed = np.angle(analytic[n_pad:data.shape[1] - n_pad] if n_pad > 0 else analytic)
        phase[idx] = trimmed

    return phase


# ══════════════════════════════════════════════════════════════════════
#  Alternative montages (volume-conduction diagnostics)
# ══════════════════════════════════════════════════════════════════════


def extract_phase_bipolar(
    data: np.ndarray, fs: float, low: float = BAND_LOW, high: float = BAND_HIGH,
) -> np.ndarray:
    """Bandpass + Hilbert on bipolar pairs (adjacent-channel difference).

    Forms 61 bipolar pairs from the 62 scalp EEG channels (posterior→anterior
    ordering).  The difference signal kills the common reference and localises
    phase to nearby neural sources.

    Returns phase array of shape (n_pairs, n_samples).
    """
    sos = design_bandpass(low, high, fs)
    eeg = data[:62]  # scalp only
    # 61 adjacent pairs: ch0-ch1, ch1-ch2, ..., ch60-ch61
    n_pairs = 61
    phase = np.empty((n_pairs, data.shape[1]))
    phase[:] = np.nan

    for i in tqdm(range(n_pairs), desc="Bipolar phase"):
        diff = eeg[i] - eeg[i + 1]
        filtered = sosfiltfilt(sos, diff)
        phase[i] = np.angle(hilbert(filtered))

    return phase


def extract_phase_car(
    data: np.ndarray, fs: float, low: float = BAND_LOW, high: float = BAND_HIGH,
    pad_seconds: float = 0.0,
) -> np.ndarray:
    """Common-average reference in phase space (circular-mean subtraction).

    Standard phase extraction, then subtract the instantaneous circular mean
    across all channels at each time point:
        θ_j'(t) = θ_j(t) - arg( Σ_k exp(i θ_k(t)) )
    This removes any global phase offset that all channels share (e.g. volume
    conduction from a deep common source).

    Returns phase array same shape as input.
    """
    phase_raw = extract_phase(data, fs, low, high, pad_seconds=pad_seconds)
    eeg_phase = phase_raw[:62]  # scalp only

    # Circular mean: z_bar = (1/N) Σ exp(iθ), circular_mean = arg(z_bar)
    z = np.nansum(np.exp(1j * eeg_phase), axis=0)
    n_valid = np.sum(~np.isnan(eeg_phase), axis=0)
    z /= np.maximum(n_valid, 1)
    common = np.angle(z)

    # Subtract common from each channel
    corrected = eeg_phase - common[np.newaxis, :]
    # Wrap back to [-π, π)
    corrected = np.angle(np.exp(1j * corrected))

    phase_raw[:62] = corrected
    return phase_raw


# ══════════════════════════════════════════════════════════════════════
#  (a, r) computation & uncertainty
# ══════════════════════════════════════════════════════════════════════


def bootstrap_ar(
    a_trace: np.ndarray, r_trace: np.ndarray,
    n_resamples: int = 2000, ci: float = 0.95,
) -> tuple[float, float, float, float, float, float]:
    """Bootstrap CI for mean (a, r) over time bins.

    Returns (a_mean, a_lo, a_hi, r_mean, r_lo, r_hi) where lo/hi are
    the (1-ci)/2 and (1+ci)/2 percentiles of the bootstrap distribution.
    """
    mask = ~(np.isnan(a_trace) | np.isnan(r_trace))
    a_ok, r_ok = a_trace[mask], r_trace[mask]
    n = len(a_ok)
    if n < 10:
        return (float(np.nanmean(a_trace)),)*6

    rng = np.random.default_rng(2026)
    a_boot = np.empty(n_resamples)
    r_boot = np.empty(n_resamples)
    for i in range(n_resamples):
        idx = rng.integers(0, n, n)
        a_boot[i] = np.mean(a_ok[idx])
        r_boot[i] = np.mean(r_ok[idx])

    p_lo = 100.0 * (1.0 - ci) / 2.0
    p_hi = 100.0 * (1.0 + ci) / 2.0
    a_m = float(np.mean(a_ok))
    r_m = float(np.mean(r_ok))
    a_l, a_h = map(float, np.percentile(a_boot, [p_lo, p_hi]))
    r_l, r_h = map(float, np.percentile(r_boot, [p_lo, p_hi]))
    return a_m, a_l, a_h, r_m, r_l, r_h


def order_parameter_r(phase: np.ndarray) -> float:
    """Circular resultant length r = |(1/N) Σ exp(iθ_j)|."""
    N = np.sum(~np.isnan(phase))
    if N < 8:
        return np.nan
    z = np.nansum(np.exp(1j * phase)) / N
    r = float(np.abs(z))
    return min(r, 1.0)  # guard against floating-point overshoot


def concentration_a(phase: np.ndarray, n_bins: int = 40) -> float:
    r"""Estimate von Mises concentration `a` as the log-density slope on cos θ.

    This is the estimator `main.tex:433` specifies, and the choice is forced.
    The collapse test asks whether the empirical pair (a, r) lies on
    r = I₁(a)/I₀(a).  For that question to have content, `a` must be estimated
    from information the resultant length `r` does not already contain.

    **Why maximum likelihood cannot be used.**  The von Mises family is a
    one-parameter exponential family whose sufficient statistic is Σ cos θ,
    i.e. exactly r.  Any maximum-likelihood fit therefore solves

        I₁(â)/I₀(â) = r          (the MLE score equation)

    so â = A⁻¹(r) identically, and plotting (â, r) against r = I₁(a)/I₀(a)
    reproduces the curve for *any* input whatsoever — including pure noise.
    This is not a quirk of `scipy.stats.vonmises.fit`: it holds for every ML
    estimator of the family, including a Poisson GLM of the binned counts on
    cos θ, whose score equation is the same one.  It is equally true of the
    Banerjee et al. (2005) approximation r(2−r²)/(1−r²), which is a closed
    form for the same inverse.  `main.tex:433` states the consequence: fitting
    `a` to the resultant length "would make the predicted collapse a tautology".

    **What this estimator does instead.**  Bin the phases, take the log of the
    binned density, and regress on cos θ by *unweighted* ordinary least
    squares.  Under the von Mises model log ρ(θ) = a cos θ − log(2π I₀(a)), so
    the slope is `a`.  Weighting the bins by their counts would recover the ML
    score equation and reinstate the tautology, so the regression must stay
    unweighted: equal weight per bin is what makes the estimate depend on the
    *shape* of the distribution rather than on its first trigonometric moment.

    **Bias.**  The pseudocount makes this estimator mildly biased, which is a
    real cost and was the reason the MLE was originally used here.  Measured
    against 200 synthetic replicates at this pipeline's actual per-bin sample
    size (62 channels × 500 samples = 31,000 phases, n_bins=40), the bias is
    negligible over the range the data occupy:

        a_true   0.2    0.5    1.0    1.5    2.0    3.0     5.0
        bias    0.000 -0.002 -0.001 -0.001  0.000 -0.007  -0.375
        sd      0.008  0.008  0.011  0.015  0.023  0.048   0.080

    It is under 0.01 up to a ≈ 3 and becomes material only above a ≈ 4, where
    the distribution's troughs empty out and the pseudocount dominates them.
    `A_BIAS_VALID_MAX` records that ceiling; `run_estimator_validation` checks
    it, and callers should report any estimate above it as out of range rather
    than trusting it.  Accuracy of â is in any case the wrong thing to
    optimise here: a mildly biased shape-sensitive estimator yields a valid
    test, while an unbiased function of r yields none.

    Returns NaN when there are too few samples to bin, so the point is dropped
    downstream rather than entering the trace as a spurious a = 0.
    """
    theta = phase[~np.isnan(phase)]
    if theta.size < MIN_SAMPLES_FOR_A:
        return float("nan")

    # Centre on the circular mean so the regressor is cos(θ − ψ).
    psi = np.angle(np.mean(np.exp(1j * theta)))
    centred = np.angle(np.exp(1j * (theta - psi)))

    counts, edges = np.histogram(centred, bins=n_bins, range=(-np.pi, np.pi))
    centres = 0.5 * (edges[1:] + edges[:-1])

    # Pseudocount keeps empty troughs finite; the constant normaliser is
    # absorbed into the intercept and does not affect the slope.
    density = (counts + 0.5) / (counts.sum() + 0.5 * n_bins)
    slope = float(np.polyfit(np.cos(centres), np.log(density), 1)[0])

    # Guard the upper end only.  A negative slope means the phases are
    # anti-clustered relative to their own mean, which is a genuine departure
    # from the von Mises form; clipping it to zero would hide exactly the
    # deviation this estimator exists to detect.
    return min(slope, 50.0)


def concentration_a_mle(phase: np.ndarray) -> float:
    """Von Mises MLE concentration.  Retained for diagnostics only.

    NOT for use in the collapse test — it is a deterministic function of the
    resultant length and makes that test vacuous.  See `concentration_a` for
    the argument, and `run_estimator_validation` for the demonstration.
    """
    from scipy.stats import vonmises

    theta = phase[~np.isnan(phase)]
    if theta.size < MIN_SAMPLES_FOR_A:
        return float("nan")
    try:
        _, kappa = vonmises.fit(theta, fscale=1.0)
        if np.isfinite(kappa) and kappa > 0.0:
            return float(min(kappa, 50.0))
    except Exception:  # noqa: S110 — MLE best-effort, falls back to Banerjee approx
        pass
    r = float(np.abs(np.mean(np.exp(1j * theta))))
    if r < 1e-12:
        return 0.0
    a_approx = r * (2.0 - r ** 2) / (1.0 - r ** 2)
    if not np.isfinite(a_approx) or a_approx < 0:
        return 0.0
    return float(min(a_approx, 50.0))


def compute_ar_trace(
    phase: np.ndarray, decimate: int = DECIMATE_FACTOR
) -> tuple[np.ndarray, np.ndarray]:
    """Compute (a, r) at subsampled time points.

    Returns (a_trace, r_trace), each of shape (n_bins,).
    """
    n_samples = phase.shape[1]
    n_bins = n_samples // decimate

    a_trace = np.empty(n_bins)
    r_trace = np.empty(n_bins)

    for i in tqdm(range(n_bins), desc="(a, r) bins"):
        start = i * decimate
        end = start + decimate
        chunk = phase[:, start:end]
        r_trace[i] = order_parameter_r(chunk)
        a_trace[i] = concentration_a(chunk)

    return a_trace, r_trace


# ══════════════════════════════════════════════════════════════════════
#  Theoretical curve from bifurcation.py
# ══════════════════════════════════════════════════════════════════════


# Quadrature grid on [-π, π] — copied from bifurcation.py to keep this
# script self-contained.
_N_QUAD = 4001
_THETA = np.linspace(-np.pi, np.pi, _N_QUAD)


def bessel_ratio(a: float) -> float:
    """R(a) = I₁(a)/I₀(a), the mean of cos θ under the von Mises weight."""
    c = np.cos(_THETA)
    w = np.exp(a * c - abs(a))
    Z = float(np.trapezoid(w, _THETA))
    M = float(np.trapezoid(c * w, _THETA))
    return M / Z


# ══════════════════════════════════════════════════════════════════════
#  Figure
# ══════════════════════════════════════════════════════════════════════


def make_figure(
    traces: dict[str, tuple[np.ndarray, np.ndarray]],
    out_path: str = "figures/empirical_collapse.png",
) -> None:
    """Produce the two-panel (a, r) collapse figure.

    Panel (A): scatter of (a, r) per block + theoretical curve.
    Panel (B): residual r - I₁/I₀(a) as a time series.
    """
    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)

    # Theoretical curve sampled densely
    a_theory = np.linspace(0, 10, 200)
    r_theory = np.array([bessel_ratio(ai) for ai in a_theory])

    colors = {
        "Awake EC": "#1f77b4",
        "Awake EO": "#2ca02c",
        "Sed run-1": "#d62728",
        "Sed run-2": "#ff7f0e",
        "Sed run-3": "#9467bd",
        "Sed2 run-1": "#8c564b",
        "Sed2 run-2": "#e377c2",
        "Sed2 run-3": "#7f7f7f",
    }

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5.2))

    # Panel A: (a, r) scatter + theoretical curve
    ax1.plot(
        a_theory, r_theory, color="black", lw=2.5,
        label=r"$r = I_1(a)/I_0(a)$",
    )
    for label, (a_trace, r_trace) in traces.items():
        ax1.scatter(
            a_trace, r_trace, s=1.0, alpha=0.15,
            color=colors.get(label, "gray"), label=label,
        )
    ax1.set_xlabel(r"concentration $a$")
    ax1.set_ylabel(r"order parameter $r$")
    ax1.set_xlim(0, 5)
    ax1.set_ylim(-0.02, 1.02)
    ax1.legend(fontsize=7, markerscale=4, framealpha=0.9)
    ax1.set_title("(A)  Empirical (a, r) vs. theoretical collapse")
    ax1.grid(alpha=0.3)

    # Panel B: Residuals
    for label, (a_trace, r_trace) in traces.items():
        r_pred = np.array([bessel_ratio(ai) for ai in a_trace])
        residual = r_trace - r_pred
        x = np.arange(len(residual))
        ax2.scatter(
            x, residual, s=0.5, alpha=0.1,
            color=colors.get(label, "gray"), label=label,
        )
    ax2.axhline(0, color="black", ls="--", lw=1.0)
    ax2.set_xlabel("time bin")
    ax2.set_ylabel(r"$r - I_1(a)/I_0(a)$")
    ax2.set_title("(B)  Residuals")
    ax2.legend(fontsize=7, markerscale=4, framealpha=0.9)
    ax2.grid(alpha=0.3)

    fig.suptitle(
        f"ds005620 {SUBJECT} — {BAND_LOW:.0f}–{BAND_HIGH:.0f} Hz band",
        fontsize=11,
    )
    fig.tight_layout()
    fig.savefig(out_path, dpi=200)
    print(f"Saved {out_path}")
    plt.close(fig)


# ══════════════════════════════════════════════════════════════════════
#  Montage comparison (volume-conduction test)
# ══════════════════════════════════════════════════════════════════════


def run_montage_comparison(
    task: str = "sed", acq: str = "rest", run: int = 1,
    max_seconds: float = 20.0,
    out: str = "figures/montage_comparison.png",
) -> None:
    """Compare (a, r) traces across montages on one block.

    Runs raw, bipolar, and CAR (common-average reference in phase space)
    on the same data and overlays their (a, r) traces against theory.
    Mean points shown with 95 % bootstrap CI error bars.
    """
    print("─" * 60)
    print(f"Montage comparison: {task}_{acq} run-{run}, {max_seconds}s")
    print("─" * 60)

    data, fs = read_brainvision(task, acq, run, max_seconds, pad_seconds=PAD_SECONDS)
    raw_traces: dict[str, tuple[np.ndarray, np.ndarray]] = {}
    cis: dict[str, tuple[float, float, float, float, float, float]] = {}

    print("  Raw scalp reference...", flush=True)
    a_raw, r_raw = compute_ar_trace(extract_phase(data, fs, pad_seconds=PAD_SECONDS))
    raw_traces["raw"] = (a_raw, r_raw)
    cis["raw"] = bootstrap_ar(a_raw, r_raw)
    print(f"    a={cis['raw'][0]:.3f} [{cis['raw'][1]:.3f}, {cis['raw'][2]:.3f}]  "
          f"r={cis['raw'][3]:.3f} [{cis['raw'][4]:.3f}, {cis['raw'][5]:.3f}]")

    # Bipolar
    print("  Bipolar pairs...", flush=True)
    a_bip, r_bip = compute_ar_trace(extract_phase_bipolar(data, fs))
    raw_traces["bipolar"] = (a_bip, r_bip)
    cis["bipolar"] = bootstrap_ar(a_bip, r_bip)
    print(f"    a={cis['bipolar'][0]:.3f} [{cis['bipolar'][1]:.3f}, {cis['bipolar'][2]:.3f}]  "
          f"r={cis['bipolar'][3]:.3f} [{cis['bipolar'][4]:.3f}, {cis['bipolar'][5]:.3f}]")

    # CAR phase
    print("  Circular-mean subtraction...", flush=True)
    a_car, r_car = compute_ar_trace(extract_phase_car(data, fs))
    raw_traces["car"] = (a_car, r_car)
    cis["car"] = bootstrap_ar(a_car, r_car)
    print(f"    a={cis['car'][0]:.3f} [{cis['car'][1]:.3f}, {cis['car'][2]:.3f}]  "
          f"r={cis['car'][3]:.3f} [{cis['car'][4]:.3f}, {cis['car'][5]:.3f}]")

    # Figure: 3-panel
    fig, axes = plt.subplots(1, 3, figsize=(15, 4.6))

    colors = {"raw": "#1f77b4", "bipolar": "#d62728", "car": "#2ca02c"}
    labels_out = {"raw": "Raw", "bipolar": "Bipolar", "car": "CAR"}
    montage_order = ["raw", "bipolar", "car"]

    # Panel A — (a, r) scatter with error bars
    for label in montage_order:
        a_tr, r_tr = raw_traces[label]
        axes[0].scatter(a_tr, r_tr, s=0.8, alpha=0.08, color=colors[label])
    for label in montage_order:
        ci = cis[label]
        axes[0].errorbar(ci[0], ci[3],
                         xerr=[[ci[0] - ci[1]], [ci[2] - ci[0]]],
                         yerr=[[ci[3] - ci[4]], [ci[5] - ci[3]]],
                         fmt="o", color=colors[label], ecolor=colors[label],
                         capsize=4, capthick=1.5, ms=6, zorder=5,
                         label=labels_out[label])

    # Theoretical curve
    a_grid = np.linspace(0, 5, 200)
    r_grid = np.array([bessel_ratio(ai) for ai in a_grid])
    axes[0].plot(a_grid, r_grid, "k-", lw=2.5, label=r"$I_1/I_0(a)$", zorder=4)

    axes[0].set_xlabel(r"$a$")
    axes[0].set_ylabel(r"$r$")
    axes[0].set_xlim(0, 2)
    axes[0].set_ylim(-0.02, 1.02)
    axes[0].legend(fontsize=7, markerscale=4, framealpha=0.9)
    axes[0].set_title("(A)  (a, r) — 95 % CI error bars")
    axes[0].grid(alpha=0.3)

    # Panel B — r time trace with rolling mean + CI band
    for label in montage_order:
        a_tr, r_tr = raw_traces[label]
        x = np.arange(len(r_tr))
        # Rolling mean, window=11
        w = 11
        w2 = w // 2
        pad = np.full(w2, np.nan)
        r_roll = np.concatenate([pad, np.convolve(r_tr, np.ones(w)/w, mode="valid"), pad])
        # Bootstrap per-bin CI (2000 resamples of the phase distribution is too expensive
        # per bin; use ±1.96 × SEM from the bootstrap of the mean instead)
        r_sd = np.nanstd(r_tr)
        axes[1].plot(x, r_roll, color=colors[label], lw=0.8, alpha=0.8,
                     label=labels_out[label])
        axes[1].fill_between(x, r_roll - r_sd, r_roll + r_sd,
                             color=colors[label], alpha=0.08)

    axes[1].set_xlabel("time bin")
    axes[1].set_ylabel(r"$r$")
    axes[1].set_title("(B)  r(t) — rolling mean ± 1 SD")
    axes[1].legend(fontsize=7, framealpha=0.9)
    axes[1].grid(alpha=0.3)

    # Panel C — a time trace with rolling mean + CI band
    for label in montage_order:
        a_tr, r_tr = raw_traces[label]
        x = np.arange(len(a_tr))
        w = 11
        w2 = w // 2
        a_roll = np.concatenate([np.full(w2, np.nan),
                                 np.convolve(a_tr, np.ones(w)/w, mode="valid"),
                                 np.full(w2, np.nan)])
        a_sd = np.nanstd(a_tr)
        axes[2].plot(x, a_roll, color=colors[label], lw=0.8, alpha=0.8,
                     label=labels_out[label])
        axes[2].fill_between(x, a_roll - a_sd, a_roll + a_sd,
                             color=colors[label], alpha=0.08)

    axes[2].set_xlabel("time bin")
    axes[2].set_ylabel(r"$a$")
    axes[2].set_title("(C)  a(t) — rolling mean ± 1 SD")
    axes[2].legend(fontsize=7, framealpha=0.9)
    axes[2].grid(alpha=0.3)

    fig.suptitle(
        f"Montage comparison — sub-{SUBJECT} {task} run-{run} "
        f"({BAND_LOW:.0f}–{BAND_HIGH:.0f} Hz)",
        fontsize=11,
    )
    fig.tight_layout()
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    fig.savefig(out, dpi=200)
    print(f"\nSaved {out}")
    plt.close(fig)

    # Table with CIs
    print(f"\n{'Montage':>10s}  {'a_mean':>7s}  {'a_lo':>7s}  {'a_hi':>7s}  "
          f"{'r_mean':>7s}  {'r_lo':>7s}  {'r_hi':>7s}")
    print("-" * 65)
    for label in montage_order:
        if label in cis:
            ci = cis[label]
            print(f"{label:>10s}  {ci[0]:7.3f}  {ci[1]:7.3f}  {ci[2]:7.3f}  "
                  f"{ci[3]:7.3f}  {ci[4]:7.3f}  {ci[5]:7.3f}")


# ══════════════════════════════════════════════════════════════════════
#  Band comparison (narrowband diagnostics)
# ══════════════════════════════════════════════════════════════════════


def run_band_comparison(
    task: str = "sed", acq: str = "rest", run: int = 1,
    max_seconds: float = 20.0,
    bands: list[str] | None = None,
    out: str = "figures/band_comparison.png",
) -> None:
    """Compare (a, r) across frequency bands for one block.

    Runs the full pipeline on theta (4-8), alpha (8-12), beta (13-30),
    and broad (4-40) bands using the same data.
    """
    if bands is None:
        bands = ["theta", "alpha", "beta", "broad"]

    print("─" * 60)
    print(f"Band comparison: {task}_{acq} run-{run}, {max_seconds}s")
    print(f"Bands: {bands}")
    print("─" * 60)

    data, fs = read_brainvision(task, acq, run, max_seconds, pad_seconds=PAD_SECONDS)

    fig, axes = plt.subplots(1, 3, figsize=(15, 4.6))
    band_colors = {"theta": "#1f77b4", "alpha": "#2ca02c", "beta": "#d62728", "broad": "gray"}
    results: dict[str, tuple[float, float, float, float, float, float]] = {}

    for band in bands:
        lo, hi = BANDS[band]
        print(f"\n  {band} ({lo:.0f}–{hi:.0f} Hz)...", flush=True)
        phase = extract_phase(data, fs, lo, hi, pad_seconds=PAD_SECONDS)
        a_tr, r_tr = compute_ar_trace(phase)
        a_m, a_lo, a_hi, r_m, r_lo, r_hi = bootstrap_ar(a_tr, r_tr)
        results[band] = (a_m, a_lo, a_hi, r_m, r_lo, r_hi)
        r_theory = bessel_ratio(a_m)
        print(f"    a={a_m:.3f} [{a_lo:.3f}, {a_hi:.3f}]  "
              f"r={r_m:.3f} [{r_lo:.3f}, {r_hi:.3f}]  "
              f"I₁/I₀(a)={r_theory:.3f}")

        # (a, r) scatter
        axes[0].scatter(a_tr, r_tr, s=0.6, alpha=0.1, color=band_colors.get(band, "gray"))
        axes[0].errorbar(a_m, r_m,
                         xerr=[[a_m - a_lo], [a_hi - a_m]],
                         yerr=[[r_m - r_lo], [r_hi - r_m]],
                         fmt="o", color=band_colors.get(band, "gray"),
                         capsize=4, capthick=1.5, ms=7, zorder=5,
                         label=f"{band} ({lo}–{hi} Hz)")

        # Residual
        resid = r_m - r_theory
        axes[1].bar(band, resid, color=band_colors.get(band, "gray"), alpha=0.7,
                    yerr=[[r_m - r_lo], [r_hi - r_m]])

    # Theory curve on panel A
    a_grid = np.linspace(0, 3, 200)
    axes[0].plot(a_grid, [bessel_ratio(ai) for ai in a_grid], "k-", lw=2.5,
                 label=r"$I_1/I_0(a)$", zorder=4)
    axes[0].set(xlabel=r"$a$", ylabel=r"$r$", xlim=(0, 1.5), ylim=(-0.02, 1.02))
    axes[0].legend(fontsize=7, markerscale=4, framealpha=0.9)
    axes[0].set_title("(A)  (a, r) per band — 95 % CI")
    axes[0].grid(alpha=0.3)

    axes[1].axhline(0, color="black", ls="--", lw=1)
    axes[1].set(xlabel="band", ylabel=r"$r - I_1/I_0(a)$")
    axes[1].set_title("(B)  Residual by band")
    axes[1].grid(alpha=0.3)

    # Panel C: a and r as bar plot
    x = np.arange(len(bands))
    w = 0.35
    a_vals = [results[b][0] for b in bands]
    r_vals = [results[b][3] for b in bands]
    axes[2].bar(x - w/2, a_vals, w, color="steelblue", alpha=0.7, label=r"$a$")
    axes[2].bar(x + w/2, r_vals, w, color="firebrick", alpha=0.7, label=r"$r$")
    axes[2].set_xticks(x)
    axes[2].set_xticklabels(bands)
    axes[2].set_title("(C)  Mean a and r per band")
    axes[2].legend(fontsize=7)
    axes[2].grid(alpha=0.3)

    fig.suptitle(f"Band comparison — sub-{SUBJECT} {task} run-{run}", fontsize=11)
    fig.tight_layout()
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    fig.savefig(out, dpi=200)
    print(f"\nSaved {out}")
    plt.close(fig)

    # Table
    print(f"\n{'Band':>8s}  {'a_mean':>7s}  {'a_lo':>7s}  {'a_hi':>7s}  "
          f"{'r_mean':>7s}  {'r_lo':>7s}  {'r_hi':>7s}  {'I₁/I₀':>7s}  {'resid':>7s}")
    print("-" * 80)
    for band in bands:
        if band in results:
            a_m, a_lo, a_hi, r_m, r_lo, r_hi = results[band]
            r_theory = bessel_ratio(a_m)
            print(f"{band:>8s}  {a_m:7.3f}  {a_lo:7.3f}  {a_hi:7.3f}  "
                  f"{r_m:7.3f}  {r_lo:7.3f}  {r_hi:7.3f}  {r_theory:7.3f}  "
                  f"{r_m - r_theory:7.3f}")


# ══════════════════════════════════════════════════════════════════════
#  Synthetic data validation
# ══════════════════════════════════════════════════════════════════════


def simulate_von_mises_phases(
    a_true: float, n_channels: int = 62, n_samples: int = 150000
) -> np.ndarray:
    """Draw phases from von Mises(0, a_true) and return as phase array.

    Returns array of shape (n_channels, n_samples) with values in [-π, π].
    Each channel gets independent draws from the same von Mises.
    The mean direction is 0 for all channels — so the ground-truth
    order parameter r satisfies r = I₁(a_true)/I₀(a_true).
    """
    from scipy.stats import vonmises

    rng = np.random.default_rng(42)
    # vonmises.rvs(loc=0, kappa=a, size=N) — location is μ, kappa is a
    phases = np.asarray(
        vonmises.rvs(loc=0, kappa=a_true, size=(n_channels, n_samples), random_state=rng),
        dtype=np.float64,
    )
    return phases


def simulate_with_noise(
    a_signal: float, a_noise: float = 0.1,
    n_channels: int = 62, n_samples: int = 150000,
) -> np.ndarray:
    """Von Mises signal plus independent noise phase per channel.

    Each channel's phase = von Mises(0, a_signal) + von Mises(0, a_noise)
    added in angular sense (wrapped).  a_noise = 0.1 approximates uniform.
    """
    from scipy.stats import vonmises

    rng = np.random.default_rng(71)
    signal = np.asarray(
        vonmises.rvs(loc=0, kappa=a_signal, size=(n_channels, n_samples), random_state=rng),
        dtype=np.float64,
    )
    noise = np.asarray(
        vonmises.rvs(loc=0, kappa=a_noise, size=(n_channels, n_samples), random_state=rng),
        dtype=np.float64,
    )
    return np.asarray(np.angle(np.exp(1j * signal) * np.exp(1j * noise)), dtype=np.float64)


def _negative_control_cases(n: int = 31000) -> dict[str, np.ndarray]:
    """Phase samples from distributions that are and are not von Mises.

    The `n` default matches the pipeline's real per-bin sample size
    (62 channels × 500 samples).
    """
    rng = np.random.default_rng(0)
    u = rng.uniform(0.0, 1.0, n)
    rho = 0.6
    mix = rng.uniform(0.0, 1.0, n) < 0.5
    return {
        # Model TRUE — both estimators must succeed here.
        "von Mises a=0.5": rng.vonmises(0.0, 0.5, n),
        "von Mises a=1.5": rng.vonmises(0.0, 1.5, n),
        "von Mises a=3.0": rng.vonmises(0.0, 3.0, n),
        # Model FALSE — a working test must reject these.
        "wrapped Cauchy rho=0.6": 2.0 * np.arctan(
            ((1.0 - rho) / (1.0 + rho)) * np.tan(np.pi * (u - 0.5))
        ),
        "top-hat arc |th|<1.2": rng.uniform(-1.2, 1.2, n),
        "50% vM(4) + 50% uniform": np.where(
            mix, rng.vonmises(0.0, 4.0, n), rng.uniform(-np.pi, np.pi, n)
        ),
        # Uniform IS von Mises at a = 0, so passing here is correct.
        "uniform (a=0, model true)": rng.uniform(-np.pi, np.pi, n),
    }


def run_estimator_validation() -> None:
    """Negative control: does the (a, r) collapse test actually discriminate?

    `run_synthetic` is a positive control — it draws von Mises phases and
    checks that `a` is recovered.  It cannot detect the failure mode that
    matters, because a tautological estimator passes a positive control
    perfectly.  This routine supplies the missing half: it runs both
    estimators on distributions that are *not* von Mises and reports the
    residual r − I₁(â)/I₀(â) for each.

    A usable estimator leaves the true cases on the curve and pushes the false
    ones off it.  The MLE leaves everything on the curve, which is the whole
    problem.  Exits non-zero if the log-density estimator fails to separate
    them, so this can be run as a gate.
    """
    print("─" * 78)
    print("Estimator validation — negative control on non-von-Mises phases")
    print("─" * 78)
    print(f"{'distribution':<28}{'MLE a':>8}{'resid':>9}{'  ':>3}{'logdens a':>10}{'resid':>9}")
    print("-" * 78)

    true_resid: list[float] = []
    false_resid: list[float] = []

    for name, theta in _negative_control_cases().items():
        r = order_parameter_r(theta)
        a_mle = concentration_a_mle(theta)
        a_log = concentration_a(theta)
        d_mle = r - bessel_ratio(a_mle)
        d_log = r - bessel_ratio(a_log)
        print(f"{name:<28}{a_mle:>8.3f}{d_mle:>9.4f}{'':>3}{a_log:>10.3f}{d_log:>9.4f}")
        (false_resid if "model true" not in name and "von Mises" not in name
         else true_resid).append(abs(d_log))

    worst_true = max(true_resid)
    best_false = min(false_resid)
    print("-" * 78)
    print(f"log-density: worst residual on a TRUE von Mises   = {worst_true:.4f}")
    print(f"log-density: smallest residual on a FALSE model   = {best_false:.4f}")
    print(f"separation ratio                                  = {best_false / worst_true:.1f}x")

    if best_false <= 4.0 * worst_true:
        print("\nFAIL — the estimator does not separate true from false models.")
        raise SystemExit(1)
    print("\nPASS — the collapse test discriminates.")


def run_synthetic(out: str = "figures/synthetic_collapse.png") -> None:
    """Run the full pipeline on synthetic von Mises data to validate a-recovery."""
    print("─" * 60)
    print("Synthetic (a, r) Collapse — Validation")
    print("─" * 60)

    a_true_values = [0.0, 0.2, 0.5, 1.0, 2.0, 3.0, 5.0, 10.0]
    results: list[dict[str, float]] = []

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5.2))

    for a_true in a_true_values:
        print(f"\na_true = {a_true:.1f}")
        # Generate clean von Mises phases
        phases = simulate_von_mises_phases(a_true, n_samples=150000)

        # Compute (a, r) via the same binning pipeline
        a_est, r_est = compute_ar_trace(phases)
        a_mean = float(np.nanmean(a_est))
        r_mean = float(np.nanmean(r_est))

        # Ground truth r
        r_true = bessel_ratio(a_true)

        print(f"  a_est={a_mean:.4f}  r_est={r_mean:.4f}  r_true={r_true:.4f}  "
              f"residual={r_mean - r_true:.4f}")

        results.append({
            "a_true": a_true, "a_est": a_mean,
            "r_true": r_true, "r_est": r_mean,
            "residual": r_mean - r_true,
        })

        # Scatter on the (a, r) plot
        ax1.scatter(a_est, r_est, s=2, alpha=0.3, label=f"a={a_true:.1f}", zorder=3)

    # Theoretical curve
    a_grid = np.linspace(0, 10, 200)
    r_grid = np.array([bessel_ratio(ai) for ai in a_grid])
    ax1.plot(a_grid, r_grid, "k-", lw=2.5, label=r"$r = I_1(a)/I_0(a)$", zorder=2)

    # Diagonal recovery line for a
    ax2.plot([0, 10], [0, 10], "k--", lw=1.5, alpha=0.5, label="perfect recovery")
    for r in results:
        ax2.plot(r["a_true"], r["a_est"], "o", ms=6, label=f"a={r['a_true']}")
    ax2.set_xlabel("true concentration $a$")
    ax2.set_ylabel("estimated $a$")
    ax2.set_xlim(0, 10.5)
    ax2.set_ylim(0, 10.5)
    ax2.legend(fontsize=7)
    ax2.set_title("(B)  a recovery validation")
    ax2.grid(alpha=0.3)

    ax1.set_xlim(0, 5)
    ax1.set_ylim(-0.02, 1.02)
    ax1.set_xlabel(r"concentration $a$")
    ax1.set_ylabel(r"order parameter $r$")
    ax1.legend(fontsize=7, markerscale=3, framealpha=0.9)
    ax1.set_title("(A)  Synthetic von Mises (a, r) vs theory")
    ax1.grid(alpha=0.3)

    fig.suptitle("Synthetic validation: von Mises phase data", fontsize=11)
    fig.tight_layout()
    fig.savefig(out, dpi=200)
    print(f"\nSaved {out}")
    plt.close(fig)

    # Print table
    print(f"\n{'a_true':>7s}  {'a_est':>7s}  {'r_est':>7s}  {'r_true':>7s}  {'resid':>7s}")
    print("-" * 50)
    for r in results:
        print(f"{r['a_true']:7.2f}  {r['a_est']:7.4f}  {r['r_est']:7.4f}  "
              f"{r['r_true']:7.4f}  {r['residual']:7.4f}")


# ══════════════════════════════════════════════════════════════════════
#  Multi-subject averaging
# ══════════════════════════════════════════════════════════════════════

MULTI_SUBJECTS = [
    "1010", "1016", "1022", "1033", "1045", "1054", "1060", "1067",
]  # 8 subjects, balanced across the dataset


def _plot_cross_panel_a(
    ax: Axes, all_a: list[np.ndarray], all_r: list[np.ndarray],
    names: list[str], task: str, run: int,
) -> None:
    """Scatter per-subject, overlay mean ± SEM, theory curve."""
    colors = plt.cm.tab10(np.linspace(0, 1, len(all_a)))
    for i, (a_tr, r_tr) in enumerate(zip(all_a, all_r)):
        ax.scatter(a_tr, r_tr, s=0.5, alpha=0.12, color=colors[i], label=names[i])
    n_bins = min(len(a) for a in all_a)
    sa = np.column_stack([a[:n_bins] for a in all_a])
    sr = np.column_stack([r[:n_bins] for r in all_r])
    ax.errorbar(np.nanmean(sa, axis=1), np.nanmean(sr, axis=1),
                 xerr=np.nanstd(sa, axis=1)/np.sqrt(sa.shape[1]),
                 yerr=np.nanstd(sr, axis=1)/np.sqrt(sr.shape[1]),
                 fmt="o", color="black", ms=3, capsize=2, capthick=1, zorder=5)
    a_g = np.linspace(0, 5, 200)
    ax.plot(a_g, [bessel_ratio(ai) for ai in a_g], "k-", lw=2.5, label=r"$I_1/I_0(a)$")
    ax.set(xlabel=r"$a$", ylabel=r"$r$", xlim=(0, 2), ylim=(-0.02, 1.02))
    ax.legend(fontsize=7, markerscale=3, framealpha=0.9)
    ax.set_title(f"(A)  Cross-subject {task} run-{run} ({len(all_a)} subjs)")
    ax.grid(alpha=0.3)


def _plot_cross_panel_b(ax: Axes, a_subs: np.ndarray, r_subs: np.ndarray) -> None:
    """Subject-level means vs theory."""
    ax.scatter(a_subs, r_subs, s=40, color="steelblue", zorder=3)
    a_g = np.linspace(0, 3, 200)
    ax.plot(a_g, [bessel_ratio(ai) for ai in a_g], "k-", lw=2.5)
    ax.set(xlabel=r"$a$", ylabel=r"$r$", xlim=(0, 1.5), ylim=(-0.02, 1.02))
    ax.legend(fontsize=7)
    ax.set_title("(B)  Mean per subject")
    ax.grid(alpha=0.3)


def _plot_cross_subject(
    all_a: list[np.ndarray], all_r: list[np.ndarray],
    subject_results: list[dict[str, float | str]],
    task: str, run: int,
    out: str,
) -> None:
    """Draw the two-panel cross-subject figure and print summary table."""
    pooled_a = np.concatenate(all_a)
    pooled_r = np.concatenate(all_r)
    names = [str(r["subject"]) for r in subject_results]
    a_subs = np.array([r["a_mean"] for r in subject_results])
    r_subs = np.array([r["r_mean"] for r in subject_results])

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5.2))
    _plot_cross_panel_a(ax1, all_a, all_r, names, task, run)
    _plot_cross_panel_b(ax2, a_subs, r_subs)
    fig.suptitle(f"ds005620 cross-subject — {BAND_LOW:.0f}–{BAND_HIGH:.0f} Hz", fontsize=11)
    fig.tight_layout()
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    fig.savefig(out, dpi=200)
    print(f"Saved {out}")
    plt.close(fig)

    print(f"\n{'Subject':>12s}  {'a_mean':>7s}  {'r_mean':>7s}")
    print("-" * 30)
    for r in subject_results:
        print(f"{r['subject']:>12s}  {r['a_mean']:7.3f}  {r['r_mean']:7.3f}")
    print(f"Pooled: a={float(np.nanmean(pooled_a)):.3f}±{float(np.nanstd(pooled_a)):.3f}, "
          f"r={float(np.nanmean(pooled_r)):.3f}±{float(np.nanstd(pooled_r)):.3f}")
    print(f"Group: mean_a={float(np.nanmean(a_subs)):.3f} "
          f"[{float(np.nanmin(a_subs)):.3f}–{float(np.nanmax(a_subs)):.3f}], "
          f"mean_r={float(np.nanmean(r_subs)):.3f} "
          f"[{float(np.nanmin(r_subs)):.3f}–{float(np.nanmax(r_subs)):.3f}]")


def run_multi_subject(
    task: str = "sed", acq: str = "rest", run: int = 1,
    max_seconds: float = 20.0,
    out: str = "figures/cross_subject_collapse.png",
) -> None:
    """Compute (a, r) across subjects for one common block and aggregate."""
    print("─" * 60)
    print(f"Cross-subject (a, r): {task}_{acq} run-{run}, {max_seconds}s each")
    print(f"Subjects: {MULTI_SUBJECTS}")
    print("─" * 60)

    all_a: list[np.ndarray] = []
    all_r: list[np.ndarray] = []
    subject_results: list[dict[str, float | str]] = []

    for subj in MULTI_SUBJECTS:
        label = f"sub-{subj}"
        print(f"\n── {label} ──", flush=True)
        try:
            global SUBJECT
            old_subj = SUBJECT
            SUBJECT = subj
            data, fs = read_brainvision(task, acq, run, max_seconds, pad_seconds=PAD_SECONDS)
            a_trace, r_trace = compute_ar_trace(extract_phase(data, fs, pad_seconds=PAD_SECONDS))
            SUBJECT = old_subj
            a_mean = float(np.nanmean(a_trace))
            r_mean = float(np.nanmean(r_trace))
            print(f"  a={a_mean:.3f}  r={r_mean:.3f}  (n={len(a_trace)})", flush=True)
            all_a.append(a_trace)
            all_r.append(r_trace)
            subject_results.append({"subject": f"sub-{subj}", "a_mean": a_mean, "r_mean": r_mean})
        except Exception as e:
            print(f"  ✗ FAILED: {e}", flush=True)

    if not all_a:
        print("No subjects succeeded.")
        return

    _plot_cross_subject(all_a, all_r, subject_results, task, run, out)


# ══════════════════════════════════════════════════════════════════════
#  Main & CLI dispatch
# ══════════════════════════════════════════════════════════════════════


def _parse_args() -> tuple[str, list[str]]:
    """Return (action, remaining_args) based on sys.argv.

    Actions: 'simulate', 'validate', 'montage', 'multi', 'bands', 'single'.
    """
    import sys as _sys
    if "--simulate" in _sys.argv or "-s" in _sys.argv:
        return "simulate", []
    if "--validate" in _sys.argv:
        return "validate", []
    if "--montage" in _sys.argv:
        return "montage", _sys.argv[2:]
    if "--bands" in _sys.argv:
        return "bands", _sys.argv[2:]
    if "--multi" in _sys.argv or "-m" in _sys.argv:
        return "multi", _sys.argv[2:]
    return "single", []


def _run_single_block(task: str, acq: str, run: int) -> tuple[np.ndarray, np.ndarray] | None:
    """Process one block and return (a_trace, r_trace) or None on failure."""
    try:
        data, fs = read_brainvision(task, acq, run, pad_seconds=PAD_SECONDS)
        n_ch, n_samp = data.shape
        print(f"  Loaded: {n_ch} ch × {n_samp} samples ({n_samp / fs:.1f} s @ {fs:.0f} Hz)")
        phase = extract_phase(data, fs, pad_seconds=PAD_SECONDS)
        a_trace, r_trace = compute_ar_trace(phase)
        n_valid = int(np.sum(~np.isnan(r_trace)))
        print(f"    (a, r) points: {n_valid}, "
              f"a={np.nanmean(a_trace):.3f}±{np.nanstd(a_trace):.3f}, "
              f"r={np.nanmean(r_trace):.3f}±{np.nanstd(r_trace):.3f}")
        return a_trace, r_trace
    except Exception as e:
        print(f"  ✗ FAILED: {e}")
        return None


def _run_single_subject() -> None:
    """Default: process all BLOCKS for the current subject and plot."""
    print("─" * 60)
    print("Bastos-Style (a, r) Collapse Pipeline")
    print(f"Subject: {SUBJECT}, Band: {BAND_LOW:.0f}–{BAND_HIGH:.0f} Hz")
    print("─" * 60)

    traces: dict[str, tuple[np.ndarray, np.ndarray]] = {}
    for task, acq, run, label in BLOCKS:
        print(f"\n── Processing {label} ──")
        result = _run_single_block(task, acq, run)
        if result is not None:
            traces[label] = result

    make_figure(traces)
    print("\n─" * 60)
    print("Summary: mean (a, r) per block")
    print("─" * 60)
    for label, (a_trace, r_trace) in traces.items():
        mask = ~np.isnan(r_trace)
        if mask.sum() > 0:
            print(f"  {label:20s}  a={np.nanmean(a_trace):.3f}  r={np.nanmean(r_trace):.3f}  "
                  f"(n={mask.sum()})")


def _arg(args: list[str], i: int, default: str) -> str:
    """Return args[i] if available, else default (avoids inline if/else)."""
    return args[i] if len(args) > i else default


def main() -> None:
    action, args = _parse_args()

    if action == "bands":
        run_band_comparison(
            _arg(args, 0, "sed"), _arg(args, 1, "rest"),
            int(_arg(args, 2, "1")), float(_arg(args, 3, "20.0")),
        )
    elif action == "simulate":
        run_synthetic()
    elif action == "validate":
        run_estimator_validation()
    elif action == "montage":
        run_montage_comparison(
            _arg(args, 0, "sed"), _arg(args, 1, "rest"),
            int(_arg(args, 2, "1")), float(_arg(args, 3, "20.0")),
        )
    elif action == "multi":
        run_multi_subject(
            _arg(args, 0, "sed"), _arg(args, 1, "rest"),
            int(_arg(args, 2, "1")),
        )
    else:
        _run_single_subject()


if __name__ == "__main__":
    main()
