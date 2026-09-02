"""Bastos-style empirical (a, r) collapse pipeline for ds005620 propofol EEG.

Downloads one subject's EEG from the public OpenNeuro S3 mirror, extracts
instantaneous phase via Hilbert transform, and plots the (a, r) trace against
the theoretical r = I₁(a)/I₀(a) curve from von Mises theory.

Usage:
    uv run --directory simulations python simulations/empirical_collapse.py
"""

import os

import matplotlib.pyplot as plt
import numpy as np
from scipy.signal import butter, filtfilt, hilbert
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

# Bandpass parameters: theta through gamma (4-40 Hz)
BAND_LOW = 4.0
BAND_HIGH = 40.0
FILTER_ORDER = 4

# Subsampling: don't compute (a, r) at every sample — every 100 ms = 500 pts at 5 kHz
DECIMATE_FACTOR = 500  # 500 samples × 200 µs = 100 ms per bin


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
    task: str, acq: str, run: int, max_seconds: float = 60.0
) -> tuple[np.ndarray, float]:
    """Download and parse a BrainVision recording from the S3 mirror.

    Reads at most max_seconds of data (default 60 s). The full vhdr header
    is always downloaded (it's tiny); only the first max_seconds of the
    .eeg binary file is fetched via Range requests.

    Returns (data, fs) where data has shape (n_channels, n_samples_truncated).
    """
    vhdr_file, eeg_file, _ = _filenames(task, acq, run)

    # Parse header (always download — it's tiny)
    vhdr_raw = _s3_download(vhdr_file).decode("utf-8")
    meta = _parse_vhdr(vhdr_raw)

    n_channels = int(meta["Common Infos.NumberOfChannels"])
    samp_int_us = float(meta["Common Infos.SamplingInterval"])
    fs = 1e6 / samp_int_us

    # Calculate how many bytes we need for max_seconds
    n_samp_target = int(fs * max_seconds)
    bytes_per_sample = n_channels * 4  # 4 bytes per float32 per channel
    n_bytes = n_samp_target * bytes_per_sample

    # Download truncated binary data via Range request
    eeg_raw = _s3_download(eeg_file, max_bytes=n_bytes)

    n_samp_actual = len(eeg_raw) // (4 * n_channels)
    data = np.frombuffer(eeg_raw, dtype=np.float32).reshape(
        n_samp_actual, n_channels
    ).T  # shape (n_ch, n_samp_actual)

    print(f"    {n_channels} ch × {n_samp_actual} samples "
          f"({n_samp_actual / fs:.1f} s @ {fs:.0f} Hz)")

    return data, fs


# ══════════════════════════════════════════════════════════════════════
#  Phase extraction
# ══════════════════════════════════════════════════════════════════════


def design_bandpass(
    low: float, high: float, fs: float, order: int = 4,
) -> tuple[np.ndarray, np.ndarray]:
    """Butterworth bandpass filter coefficients."""
    nyq = 0.5 * fs
    b, a = butter(order, [low / nyq, high / nyq], btype="band")
    return b, a


def extract_phase(
    data: np.ndarray, fs: float, low: float = BAND_LOW, high: float = BAND_HIGH
) -> np.ndarray:
    """Apply bandpass filter + Hilbert transform to each channel.

    Returns phase array of shape (n_channels, n_samples) with values in [-π, π].
    Filters only EEG channels (1-62), skips VEOG/HEOG/EMG (63-65).
    """
    b, a = design_bandpass(low, high, fs)

    # Only use scalp EEG channels (indices 0-61), skip EOG/EMG
    eeg_idx = np.arange(62)

    phase = np.empty_like(data)
    phase[:] = np.nan

    for idx in tqdm(eeg_idx, desc="Hilbert phase"):
        # Filter
        filtered = filtfilt(b, a, data[idx])
        # Hilbert → analytic signal → instantaneous phase
        analytic = hilbert(filtered)
        phase[idx] = np.angle(analytic)

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
    b, a = design_bandpass(low, high, fs)
    eeg = data[:62]  # scalp only
    # 61 adjacent pairs: ch0-ch1, ch1-ch2, ..., ch60-ch61
    n_pairs = 61
    phase = np.empty((n_pairs, data.shape[1]))
    phase[:] = np.nan

    for i in tqdm(range(n_pairs), desc="Bipolar phase"):
        diff = eeg[i] - eeg[i + 1]
        filtered = filtfilt(b, a, diff)
        phase[i] = np.angle(hilbert(filtered))

    return phase


def extract_phase_car(
    data: np.ndarray, fs: float, low: float = BAND_LOW, high: float = BAND_HIGH,
) -> np.ndarray:
    """Common-average reference in phase space (circular-mean subtraction).

    Standard phase extraction, then subtract the instantaneous circular mean
    across all channels at each time point:
        θ_j'(t) = θ_j(t) - arg( Σ_k exp(i θ_k(t)) )
    This removes any global phase offset that all channels share (e.g. volume
    conduction from a deep common source).

    Returns phase array same shape as input.
    """
    phase_raw = extract_phase(data, fs, low, high)
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
    """Estimate von Mises concentration `a` via log-density regression.

    The von Mises log-density is log p(θ) ∝ a cos(θ - μ) + const.  We histogram
    the phase values into n_bins, fit log(bin_count) ~ cos(θ - μ_t) by least
    squares, and return the slope `a`.
    """
    theta = phase[~np.isnan(phase)]
    if len(theta) < 100:
        return 0.0

    # First, estimate the mean direction μ
    mu = np.angle(np.sum(np.exp(1j * theta)))

    # Histogram
    bins = np.linspace(-np.pi, np.pi, n_bins + 1)
    counts, edges = np.histogram(theta, bins=bins)
    bin_centers = 0.5 * (edges[:-1] + edges[1:])

    # Log-counts (add pseudocount to avoid log(0))
    log_counts = np.log(counts + 1.0)

    # Design matrix: [cos(θ - μ), constant]
    cos_theta = np.cos(bin_centers - mu)
    X = np.column_stack([cos_theta, np.ones_like(cos_theta)])
    coeffs, *_ = np.linalg.lstsq(X, log_counts, rcond=None)

    a_est = float(coeffs[0])
    # Guard against pathological values
    if a_est < 0:
        return 0.0
    return min(a_est, 50.0)


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

    data, fs = read_brainvision(task, acq, run, max_seconds)

    raw_traces: dict[str, tuple[np.ndarray, np.ndarray]] = {}
    cis: dict[str, tuple[float, float, float, float, float, float]] = {}

    # Raw
    print("\n  Raw scalp reference...", flush=True)
    a_raw, r_raw = compute_ar_trace(extract_phase(data, fs))
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
            data, fs = read_brainvision(task, acq, run, max_seconds)
            phase = extract_phase(data, fs)
            a_trace, r_trace = compute_ar_trace(phase)
            SUBJECT = old_subj

            a_mean = float(np.nanmean(a_trace))
            r_mean = float(np.nanmean(r_trace))
            print(f"  a={a_mean:.3f}  r={r_mean:.3f}  (n={len(a_trace)})", flush=True)

            all_a.append(a_trace)
            all_r.append(r_trace)
            subject_results.append({
                "subject": f"sub-{subj}",
                "a_mean": a_mean, "r_mean": r_mean,
            })
        except Exception as e:
            print(f"  ✗ FAILED: {e}", flush=True)

    if not all_a:
        print("No subjects succeeded.")
        return

    # Pool all (a, r) points across subjects
    pooled_a = np.concatenate(all_a)
    pooled_r = np.concatenate(all_r)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5.2))

    # Panel A: scatter per subject
    colors = plt.cm.tab10(np.linspace(0, 1, len(all_a)))
    for i, (a_trace, r_trace) in enumerate(zip(all_a, all_r)):
        ax1.scatter(a_trace, r_trace, s=0.5, alpha=0.12, color=colors[i],
                    label=f"{subject_results[i]['subject']}")

    # Overlay the mean trace (mean a per time-bin across subjects)
    n_bins = min(len(a) for a in all_a)
    stacked_a = np.column_stack([a[:n_bins] for a in all_a])
    stacked_r = np.column_stack([r[:n_bins] for r in all_r])
    mean_a = np.nanmean(stacked_a, axis=1)
    mean_r = np.nanmean(stacked_r, axis=1)
    sem_a = np.nanstd(stacked_a, axis=1) / np.sqrt(stacked_a.shape[1])
    sem_r = np.nanstd(stacked_r, axis=1) / np.sqrt(stacked_r.shape[1])

    ax1.errorbar(mean_a, mean_r, xerr=sem_a, yerr=sem_r,
                 fmt="o", color="black", ms=3, capsize=2, capthick=1,
                 label="mean ± SEM across subjects", zorder=5)

    # Theoretical curve
    a_grid = np.linspace(0, 5, 200)
    r_grid = np.array([bessel_ratio(ai) for ai in a_grid])
    ax1.plot(a_grid, r_grid, "k-", lw=2.5,
             label=r"$r = I_1(a)/I_0(a)$", zorder=4)

    ax1.set_xlabel(r"concentration $a$")
    ax1.set_ylabel(r"order parameter $r$")
    ax1.set_xlim(0, 2)
    ax1.set_ylim(-0.02, 1.02)
    ax1.legend(fontsize=7, markerscale=3, framealpha=0.9)
    ax1.set_title(f"(A)  Cross-subject {task} run-{run} ({len(MULTI_SUBJECTS)} subjs)")
    ax1.grid(alpha=0.3)

    # Panel B: subject-level means with error bars
    a_subs = np.array([r["a_mean"] for r in subject_results])
    r_subs = np.array([r["r_mean"] for r in subject_results])
    ax2.scatter(a_subs, r_subs, s=40, color="steelblue", zorder=3)
    # Overlay theoretical curve
    a_grid2 = np.linspace(0, 3, 200)
    r_grid2 = np.array([bessel_ratio(ai) for ai in a_grid2])
    ax2.plot(a_grid2, r_grid2, "k-", lw=2.5,
             label=r"$r = I_1(a)/I_0(a)$")
    ax2.set_xlabel(r"concentration $a$")
    ax2.set_ylabel(r"order parameter $r$")
    ax2.set_xlim(0, 1.5)
    ax2.set_ylim(-0.02, 1.02)
    ax2.legend(fontsize=7)
    ax2.set_title("(B)  Mean per subject — sed run-1")
    ax2.grid(alpha=0.3)

    fig.suptitle(
        f"ds005620 cross-subject — {BAND_LOW:.0f}–{BAND_HIGH:.0f} Hz band",
        fontsize=11,
    )
    fig.tight_layout()
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    fig.savefig(out, dpi=200)
    print(f"\nSaved {out}")
    plt.close(fig)

    # Summary table
    print(f"\n{'Subject':>12s}  {'a_mean':>7s}  {'r_mean':>7s}")
    print("-" * 30)
    for r in subject_results:
        print(f"{r['subject']:>12s}  {r['a_mean']:7.3f}  {r['r_mean']:7.3f}")
    print(f"\nPooled: a={float(np.nanmean(pooled_a)):.3f}±{float(np.nanstd(pooled_a)):.3f}, "
          f"r={float(np.nanmean(pooled_r)):.3f}±{float(np.nanstd(pooled_r)):.3f}")
    print(f"Group-level: mean_a={float(np.nanmean(a_subs)):.3f} [{float(np.nanmin(a_subs)):.3f}–"
          f"{float(np.nanmax(a_subs)):.3f}], "
          f"mean_r={float(np.nanmean(r_subs)):.3f} [{float(np.nanmin(r_subs)):.3f}–"
          f"{float(np.nanmax(r_subs)):.3f}]")


# ══════════════════════════════════════════════════════════════════════
#  Main
# ══════════════════════════════════════════════════════════════════════


def main() -> None:
    import sys as _sys

    if "--simulate" in _sys.argv or "-s" in _sys.argv:
        run_synthetic()
        return
    if "--montage" in _sys.argv:
        task = _sys.argv[2] if len(_sys.argv) >= 3 else "sed"
        acq = _sys.argv[3] if len(_sys.argv) >= 4 else "rest"
        run_n = int(_sys.argv[4]) if len(_sys.argv) >= 5 else 1
        seconds = float(_sys.argv[5]) if len(_sys.argv) >= 6 else 20.0
        run_montage_comparison(task, acq, run_n, seconds)
        return
    if "--multi" in _sys.argv or "-m" in _sys.argv:
        task, acq, run = "sed", "rest", 1
        if len(_sys.argv) >= 4:
            task = _sys.argv[2]
            acq = _sys.argv[3]
        if len(_sys.argv) >= 5:
            run = int(_sys.argv[4])
        run_multi_subject(task, acq, run)
        return

    print("─" * 60)
    print("Bastos-Style (a, r) Collapse Pipeline")
    print(f"Subject: {SUBJECT}, Band: {BAND_LOW:.0f}–{BAND_HIGH:.0f} Hz")
    print(" Flags: --simulate | --multi [t] [a] [r] | --montage [t] [a] [r] [sec]")
    print("─" * 60)

    traces: dict[str, tuple[np.ndarray, np.ndarray]] = {}

    for task, acq, run, label in BLOCKS:
        print(f"\n── Processing {label} ──")
        try:
            data, fs = read_brainvision(task, acq, run)
            n_ch, n_samp = data.shape
            print(f"  Loaded: {n_ch} ch × {n_samp} samples ({n_samp / fs:.1f} s @ {fs:.0f} Hz)")

            phase = extract_phase(data, fs)
            a_trace, r_trace = compute_ar_trace(phase)
            n_valid = int(np.sum(~np.isnan(r_trace)))
            print(f"    (a, r) points: {n_valid}, "
                  f"a={np.nanmean(a_trace):.3f}±{np.nanstd(a_trace):.3f}, "
                  f"r={np.nanmean(r_trace):.3f}±{np.nanstd(r_trace):.3f}")

            traces[label] = (a_trace, r_trace)

        except Exception as e:
            print(f"  ✗ FAILED: {e}")

    make_figure(traces)

    print("\n─" * 60)
    print("Summary: mean (a, r) per block")
    print("─" * 60)
    for label, (a_trace, r_trace) in traces.items():
        mask = ~np.isnan(r_trace)
        if mask.sum() > 0:
            print(f"  {label:20s}  a={np.nanmean(a_trace):.3f}  r={np.nanmean(r_trace):.3f}  "
                  f"(n={mask.sum()})")


if __name__ == "__main__":
    main()
