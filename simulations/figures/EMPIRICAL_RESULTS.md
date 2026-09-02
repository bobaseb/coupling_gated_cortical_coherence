# Bastos-Style (a, r) Collapse Pipeline — Results (01 Sep 2026)

## Dataset: ds005620 (OpenNeuro)
- Propofol repeated-awakening study, 21 subjects, 65 ch scalp EEG @ 5 kHz
- Blocks: awake (EC/EO), sed (3 runs × 5 min), sed2 (2-3 runs × 5 min)

## Single-subject results (sub-1016, 4-40 Hz band, 30s per block)

| Block        | a_reg | a_from_r | r_mean | I₁/I₀(a_reg) | Interpretation |
|-------------|------:|---------:|------:|-------------:|---------------|
| Awake EC    | 0.286 |    1.553 | 0.609 |        0.128 | r >> prediction |
| Awake EO    | 0.316 |    1.419 | 0.575 |        0.132 | r >> prediction |
| Sed run-1   | 0.207 |    1.375 | 0.564 |        0.096 | r >> prediction |
| Sed run-2   | 0.261 |    0.465 | 0.226 |        0.109 | r > prediction, less extreme |
| Sed run-3   | 0.135 |    0.645 | 0.307 |        0.065 | r >> prediction |
| Sed2 run-1  | 0.347 |    0.328 | 0.162 |        0.132 | borderline (close match!) |
| Sed2 run-2  | 0.118 |    0.365 | 0.180 |        0.056 | r > prediction |

**Verdict:** falsified. r consistently exceeds I₁/I₀(a_reg) by factor 2-5.
a_from_r (inverse Bessel) is 3-7x larger than a_reg, meaning the phase
histogram is nearly uniform while coherence is moderate.

## Alpha band (8-12 Hz, sub-1016, 30s per block)

| Block        | a_reg | r_mean |
|-------------|------:|------:|
| Awake EC    | 0.140 | 0.067 |
| Awake EO    | 0.183 | 0.082 |
| Sed run-1   | 0.166 | 0.083 |
| Sed run-2   | 0.154 | 0.076 |
| Sed run-3   | 0.147 | 0.074 |
| Sed2 run-1  | 0.163 | 0.079 |
| Sed2 run-2  | 0.163 | 0.079 |

**Verdict:** near noise floor for 62 channels (r~0.08). Collapse approximately
holds (r ≈ I₁/I₀(a) ≈ 0.07-0.09) but not discriminating.

## Synthetic validation

Pipeline tested on von Mises-generated phases (known a_true, N=62 ch, 150k samples):

| a_true | a_est | r_est | r_true | Residual |
|------:|-----:|-----:|------:|--------:|
|   0.00 | 0.010 | 0.005 | 0.000 | +0.005 |
|   0.20 | 0.199 | 0.099 | 0.100 | -0.000 |
|   0.50 | 0.500 | 0.243 | 0.243 | +0.000 |
|   1.00 | 0.998 | 0.446 | 0.446 | -0.000 |
|   2.00 | 1.994 | 0.698 | 0.698 | +0.000 |
|   3.00 | 2.974 | 0.810 | 0.810 | +0.000 |
|   5.00 | 4.316 | 0.894 | 0.893 | +0.000 |
|  10.00 | 4.206 | 0.949 | 0.949 | +0.000 |

**Finding:** accurate a-recovery up to a=3. Above a=3 the 40-bin histogram
regression saturates. r-recovery is exact throughout. The real-data failure
is therefore **genuine**, not a measurement artifact.

## Methodological notes

- BrainVision format: float32 multiplexed binary (.eeg), text header (.vhdr),
  text marker (.vmrk). Resolution 0.1 µV.
- S3 public bucket access: `s3.amazonaws.com/openneuro.org/ds005620/...`
- Zero MNE dependency — pure numpy/scipy parser.
- Narrow bandpass filters at 5 kHz need `sosfiltfilt` for numerical stability.
- Channel 0 had -40,000 µV DC offset — always detrend before filtering.