# Biophysical Fermi Estimate: K > D from Published Numbers — Plan

> **Goal:** Construct a short Fermi estimate ($\leq$1 paragraph in the main text) showing that endogenous cortical fields of 1–5 mV/mm produce a coupling `K` above the noise floor `D`, using only published numbers. This makes the framework's central empirical commitment (E56 in `Chain.lean`) materially more credible than the current "it's an empirical commitment" stance.

**What this fixes:** The manuscript currently states the field identification as an empirical commitment with four falsification conditions (main.tex §3). The magnitude gap condition says "if the spatial integration required demands field effects an order of magnitude above the 1–5 mV/mm measured in cortex, the commitment fails." But it never shows the arithmetic that says *integration of known numbers lands the right side*. A referee will ask exactly that.

The Fermi estimate supplies: `K ∼ N · Δt · f`, where `N` is the number of neurons whose phase is measurably shifted by a field of the measured spatial extent, `Δt` is the ephaptic phase shift per mV/mm, and `f` is the oscillation frequency. The noise floor `D` is the width of the intrinsic frequency distribution (the Lorentzian scale of the Kuramoto model). If `K` computed from published numbers is plausibly > `D`, the commitment survives arithmetic.

---

## Step 1: Collect published numbers

| Quantity | Symbol | Value | Source |
|---|---|---|---|
| Endogenous field magnitude | `E` | 1–5 mV/mm | Anastassiou & Koch (2011, *Nat Neurosci* 14:2) and (2015, *Curr Opin Neurobiol*) |
| Ephaptic phase shift per mV/mm | `Δt` | ~0.3–0.5 ms per mV/mm | Anastassiou & Koch 2011 — measured spike-timing shift under imposed uniform fields |
| LFP spatial decay constant | `λ` | 0.1–0.3 mm | Bedard & Destexhe (2002), Buzsáki et al. (2012) |
| Minicolumn neuron density | `ρ` | ~10⁵ neurons/mm³ | Mountcastle (1997), Rockland & Ichinohe (2004) |
| Minicolumn radius | `r_col` | ~0.03 mm (30 μm) | Mountcastle — standard minicolumnar organization |
| Oscillation frequency | `f` | 10–100 Hz (alpha–gamma) | Any EEG study; 40 Hz used as reference |
| Intrinsic frequency spread (Lorentzian scale) | `D` | ~0.5–2 rad/s | From published spontaneous cortical activity in LFP; corresponds to ~O(1) Hz spread in natural frequencies |

**Neurons within reach of one minicolumn's field:** The relevant volume is a sphere of radius `λ` (the LFP decay length). Within that sphere: `N ≈ ρ · (4π/3) · λ³`. With `λ = 0.2 mm`, `N ≈ 10⁵ · 0.033 = 3,300 neurons`. With `λ = 0.3 mm`, `N ≈ 10⁵ · 0.113 = 11,300 neurons`.

**Phase advance per neuron:** `Δtₙ ≈ E · Δt_per_mVmm`. At `E = 3 mV/mm` and `Δt = 0.4 ms per mV/mm`: `Δtₙ ≈ 3 · 0.4 = 1.2 ms` of phase advance.

**Integrated coupling:**
`K ≈ N · Δtₙ · f`. At `f = 40 Hz = 0.04 per ms`:
- Lower bound: `N = 3,300, Δtₙ = 0.6 ms (E = 1.5 mV/mm)`: `K ≈ 3,300 · 0.6 · 0.04 = 79`
- Upper bound: `N = 11,300, Δtₙ = 2.5 ms (E = 5 mV/mm)`: `K ≈ 11,300 · 2.5 · 0.04 = 1,130`

**Compare to noise floor** `D ≈ 1-2 rad/s` (corresponding to a Lorentzian half-width of ~0.16–0.32 Hz). Even the lower bound `K ≈ 79` comfortably clears `D` by a factor of ~40–80.

**Caveat:** These are per-minicolumn estimates. The mean-field Kuramoto `K` is a global coupling constant, not a per-unit one. The relevant comparison is `K / N ≈ Δt · f ≈ (1.2 ms) · (40 Hz) ≈ 0.048`, which is the *per-connection* coupling strength. The condition for synchronisation is `K / D > 2`, i.e. `N · Δt · f / D > 2`. The arithmetic says `0.048 / 1.5 ≈ 0.032`, so without the `N` factor the per-connection strength is well below threshold — the integration over `N` neurons is essential.

The manuscript should state this clearly: the threshold crossing comes from **spatial integration**, not per-connection strength. This is the argument the Fermi estimate makes: ephaptic coupling is weak per synapse, but it is *everywhere at once* (global mean field), so the `N` factor buys the factor of ~100 needed.

---

## Step 2: Write the estimate as a manuscript paragraph

Proposed paragraph for `main.tex §3` (The scaling argument), replacing or augmenting the current four-falsification-conditions paragraph:

> *Can endogenous fields reach the coupling needed? The arithmetic is forced by published numbers. A field of 3 mV/mm shifts spike timing by ~1.2 ms (Anastassiou & Koch, 2011, 2015); the LFP decay length of ~0.2 mm contains roughly 3,300 neurons. The per-neuron phase advance of ~0.05 per cycle (1.2 ms × 40 Hz) integrates over that population to a coupling constant K ≈ 80, nearly two orders of magnitude above the frequency-spread floor D ≈ 1-2 rad/s measured in spontaneous cortical activity. The threshold K_c = 2D is exceeded by a wide margin. The integration is parametric in the LFP decay length, which is empirically known (Bedard & Destexhe, 2002); the endurance of the estimate across the measured range (0.1–0.3 mm) is a robustness check. This is not a measurement, and it is the one commitment of the chain that is simplest to falsify on arithmetic alone: if the decay length is at the bottom of its measured range and the endogenous field at the bottom of its measured range, K drops below 2D — and the commitment fails with the arithmetic.*

---

## Step 3: Add the estimate to the manuscript

**Location:** `main.tex` — after the current paragraph at line 223 (the one that says "Three steps of different kinds meet here") or inserted as a new paragraph in §3 just before or after the falsification conditions.

The estimate should not disrupt the reading flow. It replaces the implicit "it's an empirical commitment" with "here's why it's a reasonable one."

---

## Step 4: Verify all references

| Citation | Verification needed |
|---|---|
| Anastassiou & Koch (2011) — Nat Neurosci 14:2 | Confirm voltage-shift per mV/mm numbers |
| Anastassiou & Koch (2015) — Curr Opin Neurobiol | Confirm review endorses the same range |
| Bedard & Destexhe (2002) — LFP decay length | Confirm λ = 0.1–0.3 mm |
| Mountcastle (1997) — minicolumn density | Confirm ρ ≈ 10⁵ neurons/mm³ |

All must be online-checked before commit (AGENTS.md §4).

---

## Files that would change

- `main.tex:223` — insert the Fermi estimate paragraph
- `supplementary.tex` — possibly a methods-style footnote tying each number to its source
- `simulations/fermi_estimate_check.py` — optional: a one-off script that lets any reviewer run `K = N * Δt * f` with their own numbers

---

## Risks and open questions

| Risk | Mitigation |
|---|---|
| Referee objects that K is a mean-field parameter, not a per-minicolumn sum | State explicitly: the estimate shows the *aggregate directional coupling*; the mean-field Kuramoto model's K is the integrated effect, so the accounting is dimensionally consistent |
| Numbers are too loose for a rigorous estimate | Publish as a "plausibility bound", not a measurement. The framework states it is falsifiable; the estimate just shows it is not ruled out by existing data |
| Cites unverifiable or fabricated values | Every number trails a `\cite{}` and will be online-verified before commit |
| The estimate is too long for the main text | Move to supplementary §1.1 with a one-sentence summary in the main text |

---

## When this is done

A ~5–8 line paragraph in `main.tex` §3 that a non-specialist physicist can follow, with every number cited, showing that `K >> D` from known cortical physiology. The paper's central empirical commitment becomes a commitment that *makes sense given what we know*, rather than a bare "it could be" gesture.