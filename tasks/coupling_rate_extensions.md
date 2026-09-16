# N12–N13 — the rate and the fluctuation of an evolving coupling — 2026-09-16

## Intent, constraints and success criteria

Close the two remaining numerical items in `tasks/todo.md`: the error the
quasi-static reduction introduces as a function of rate (N12), and which
statistic of a randomly varying coupling controls coherence (N13). Both are
about the same gap — `K_c = 2D` is proved for a *fixed* scalar coupling, and
every use of it for a coupling that moves substitutes something for that fixed
number without saying what the substitution costs.

Constraints carried from the ledger's acceptance rule for the numerical items:

- **No item closes on a specification.** Each runs, saves a machine-readable
  summary and reports.
- **A negative result closes its item.** Where a quantity does not separate, or
  where neither candidate substitution is right, that is the finding.
- **At least one case each is required to fail.** N12 keeps a comparison against
  a branch that has quietly stopped updating; N13 keeps a coupling whose mean
  says there is no order where there is.
- **No production sweep on the regeneration path** (AGENTS.md §3): the figures
  and the report read saved artifacts and integrate nothing.
- Python quality gates apply in full (AGENTS.md §2).

Two constraints are specific to this pair and come from the ledger's N-group
preamble. **Neither item licenses a trajectory claim**: both are about the
stationary problem an instantaneous coupling poses, and the residual between a
trajectory and that problem's answer. And **no item may substitute a mean for a
supremum without measuring what that costs** — which is exactly what N13 does
measure, and what N11 fences in Lean.

## Deferred, deliberately

The publication alignment is **not** part of this pass, on the same footing as
the N7–N9 pass. No numeral below has reached `main.tex` or `supplementary.tex`,
no macro has been generated and `simulation_results.tex` is unchanged. The
sentences these measurements bear on are listed under *What the publication
would have to say*.

## Plan

- [x] Write the mean-field integrator the two items share, with its positive
      control: the stationary density must not move.
- [x] N12: measure `r(t) - r_ss(K(t))` on subcritical, supercritical and
      crossing legs; state the admissible-rate criterion against distance from
      threshold; recover the published bifurcation-delay exponent as the
      threshold limit of the same measurement; read the result against
      `main.tex:182`.
- [x] N13: drive the same equation with a telegraph and an Ornstein--Uhlenbeck
      coupling; compare the measured mean order against both candidate
      substitutions; recover both limits and the crossover; retain the regime in
      which mean-coupling substitution is refused.
- [x] Regressions for both, the report module, and the repository gates.

## Execution record

### Modules and artifacts

| Module | Layer | Writes |
| :--- | :--- | :--- |
| `quasistatic_error.py` | simulation | `figures/quasistatic_error/quasistatic_error_summary.json` |
| `fluctuating_coupling.py` | simulation | `figures/fluctuating_coupling/fluctuating_coupling_summary.json` |
| `coupling_rate_report.py` | report | the two figures and `figures/COUPLING_RATE_REPORT.md` |

`tach.toml` places the report above both sweeps, `quasistatic_error` above
`recovery_mechanisms` and `fluctuating_coupling` above `quasistatic_error`, so
the report cannot start a run and the two sweeps share one integrator rather
than two.

### The integrator, and why it is not `dynamic_ramp`

The mean-field Fokker--Planck equation at identical frequencies closes on the
Fourier coefficients of the phase density:

    dh_k/dt = - D k^2 h_k + (K r k / 2) (h_{k-1} - h_{k+1}),  h_0 = 1,  r = h_1,

integrated by exponential Heun, which treats the diffusive part exactly and is
therefore stable at every retained harmonic. This is deterministic, so what it
measures is the error of the *reduction*; `dynamic_ramp.py` is a finite-`N`
Langevin integrator on phases and its residual is the reduction error and the
population fluctuation together, with no way to separate them. There was no
shared integrator in this repository to reuse, which the R8 triage had already
recorded.

The positive control is exact and is the reason the residuals below can be
trusted: started at the von Mises density of the coherent branch and held at a
fixed coupling, the order parameter moves by `1.1e-16` over 200 steps. Halving
the step moves a measured residual by `4.4e-6`, against a tolerance of `5e-3`.

### Order of work, stated honestly

The regressions in `test_quasistatic_error.py`, `test_fluctuating_coupling.py`
and `test_coupling_rate_report.py` were written **after** the modules they
exercise, not before, so this pass did not follow the red-green order AGENTS.md
§1 asks for — the same departure the N7–N9 pass recorded. The written
specification above and the two exact controls stand in for the red half:

1. The stationary control is a statement the integrator can fail and does not:
   an exactly stationary density that moves would manufacture a residual the
   rate did not cause.
2. Both modules carry a case the measurement is *required* to fail, and both
   fail it. They are reported below rather than hidden in a test.

### N12 — the quasi-static residual as a function of rate

`quasistatic_error.py`. Every leg starts at the stationary density for its
initial coupling displaced by `0.02` in `r`, and ramps `K` linearly. The
displacement is not decoration: below threshold `r_ss` is identically zero and
the uniform density solves the time-dependent equation exactly, so **a
subcritical leg started on the branch has zero residual at every rate** and
measures nothing. That is a finding about what the subcritical question is —
below threshold the question is how fast a departure decays, not how well a
moving branch is tracked — and it is a regression.

**Findings**, over nine speeds from `1e-4` to `1`, `D = 1`, tolerance `5e-3`:

- **The admissible rate collapses at the threshold, and at the threshold itself
  it does not exist.** On the crossing leg the terminal residual is `0.3934` at
  *every one of the nine speeds*, to four decimals. The reason is exact: on a
  leg symmetric about `K_c` the exponential suppression below threshold and the
  amplification above cancel, `-w^2/4v + w^2/4v = 0`, so the residual is
  rate-independent. A slower ramp does not help, and no admissible speed exists
  at zero distance from threshold at any tolerance below `0.39`.
- **Away from the threshold the criterion is a required time-scale ratio, and it
  is asymmetric.** Writing the coupling time scale as `K_c/|dK/dt|` and the
  phase time scale as `1/D`, the required ratio is `2000` at `|K-K_c| = 0.05`
  and `0.1` above threshold, `632` at `0.2` and `0.4`, and `200` at `0.8`. Below
  threshold the same distances require `200`, `200`, `200`, `63` and `63`. The
  coherent side is three to ten times more demanding than the incoherent one at
  the same distance, because the branch the density must track is moving there
  and the branch below threshold is not.
- **The published bifurcation-delay exponent is the threshold limit of this
  measurement.** Seeding the deterministic run *at* the threshold with the
  finite-`N` fluctuation floor `1/sqrt(2000) = 0.02236` and using
  `dynamic_ramp_report`'s escape level `0.2`, the coupling excess at escape fits
  `v^0.447` over the four published speeds and `v^0.418` over the three the
  published fit used, against the recorded `\rampDelayExponent = 0.443`. The
  published value sits between the two, so the finite-`N` delay and the
  deterministic reduction error are one measurement rather than two results.
- **The required failure.** A residual measured against `r_ss` at each leg's
  *initial* coupling — a branch that has quietly stopped updating — is `0.0814`
  at the slowest speed and `0.0225` at the fastest. It exceeds the tolerance at
  every speed and it *rises* as the rate falls, which is the opposite of the
  behaviour the reduction requires and is how a silently frozen branch looks.

**Read against `main.tex:182`.** The passage motivates coupling that "evolves
more slowly than phase dynamics" and nothing quantified it. The measurement says
what it has to mean: a ratio of coupling to phase time scales of at least the
numbers above, growing without bound as the threshold is approached. Two
declared ranges close the reading, neither of them measured here and neither
stated as a rate by the work cited: the extracellular-geometry change of the
sleep study as a 60–600 s transition, and cortical phase coherence as 10–100 ms.
Together they give a ratio between `600` and `60,000`. **Every scanned leg meets that requirement from `|K-K_c| = 0.8` at the
slow end of the cited range and from `0.05` at the fast end** — and at no
distance for a coupling actually crossing the threshold, where the residual is
rate-independent. The cited time scales are therefore comfortable away from
threshold and buy nothing at it; the sentence "evolves more slowly than phase
dynamics" is true of the cited geometry and is not the condition the crossing
argument needs.

### N13 — a fluctuating coupling and the threshold

`fluctuating_coupling.py`. Two declared processes at equal mean, spread and
correlation time — a symmetric telegraph and an Ornstein--Uhlenbeck process,
both advanced by their exact stationary transition over a step, so the
correlation time is a parameter and not a by-product of `dt`. The Gaussian
coupling is **not** clipped at zero: clipping would move the mean, which is the
statistic under test. 168 drives: 2 processes × 3 amplitudes × 4 correlation
times × 7 mean couplings, 32 replicas each.

**Findings.**

- **The fast limit is the mean coupling, and the slow limit is not.** At
  `tau = 0.03` the worst gap between the measured mean order and `r_ss(mean)` is
  `0.0347` across every drive, against `0.341` for the quasi-static average — a
  factor of ten the right way. At `tau = 30`, on the eight drives whose coupling
  never crosses the threshold, it reverses: the worst gap to `r_ss(mean)` is
  `0.0843` and to `E[r_ss(K)]` is `0.0197`.
- **Mean-coupling substitution is refused in 25 of the 168 drives.** In each the
  mean coupling is at or below `K_c`, so `r_ss(mean)` is exactly zero, and the
  measured mean order exceeds the `0.02` seed the run started from. The
  strongest is a telegraph at mean `2.0` — the threshold itself — amplitude
  `1.0` and correlation time `3`, which gives a mean order of `0.0924`.
- **That failure is a finite-horizon effect, and saying so is part of the
  result.** The growth rate of a small order is linear in `K`, so the long-run
  Lyapunov exponent of a fluctuating coupling is `mean/2 - D` and the *onset*
  threshold is at the mean after all. At four times the measured horizon the
  strongest rejection falls from `0.0924` to `0.0392`. What the mean fails to
  predict is the order on a horizon, not the asymptotic threshold, and a
  recovery measurement is made on a horizon.
- **Neither substitution describes a slow crossing drive.** Where the coupling
  spends time on both sides of the threshold and moves slowly, the order
  collapses on every subcritical excursion and has to be rebuilt from whatever
  is left, so it tracks neither `r_ss(mean)` nor `E[r_ss(K)]`. This is a third
  regime and it is why the slow limit above is read on the non-crossing drives.
- **A crossing drive is not self-averaging.** The strongest rejection's spread
  across replicas is `0.106`, larger than its mean of `0.0924`. A single
  realization of such a coupling says very little about the ensemble, which is a
  constraint on any single-subject reading.
- **The crossover moves with the amplitude.** At amplitude `0.25` the
  quasi-static average first becomes the closer substitution at `tau = 30`; at
  amplitude `1.0` and mean `2.2` it is already closer at `tau = 0.03`. The
  crossover is not a property of the coupling's time scale alone.

## Validation

- `ruff`, `ruff format`, `mypy --strict`, `bandit`, `vulture`, `xenon` and
  `tach` all pass over `simulations/`.
- The full Python suite passes at 257 tests, 43 of them new.
- No publication source, tracked PDF, reference or generated macro is touched.
  The Lean development is untouched by *this* pass; N10 and N11 are a separate
  pass recorded in `tasks/todo.md`.

## What the publication would have to say

Recorded here for the editorial pass that is not part of this one, and tracked
in `tasks/todo.md` as **M1–M3** together with the four sentences N7–N9 deferred.
Eight in all; two deferrals with nothing tracking them is how a numeral that
contradicts a published sentence stays published.

1. `main.tex:182` motivates coupling that "evolves more slowly than phase
   dynamics" and quantifies nothing. N12 supplies the criterion — a required
   ratio of coupling to phase time scales that grows without bound at the
   threshold — and the reading of the cited geometry against it.
2. `supplementary.tex` reports `Delta K ∝ v^0.443` as "near the predicted
   exponent 1/2 at this resolution". N12 supplies the rest: the deterministic
   threshold limit of the same measurement gives `0.447` over four speeds and
   `0.418` over three, so the shortfall from `1/2` belongs to the seed and the
   speed window rather than to the finite population.
3. The recovery section reads a crossing of `K_c` as an onset. N12 shows the
   quasi-static residual on a leg symmetric about `K_c` is rate-independent, so
   "slowly enough to track the branch" is unattainable *at* the crossing, which
   is where the recovery argument uses it.
4. Nothing in the publication says which statistic of a varying coupling `K_c`
   is to be read against. N13 supplies the answer and its two failure modes: the
   mean in the fast limit, the quasi-static average of the branch in the slow
   non-crossing limit, and neither for a slow crossing drive.
