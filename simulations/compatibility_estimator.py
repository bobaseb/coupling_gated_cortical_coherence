"""An observable for the compatibility clause, measured against constructed answers.

The framework's unity claim has two halves. Supercritical coupling has an
observable and a competing account; the compatibility clause — that overlapping
regions carry local descriptions which agree where they meet — has no observable
at all. This module builds one, and spends most of its length finding out what
it cannot do.

**The restriction map.** A patch's decoded object here is one probability
distribution over a finite content alphabet per site of the patch. Restriction
to a shared sub-territory is the tuple of those distributions at the shared
sites, and two patches are compatible when the restricted tuples are equal. This
is the pointwise reading of `restrict_eq_iff_densityOn_eqOn`, transported to
probability laws: that theorem is about finite spatial measures, and whether
compatible overlaps extend to a unique global law is a separate question that is
neither imported nor assumed here.

**The statistic.** The mean total-variation distance between the two patches'
distributions over the shared sites. Its null is the same generative
configuration with a single-valued content field, so the null spread is decoding
noise and nothing else, and its uncertainty is taken by resampling *trials*
rather than site-level values: sites within a trial share a latent content field
and an overlap, so a site-level resample would treat dependent numbers as
independent. Both are reported, and their ratio is the inflation a
dependence-blind interval would have missed.

**The constructed configurations.** Compatibility is built in rather than
inferred. `single_valued` gives both patches the same content field;
`disagreeing` shifts the second patch's labels on the overlap alone, which is
`overlap_agreement_fails` in the Lean development — one common phase, two
descriptions differing exactly where the patches meet.

**The silent failures.** A decoder shrinking both regional posteriors toward a
shared prior reports compatibility whatever the regions encode; a decoder with
independent per-region bias reports incompatibility whatever they encode.
Neither is visible in the statistic, so each is caught by a separate per-patch
diagnostic, and the run records that the statistic alone did not catch it.

**Scope.** Synthetic and constructed data only. No neural recording is analysed;
the per-patch diagnostics read the true content on each patch's private sites,
which a real experiment would have to supply as a decodable variable with known
values. Nothing here derives compatibility from coherence, selects a cover, or
identifies the content model with neural variables.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import cast

import numpy as np
from numpy.typing import NDArray
from scipy.stats import rankdata


FloatArray = NDArray[np.float64]
IntArray = NDArray[np.int64]

# Anchored on this file, not the working directory: simulations/README.md.
FIGURES = Path(__file__).resolve().parent / "figures"
PRODUCTION_OUTPUT = FIGURES / "compatibility_estimator"

SEED = 20260916
# The interval's resampling runs on its own stream, so that quoting an interval
# beside a score does not move the score.
INTERVAL_SEED = 20260917
BOOTSTRAP_RESAMPLES = 2000
CONFIDENCE_LEVEL = 0.95

# A patch's decoded content must carry at least this share of the content
# entropy before its compatibility reading is admitted, and its private-site
# accuracy must stay within this factor of the matched decoder's. Both are
# declared thresholds, not measurements.
INFORMATION_FLOOR = 0.25
ACCURACY_FLOOR = 0.75

# A patch's reported confidence must also match how often it is right, to within
# this much, on its own private sites. It is the diagnostic that catches a bias
# too mild to move the modal label: such a decoder stays accurate and stays
# informative, and only its confidence gives it away.
CALIBRATION_CEILING = 0.15

# The separation a usable observable is required to reach: the incompatible
# statistic must stand this many null standard deviations above the null mean.
SEPARATION_TARGET = 3.0


@dataclass(frozen=True)
class Territory:
    """Two patches on a line of sites, and the alphabet their content takes."""

    sites: int = 24
    patch_size: int = 16
    alphabet: int = 4
    content_block: int = 4

    def __post_init__(self) -> None:
        if not 1 <= self.patch_size <= self.sites:
            raise ValueError("each patch fits inside the territory")
        if self.overlap < 1:
            raise ValueError("the two patches must share at least one site")
        if self.alphabet < 2:
            raise ValueError("a content alphabet has at least two labels")
        if self.content_block < 1:
            raise ValueError("a content block holds at least one site")

    @property
    def blocks(self) -> int:
        """Independently drawn content blocks behind the site field."""
        return -(-self.sites // self.content_block)

    @property
    def overlap(self) -> int:
        """Sites the two patches share: the sub-territory the statistic reads."""
        return 2 * self.patch_size - self.sites

    @property
    def shared(self) -> slice:
        return slice(self.sites - self.patch_size, self.patch_size)

    @property
    def private_first(self) -> slice:
        return slice(0, self.sites - self.patch_size)

    @property
    def private_second(self) -> slice:
        return slice(self.patch_size, self.sites)


@dataclass(frozen=True)
class Decoder:
    """One patch's readout: its own noise, and the two ways it can fail silently."""

    error: float = 0.2
    shrinkage: float = 0.0
    bias: int = 0
    bias_weight: float = 0.0
    trial_spread: float = 1.0

    def __post_init__(self) -> None:
        if not 0.0 <= self.error < 1.0:
            raise ValueError("the per-site decoding error is a probability below one")
        if not 0.0 <= self.shrinkage <= 1.0 or not 0.0 <= self.bias_weight <= 1.0:
            raise ValueError("shrinkage and bias weight are probabilities")
        if self.trial_spread < 0.0:
            raise ValueError("the trial-to-trial quality spread is nonnegative")


@dataclass(frozen=True)
class Configuration:
    """One constructed answer: what the content is, and how it relates to phase."""

    name: str
    disagree: bool = False
    phase_content: bool = False
    phase_locked: bool = False
    label_shift: int = 1


def _expand(blocked: NDArray[np.generic], territory: Territory) -> NDArray[np.generic]:
    """Broadcast a per-block field onto the sites of the territory."""
    return np.repeat(blocked, territory.content_block, axis=1)[:, : territory.sites]


def _draw_phases(rng: np.random.Generator, shape: tuple[int, int], locked: bool) -> FloatArray:
    if locked:
        common = rng.uniform(-np.pi, np.pi, size=(shape[0], 1))
        return np.repeat(common, shape[1], axis=1)
    return rng.uniform(-np.pi, np.pi, size=shape)


def _content_from(
    rng: np.random.Generator, phases: FloatArray, territory: Territory, phase_content: bool
) -> IntArray:
    if phase_content:
        fraction = (phases + np.pi) / (2.0 * np.pi)
        return cast(
            IntArray,
            np.minimum((fraction * territory.alphabet).astype(np.int64), territory.alphabet - 1),
        )
    return rng.integers(0, territory.alphabet, size=phases.shape)


@dataclass(frozen=True)
class Trials:
    """One generated block: phases, each patch's content field, and the observations."""

    phases: FloatArray
    content_first: IntArray
    content_second: IntArray
    observed_first: IntArray
    observed_second: IntArray


def _trial_error(rng: np.random.Generator, decoder: Decoder, trials: int) -> FloatArray:
    """The true per-trial corruption rate, which the decoder does not know.

    Decoding quality is not constant across trials, and the decoder's likelihood
    table is built from its declared `error` rather than from the trial's actual
    one. This is what makes the per-site statistics within a trial dependent:
    every shared site of a bad trial is decoded badly together. A resample that
    treats those sites as independent is the interval this module reports
    alongside the honest one.
    """
    if decoder.trial_spread <= 0.0:
        return cast(FloatArray, np.full(trials, decoder.error))
    draw = rng.lognormal(-0.5 * decoder.trial_spread**2, decoder.trial_spread, size=trials)
    return cast(FloatArray, np.clip(decoder.error * draw, 0.0, 0.95))


def _corrupt(
    rng: np.random.Generator, content: IntArray, alphabet: int, error: FloatArray
) -> IntArray:
    """Replace each label by a uniformly drawn one at that trial's corruption rate."""
    flipped = rng.random(content.shape) < error[:, None]
    replacement = rng.integers(0, alphabet, size=content.shape)
    return cast(IntArray, np.where(flipped, replacement, content))


def generate(
    rng: np.random.Generator,
    territory: Territory,
    configuration: Configuration,
    decoders: tuple[Decoder, Decoder],
    trials: int,
) -> Trials:
    """Build one block of trials realising a configuration whose answer is known."""
    blocked = _draw_phases(rng, (trials, territory.blocks), configuration.phase_locked)
    phases = cast(FloatArray, _expand(blocked, territory))
    content = cast(
        IntArray,
        _expand(_content_from(rng, blocked, territory, configuration.phase_content), territory),
    )
    second = content.copy()
    if configuration.disagree:
        shared = territory.shared
        second[:, shared] = (second[:, shared] + configuration.label_shift) % territory.alphabet
    return Trials(
        phases=phases,
        content_first=content,
        content_second=second,
        observed_first=_corrupt(
            rng, content, territory.alphabet, _trial_error(rng, decoders[0], trials)
        ),
        observed_second=_corrupt(
            rng, second, territory.alphabet, _trial_error(rng, decoders[1], trials)
        ),
    )


def posterior(observed: IntArray, territory: Territory, decoder: Decoder) -> FloatArray:
    """The per-site Bayes posterior a patch reports, after its own two distortions.

    The matched part is the likelihood of a uniformly drawn label corrupted with
    probability `error`. `shrinkage` then mixes the posterior toward the shared
    prior and `bias` rotates a fixed share of its mass onto a neighbouring label;
    both are decoder properties, applied after decoding and invisible to anyone
    reading the posterior alone.
    """
    alphabet = territory.alphabet
    matched = decoder.error / alphabet
    hit = 1.0 - decoder.error + matched
    table = np.full((alphabet, alphabet), matched)
    np.fill_diagonal(table, hit)
    posteriors = table[observed] / table[observed].sum(axis=-1, keepdims=True)
    if decoder.bias_weight > 0.0:
        rotated = np.roll(posteriors, decoder.bias, axis=-1)
        posteriors = (1.0 - decoder.bias_weight) * posteriors + decoder.bias_weight * rotated
    if decoder.shrinkage > 0.0:
        uniform = np.full(alphabet, 1.0 / alphabet)
        posteriors = (1.0 - decoder.shrinkage) * posteriors + decoder.shrinkage * uniform
    return cast(FloatArray, posteriors)


def restrict(posteriors: FloatArray, territory: Territory) -> FloatArray:
    """The restriction map: the patch's distributions at the shared sites."""
    return posteriors[:, territory.shared, :]


def per_trial_statistic(first: FloatArray, second: FloatArray) -> FloatArray:
    """Mean total-variation distance between the restricted tuples, per trial."""
    return cast(FloatArray, 0.5 * np.abs(first - second).sum(axis=-1).mean(axis=-1))


@dataclass(frozen=True)
class Uncertainty:
    """The statistic with a dependence-aware and a dependence-blind interval."""

    value: float
    trial_sd: float
    site_sd: float

    @property
    def inflation(self) -> float:
        """How much a site-level resample would have understated the spread."""
        return self.trial_sd / self.site_sd if self.site_sd > 0.0 else float("inf")


def uncertainty(
    per_trial: FloatArray,
    per_site: FloatArray,
    rng: np.random.Generator,
    resamples: int = BOOTSTRAP_RESAMPLES,
) -> Uncertainty:
    """Bootstrap the statistic by trial and, for comparison, by site."""
    trials = per_trial.size
    flat = per_site.reshape(-1)
    trial_draws = per_trial[rng.integers(0, trials, size=(resamples, trials))].mean(axis=1)
    site_draws = flat[rng.integers(0, flat.size, size=(resamples, flat.size))].mean(axis=1)
    return Uncertainty(
        value=float(per_trial.mean()),
        trial_sd=float(np.std(trial_draws)),
        site_sd=float(np.std(site_draws)),
    )


def decoded_information(posteriors: FloatArray, truth: IntArray, alphabet: int) -> float:
    """Share of the content entropy the reported posteriors carry, in `[0, 1]`.

    The log-score gain over the uniform prior, divided by that prior's entropy.
    A decoder shrunk all the way onto the shared prior scores zero here while
    leaving its own modal label unchanged, which is why sharpness rather than
    accuracy is the diagnostic that catches it.
    """
    taken = np.take_along_axis(posteriors, truth[..., None], axis=-1)[..., 0]
    gain = float(np.log(alphabet) + np.mean(np.log(np.clip(taken, 1e-12, None))))
    return gain / float(np.log(alphabet))


def modal_accuracy(posteriors: FloatArray, truth: IntArray) -> float:
    """How often the reported mode is the true label."""
    return float(np.mean(np.argmax(posteriors, axis=-1) == truth))


def calibration_gap(posteriors: FloatArray, truth: IntArray) -> float:
    """How far the reported confidence is from how often the report is right."""
    confidence = float(np.mean(np.max(posteriors, axis=-1)))
    return abs(confidence - modal_accuracy(posteriors, truth))


def phase_observable(phases: FloatArray, territory: Territory) -> dict[str, float]:
    """The compatibility residual a phase measurement alone licenses.

    `compatible_of_coherence` bounds overlap disagreement by a Lipschitz
    constant times a chord set by the phases, so the phase-derived observable is
    the chord between the two patches' mean phases plus the coherence residual
    each patch's own order parameter leaves. At unit Lipschitz constant this is
    directly comparable with the total-variation statistic; the comparison is
    the point, and what it exposes is that the bound is silent about any content
    that is not a function of the phase.
    """
    first = np.mean(np.exp(1j * phases[:, : territory.patch_size]), axis=1)
    second = np.mean(np.exp(1j * phases[:, territory.sites - territory.patch_size :]), axis=1)
    chord = np.abs(np.exp(1j * np.angle(first)) - np.exp(1j * np.angle(second)))
    coherence = np.minimum(np.abs(first), np.abs(second))
    residual = np.sqrt(np.clip(1.0 - coherence**2, 0.0, None))
    return {
        "chord": float(np.mean(chord)),
        "coherence_residual": float(np.mean(residual)),
        "bound": float(np.mean(chord + residual)),
    }


def phase_content_share(phases: FloatArray, content: IntArray, alphabet: int, bins: int) -> float:
    """`I(binned phase; content) / H(content)`: what fraction of the content is phase.

    The plug-in estimate on the generated trials. It is the quantity that
    decides whether a phase-derived observable could stand in for the content
    one at all: `compatible_of_coherence` bounds disagreement of content that is
    a function of the local phase, and says nothing about the rest.
    """
    binned = np.minimum(((phases + np.pi) / (2.0 * np.pi) * bins).astype(np.int64), bins - 1)
    joint = np.zeros((bins, alphabet))
    np.add.at(joint, (binned.reshape(-1), content.reshape(-1)), 1.0)
    joint /= joint.sum()
    row = joint.sum(axis=1, keepdims=True)
    column = joint.sum(axis=0, keepdims=True)
    with np.errstate(divide="ignore", invalid="ignore"):
        terms = joint * np.log(joint / (row * column))
    entropy = float(-np.sum(column * np.log(np.where(column > 0.0, column, 1.0))))
    mutual = float(np.nansum(terms))
    return mutual / entropy if entropy > 0.0 else 0.0


def auc(positive: FloatArray, negative: FloatArray) -> float:
    """Probability that a draw from `positive` exceeds one from `negative`.

    Ranks are tie-averaged, so two identical samples score exactly one half
    rather than whichever of them the sort happened to put first.
    """
    ranks = rankdata(np.concatenate((negative, positive)))
    rank_sum = float(np.sum(ranks[negative.size :]))
    return (rank_sum - positive.size * (positive.size + 1) / 2.0) / (positive.size * negative.size)


def auc_interval(
    positive: FloatArray,
    negative: FloatArray,
    rng: np.random.Generator,
    resamples: int = BOOTSTRAP_RESAMPLES,
    level: float = CONFIDENCE_LEVEL,
) -> tuple[float, float]:
    """Percentile bootstrap interval for `auc`, resampling both sides by trial.

    The trial is the independent unit here for the reason `uncertainty` gives:
    sites within a trial share a latent content field, so resampling sites would
    treat dependent numbers as independent and return an interval too narrow to
    be worth quoting. Both samples are resampled, because the score is a
    comparison and the null's spread is half of what moves it.
    """
    draws = [
        auc(
            positive[rng.integers(0, positive.size, positive.size)],
            negative[rng.integers(0, negative.size, negative.size)],
        )
        for _ in range(resamples)
    ]
    tail = 100.0 * (1.0 - level) / 2.0
    low, high = np.percentile(draws, (tail, 100.0 - tail))
    return float(low), float(high)


@dataclass(frozen=True)
class Assessment:
    """One configuration measured, with the diagnostics that admit or reject it."""

    configuration: str
    statistic: float
    trial_sd: float
    site_sd: float
    dependence_inflation: float
    information_first: float
    information_second: float
    accuracy_first: float
    accuracy_second: float
    calibration_first: float
    calibration_second: float
    admitted: bool
    phase_bound: float
    phase_share: float
    z_against_null: float | None = None
    auc_against_null: float | None = None
    auc_low: float | None = None
    auc_high: float | None = None


@dataclass(frozen=True)
class Measurement:
    """An assessment together with the per-trial values a comparison needs."""

    assessment: Assessment
    per_trial: FloatArray


def measure(
    rng: np.random.Generator,
    territory: Territory,
    configuration: Configuration,
    decoders: tuple[Decoder, Decoder],
    trials: int,
) -> Measurement:
    """Generate one configuration, decode it, and run the statistic and diagnostics."""
    data = generate(rng, territory, configuration, decoders, trials)
    first = posterior(data.observed_first, territory, decoders[0])
    second = posterior(data.observed_second, territory, decoders[1])
    per_site = 0.5 * np.abs(restrict(first, territory) - restrict(second, territory)).sum(axis=-1)
    per_trial = cast(FloatArray, per_site.mean(axis=-1))
    spread = uncertainty(per_trial, per_site, rng)
    private = (
        (first[:, territory.private_first], data.content_first[:, territory.private_first]),
        (second[:, territory.private_second], data.content_second[:, territory.private_second]),
    )
    information = tuple(decoded_information(*side, territory.alphabet) for side in private)
    accuracy = tuple(modal_accuracy(*side) for side in private)
    calibration = tuple(calibration_gap(*side) for side in private)
    assessment = Assessment(
        configuration=configuration.name,
        statistic=spread.value,
        trial_sd=spread.trial_sd,
        site_sd=spread.site_sd,
        dependence_inflation=spread.inflation,
        information_first=information[0],
        information_second=information[1],
        accuracy_first=accuracy[0],
        accuracy_second=accuracy[1],
        calibration_first=calibration[0],
        calibration_second=calibration[1],
        admitted=min(information) >= INFORMATION_FLOOR
        and min(accuracy) >= ACCURACY_FLOOR
        and max(calibration) <= CALIBRATION_CEILING,
        phase_bound=phase_observable(data.phases, territory)["bound"],
        phase_share=phase_content_share(
            data.phases, data.content_first, territory.alphabet, territory.alphabet
        ),
    )
    return Measurement(assessment=assessment, per_trial=per_trial)


def against(measurement: Measurement, null: Measurement) -> Assessment:
    """Score a measurement against the constructed compatible null."""
    spread = null.assessment.trial_sd
    return replace(
        measurement.assessment,
        z_against_null=(
            None
            if spread <= 0.0
            else (measurement.assessment.statistic - null.assessment.statistic) / spread
        ),
        auc_against_null=auc(measurement.per_trial, null.per_trial),
    )


SINGLE_VALUED = Configuration("single_valued")
DISAGREEING = Configuration("disagreeing", disagree=True)
LOCKED_SINGLE_VALUED = Configuration("phase_locked_single_valued", phase_locked=True)
LOCKED_DISAGREEING = Configuration("phase_locked_disagreeing", disagree=True, phase_locked=True)
PHASE_CONTENT = Configuration("phase_derived_content", phase_content=True)
PHASE_CONTENT_DISAGREEING = Configuration(
    "phase_derived_content_disagreeing", disagree=True, phase_content=True
)

TRIALS = 600
ERROR_SWEEP = (0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7)
OVERLAP_SWEEP = (2, 4, 8, 12, 16)


def _matched(error: float) -> tuple[Decoder, Decoder]:
    return (Decoder(error=error), Decoder(error=error))


def _pair(
    rng: np.random.Generator,
    territory: Territory,
    decoders: tuple[Decoder, Decoder],
    configuration: Configuration,
    trials: int,
    null_configuration: Configuration = SINGLE_VALUED,
) -> tuple[Assessment, Assessment]:
    """Measure a configuration and its constructed compatible null side by side."""
    null = measure(rng, territory, null_configuration, decoders, trials)
    test = measure(rng, territory, configuration, decoders, trials)
    return against(null, null), against(test, null)


def _scored(
    measurement: Measurement, null: Measurement, interval_rng: np.random.Generator
) -> Assessment:
    """Score a measurement against the null and attach the interval of that score."""
    low, high = auc_interval(measurement.per_trial, null.per_trial, interval_rng)
    return replace(against(measurement, null), auc_low=low, auc_high=high)


def baseline(
    rng: np.random.Generator, territory: Territory, error: float, trials: int
) -> list[Assessment]:
    """Every constructed configuration at the declared decoding quality, with intervals.

    These are the rows the manuscript quotes, so these are the rows that carry
    an interval; the degradation sweeps report separation in null standard
    deviations, which is an interval statement already.
    """
    decoders = _matched(error)
    null = measure(rng, territory, SINGLE_VALUED, decoders, trials)
    interval_rng = np.random.default_rng(INTERVAL_SEED)
    configurations = (
        SINGLE_VALUED,
        DISAGREEING,
        LOCKED_SINGLE_VALUED,
        LOCKED_DISAGREEING,
        PHASE_CONTENT,
        PHASE_CONTENT_DISAGREEING,
    )
    return [
        _scored(measure(rng, territory, configuration, decoders, trials), null, interval_rng)
        for configuration in configurations
    ]


def silent_failure_controls(
    rng: np.random.Generator, territory: Territory, error: float, trials: int
) -> list[dict[str, object]]:
    """The two decoder failures the statistic alone cannot see.

    Each is run against the constructed answer it contradicts: shrinkage against
    a genuinely incompatible pair, per-region bias against a genuinely
    compatible one. What is recorded is both the statistic's verdict and the
    diagnostic's, so that the statistic silently agreeing with the decoder is
    part of the saved record rather than a claim about it.
    """
    shrunk = (Decoder(error=error, shrinkage=0.98), Decoder(error=error, shrinkage=0.98))
    biased = (
        Decoder(error=error, bias=1, bias_weight=0.45),
        Decoder(error=error, bias=-1, bias_weight=0.45),
    )
    honest = measure(rng, territory, SINGLE_VALUED, _matched(error), trials)
    null = against(honest, honest)
    reference = against(measure(rng, territory, DISAGREEING, _matched(error), trials), honest)
    shrunk_case = against(measure(rng, territory, DISAGREEING, shrunk, trials), honest)
    biased_case = against(measure(rng, territory, SINGLE_VALUED, biased, trials), honest)
    return [
        _control_row(
            "shrinkage_toward_shared_prior", "compatibility", shrunk_case, null, reference
        ),
        _control_row(
            "independent_per_region_bias", "incompatibility", biased_case, null, reference
        ),
    ]


def _control_row(
    name: str, manufactures: str, case: Assessment, null: Assessment, reference: Assessment
) -> dict[str, object]:
    """Record what the statistic said, what the truth was, and what caught it."""
    separated = case.z_against_null is not None and case.z_against_null >= SEPARATION_TARGET
    truth_is_incompatible = manufactures == "compatibility"
    return {
        "control": name,
        "manufactures": manufactures,
        "honest_null_statistic": null.statistic,
        "honest_null_trial_sd": null.trial_sd,
        "honest_incompatible_statistic": reference.statistic,
        "assessment": asdict(case),
        "statistic_alone_is_fooled": separated is not truth_is_incompatible,
        "rejected_by_information": min(case.information_first, case.information_second)
        < INFORMATION_FLOOR,
        "rejected_by_accuracy": min(case.accuracy_first, case.accuracy_second) < ACCURACY_FLOOR,
        "rejected_by_calibration": max(case.calibration_first, case.calibration_second)
        > CALIBRATION_CEILING,
        "rejected_by_diagnostic": not case.admitted,
    }


def phase_observable_control(
    rng: np.random.Generator, territory: Territory, error: float, trials: int
) -> dict[str, object]:
    """The constructed case a phase-derived statistic is required to fail.

    One common phase across both patches and content that differs exactly on the
    overlap: `overlap_agreement_fails`. The phase bound goes to zero, reporting
    perfect compatibility, while the content statistic reports the disagreement
    that was built in.
    """
    decoders = _matched(error)
    null, locked = _pair(rng, territory, decoders, LOCKED_DISAGREEING, trials, LOCKED_SINGLE_VALUED)
    return {
        "control": "phase_derived_statistic",
        "assessment": asdict(locked),
        "null_assessment": asdict(null),
        "phase_bound_reports_compatible": locked.phase_bound < 1e-6,
        "content_statistic_reports_incompatible": locked.z_against_null is not None
        and locked.z_against_null > SEPARATION_TARGET,
        "required_failure_observed": locked.phase_bound < 1e-6
        and locked.z_against_null is not None
        and locked.z_against_null > SEPARATION_TARGET,
    }


def phase_carried_content(rows: list[Assessment]) -> dict[str, object]:
    """What the phase carries of each content model, and whether the bound sees it.

    `compatible_of_coherence` bounds overlap disagreement of content that is a
    Lipschitz function of the local phase. One content model here is exactly
    that and the other is drawn free of the phase, so the share of content
    entropy the phase carries separates them completely. The phase-derived bound
    does not: it is computed from the phases and is blind to which content model
    produced them, which is why it cannot decide the compatibility question on
    its own.
    """
    by_name = {row.configuration: row for row in rows}
    derived = by_name[PHASE_CONTENT.name]
    free = by_name[SINGLE_VALUED.name]
    return {
        "phase_derived_share": derived.phase_share,
        "phase_free_share": free.phase_share,
        "phase_derived_bound": derived.phase_bound,
        "phase_free_bound": free.phase_bound,
        "share_separates_the_models": derived.phase_share - free.phase_share > 0.5,
        "bound_separates_the_models": abs(derived.phase_bound - free.phase_bound) > 0.5,
    }


def _usable(assessment: Assessment) -> bool:
    return (
        assessment.admitted
        and assessment.z_against_null is not None
        and assessment.z_against_null >= SEPARATION_TARGET
    )


def error_degradation(
    rng: np.random.Generator, territory: Territory, trials: int
) -> list[dict[str, object]]:
    """Separation of the constructed pair as the decoders get worse."""
    rows: list[dict[str, object]] = []
    for error in ERROR_SWEEP:
        _, test = _pair(rng, territory, _matched(error), DISAGREEING, trials)
        rows.append(
            {
                "error": error,
                "usable": _usable(test),
                "admitted": test.admitted,
                "separated": test.z_against_null is not None
                and test.z_against_null >= SEPARATION_TARGET,
                "assessment": asdict(test),
            }
        )
    return rows


def coverage_degradation(
    rng: np.random.Generator, territory: Territory, error: float, trials: int
) -> list[dict[str, object]]:
    """Separation as the shared sub-territory shrinks."""
    rows: list[dict[str, object]] = []
    for overlap in OVERLAP_SWEEP:
        patch_size = (territory.sites + overlap) // 2
        if 2 * patch_size - territory.sites != overlap or patch_size > territory.sites:
            continue
        narrowed = replace(territory, patch_size=patch_size)
        _, test = _pair(rng, narrowed, _matched(error), DISAGREEING, trials)
        rows.append(
            {
                "overlap": overlap,
                "usable": _usable(test),
                "admitted": test.admitted,
                "separated": test.z_against_null is not None
                and test.z_against_null >= SEPARATION_TARGET,
                "assessment": asdict(test),
            }
        )
    return rows


def build_summary(trials: int = TRIALS, error: float = 0.2, seed: int = SEED) -> dict[str, object]:
    """Run every constructed case, control and sweep, and collect the record."""
    rng = np.random.default_rng(seed)
    territory = Territory()
    rows = baseline(rng, territory, error, trials)
    errors = error_degradation(rng, territory, trials)
    coverage = coverage_degradation(rng, territory, error, trials)
    usable_errors = [float(cast(float, row["error"])) for row in errors if row["usable"]]
    usable_overlaps = [int(cast(int, row["overlap"])) for row in coverage if row["usable"]]
    return {
        "source": "compatibility_estimator.py",
        "territory": asdict(territory),
        "overlap": territory.overlap,
        "trials": trials,
        "decoding_error": error,
        "seed": seed,
        "thresholds": {
            "information_floor": INFORMATION_FLOOR,
            "accuracy_floor": ACCURACY_FLOOR,
            "separation_target": SEPARATION_TARGET,
        },
        "restriction_map": (
            "per-site distributions at the shared sites; compatibility is equality of "
            "those restricted tuples, with global extension and uniqueness neither "
            "imported nor assumed"
        ),
        "baseline": [asdict(row) for row in rows],
        "phase_carried_content": phase_carried_content(rows),
        "silent_failure_controls": silent_failure_controls(rng, territory, error, trials),
        "phase_observable_control": phase_observable_control(rng, territory, error, trials),
        "error_degradation": errors,
        "coverage_degradation": coverage,
        "worst_usable_error": max(usable_errors) if usable_errors else None,
        "smallest_usable_overlap": min(usable_overlaps) if usable_overlaps else None,
        "scope": (
            "synthetic and constructed data only; no recording is analysed and the "
            "per-patch diagnostics read ground truth on each patch's private sites"
        ),
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="fewer trials, same code path")
    parser.add_argument("--output", type=Path, default=None)
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    output = args.output or PRODUCTION_OUTPUT
    summary = build_summary(trials=40 if args.smoke else TRIALS)
    output.mkdir(parents=True, exist_ok=True)
    (output / "compatibility_estimator_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    for row in cast(list[dict[str, object]], summary["baseline"]):
        print(
            f"{row['configuration']:34s} stat={row['statistic']:.4f} "
            f"z={row['z_against_null']} auc={row['auc_against_null']} "
            f"phase_bound={row['phase_bound']:.4f} phase_share={row['phase_share']:.3f}"
        )
    print(f"worst usable decoding error: {summary['worst_usable_error']}")
    print(f"smallest usable overlap: {summary['smallest_usable_overlap']}")
    print(f"wrote {output / 'compatibility_estimator_summary.json'}")


if __name__ == "__main__":
    main()
