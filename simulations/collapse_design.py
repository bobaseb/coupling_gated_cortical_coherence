"""What a measurement must look like for the concentration--coherence test to decide.

The supplement concedes that the observed concentration range does not separate
the Bessel ratio `R(a) = I_1(a)/I_0(a)` from its tangent `a/2` at the trace's
scatter, and does not say what range would. This module says what range would,
and at what sample count and under how much between-site dependence.

**The separation.** `tangent_gap(a) = a/2 - R(a)` is the difference in what the
two relations predict at the same concentration. It is zero to third order at
`a = 0` and grows without bound, so a recording confined to small `a` cannot
tell the relations apart however many samples it collects.

**The floor.** The estimator `empirical_collapse.concentration_a` is a
pseudocount-regularised log-density slope. Its null residual `r - R(a-hat)` on
data drawn from a genuine von Mises has a bias and a scatter, both of which grow
as the per-bin sample count falls. `residual_floor` is
`|bias| + FLOOR_SIGMA * scatter`: a systematic offset masquerades as a departure
from the curve just as a wide scatter does, so both enter the floor.

**The dependence model.** The published calibration draws independent samples,
which the supplement already calls optimistic for EEG. The model declared here
is a two-level cluster: `SITES_PER_CLUSTER` sites share a cluster mean drawn
from `VM(0, kappa_between)`, and each site is drawn from `VM(mu_cluster,
kappa_within)`. One parameter `dependence` in `[0, 1]` moves the marginal
resultant between the two levels, holding `R(kappa_between) * R(kappa_within) =
R(a)` so that every dependence level has the same marginal concentration and the
comparison is about dependence alone. `dependence = 0` reproduces the
independent calibration exactly; `dependence = 1` makes the sites within a
cluster identical, so the effective count is the number of clusters.

**What this is not.** No recording is re-analysed here and no coupling constant
is fitted. The observed range enters only as the interval already saved by the
exploratory analysis, read against the specification rather than re-measured,
and nothing below claims that cortex occupies the required range.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import cast

import numpy as np
from numpy.typing import NDArray
from scipy.optimize import brentq

import empirical_collapse as collapse


FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
FIGURES = Path(__file__).resolve().parent / "figures"
PRODUCTION_OUTPUT = FIGURES / "collapse_design"

# Sites sharing one cluster mean under the declared dependence model. Ten is the
# order of magnitude at which scalp channels duplicate one another; it is a
# declared modelling choice and not a measurement of volume conduction.
SITES_PER_CLUSTER = 10

# Multiples of the null scatter that the floor adds to the null bias.
FLOOR_SIGMA = 2.0

# Replicates per calibration cell. The published calibration uses 500 at 100
# samples and the floor is a mean and a standard deviation over the same kind of
# draw, so 500 is the cap. It is not affordable at every count in the grid: the
# budget below holds the drawn phases per cell roughly fixed, which spends
# replicates where the floor is wide and the estimate of it needs them.
REPLICAS = 500
REPLICA_BUDGET = 5_000_000
REPLICA_MINIMUM = 150

# The site count the proposed spatial protocol permits, and the pooled count the
# exploratory EEG bins actually contain.
PROTOCOL_SITES = 100
POOLED_SITES = 31_000

# Histogram bins the published estimator uses. It is a free parameter of the
# estimator rather than of the physics, so a specification that reports a count
# as unusable owes a check that the count is not simply under-binned.
DEFAULT_BINS = 40
BIN_SWEEP = (6, 10, 16, 24, 40)

DEFAULT_SITE_COUNTS = (100, 300, 1_000, 3_000, 31_000)
DEFAULT_DEPENDENCES = (0.0, 0.25, 0.5, 0.75, 1.0)
DEFAULT_CONCENTRATIONS = (0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0)

SEED = 20260916


def bessel_ratio(a: float) -> float:
    """`R(a) = I_1(a)/I_0(a)`, by the quadrature the rest of the repository uses."""
    return collapse.bessel_ratio(a)


def tangent_gap(a: float) -> float:
    """`a/2 - R(a)`: what the linear approximation over-predicts at concentration `a`."""
    return a / 2.0 - bessel_ratio(a)


def inverse_bessel_ratio(target: float, upper: float = 200.0) -> float:
    """The concentration whose resultant is `target`, or infinity at `target = 1`."""
    if not 0.0 <= target <= 1.0:
        raise ValueError("a resultant length lies in [0, 1]")
    if target <= 0.0:
        return 0.0
    if target >= 1.0:
        return float("inf")
    return float(brentq(lambda a: bessel_ratio(a) - target, 1e-12, upper))


@dataclass(frozen=True)
class Dependence:
    """One level of the declared two-level cluster model."""

    share: float
    sites_per_cluster: int = SITES_PER_CLUSTER

    def __post_init__(self) -> None:
        if not 0.0 <= self.share <= 1.0:
            raise ValueError("the dependence share lies in [0, 1]")
        if self.sites_per_cluster < 1:
            raise ValueError("a cluster holds at least one site")

    def clusters(self, n_sites: int) -> int:
        """Independent cluster means behind `n_sites` sites."""
        return max(1, n_sites // self.sites_per_cluster)

    def effective_sites(self, n_sites: int) -> float:
        """The count an independent calibration would have to use instead.

        At `share = 0` every site is its own draw and this is `n_sites`; at
        `share = 1` the sites within a cluster are identical and only the
        cluster means vary, so it is the cluster count. In between the sites are
        neither, and the interpolation below is a reported diagnostic rather
        than a substitute for the calibration itself: the point of measuring the
        floor under dependence is that no single effective count reproduces it.
        """
        clusters = self.clusters(n_sites)
        return float(n_sites ** (1.0 - self.share) * clusters**self.share)


def draw_phases(
    rng: np.random.Generator, a: float, n_sites: int, dependence: Dependence
) -> FloatArray:
    """Draw one clustered sample of `n_sites` phases with marginal concentration `a`."""
    if n_sites < 1:
        raise ValueError("a sample holds at least one site")
    resultant = bessel_ratio(a)
    kappa_within = inverse_bessel_ratio(resultant ** (1.0 - dependence.share))
    kappa_between = inverse_bessel_ratio(resultant**dependence.share)
    clusters = dependence.clusters(n_sites)
    means = (
        np.zeros(clusters)
        if not np.isfinite(kappa_between)
        else rng.vonmises(0.0, kappa_between, clusters)
    )
    assignment = np.arange(n_sites) % clusters
    centres = means[assignment]
    if not np.isfinite(kappa_within):
        return centres
    return centres + rng.vonmises(0.0, kappa_within, n_sites)


def replicas_for(n_sites: int, cap: int = REPLICAS) -> int:
    """Replicates at this count: the cap, thinned by the per-cell phase budget."""
    if n_sites < 1:
        raise ValueError("a sample holds at least one site")
    return int(min(cap, max(min(cap, REPLICA_MINIMUM), REPLICA_BUDGET // n_sites)))


@dataclass(frozen=True)
class NullResidual:
    """The estimator's own residual on data the curve is true of."""

    concentration: float
    n_sites: int
    dependence: float
    replicas: int
    bins: int
    a_mean: float
    residual_mean: float
    residual_sd: float

    @property
    def floor(self) -> float:
        """`|bias| + FLOOR_SIGMA * scatter`, the departure a measurement cannot call real."""
        return abs(self.residual_mean) + FLOOR_SIGMA * self.residual_sd

    @property
    def separation(self) -> float:
        """The tangent gap a measurement here could actually exploit.

        The curve is separated from its tangent by `tangent_gap(a)` at the true
        concentration, but an analyst reads `a-hat`, and at small counts the
        pseudocount pulls `a-hat` well below `a` into a part of the curve where
        the two relations are closer together. Taking the smaller of the two
        gaps makes the specification hold whichever of them the measurement is
        really working with, rather than crediting it with a separation it
        cannot see.
        """
        return min(tangent_gap(self.concentration), tangent_gap(self.a_mean))


def null_residual(
    a: float,
    n_sites: int,
    dependence: Dependence,
    replicas: int = REPLICAS,
    seed: int = SEED,
    bins: int = DEFAULT_BINS,
) -> NullResidual:
    """Calibrate `r - R(a-hat)` on von Mises draws at this count and dependence."""
    rng = np.random.default_rng(seed)
    estimates = np.empty((replicas, 2))
    for index in range(replicas):
        phases = draw_phases(rng, a, n_sites, dependence)
        estimates[index] = (
            collapse.concentration_a(phases, n_bins=bins),
            collapse.order_parameter_r(phases),
        )
    predicted = np.array([bessel_ratio(value) for value in estimates[:, 0]])
    residual = estimates[:, 1] - predicted
    return NullResidual(
        concentration=a,
        n_sites=n_sites,
        dependence=dependence.share,
        replicas=replicas,
        bins=bins,
        a_mean=float(np.mean(estimates[:, 0])),
        residual_mean=float(np.mean(residual)),
        residual_sd=float(np.std(residual)),
    )


def separates(row: NullResidual) -> bool:
    """Does the usable tangent gap here clear the estimator's own residual floor?"""
    return row.separation > row.floor


def calibration_grid(
    concentrations: tuple[float, ...] = DEFAULT_CONCENTRATIONS,
    site_counts: tuple[int, ...] = DEFAULT_SITE_COUNTS,
    dependences: tuple[float, ...] = DEFAULT_DEPENDENCES,
    replica_cap: int = REPLICAS,
) -> list[NullResidual]:
    """Calibrate every declared (concentration, count, dependence) cell."""
    rows: list[NullResidual] = []
    for n_sites in site_counts:
        replicas = replicas_for(n_sites, replica_cap)
        for share in dependences:
            for a in concentrations:
                row = null_residual(a, n_sites, Dependence(share), replicas)
                rows.append(row)
                print(
                    f"n={n_sites:6d} d={share:.2f} a={a:.1f} "
                    f"bias={row.residual_mean:+.4f} sd={row.residual_sd:.4f} "
                    f"sep={row.separation:.4f} floor={row.floor:.4f} "
                    f"{'separates' if separates(row) else 'below floor'}",
                    flush=True,
                )
    return rows


def bin_sensitivity(
    n_sites: int = PROTOCOL_SITES,
    concentrations: tuple[float, ...] = DEFAULT_CONCENTRATIONS,
    bins_grid: tuple[int, ...] = BIN_SWEEP,
    dependences: tuple[float, ...] = DEFAULT_DEPENDENCES,
    replicas: int = REPLICAS,
) -> list[dict[str, object]]:
    """Does re-binning rescue a count the default estimator cannot use?

    At one hundred sites the published forty bins hold two or three phases each,
    the pseudocount dominates every trough, and the estimate saturates well
    below the concentration it is measuring. Coarser bins are the obvious
    remedy and they cost shape sensitivity, so whether they help is a
    measurement rather than an argument. It is run at every declared dependence
    level, because a bin count chosen under independence is a bin count chosen
    for a sample the protocol will not collect.
    """
    rows: list[dict[str, object]] = []
    for bins, share in ((bins, share) for bins in bins_grid for share in dependences):
        calibrated = [
            null_residual(a, n_sites, Dependence(share), replicas, bins=bins)
            for a in concentrations
        ]
        separating = [row.concentration for row in calibrated if separates(row)]
        rows.append(
            {
                "bins": bins,
                "dependence": share,
                "a_min": min(separating) if separating else None,
                "calibration": [
                    asdict(row) | {"floor": row.floor, "separation": row.separation}
                    for row in calibrated
                ],
            }
        )
        print(f"bins={bins:3d} d={share:.2f} a_min={rows[-1]['a_min']}", flush=True)
    return rows


def minimum_separating_concentration(
    rows: list[NullResidual], n_sites: int, share: float
) -> float | None:
    """The smallest calibrated concentration whose gap clears the floor, if any.

    `None` means no concentration in the declared grid separates, which within
    `A_BIAS_VALID_MAX` is the reportable finding rather than a reason to extend
    the grid: above that ceiling the estimator's own bias is the larger effect
    and the comparison stops being about the curve.
    """
    matching = [
        row for row in rows if row.n_sites == n_sites and row.dependence == share and separates(row)
    ]
    if not matching:
        return None
    return min(row.concentration for row in matching)


def maximum_tolerable_dependence(
    rows: list[NullResidual], n_sites: int, dependences: tuple[float, ...] = DEFAULT_DEPENDENCES
) -> float | None:
    """The largest declared dependence at which some concentration still separates."""
    tolerable = [
        share
        for share in dependences
        if minimum_separating_concentration(rows, n_sites, share) is not None
    ]
    return max(tolerable) if tolerable else None


# Counts scanned when asking what a measurement at the observed concentration
# would need. Replicates are reduced at the top of the ladder: the quantity read
# off it is a floor, and a floor is a mean and a spread rather than a tail.
REQUIREMENT_COUNTS = (3_000, 10_000, 31_000, 100_000, 300_000)
REQUIREMENT_REPLICAS = 200


def required_sites(
    a: float,
    dependence: Dependence,
    counts: tuple[int, ...] = REQUIREMENT_COUNTS,
    replicas: int = REQUIREMENT_REPLICAS,
) -> tuple[int | None, list[NullResidual]]:
    """The smallest scanned count whose floor falls below the gap at `a`.

    Returns `None` for the count when no scanned size suffices, which is a
    reportable finding about the concentration and not a reason to keep
    doubling: the ladder already reaches three orders of magnitude above the
    site count the proposed protocol permits.
    """
    rows: list[NullResidual] = []
    found: int | None = None
    for n_sites in counts:
        row = null_residual(a, n_sites, dependence, replicas)
        rows.append(row)
        print(
            f"requirement a={a:.3f} n={n_sites:7d} floor={row.floor:.4f} sep={row.separation:.4f}",
            flush=True,
        )
        if found is None and separates(row):
            found = n_sites
    return found, rows


# Concentrations at which the saved site ladder was computed. They are a
# declared design point near the low end of the scanned grid, not an EEG
# measurement: the exploratory recording's pooled estimand lies below them
# (`empirical_collapse.OBSERVED_CONCENTRATION_RANGE`).
LADDER_CONCENTRATION_RANGE = (0.302, 0.542)


def observed_range_verdict(
    observed: tuple[float, float] = LADDER_CONCENTRATION_RANGE,
) -> dict[str, object]:
    """Site counts needed at the upper end of the declared ladder range.

    The saved summary keeps the historical keys ``observed_min`` and
    ``observed_max`` for the two ends of `LADDER_CONCENTRATION_RANGE`.
    """
    ceiling = max(observed)
    ladders: dict[str, object] = {}
    required: dict[str, int | None] = {}
    for share in (0.0, 0.5, 1.0):
        count, rows = required_sites(ceiling, Dependence(share))
        required[f"{share:g}"] = count
        ladders[f"{share:g}"] = [
            asdict(row) | {"floor": row.floor, "separation": row.separation} for row in rows
        ]
    return {
        "observed_min": min(observed),
        "observed_max": ceiling,
        "gap_at_observed_max": tangent_gap(ceiling),
        "sites_required_by_dependence": required,
        "counts_scanned": list(REQUIREMENT_COUNTS),
        "protocol_sites": PROTOCOL_SITES,
        "pooled_sites": POOLED_SITES,
        "ladders": ladders,
    }


def design_specification(rows: list[NullResidual]) -> list[dict[str, object]]:
    """One row per site count: where the test starts to decide, and how much
    dependence it survives."""
    specification: list[dict[str, object]] = []
    for n_sites in sorted({row.n_sites for row in rows}):
        entry: dict[str, object] = {
            "n_sites": n_sites,
            "maximum_tolerable_dependence": maximum_tolerable_dependence(rows, n_sites),
        }
        for share in DEFAULT_DEPENDENCES:
            entry[f"a_min_at_dependence_{share:g}"] = minimum_separating_concentration(
                rows, n_sites, share
            )
        specification.append(entry)
    return specification


def rejection_cases(rows: list[NullResidual]) -> dict[str, object]:
    """The cases the specification is required to fail, and the one it must pass.

    A specification that nothing fails is a specification that measures nothing.
    The first two are the failures that matter: the site count the proposed
    protocol actually permits, and a sample whose sites duplicate one another.
    The third is the control that keeps the other two from being vacuous.
    """
    protocol_independent = minimum_separating_concentration(rows, PROTOCOL_SITES, 0.0)
    protocol_dependent = minimum_separating_concentration(rows, PROTOCOL_SITES, 1.0)
    pooled_independent = minimum_separating_concentration(rows, POOLED_SITES, 0.0)
    return {
        "protocol_sites_independent_a_min": protocol_independent,
        "protocol_sites_fully_clustered_a_min": protocol_dependent,
        "protocol_sites_fully_clustered_rejected": protocol_dependent is None,
        "pooled_sites_independent_a_min": pooled_independent,
        "pooled_sites_independent_separates": pooled_independent is not None,
    }


def build_summary(replica_cap: int = REPLICAS) -> dict[str, object]:
    """Calibrate the grid, read the specification off it and record the verdicts."""
    rows = calibration_grid(replica_cap=replica_cap)
    return {
        "source": "collapse_design.py",
        "dependence_model": (
            "two-level cluster: sites_per_cluster sites share a mean drawn from "
            "VM(0, kappa_between), each site drawn from VM(mean, kappa_within), with "
            "R(kappa_between) * R(kappa_within) = R(a) held fixed"
        ),
        "sites_per_cluster": SITES_PER_CLUSTER,
        "floor_rule": f"|residual bias| + {FLOOR_SIGMA:g} * residual sd",
        "replica_cap": replica_cap,
        "replica_budget": REPLICA_BUDGET,
        "seed": SEED,
        "concentrations": list(DEFAULT_CONCENTRATIONS),
        "site_counts": list(DEFAULT_SITE_COUNTS),
        "dependences": list(DEFAULT_DEPENDENCES),
        "calibration": [
            asdict(row)
            | {
                "floor": row.floor,
                "separation": row.separation,
                "tangent_gap": tangent_gap(row.concentration),
            }
            for row in rows
        ],
        "effective_sites": {
            f"{n}_{share:g}": Dependence(share).effective_sites(n)
            for n in DEFAULT_SITE_COUNTS
            for share in DEFAULT_DEPENDENCES
        },
        "specification": design_specification(rows),
        "bin_sensitivity": bin_sensitivity(replicas=replica_cap),
        "bins": DEFAULT_BINS,
        "rejection_cases": rejection_cases(rows),
        "observed_range": observed_range_verdict(),
        "estimator_valid_max_concentration": collapse.A_BIAS_VALID_MAX,
        "scope": (
            "synthetic calibration of one estimator under one declared dependence model; "
            "no recording is re-analysed and no coupling constant is fitted"
        ),
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="fewer replicates, same code path")
    parser.add_argument("--output", type=Path, default=None)
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    output = args.output or PRODUCTION_OUTPUT
    summary = build_summary(replica_cap=20 if args.smoke else REPLICAS)
    output.mkdir(parents=True, exist_ok=True)
    (output / "collapse_design_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    for entry in cast(list[dict[str, object]], summary["specification"]):
        print(
            f"n={entry['n_sites']:6}  a_min(independent)="
            f"{entry['a_min_at_dependence_0']}  "
            f"max tolerable dependence={entry['maximum_tolerable_dependence']}"
        )
    print(f"wrote {output / 'collapse_design_summary.json'}")


if __name__ == "__main__":
    main()
