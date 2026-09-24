"""Small analytical counterparts of G22–G24's first Lean increment.

These helpers neither integrate dynamics nor train benchmark candidates. The
current quadrature uses uniform periodic nodes without a duplicated endpoint.
Rank weights are diagonal input second moments in the target eigenbasis.
"""

import numpy as np
from numpy.typing import NDArray

FloatArray = NDArray[np.float64]


def _finite_vector(values: FloatArray) -> None:
    if values.ndim != 1 or values.size == 0 or not np.isfinite(values).all():
        raise ValueError("Expected a nonempty finite vector")


def _density_grid(rho: FloatArray, current: FloatArray, diffusion: float) -> None:
    _finite_vector(rho)
    _finite_vector(current)
    if current.shape != rho.shape or np.any(rho <= 0):
        raise ValueError("Current and strictly positive density must share a grid")
    if not np.isfinite(diffusion) or diffusion <= 0:
        raise ValueError("Diffusion must be finite and positive")
    spacing = 2 * np.pi / rho.size
    if not np.isclose(spacing * rho.sum(), 1, rtol=1e-10, atol=1e-12):
        raise ValueError("Density must be normalized on the periodic grid")


def current_bound(rho: FloatArray, current: FloatArray, diffusion: float) -> dict[str, float]:
    """Measure directional flux and its order-dependent bound at the mean angle.

    At zero order choose angle zero; the returned flux is not a norm derivative.
    The caller must separately establish a continuity equation for any speed claim.
    """
    _density_grid(rho, current, diffusion)
    spacing = 2 * np.pi / rho.size
    theta = np.arange(rho.size) * spacing
    moment = spacing * np.sum(rho * np.exp(1j * theta))
    angle = float(np.angle(moment)) if abs(moment) > 1e-12 else 0.0
    order = float(abs(moment))
    cost = float(spacing * np.sum(current**2 / (diffusion * rho)))
    flux = float(spacing * np.sum(np.sin(theta - angle) * current))
    return {
        "order": order,
        "cost": cost,
        "flux_squared": flux**2,
        "bound": diffusion * cost * (1 - order**2),
    }


def _channel(values: FloatArray, dimensions: int) -> None:
    if values.ndim != dimensions or 0 in values.shape:
        raise ValueError("Channel has incorrect or empty dimensions")
    if not np.isfinite(values).all() or np.any(values < 0):
        raise ValueError("Channel entries must be finite and nonnegative")
    if not np.allclose(values.sum(axis=-1), 1, rtol=1e-10, atol=1e-12):
        raise ValueError("Channel rows must sum to one")


def _feedback_shapes(
    evolve: FloatArray,
    sensor: FloatArray,
    update: FloatArray,
    install: NDArray[np.int64],
) -> None:
    _channel(evolve, 3)
    _channel(sensor, 2)
    _channel(update, 3)
    actions, phases, next_phases = evolve.shape
    observations, registers, next_registers = update.shape
    if (
        phases != next_phases
        or registers != next_registers
        or sensor.shape != (phases, observations)
    ):
        raise ValueError("Channel state spaces do not match")
    if install.shape != (registers,) or not np.issubdtype(install.dtype, np.integer):
        raise ValueError("Installation must assign one integer action per register")
    if np.any(install < 0) or np.any(install >= actions):
        raise ValueError("Installed action index is out of range")


def feedback_transition(
    evolve: FloatArray,
    sensor: FloatArray,
    update: FloatArray,
    install: NDArray[np.int64],
) -> FloatArray:
    """Return T[old_phase, old_register, new_phase, new_register].

    evolve[action, phase, phase'], sensor[phase', observation], and
    update[observation, register, register'] are row-stochastic channels.
    Work, heat and current costs are not inferred from these probabilities.
    """
    _feedback_shapes(evolve, sensor, update, install)
    return np.asarray(
        np.einsum("rpq,qo,ors->prqs", evolve[install], sensor, update), dtype=np.float64
    )


def _joint_transition(transition: FloatArray) -> None:
    if (
        transition.ndim != 4
        or 0 in transition.shape
        or not np.isfinite(transition).all()
        or np.any(transition < 0)
        or not np.allclose(transition.sum(axis=(2, 3)), 1, rtol=1e-10, atol=1e-12)
    ):
        raise ValueError("Transition must have normalized joint output rows")


def _joint_prior(prior: FloatArray, transition: FloatArray) -> None:
    if (
        prior.ndim != 2
        or prior.shape != transition.shape[:2]
        or prior.shape != transition.shape[2:]
        or not np.isfinite(prior).all()
        or np.any(prior < 0)
        or not np.isclose(prior.sum(), 1, rtol=1e-10, atol=1e-12)
    ):
        raise ValueError("Prior must be a normalized joint law matching the transition")


def feedback_laws(prior: FloatArray, transition: FloatArray, steps: int) -> FloatArray:
    """Carry the phase/register joint law through a finite feedback process.

    Axis zero of the result includes the prior and each successive update.
    Marginalizing phase or register before an update would discard feedback.
    """
    if not isinstance(steps, int) or steps < 0:
        raise ValueError("Steps must be a nonnegative integer")
    _joint_transition(transition)
    _joint_prior(prior, transition)
    laws = np.empty((steps + 1, *prior.shape), dtype=np.float64)
    laws[0] = prior
    for index in range(steps):
        laws[index + 1] = np.einsum("pr,prqs->qs", laws[index], transition)
    return laws


def feedback_expected_costs(
    laws: FloatArray, transition: FloatArray, price: FloatArray
) -> FloatArray:
    """Expected path price on each executed joint transition.

    Prices can include sensing, reset, and signed installation-energy changes.
    They are declared work values, not heat inferred from transition rates.
    """
    _joint_transition(transition)
    if laws.ndim != 3 or laws.shape[0] < 1 or laws.shape[1:] != transition.shape[:2]:
        raise ValueError("Laws must include a matching prior")
    for law in laws:
        _joint_prior(law, transition)
    propagated = np.einsum("tpr,prqs->tqs", laws[:-1], transition)
    if not np.allclose(laws[1:], propagated, rtol=1e-10, atol=1e-12):
        raise ValueError("Supplied laws do not follow the declared transition")
    if price.shape != transition.shape or not np.isfinite(price).all():
        raise ValueError("Path prices must be finite and match the joint transition")
    return np.asarray(np.einsum("tpr,prqs,prqs->t", laws[:-1], transition, price), dtype=np.float64)


def feedback_store(
    initial: float, preparation: float, costs: FloatArray, replenish: FloatArray
) -> FloatArray:
    """Expected available work after preparation and each funded update."""
    if not np.isfinite(initial) or not np.isfinite(preparation):
        raise ValueError("Initial store and preparation must be finite")
    if costs.ndim != 1 or costs.shape != replenish.shape or not np.isfinite(costs).all():
        raise ValueError("Costs and replenishment must be matching finite vectors")
    if not np.isfinite(replenish).all():
        raise ValueError("Replenishment must be finite")
    available = initial - preparation
    return np.concatenate(([available], available + np.cumsum(replenish - costs)))


def _prediction_shapes(
    laws: FloatArray,
    evolve: FloatArray,
    install: NDArray[np.int64],
    prediction: NDArray[np.int64],
) -> None:
    if evolve.ndim != 3 or 0 in evolve.shape or evolve.shape[1] != evolve.shape[2]:
        raise ValueError("Evolution must be a nonempty square phase channel")
    if laws.ndim != 3 or laws.shape[1:] != (evolve.shape[1], install.size):
        raise ValueError("Laws and installed actions have incompatible dimensions")
    if install.ndim != 1 or prediction.shape != install.shape:
        raise ValueError("Each register needs an installed action and prediction")


def _prediction_indices(
    evolve: FloatArray,
    install: NDArray[np.int64],
    prediction: NDArray[np.int64],
) -> None:
    if np.any(install < 0) or np.any(install >= evolve.shape[0]):
        raise ValueError("Installed action out of range")
    if np.any(prediction < 0) or np.any(prediction >= evolve.shape[1]):
        raise ValueError("Predicted phase out of range")


def _prediction_distributions(laws: FloatArray, evolve: FloatArray) -> None:
    if not np.isfinite(laws).all() or np.any(laws < 0):
        raise ValueError("Joint laws must be finite and nonnegative")
    if not np.allclose(laws.sum(axis=(1, 2)), 1, rtol=1e-10, atol=1e-12):
        raise ValueError("Joint laws must be normalized")
    _channel(evolve, 3)


def feedback_prediction_accuracy(
    laws: FloatArray,
    evolve: FloatArray,
    install: NDArray[np.int64],
    prediction: NDArray[np.int64],
) -> FloatArray:
    """Next-phase prediction accuracy from each current joint law.

    `prediction[register]` is fixed before the phase evolves. The score uses
    the actual installed action and retained phase/register correlations.
    """
    _prediction_shapes(laws, evolve, install, prediction)
    _prediction_indices(evolve, install, prediction)
    _prediction_distributions(laws, evolve)
    phase = np.arange(evolve.shape[1])
    success = evolve[install[:, None], phase[None, :], prediction[:, None]]
    return np.asarray(np.einsum("tpr,rp->t", laws, success), dtype=np.float64)


def weighted_tail(eigenvalues: FloatArray, second_moments: FloatArray, rank: int) -> float:
    """Optimal linear error floor for the supplied diagonal second moments.

    Applies to an actual operator rank budget, not query/key dimension or a
    nonlinear decoder's effective rank. Non-diagonal covariance is outside scope.
    """
    _finite_vector(eigenvalues)
    _finite_vector(second_moments)
    if eigenvalues.shape != second_moments.shape or np.any(second_moments < 0):
        raise ValueError("Second moments must be nonnegative and match eigenvalues")
    if not isinstance(rank, int) or not 0 <= rank <= eigenvalues.size:
        raise ValueError("Rank must be an integer between zero and dimension")
    energies = second_moments * eigenvalues**2
    return float(np.sort(energies)[::-1][rank:].sum())


def _covariance_spectrum(covariance: FloatArray, dimension: int) -> tuple[FloatArray, FloatArray]:
    if covariance.shape != (dimension, dimension) or not np.isfinite(covariance).all():
        raise ValueError("Second-moment matrix has incorrect shape or nonfinite entries")
    if not np.allclose(covariance, covariance.T, rtol=1e-10, atol=1e-12):
        raise ValueError("Second-moment matrix must be symmetric")
    eigenvalues, eigenvectors = np.linalg.eigh(covariance)
    if np.min(eigenvalues) < -1e-10:
        raise ValueError("Second-moment matrix must be positive semidefinite")
    return eigenvalues, eigenvectors


def _covariance_root(covariance: FloatArray, dimension: int) -> FloatArray:
    eigenvalues, eigenvectors = _covariance_spectrum(covariance, dimension)
    return np.asarray(
        (eigenvectors * np.sqrt(np.maximum(eigenvalues, 0))) @ eigenvectors.T,
        dtype=np.float64,
    )


def covariance_rank_tail(target: FloatArray, covariance: FloatArray, rank: int) -> float:
    """Optimal linear rank error for a declared input second-moment matrix.

    For any rank-limited linear decoder A, expected squared error is
    ||(K-A) C^(1/2)||_F^2. Eckart--Young gives the squared singular-value tail
    of K C^(1/2), including correlated and noncentered input laws. This is an
    analytical prediction; it does not score a trained nonlinear candidate.
    """
    if target.ndim != 2 or 0 in target.shape or not np.isfinite(target).all():
        raise ValueError("Target must be a finite matrix with nonempty dimensions")
    if not isinstance(rank, int) or not 0 <= rank <= min(target.shape):
        raise ValueError("Rank must be an integer between zero and the smaller dimension")
    root = _covariance_root(covariance, target.shape[1])
    singular = np.linalg.svd(target @ root, compute_uv=False)
    return float(np.sum(singular[rank:] ** 2))


def covariance_rank_truncation(target: FloatArray, covariance: FloatArray, rank: int) -> FloatArray:
    """Construct a rank-limited linear decoder attaining the covariance tail.

    The pseudoinverse handles singular input laws; decoder behavior outside the
    input support is unconstrained and has no effect on expected error.
    """
    covariance_rank_tail(target, covariance, rank)
    root = _covariance_root(covariance, target.shape[1])
    left, singular, right = np.linalg.svd(target @ root, full_matrices=False)
    truncated = (left[:, :rank] * singular[:rank]) @ right[:rank, :]
    return np.asarray(truncated @ np.linalg.pinv(root, rcond=1e-10), dtype=np.float64)
