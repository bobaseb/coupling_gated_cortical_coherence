"""Bifurcation diagram of the self-consistency equation formalized in Lean.

This script draws the object that `Phase8_SelfConsistency.lean` proves things
about, and nothing else.  Every quantity below is the numerical value of a
definition in that file, computed by quadrature over the same interval the Lean
definitions integrate over:

    vonMisesWeight a θ = exp(a cos θ)                        `vonMisesWeight`
    Z(a) = ∫_{-π}^{π} exp(a cos θ) dθ                        `vonMisesZ`
    M(a) = ∫_{-π}^{π} cos θ · exp(a cos θ) dθ                `vonMisesM`
    S(a) = ∫_{-π}^{π} sin²θ · exp(a cos θ) dθ                `vonMisesS`
    R(a) = M(a)/Z(a)      (the Bessel ratio I₁/I₀)           `besselRatio`
    E(a) = S(a)/Z(a)      (so R(a) = a·E(a))                 `vonMisesSRatio`

and the self-consistency equation is `selfConsistency K D r = R(K r / D)`.

A non-zero solution satisfies E(K r / D) = D/K (`coherent_iff_sRatio_eq`), so
writing a = K r / D for the concentration, the coherent branch is obtained by
solving E(a) = D/K for a and reading off r = a D / K.  Bisection is legitimate
here precisely because `vonMisesSRatio_strictAntiOn` proves E strictly
decreasing on [0, ∞); the root is unique, which is
`supercritical_fixed_point_existsUnique`.

The figure is therefore an illustration of proved statements, not evidence for
them:  r = 0 is the only solution at or below K_c = 2D
(`fixed_point_eq_zero_of_le_critical`), a unique r > 0 joins it above,
r → 0 as K ↓ K_c (`coherent_branch_continuous_at_threshold`), and r increases
strictly with K (`coherent_branch_strictMono`).
"""

import numpy as np
import matplotlib.pyplot as plt

# Quadrature grid on [-pi, pi], the interval the Lean definitions integrate over.
_N_QUAD = 4001
_THETA = np.linspace(-np.pi, np.pi, _N_QUAD)


def _moments(a: float) -> tuple[float, float, float]:
    """Return (Z, M, S) at concentration `a`.

    The weight is evaluated as exp(a·cosθ − a) rather than exp(a·cosθ): the
    three integrals are only ever used in ratios, so the common factor exp(−a)
    cancels, and subtracting the maximum keeps the exponential from overflowing
    at the large concentrations the supercritical branch reaches.
    """
    c = np.cos(_THETA)
    w = np.exp(a * c - abs(a))
    Z = float(np.trapezoid(w, _THETA))
    M = float(np.trapezoid(c * w, _THETA))
    S = float(np.trapezoid(np.sin(_THETA) ** 2 * w, _THETA))
    return Z, M, S


def bessel_ratio(a: float) -> float:
    """`besselRatio`: R(a) = M(a)/Z(a), the mean of cos θ under the von Mises weight."""
    Z, M, _ = _moments(a)
    return M / Z


def s_ratio(a: float) -> float:
    """`vonMisesSRatio`: E(a) = S(a)/Z(a), the mean of sin²θ. E(0) = 1/2 and E < 1/2 for a > 0."""
    Z, _, S = _moments(a)
    return S / Z


def coherent_r(K: float, D: float = 1.0, a_max: float = 200.0) -> float:
    """The unique r > 0 solving r = R(K r / D), or 0.0 when K <= 2D.

    Solves E(a) = D/K by bisection on the concentration a, then returns
    r = a D / K.  Below threshold no positive root exists, because E < 1/2
    everywhere on (0, ∞) while D/K >= 1/2.
    """
    if K <= 2 * D:
        return 0.0
    target = D / K
    lo, hi = 1e-9, a_max
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        # E is strictly decreasing, so E(mid) > target means the root is above mid.
        if s_ratio(mid) > target:
            lo = mid
        else:
            hi = mid
    a = 0.5 * (lo + hi)
    return a * D / K


def plot_bifurcation(D: float = 1.0, out: str = "simulations/bifurcation_diagram.png") -> None:
    Kc = 2 * D
    K_sub = np.linspace(0.0, Kc, 60)
    # Sampled densely just above threshold, where the branch leaves the axis with
    # infinite slope, and sparsely far from it.
    K_sup = Kc + np.geomspace(1e-6, 4 * D - Kc, 500)

    r_sup = np.array([coherent_r(K, D) for K in K_sup])

    fig, ax = plt.subplots(figsize=(7.0, 4.4))

    # Incoherent branch: the only solution below threshold, still a solution above it.
    ax.plot(K_sub, np.zeros_like(K_sub), color="#1f77b4", lw=2.2,
            label=r"incoherent branch $r=0$ (only solution for $K \leq K_c$)")
    ax.plot(np.concatenate([[Kc], K_sup]), np.zeros(len(K_sup) + 1),
            color="#1f77b4", lw=2.2, ls=":", alpha=0.9,
            label=r"$r=0$, still a solution above $K_c$")

    # Coherent branch.
    ax.plot(K_sup, r_sup, color="#d62728", lw=2.4,
            label=r"coherent branch: the unique $r>0$ with $r=R(Kr/D)$")

    ax.axvline(Kc, color="0.4", ls="--", lw=1.2)
    ax.annotate(r"$K_c = 2D$", xy=(Kc, 0.30), xytext=(Kc + 0.07, 0.28),
                fontsize=11, color="0.25")

    ax.set_xlim(0, 4 * D)
    ax.set_ylim(-0.04, 1.0)
    ax.set_xlabel(r"coupling $K$   (noise $D=%g$)" % D)
    ax.set_ylabel(r"order parameter $r$")
    ax.set_title("Self-consistent order parameter of the noisy mean-field Kuramoto model")
    ax.legend(loc="upper left", fontsize=9, framealpha=0.95)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(out, dpi=200)
    print(f"wrote {out}")

    # Numerical checks of the four proved qualitative facts, printed so the
    # figure is not the only record that they hold of the computed curve.
    print(f"  r just above threshold (K={K_sup[0]:.6f}): {r_sup[0]:.4g}"
          "   [coherent_branch_continuous_at_threshold]")
    print(f"  branch strictly increasing: {bool(np.all(np.diff(r_sup) > 0))}"
          "   [coherent_branch_strictMono]")
    print(f"  E(0) = {s_ratio(0.0):.6f} (proved exactly 1/2);"
          f" E(1) = {s_ratio(1.0):.6f} < 1/2   [vonMisesSRatio_lt_half]")
    print(f"  residual |r - R(Kr/D)| at K=4D: "
          f"{abs(r_sup[-1] - bessel_ratio(K_sup[-1] * r_sup[-1] / D)):.2e}")


if __name__ == "__main__":
    plot_bifurcation()
