"""Fixed versus adaptive coupling on one finite Kuramoto system.

Both systems here are finite ``N x N`` coupling matrices on the same
oscillators, started from the same phases and the same total coupling weight.
One matrix is held fixed; the other is reallocated by gradient descent on the
Kuramoto potential and renormalised after every step, so the two are compared
at matched total weight. That is the whole of the comparison: it is a numerical
illustration of the finite reallocation model of ``Phase7_HardwareComparison``
and ``Phase7_Rigidity``, and it measures no device.

In particular this script does not compare a GPU with a brain, does not model a
continuous field, and is not evidence about any physical hardware. The
"continuous versus rigid" distinction belongs to the measure-theoretic
comparison in ``Phase7_FiniteRegion``, which is about the measure of a kernel's
support and not about these matrices.
"""

import numpy as np
import matplotlib.pyplot as plt


def simulate_hardware_comparison(N: int = 30, steps: int = 1000, dt: float = 0.05) -> None:
    """Run both systems and plot their Kuramoto potentials.

    The fixed matrix is a sparsified symmetric random matrix with zero
    diagonal, normalised to a declared total weight. The adaptive matrix starts
    as its copy and follows the negative gradient of the potential with respect
    to the weights, clipped to stay nonnegative and renormalised to the same
    total weight, so no extra coupling resource is introduced.
    """
    np.random.seed(123)

    omega = np.random.randn(N) * 0.5
    theta_init = np.random.uniform(0, 2 * np.pi, N)

    # The matched resource: total coupling weight, shared by both matrices.
    total_K = N * 2.0

    # FIXED SUPPORT: a sparsified symmetric random matrix, held constant.
    A_fixed = np.random.rand(N, N)
    A_fixed = (A_fixed + A_fixed.T) / 2
    np.fill_diagonal(A_fixed, 0)
    A_fixed[A_fixed < 0.7] = 0
    A_fixed = A_fixed / np.sum(A_fixed) * total_K

    # ADAPTIVE WEIGHTS: the same matrix, free to be reallocated.
    A_adapt = A_fixed.copy()

    theta_f = theta_init.copy()
    theta_a = theta_init.copy()

    pot_f_list = []
    pot_a_list = []

    eta = 0.1  # reallocation rate for the adaptive weights

    for _ in range(steps):
        # 1. Fixed-matrix dynamics.
        diff_f = theta_f.reshape(1, N) - theta_f.reshape(N, 1)
        dtheta_f = omega + np.sum(A_fixed * np.sin(diff_f), axis=1)
        theta_f += dtheta_f * dt

        # Kuramoto potential: V = - (1/2) \sum A_ij cos(theta_j - theta_i)
        pot_f = -0.5 * np.sum(A_fixed * np.cos(diff_f))
        pot_f_list.append(pot_f)

        # 2. Adaptive-matrix dynamics, same phase law.
        diff_a = theta_a.reshape(1, N) - theta_a.reshape(N, 1)
        dtheta_a = omega + np.sum(A_adapt * np.sin(diff_a), axis=1)
        theta_a += dtheta_a * dt

        pot_a = -0.5 * np.sum(A_adapt * np.cos(diff_a))
        pot_a_list.append(pot_a)

        # Reallocate the weights down the potential gradient: dV/dA_ij is
        # -0.5 cos(theta_j - theta_i). Clipping keeps the matrix nonnegative and
        # the renormalisation keeps the total weight matched.
        dA = 0.5 * np.cos(diff_a)
        A_adapt += eta * dA * dt
        A_adapt = np.clip(A_adapt, 0, None)
        np.fill_diagonal(A_adapt, 0)
        A_adapt = A_adapt / np.sum(A_adapt) * total_K

    plt.figure(figsize=(8, 5))
    plt.plot(pot_f_list, label="Fixed coupling matrix", color="red")
    plt.plot(pot_a_list, label="Reallocated coupling matrix", color="green")
    plt.xlabel("Time Step")
    plt.ylabel("Kuramoto potential")
    plt.title("Fixed versus reallocated weights at matched total coupling weight")
    plt.legend()
    plt.grid(True)
    plt.savefig("simulations/hardware_comparison.png")
    print("Fixed-versus-reallocated comparison saved to hardware_comparison.png")


if __name__ == "__main__":
    simulate_hardware_comparison()
