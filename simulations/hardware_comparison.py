import numpy as np
import matplotlib.pyplot as plt


def simulate_hardware_comparison(N: int = 30, steps: int = 1000, dt: float = 0.05) -> None:
    """
    Simulate identical Kuramoto systems with rigid (GPU) vs adaptive (Bio) coupling.
    Compare minimum achievable potential.
    """
    np.random.seed(123)

    omega = np.random.randn(N) * 0.5
    theta_init = np.random.uniform(0, 2 * np.pi, N)

    # Total thermodynamic coupling resource
    total_K = N * 2.0

    # RIGID HARDWARE (e.g. 2D grid topology)
    # We create a random sparse adjacency matrix to simulate fixed hardware routing
    A_rigid = np.random.rand(N, N)
    A_rigid = (A_rigid + A_rigid.T) / 2
    np.fill_diagonal(A_rigid, 0)
    # Sparsify
    A_rigid[A_rigid < 0.7] = 0
    # Normalize to total_K
    A_rigid = A_rigid / np.sum(A_rigid) * total_K

    # ADAPTIVE BIOLOGY (continuous EM field)
    # Initializes similarly but can deform
    A_adapt = A_rigid.copy()

    theta_r = theta_init.copy()
    theta_a = theta_init.copy()

    pot_r_list = []
    pot_a_list = []

    eta = 0.1  # learning rate for adaptive structure

    for _ in range(steps):
        # 1. Rigid System Dynamics
        diff_r = theta_r.reshape(1, N) - theta_r.reshape(N, 1)
        dtheta_r = omega + np.sum(A_rigid * np.sin(diff_r), axis=1)
        theta_r += dtheta_r * dt

        # Rigid Potential: V = - (1/2) \sum A_ij cos(theta_j - theta_i)
        pot_r = -0.5 * np.sum(A_rigid * np.cos(diff_r))
        pot_r_list.append(pot_r)

        # 2. Adaptive System Dynamics
        diff_a = theta_a.reshape(1, N) - theta_a.reshape(N, 1)
        dtheta_a = omega + np.sum(A_adapt * np.sin(diff_a), axis=1)
        theta_a += dtheta_a * dt

        pot_a = -0.5 * np.sum(A_adapt * np.cos(diff_a))
        pot_a_list.append(pot_a)

        # Adaptive System Structure updates to minimize potential (gradient descent on V)
        # dV/dA_ij = -0.5 * cos(theta_j - theta_i)
        dA = 0.5 * np.cos(diff_a)
        A_adapt += eta * dA * dt
        A_adapt = np.clip(A_adapt, 0, None)
        np.fill_diagonal(A_adapt, 0)
        # Re-normalize to conserve thermodynamic resources
        A_adapt = A_adapt / np.sum(A_adapt) * total_K

    plt.figure(figsize=(8, 5))
    plt.plot(pot_r_list, label="Rigid Hardware (Fixed Topology)", color="red")
    plt.plot(pot_a_list, label="Continuous Biological Field (Adaptive)", color="green")
    plt.xlabel("Time Step")
    plt.ylabel("Dynamical Potential (Energy)")
    plt.title("Hardware Strict Inequality: Continuous Beats Rigid")
    plt.legend()
    plt.grid(True)
    plt.savefig("simulations/hardware_comparison.png")
    print("Hardware comparison simulation saved to hardware_comparison.png")


if __name__ == "__main__":
    simulate_hardware_comparison()
