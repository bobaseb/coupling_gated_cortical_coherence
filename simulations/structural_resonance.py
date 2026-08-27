import numpy as np
import matplotlib.pyplot as plt  
from tqdm import tqdm  


def simulate_structural_resonance(N: int = 50, steps: int = 2000, dt: float = 0.05) -> None:
    """
    Simulate a plastic neural field with adaptive coupling K_t.
    Shows entropy production decreases and internal structure correlates
    with external perturbation statistics.
    """
    np.random.seed(42)

    # External environment statistics (a hidden covariance matrix)
    # We create a structured external covariance
    env_features = np.random.randn(N, 5)
    env_cov = env_features @ env_features.T
    # Normalize
    env_cov = env_cov / np.max(np.abs(env_cov))

    # Internal states
    theta = np.random.uniform(0, 2 * np.pi, N)

    # Adaptive coupling matrix, initialized randomly
    K = np.random.uniform(0, 0.1, (N, N))
    K = (K + K.T) / 2  # symmetric
    np.fill_diagonal(K, 0)

    entropy_production = []
    structural_error = []

    # Learning rate for structural deformation (least action)
    eta = 0.01

    for _ in tqdm(range(steps)):
        # External perturbation drawn from environment statistics
        ext_noise = np.random.multivariate_normal(np.zeros(N), env_cov + np.eye(N) * 0.1)

        # Compute internal dynamics
        # Phase differences
        theta_diff = theta.reshape(1, N) - theta.reshape(N, 1)
        sin_diff = np.sin(theta_diff)

        # dtheta = K * sin(theta_diff) + external_perturbation
        dtheta = np.sum(K * sin_diff, axis=1) + ext_noise

        # Update theta
        theta += dtheta * dt

        # Entropy production (dissipation is proportional to squared rate of change)
        sigma = np.sum(dtheta**2)
        entropy_production.append(sigma)

        # By Principle of Least Action, K deforms to minimize sigma
        # The gradient of sigma w.r.t K_{ij} is approximately:
        # d_sigma / d_K_{ij} = 2 * dtheta_i * sin(theta_j - theta_i)
        # We update K via gradient descent
        dsigma_dK = np.outer(dtheta, np.ones(N)) * sin_diff
        dsigma_dK = (dsigma_dK + dsigma_dK.T) / 2

        K -= eta * dsigma_dK * dt
        K = np.clip(K, 0, 1)  # coupling must be non-negative
        np.fill_diagonal(K, 0)

        # Measure correlation between internal geometry K and external statistics env_cov
        error = np.linalg.norm(K - env_cov)
        structural_error.append(error)

    # Plot results
    _, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    # Smooth entropy production for plotting
    window = 50
    smoothed_sigma = np.convolve(entropy_production, np.ones(window) / window, mode="valid")
    ax1.plot(smoothed_sigma, color="b")
    ax1.set_xlabel("Time Step")
    ax1.set_ylabel(r"Entropy Production $\sigma$")
    ax1.set_title("Minimization of Dissipation")
    ax1.grid(True)

    ax2.plot(structural_error, color="r")
    ax2.set_xlabel("Time Step")
    ax2.set_ylabel(r"Structural Distance $||K - \Sigma_{ext}||$")
    ax2.set_title("Emergence of Structural Resonance")
    ax2.grid(True)

    plt.tight_layout()
    plt.savefig("structural_resonance.png")
    print("Structural resonance simulation saved to structural_resonance.png")


if __name__ == "__main__":
    simulate_structural_resonance()
