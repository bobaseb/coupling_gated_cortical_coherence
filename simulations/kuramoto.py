import numpy as np
from scipy.integrate import odeint  
import matplotlib.pyplot as plt  


def kuramoto_derivative(
    theta: np.ndarray, t: float, omega: np.ndarray, K: float, N: int
) -> np.ndarray:
    """Derivative for Kuramoto model."""
    dtheta = np.zeros(N)
    for i in range(N):
        dtheta[i] = omega[i] + (K / N) * np.sum(np.sin(theta - theta[i]))
    return dtheta


def simulate_kuramoto(
    N: int = 100, K_values: list[float] | np.ndarray | None = None, D: float = 1.0
) -> None:
    """
    Simulate N-oscillator Kuramoto system.
    Measure order parameter r vs coupling K.
    Verify critical threshold K_c = 2D numerically.
    """
    if K_values is None:
        K_values = np.linspace(0, 4 * D, 20)

    # Natural frequencies drawn from a Lorentzian with scale D
    # Standard Cauchy/Lorentzian distribution: D * tan(pi * (U - 0.5))
    np.random.seed(42)
    U = np.random.uniform(0, 1, N)
    omega = D * np.tan(np.pi * (U - 0.5))

    # Trim extreme outliers to avoid ODE solver issues
    omega = np.clip(omega, -10 * D, 10 * D)

    t = np.linspace(0, 100, 1000)
    r_asymptotic = []

    for K in K_values:
        theta0 = np.random.uniform(0, 2 * np.pi, N)
        theta_t = odeint(kuramoto_derivative, theta0, t, args=(omega, K, N))

        # Order parameter r
        # r * e^{i psi} = (1/N) \sum e^{i theta_j}
        # We average over the last 100 time steps to get asymptotic r
        r_t = np.abs(np.mean(np.exp(1j * theta_t), axis=1))
        r_inf = np.mean(r_t[-100:])
        r_asymptotic.append(r_inf)

    plt.figure(figsize=(8, 5))
    plt.plot(K_values, r_asymptotic, "o-", label="Numerical $r$")
    plt.axvline(x=2 * D, color="r", linestyle="--", label=r"Theoretical $K_c = 2D$")
    plt.xlabel("Coupling $K$")
    plt.ylabel("Order Parameter $r$")
    plt.title("Kuramoto Phase Transition")
    plt.legend()
    plt.grid(True)
    plt.savefig("kuramoto_transition.png")
    print("Kuramoto transition simulation saved to kuramoto_transition.png")


if __name__ == "__main__":
    simulate_kuramoto()
