import numpy as np
import matplotlib.pyplot as plt


def periodic_distance(x: float, y: float, L: float = 2 * np.pi) -> float:
    """Calculate the shortest distance on a periodic domain of length L."""
    d = np.abs(x - y) % L
    return float(np.minimum(d, L - d))


def K_func(x: float, y: float, sigma: float = 1.0) -> float:
    """Gaussian coupling function based on periodic distance."""
    d = periodic_distance(x, y)
    return float(np.exp(-(d**2) / (2 * sigma**2)))


def theta_func(x: float) -> float:
    """Continuous phase distribution on the ring."""
    return float(np.sin(x))


def integrand(x: float, y: float) -> float:
    """Integrand for the continuous Kuramoto potential."""
    return float(K_func(x, y) * np.cos(theta_func(y) - theta_func(x)))


def compute_continuous_potential(N_ground_truth: int = 2000) -> float:
    """
    Compute the continuous potential using a very fine grid Riemann sum
    as a surrogate for the exact integral, to avoid slow dblquad over 2D.
    """
    x = np.linspace(0, 2 * np.pi, N_ground_truth, endpoint=False)
    dx = 2 * np.pi / N_ground_truth

    # Vectorize evaluation for speed
    X, Y = np.meshgrid(x, x)
    d = np.abs(X - Y) % (2 * np.pi)
    d = np.minimum(d, 2 * np.pi - d)
    K = np.exp(-(d**2) / 2.0)
    Theta_X = np.sin(X)
    Theta_Y = np.sin(Y)

    # The array above is `integrand` evaluated on the grid; check the
    # transcription at one point rather than trusting it.  `meshgrid` puts the
    # pair (x_i, x_j) at [j, i].
    i, j = 1, 2
    vectorised = float(K[j, i] * np.cos(Theta_Y[j, i] - Theta_X[j, i]))
    if abs(integrand(float(x[i]), float(x[j])) - vectorised) > 1e-12:
        raise AssertionError("vectorised kernel does not match the scalar integrand")

    integral = np.sum(K * np.cos(Theta_Y - Theta_X)) * (dx**2)
    return float(-0.5 * integral)


def compute_discrete_potential(N: int) -> float:
    """
    Compute the discrete Kuramoto potential for a mesh of N nodes.
    The nodes are centers of N equal segments.
    """
    x = np.linspace(0, 2 * np.pi, N, endpoint=False)
    dx = 2 * np.pi / N

    # A_ij is approximated by K(x_i, x_j) * (dx)^2
    X, Y = np.meshgrid(x, x)
    d = np.abs(X - Y) % (2 * np.pi)
    d = np.minimum(d, 2 * np.pi - d)
    A = np.exp(-(d**2) / 2.0) * (dx**2)

    Theta_X = np.sin(X)
    Theta_Y = np.sin(Y)

    V_disc = -0.5 * np.sum(A * np.cos(Theta_Y - Theta_X))
    return float(V_disc)


def run_mesh_refinement_simulation() -> None:
    """
    Run the mesh refinement convergence simulation and plot the results.
    """
    print("Computing continuous potential ground truth...")
    V_cont = compute_continuous_potential(2000)
    print(f"V_cont = {V_cont:.6f}")

    N_values = [10, 20, 40, 80, 160, 320, 640]
    errors = []

    print("Computing discrete potentials...")
    for N in N_values:
        V_disc = compute_discrete_potential(N)
        error = abs(V_disc - V_cont)
        errors.append(error)
        print(f"N = {N:3d}, V_disc = {V_disc:.6f}, Error = {error:.2e}")

    plt.figure(figsize=(8, 5))
    plt.loglog(N_values, errors, "o-", label="Numerical Error $|V_{disc} - V_{cont}|$")

    # Plot reference O(1/N^2) line
    ref_errors = [errors[0] * (N_values[0] / n) ** 2 for n in N_values]
    plt.loglog(N_values, ref_errors, "k--", label=r"$\mathcal{O}(1/N^2)$ reference")

    plt.xlabel("Number of Mesh Nodes $N$")
    plt.ylabel("Absolute Error")
    plt.title("Mesh Refinement Convergence of Kuramoto Potential")
    plt.legend()
    plt.grid(True, which="both", ls="--")
    plt.savefig("simulations/mesh_refinement_convergence.png")
    print("Plot saved to simulations/mesh_refinement_convergence.png")


if __name__ == "__main__":
    run_mesh_refinement_simulation()
