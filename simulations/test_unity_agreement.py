import unittest

import numpy as np

import unity_agreement as ua


def _dense_resistance(kernel: np.ndarray, separation: int) -> float:
    """Effective resistance between site (0, 0) and (0, separation) by pseudoinverse."""
    side = kernel.shape[0]
    count = side * side
    conductance = np.array(
        [
            [kernel[(k - i) % side, (b - a) % side] for k in range(side) for b in range(side)]
            for i in range(side)
            for a in range(side)
        ]
    )
    laplacian = np.diag(conductance.sum(axis=1)) - conductance
    probe = np.zeros(count)
    probe[0] = 1.0
    probe[separation] = -1.0
    return float(probe @ np.linalg.pinv(laplacian) @ probe)


class KernelTest(unittest.TestCase):
    def test_every_kernel_is_symmetric_with_the_declared_row_sum_and_no_self_coupling(
        self,
    ) -> None:
        for shape in ua.KERNEL_SHAPES:
            kernel = ua.build_shape_kernel(shape, 16, 2.5)
            self.assertAlmostEqual(float(kernel.sum()), 2.5)
            self.assertEqual(kernel[0, 0], 0.0)
            self.assertTrue(np.allclose(kernel, np.roll(kernel[::-1, ::-1], 1, axis=(0, 1))))

    def test_nearest_neighbour_couples_only_the_four_adjacent_sites(self) -> None:
        kernel = ua.build_shape_kernel("nearest", 8, 4.0)
        self.assertEqual(int(np.count_nonzero(kernel)), 4)
        self.assertAlmostEqual(float(kernel[0, 1]), 1.0)

    def test_an_unknown_shape_is_refused(self) -> None:
        with self.assertRaises(ValueError):
            ua.build_shape_kernel("gaussian", 8, 1.0)


class EffectiveResistanceTest(unittest.TestCase):
    def test_the_fourier_formula_matches_the_dense_pseudoinverse(self) -> None:
        for shape in ("nearest", "power_sigma1"):
            kernel = ua.build_shape_kernel(shape, 6, 3.0)
            resistance = ua.effective_resistance(kernel)
            for separation in (1, 2, 3):
                self.assertAlmostEqual(
                    float(resistance[separation]), _dense_resistance(kernel, separation), places=8
                )

    def test_short_range_resistance_grows_as_the_logarithm_of_distance(self) -> None:
        # One bond of conductance k per neighbour pair: R(d) ~ ln(d) / (pi k).
        bond = 1.0
        kernel = ua.build_shape_kernel("nearest", 256, 4.0 * bond)
        resistance = ua.effective_resistance(kernel)
        slope = (resistance[32] - resistance[4]) / np.log(32 / 4)
        self.assertAlmostEqual(slope * np.pi * bond, 1.0, delta=0.05)

    def test_a_tail_slower_than_r_minus_four_bounds_the_resistance(self) -> None:
        # Doubling the sheet adds a constant ln(2)/(pi k) to the short-range
        # resistance at half the side; a sigma < 2 tail adds next to nothing (the
        # sign can even be negative, since row normalization moves weight outwards).
        def far_increments(shape: str) -> list[float]:
            far = [
                float(ua.effective_resistance(ua.build_shape_kernel(shape, side, 4.0))[side // 2])
                for side in (32, 64, 128)
            ]
            return [far[1] - far[0], far[2] - far[1]]

        short = far_increments("nearest")
        tail = far_increments("power_sigma1")
        self.assertAlmostEqual(short[1] / short[0], 1.0, delta=0.1)
        self.assertTrue(all(abs(step) < 0.05 * short[0] for step in tail))


class SimulationTest(unittest.TestCase):
    def test_low_noise_variance_matches_the_harmonic_prediction(self) -> None:
        config = ua.SheetConfig(
            side=16, coupling=4.0, noise=0.05, dt=0.05, burn_in=400, steps=4000, sample_every=5
        )
        result = ua.simulate_sheet("nearest", config)
        predicted = config.noise * ua.effective_resistance(
            ua.build_shape_kernel("nearest", config.side, config.coupling)
        )
        for separation in (1, 2, 4, 8):
            self.assertAlmostEqual(
                result.variance[separation] / predicted[separation], 1.0, delta=0.15
            )

    def test_the_chord_discrepancy_is_bounded_by_the_variance(self) -> None:
        # 1 - cos x <= x^2 / 2 pointwise, so the averages obey it too.
        config = ua.SheetConfig(side=8, noise=0.2, burn_in=50, steps=300, sample_every=5)
        result = ua.simulate_sheet("exponential", config)
        self.assertTrue(np.all(result.discrepancy <= result.variance / 2 + 1e-12))

    def test_a_run_is_reproducible_from_its_seed(self) -> None:
        config = ua.SheetConfig(side=8, burn_in=10, steps=50, sample_every=5)
        first = ua.simulate_sheet("nearest", config)
        second = ua.simulate_sheet("nearest", config)
        self.assertTrue(np.array_equal(first.variance, second.variance))


class GrowthFitTest(unittest.TestCase):
    def test_logarithmic_data_is_classified_logarithmic(self) -> None:
        distance = np.arange(2, 33, dtype=float)
        fit = ua.growth_fit(distance, 0.3 + 0.1 * np.log(distance))
        self.assertEqual(fit.better, "logarithmic")

    def test_linear_data_is_classified_linear(self) -> None:
        distance = np.arange(2, 33, dtype=float)
        fit = ua.growth_fit(distance, 0.3 + 0.1 * distance)
        self.assertEqual(fit.better, "linear")


if __name__ == "__main__":
    unittest.main()
