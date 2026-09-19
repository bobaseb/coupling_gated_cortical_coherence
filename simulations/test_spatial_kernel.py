import tempfile
import unittest
from pathlib import Path
from typing import cast
from unittest import mock

import hypothesis.strategies as st
import numpy as np
from hypothesis import given, settings
from hypothesis.extra.numpy import arrays

import spatial_kernel
from spatial_kernel import (
    SpatialConfig,
    build_kernel,
    coupling_drift,
    defect_winding,
    empirical_lambda_grid_units,
    estimate_critical_decay,
    refined_decay_lengths,
    simulate_spatial,
    spacing_mm,
    transition_band,
)


class SpatialKernelTest(unittest.TestCase):
    def test_kernel_excludes_self_and_has_fixed_row_sum(self) -> None:
        kernel = build_kernel(side=8, decay_grid=1.7, coupling=6.0)

        self.assertEqual(kernel.shape, (8, 8))
        self.assertEqual(kernel[0, 0], 0.0)
        self.assertAlmostEqual(float(np.sum(kernel)), 6.0)
        reflected = np.roll(np.flip(kernel, axis=(0, 1)), shift=(1, 1), axis=(0, 1))
        np.testing.assert_array_equal(kernel, reflected)

    def test_fft_coupling_matches_explicit_periodic_sum(self) -> None:
        phases = np.arange(16, dtype=float).reshape(4, 4) * 0.31
        kernel = build_kernel(side=4, decay_grid=1.2, coupling=3.5)
        fft_drift = coupling_drift(phases, np.fft.fft2(kernel))
        direct = np.zeros_like(phases)
        for row in range(4):
            for column in range(4):
                for delta_row in range(4):
                    for delta_column in range(4):
                        neighbour = phases[(row - delta_row) % 4, (column - delta_column) % 4]
                        direct[row, column] += kernel[delta_row, delta_column] * np.sin(
                            neighbour - phases[row, column]
                        )

        np.testing.assert_allclose(fft_drift, direct, atol=1e-12)

    def test_winding_detects_a_single_vortex_and_antivortex(self) -> None:
        phases = np.array(
            [
                [-3.0 * np.pi / 4.0, 3.0 * np.pi / 4.0],
                [-np.pi / 4.0, np.pi / 4.0],
            ]
        )

        winding = defect_winding(phases)

        self.assertGreater(int(np.count_nonzero(winding)), 0)
        self.assertEqual(int(np.sum(winding == 1)), int(np.sum(winding == -1)))
        self.assertEqual(int(np.sum(winding)), 0)

    def test_empirical_lengths_convert_from_shared_physical_constants(self) -> None:
        converted = empirical_lambda_grid_units(side=128, extent_mm=2.0)

        np.testing.assert_allclose(converted, [6.4, 12.8, 19.2])

    def test_critical_length_requires_a_sustained_order_crossing(self) -> None:
        decay = np.array([0.01, 0.02, 0.03, 0.04, 0.05])
        order = np.array([0.1, 0.3, 0.15, 0.4, 0.5])

        critical = estimate_critical_decay(decay, order, threshold=0.2)

        self.assertIsNotNone(critical)
        self.assertAlmostEqual(cast(float, critical), 0.032)

    def test_transition_band_keeps_samples_past_the_first_sustained_crossing(self) -> None:
        decay = np.array([0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07])
        order = np.array([0.1, 0.3, 0.15, 0.4, 0.5, 0.6, 0.7])

        np.testing.assert_allclose(
            transition_band(decay, order, threshold=0.2, follow=0), [0.01, 0.02, 0.03, 0.04]
        )
        np.testing.assert_allclose(
            transition_band(decay, order, threshold=0.2), [0.01, 0.02, 0.03, 0.04, 0.05, 0.06]
        )

    def test_refined_lengths_sample_both_a_fixed_length_and_a_fixed_cell_count(self) -> None:
        base = SpatialConfig(side=128, extent_mm=2.0)
        refined = SpatialConfig(side=256, extent_mm=2.0)
        band = np.array([0.0085, 0.0140, 0.0147])

        lengths = refined_decay_lengths(band, base, refined)

        refined_cells = lengths / spacing_mm(refined)
        base_cells = band / spacing_mm(base)
        for cells in base_cells:
            self.assertTrue(np.any(np.isclose(refined_cells, cells)), f"{cells} cells unsampled")
            self.assertTrue(np.any(np.isclose(lengths, cells * spacing_mm(base))))
        self.assertEqual(lengths.size, 2 * band.size)

    def test_refined_lengths_follow_the_spacing_ratio_rather_than_a_literal_half(self) -> None:
        base = SpatialConfig(side=128, extent_mm=2.0)
        band = np.array([0.012])

        quartered = refined_decay_lengths(band, base, SpatialConfig(side=512, extent_mm=2.0))

        np.testing.assert_allclose(np.sort(quartered), [0.003, 0.012])

    def test_smoke_simulation_is_reproducible_and_stores_only_summaries(self) -> None:
        config = SpatialConfig(
            side=12,
            extent_mm=2.0,
            decay_mm=0.2,
            coupling=5.0,
            diffusion=0.1,
            frequency_sigma=0.2,
            dt=0.02,
            steps=20,
            sample_every=4,
            seed=91,
        )

        first = simulate_spatial(config)
        second = simulate_spatial(config)

        np.testing.assert_array_equal(first.order, second.order)
        np.testing.assert_array_equal(first.defect_density, second.defect_density)
        np.testing.assert_array_equal(first.final_phases, second.final_phases)
        self.assertEqual(first.order.shape, (6,))
        self.assertEqual(first.final_phases.shape, (12, 12))
        self.assertFalse(hasattr(first, "phase_history"))
        self.assertAlmostEqual(first.time[-1], 0.4)


class SpatialKernelPropertyTest(unittest.TestCase):
    @given(
        st.integers(min_value=4, max_value=24).filter(lambda x: x % 2 == 0),
        st.floats(min_value=0.1, max_value=10.0),
        st.floats(min_value=0.1, max_value=100.0),
    )
    @settings(deadline=None)
    def test_property_kernel_invariants(
        self, side: int, decay_grid: float, coupling: float
    ) -> None:
        kernel = build_kernel(side=side, decay_grid=decay_grid, coupling=coupling)
        self.assertEqual(kernel.shape, (side, side))
        self.assertEqual(kernel[0, 0], 0.0)
        self.assertAlmostEqual(float(np.sum(kernel)) / coupling, 1.0, places=5)
        reflected = np.roll(np.flip(kernel, axis=(0, 1)), shift=(1, 1), axis=(0, 1))
        np.testing.assert_allclose(kernel, reflected, atol=1e-10)

    @given(
        arrays(dtype=float, shape=(4, 4), elements=st.floats(min_value=-np.pi, max_value=np.pi)),
        st.floats(min_value=0.5, max_value=5.0),
        st.floats(min_value=1.0, max_value=10.0),
    )
    @settings(deadline=None, max_examples=20)
    def test_property_fft_coupling_matches_explicit_sum(
        self, phases: np.ndarray, decay: float, coupling: float
    ) -> None:
        kernel = build_kernel(side=4, decay_grid=decay, coupling=coupling)
        fft_drift = coupling_drift(phases, np.fft.fft2(kernel))
        direct = np.zeros_like(phases)
        for row in range(4):
            for column in range(4):
                for delta_row in range(4):
                    for delta_column in range(4):
                        neighbour = phases[(row - delta_row) % 4, (column - delta_column) % 4]
                        direct[row, column] += kernel[delta_row, delta_column] * np.sin(
                            neighbour - phases[row, column]
                        )
        np.testing.assert_allclose(fft_drift, direct, atol=1e-10)


if __name__ == "__main__":
    unittest.main()


class ReplotTest(unittest.TestCase):
    """Redrawing a finished sweep must read its artifacts, never the integrator."""

    def test_replot_redraws_from_saved_artifacts_without_integrating(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            output = Path(name)
            config = spatial_kernel.SpatialConfig(side=8, steps=4, sample_every=2, dt=0.02)
            lengths = np.array([0.05, 0.2])
            spatial_kernel.run_sweep(config, lengths, output)
            figure = output / "spatial_kernel_sweep.png"
            figure.unlink()

            def explode(*_: object, **__: object) -> None:
                raise AssertionError("replot must not integrate")

            with mock.patch.object(spatial_kernel, "simulate_spatial", explode):
                spatial_kernel.replot(output)
            self.assertTrue(figure.exists())

    def test_replot_reports_a_sweep_whose_checkpoints_are_missing(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            output = Path(name)
            config = spatial_kernel.SpatialConfig(side=8, steps=4, sample_every=2, dt=0.02)
            spatial_kernel.run_sweep(config, np.array([0.05]), output)
            next(output.glob("spatial_lambda_*.npz")).unlink()
            with self.assertRaises(FileNotFoundError):
                spatial_kernel.replot(output)
