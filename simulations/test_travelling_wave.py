import json
import tempfile
import unittest
from pathlib import Path
from typing import cast

import hypothesis.strategies as st
import numpy as np
from hypothesis import assume, given, settings
from hypothesis.extra.numpy import arrays

from spatial_kernel import build_kernel, coupling_drift, defect_winding
from travelling_wave import (
    WaveConfig,
    axis_winding,
    coherence_gap,
    detuning_field,
    global_order,
    local_order,
    patch_cells,
    retention_boundary,
    run_sweep,
    simulate_wave,
    twisted_phases,
)

PHASES = arrays(
    dtype=float,
    shape=(8, 8),
    elements=st.floats(min_value=-np.pi, max_value=np.pi),
)


class TwistedStateTest(unittest.TestCase):
    """A twist is the wave state the chain's own hypotheses admit."""

    def test_twist_winds_once_across_the_sheet_without_a_point_defect(self) -> None:
        phases = twisted_phases(side=16, winding_q=1)

        self.assertEqual(axis_winding(phases), (0, 1))
        self.assertEqual(int(np.count_nonzero(defect_winding(phases))), 0)

    def test_twist_is_globally_incoherent_and_locally_ordered(self) -> None:
        phases = twisted_phases(side=128, winding_q=1)

        self.assertAlmostEqual(global_order(phases), 0.0, places=12)
        self.assertGreater(local_order(phases, cells=12), 0.9)

    def test_uniform_sheet_has_no_coherence_gap(self) -> None:
        phases = twisted_phases(side=32, winding_q=0)

        self.assertAlmostEqual(global_order(phases), 1.0, places=12)
        self.assertAlmostEqual(local_order(phases, cells=4), 1.0, places=12)

    def test_patch_size_converts_from_millimetres_and_stays_on_the_sheet(self) -> None:
        self.assertEqual(patch_cells(WaveConfig(side=128, extent_mm=2.0, patch_mm=0.2)), 12)
        self.assertEqual(patch_cells(WaveConfig(side=8, extent_mm=2.0, patch_mm=8.0)), 3)

    def test_detuning_is_periodic_across_the_sheet_and_has_zero_mean(self) -> None:
        """A linear ramp has a seam on a torus; the periodic detuning does not."""
        field = detuning_field(side=16, detuning_rad_s=2.0)

        self.assertAlmostEqual(float(np.mean(field)), 0.0, places=12)
        self.assertAlmostEqual(float(np.max(np.abs(field))), 2.0, places=12)
        np.testing.assert_allclose(field[0], field[5], atol=1e-12)
        self.assertGreater(float(np.std(field[0])), 0.0)


class SimulationTest(unittest.TestCase):
    def test_smoke_simulation_is_reproducible(self) -> None:
        config = WaveConfig(
            side=12, decay_mm=0.2, diffusion=0.05, dt=0.02, steps=20, sample_every=4, seed=7
        )

        first = simulate_wave(config)
        second = simulate_wave(config)

        np.testing.assert_array_equal(first.global_order, second.global_order)
        np.testing.assert_array_equal(first.local_order, second.local_order)
        self.assertEqual(first.final_phases.shape, (12, 12))
        self.assertEqual(first.global_order.shape, (6,))

    def test_noiseless_twist_persists_and_keeps_the_coherence_gap_open(self) -> None:
        config = WaveConfig(
            side=32,
            decay_mm=0.2,
            diffusion=0.0,
            winding_q=1,
            dt=0.01,
            steps=200,
            sample_every=50,
            seed=3,
        )

        result = simulate_wave(config)

        self.assertEqual(result.axis_winding[-1], (0, 1))
        self.assertLess(result.global_order[-1], 0.05)
        self.assertGreater(result.local_order[-1], 0.9)
        self.assertGreater(coherence_gap(result), 0.8)

    def test_noiseless_uniform_start_has_no_gap_to_report(self) -> None:
        config = WaveConfig(
            side=32, diffusion=0.0, winding_q=0, dt=0.01, steps=200, sample_every=50, seed=3
        )

        result = simulate_wave(config)

        self.assertGreater(result.global_order[-1], 0.99)
        self.assertLess(coherence_gap(result), 0.01)


class SweepTest(unittest.TestCase):
    def test_sweep_runs_the_twist_against_its_uniform_control(self) -> None:
        config = WaveConfig(
            side=16,
            winding_q=1,
            diffusion=0.0,
            dt=0.02,
            steps=40,
            sample_every=20,
            patch_mm=0.3,
            seed=5,
        )

        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            summary = run_sweep(config, np.asarray([0.05, 0.2]), output)
            payload = json.loads((output / "travelling_wave_summary.json").read_text())
            self.assertTrue((output / "travelling_wave_sweep.png").exists())
            saved_runs = len(list(output.glob("wave_lambda_*.npz")))
            resumed = run_sweep(config, np.asarray([0.05, 0.2]), output)
            np.testing.assert_array_equal(resumed.steady_global, summary.steady_global)

        self.assertEqual(summary.steady_defect_density.shape, (2,))
        self.assertEqual(saved_runs, 4)
        self.assertEqual(payload["decay_mm"], [0.05, 0.2])
        for control in payload["control_global_order"]:
            self.assertGreater(control, 0.99)
        for gap in payload["steady_coherence_gap"]:
            self.assertGreaterEqual(gap, -1e-9)

    def test_boundary_needs_the_loss_of_the_twist_to_be_sustained(self) -> None:
        decay = np.array([0.05, 0.1, 0.2, 0.4])

        held = retention_boundary(decay, np.array([1, 1, 0, 0]))
        self.assertIsNotNone(held)
        self.assertAlmostEqual(cast(float, held), float(np.sqrt(0.1 * 0.2)))

        self.assertIsNone(retention_boundary(decay, np.array([1, 1, 0, 1])))
        self.assertIsNone(retention_boundary(decay, np.array([1, 1, 1, 1])))
        self.assertIsNone(retention_boundary(decay, np.array([0, 0, 0, 0])))


class WavePropertyTest(unittest.TestCase):
    @given(PHASES, st.integers(min_value=1, max_value=3))
    @settings(deadline=None, max_examples=30)
    def test_property_local_order_dominates_global_order(
        self, phases: np.ndarray, cells: int
    ) -> None:
        """Patch means average to the global mean, so |mean| <= mean|.|."""
        self.assertGreaterEqual(local_order(phases, cells) + 1e-9, global_order(phases))

    @given(PHASES, st.floats(min_value=-10.0, max_value=10.0), st.integers(1, 3))
    @settings(deadline=None, max_examples=30)
    def test_property_orders_are_invariant_under_a_global_phase_shift(
        self, phases: np.ndarray, shift: float, cells: int
    ) -> None:
        np.testing.assert_allclose(global_order(phases + shift), global_order(phases), atol=1e-9)
        np.testing.assert_allclose(
            local_order(phases + shift, cells), local_order(phases, cells), atol=1e-9
        )

    @given(PHASES, st.integers(-7, 7), st.integers(-7, 7), st.integers(1, 3))
    @settings(deadline=None, max_examples=30)
    def test_property_local_order_is_invariant_under_translation(
        self, phases: np.ndarray, down: int, across: int, cells: int
    ) -> None:
        rolled = np.roll(np.roll(phases, down, axis=0), across, axis=1)
        np.testing.assert_allclose(
            local_order(rolled, cells), local_order(phases, cells), atol=1e-9
        )

    @given(
        st.integers(min_value=4, max_value=24).filter(lambda value: value % 2 == 0),
        st.integers(min_value=-4, max_value=4),
        st.floats(min_value=0.5, max_value=6.0),
    )
    @settings(deadline=None, max_examples=30)
    def test_property_a_twist_is_a_stationary_state_of_the_symmetric_kernel(
        self, side: int, winding_q: int, decay_grid: float
    ) -> None:
        """Isotropy makes the coupling drift on a twist cancel pair by pair."""
        kernel = build_kernel(side=side, decay_grid=decay_grid, coupling=8.0)
        drift = coupling_drift(twisted_phases(side, winding_q), np.fft.fft2(kernel))

        np.testing.assert_allclose(drift, np.zeros_like(drift), atol=1e-9)

    @given(
        st.integers(min_value=4, max_value=24).filter(lambda value: value % 2 == 0),
        st.integers(min_value=-4, max_value=4),
    )
    @settings(deadline=None, max_examples=30)
    def test_property_a_twist_carries_winding_without_a_singularity(
        self, side: int, winding_q: int
    ) -> None:
        """Below the Nyquist twist the winding is readable and no defect appears."""
        assume(abs(winding_q) * 2 < side)
        phases = twisted_phases(side, winding_q)

        self.assertEqual(axis_winding(phases), (0, winding_q))
        self.assertEqual(int(np.count_nonzero(defect_winding(phases))), 0)

    @given(
        st.lists(st.floats(min_value=0.01, max_value=1.0), min_size=2, max_size=8, unique=True),
        st.integers(min_value=1, max_value=7),
    )
    @settings(deadline=None, max_examples=30)
    def test_property_a_boundary_separates_held_lengths_from_lost_ones(
        self, lengths: list[float], split: int
    ) -> None:
        """Any monotone held-then-lost pattern puts the boundary between the two."""
        decay = np.sort(np.asarray(lengths))
        assume(0 < split < decay.size)
        retained = np.array([1] * split + [0] * (decay.size - split))

        boundary = retention_boundary(decay, retained)

        self.assertIsNotNone(boundary)
        self.assertGreater(cast(float, boundary), decay[split - 1])
        self.assertLess(cast(float, boundary), decay[split])

    @given(
        st.integers(min_value=8, max_value=32).filter(lambda value: value % 2 == 0),
        st.integers(min_value=1, max_value=6),
    )
    @settings(deadline=None, max_examples=30)
    def test_property_any_nonzero_twist_reads_as_globally_incoherent(
        self, side: int, winding_q: int
    ) -> None:
        assume(winding_q % side != 0)

        self.assertAlmostEqual(global_order(twisted_phases(side, winding_q)), 0.0, places=10)


if __name__ == "__main__":
    unittest.main()
