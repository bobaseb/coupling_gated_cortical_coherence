"""Checks for the field-energy scale used by the cortical budget."""

import math
import unittest

from fermi_estimate_check import stored_field_energy


class StoredFieldEnergyTest(unittest.TestCase):
    def test_energy_uses_field_squared_and_spherical_volume(self) -> None:
        epsilon_0 = 8.8541878128e-12
        radius = 0.2e-3
        expected = 0.5 * epsilon_0 * 1e5 * 0.3**2 * (4.0 / 3.0) * math.pi * radius**3
        self.assertAlmostEqual(stored_field_energy(0.3, 1e5, radius), expected)

    def test_field_energy_scales_quadratically(self) -> None:
        baseline = stored_field_energy(0.1, 1e5, 0.1e-3)
        self.assertAlmostEqual(stored_field_energy(0.2, 1e5, 0.1e-3), 4 * baseline)


if __name__ == "__main__":
    unittest.main()
