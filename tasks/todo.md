# Plan: Add Property-Based Testing

**Intent:** Introduce property-based testing to the Python simulation suite using the `hypothesis` library to verify mathematical invariants of core numerical functions.
**Constraints:** 
- Must use the `hypothesis` framework alongside the existing `unittest` structure.
- Must not break existing deterministic tests. 
- Must comply with the existing strict static type checking (`mypy`) and linting (`ruff`).
- Keep additions Small, Reviewable, Reversible (SRR).
**Success Criteria:** Property tests run successfully and all pre-commit checks pass.

## Tasks

- [x] Add `hypothesis` to the `dev` dependency group in `simulations/pyproject.toml`.
- [x] Run `uv lock` in `simulations/` to update the lockfile.
- [x] Add property-based tests to `simulations/test_structural_resonance.py` for mathematical functions:
  - `project`: prove that total resources are conserved and the matrix is symmetrical with zero diagonal.
  - `symmetric_gradient`: prove symmetry for arbitrary inputs.
- [x] Add property-based tests to `simulations/test_quasistatic_error.py` for logical invariants:
  - `stationary_order`: prove it evaluates to 0 below threshold and falls within (0, 1) above threshold for varied ranges of inputs.
- [x] Run `uv run pytest` to ensure tests pass.
- [x] Run `uv run pre-commit run --all-files` to ensure format, types, and style checks pass.
