# Agent Rules for Physics of Consciousness Repository

The following rules apply to all AI agents working on this project. These rules must be strictly adhered to without exception.

## 1. Spec-Driven & Test-Driven Development (SDD/TDD)
- **SDD:** Before writing code, state the intent, constraints, and success criteria. Enter plan mode for any non-trivial task.
- **TDD:** Write failing tests first before implementation. Follow the red-green-refactor cycle.

## 2. Python Code Quality & CI/CD
If Python code is introduced to this repository, the following tooling MUST be configured and gated as pre-commit hooks (`.pre-commit-config.yaml`):

*   **Linting & Formatting:** Use `ruff`.
*   **Static Type Checking:** Use `mypy` with strict settings.
*   **Security Scanning:** Use `bandit` and/or `ruff`'s security rules (`S` rules). Never hardcode secrets.
*   **Dead Code Elimination:** Use `vulture` to find and eliminate dead code.
*   **Cyclomatic Complexity:** Use `radon` and `xenon`. Code complexity must be strictly gated: Cyclomatic complexity must remain **below 10**.
*   **Architecture Enforcement:** Use `tach` to enforce modularity and architectural boundaries.

## 3. General Operating Model
- Treat output as a draft, not ground truth. Stop and list Open Questions if information is missing.
- Default to SRR (Small, Reviewable, Reversible) changes.
- Ensure simplicity. Push back if a simpler solution exists over a clever one.
- Match existing patterns in the codebase. Consistency over novelty.
- If scope expands, stop and split into separate changes.
