# Agent Rules for Physics of Consciousness Repository

The following rules apply to all AI agents working on this project. These rules must be strictly adhered to without exception.

## 1. Spec-Driven & Test-Driven Development (SDD/TDD)
- **SDD:** Before writing code, state the intent, constraints, and success criteria. Enter plan mode for any non-trivial task.
- **TDD:** Write failing tests first before implementation. Follow the red-green-refactor cycle.

## 2. Python Code Quality & CI/CD
If Python code is introduced to this repository, the following tooling MUST be configured and gated as pre-commit hooks (`.pre-commit-config.yaml`):

*   **Package Management:** Use `uv` for all Python project management, dependency resolution, and virtual environments.

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

## 4. Anti-Hallucination Gate for References
- **Verify All References:** Any time a new reference or citation is added to the project (e.g., in `main.tex`), it MUST be verified for correctness via an online web search before being committed. You must independently confirm the authors, title, year, and publication venue. No fabricated or unverified references are allowed.

## 5. The Publication Is Not a Changelog
`main.tex` and `supplementary.tex` state the theory's current state only. The supplement is part of the publication and this rule covers it identically.

- **No drafting-history narration.** No "earlier drafts claimed X", no "we had recorded Y; that was a misdiagnosis", no "this is no longer assumed", and **no appendix or supplementary section collecting such material**.
- **The test** is not "is this about our past" but: *does this sentence still make sense to a reader who has never seen a previous draft?* A refutation of an axiom shape is a permanent mathematical fact and stays. "Earlier drafts of this work declared five axioms" is autobiography and goes.
- **Rewrite, do not delete blindly.** Each site becomes a present-tense statement of scope, or is removed once its content is recoverable from one of the destinations below.
- **Where it goes instead:** `CHANGELOG.md` for what a reader of the repository needs; a Lean docstring where the content is technical; `tasks/todo.md` and its archives under `_archive/` for the working record.
- **The gate:** `simulations/check_prose.py`, wired into `.pre-commit-config.yaml` as `check-prose`. It scans both publication files for drafting-history markers and fails the commit. It has **no allowlist**, deliberately: an escape hatch with one entry becomes an escape hatch with twenty. Where a pattern has a legitimate non-autobiographical use — a sequence that is no longer monotone, a quantity previously defined in the same document — reword the sentence rather than widen the gate.

The rule exists for the same reason the development declares no axioms: a constraint that lives in prose is negotiable, and one that fails the build is not. The gate catches violations; this section explains them, so that the right sentence gets written the first time.
