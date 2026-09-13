# Active branch of the conditional chain — 2026-09-13

## Intent and scope

Extend the composition to the finite feedback process developed in
`tasks/agency.md`. Preserve the passive composition and share the proof from
coarse-graining to the same cover's unique fixed point. The active path must
name its process throughout; existence of an unrelated agent is insufficient.

This is a separate, bounded follow-up to the agency extension. It introduces
no learning rule, cortical identification, simulation or new reference.

## Design and constraints

- `ActiveBound M θ q B` records a positive thermal scale, the derived bound
  `θ (H(M.initial) - H(M.final)) ≤ M.meanHeat q`, and actual heat at most `B`.
  The signed passive information difference is not substituted into this bound.
- `E34Active` names a `FiniteFeedbackStep sys S` on the register's own state
  type. Positivity, local detailed balance at the register's temperature and
  heat within the register's named budget are physical bridge hypotheses.
  Landauer's lower bound does not imply this upper-budget allocation. The
  register update and controlled substep are not claimed to be one operation.
- `E45Active` consumes that very process, heat observable, temperature and
  budget. Its implication to the specified coupling-energy limit remains an
  explicit modelling assumption; it is not a thermodynamic theorem.
- Reuse `E12`, `E23` and `E56` through `E89`. Remove the unused predictive
  carrier parameters of `E56` so both branches share a carrier-independent
  downstream proof. Preserve the passive theorem's mathematical statement.
- Keep the fixed-controller, finite, strictly positive autonomous-step scope
  visible. General perception--action cycles require additional thermodynamic
  accounting; the supplied reciprocal example accounts for its two substeps.
- No axioms, placeholders or new physical structure fields. Preserve the
  user's existing primer source edits.

## Success criteria and execution plan

1. Write Lean regression specifications first and observe their failure.
2. Derive the active node, factor the downstream proof and compose
   `chain_active` with eight named bridge hypotheses.
3. Witness the complete branch using the nontrivial thermal actuator and
   existing moving mesh/cover. Check rejection of zero heat budget and an
   incompatible coupling-energy limit. The witness proves satisfiability,
   not a common physical mechanism or budget-driven mesh convergence.
4. Update the article's edge table, supplement and repository ledgers. Rebuild
   both publication PDFs twice and the assembled arXiv submission.
5. Pass the full Lean build and axiom audit, headline axiom checks and relevant
   prose/table/figure/placeholder/freshness gates.

## Progress

- [x] Red regression specifications fail before implementation (missing active
      predicates, constructors, rejection results and joint witness).
- [x] Shared downstream proof and active composition pass with zero warnings.
- [x] Nontrivial witness and rejection tests pass. Headline axiom checks report
      only `propext`, `Classical.choice` and `Quot.sound`.
- [x] Publication source and built artifacts agree.
- [x] Required validation passes.

## Completed result and validation

`Chain.lean` contains the active predicates, node constructors, shared downstream
proof and `chain_active`. Its passive joint witness still compiles. The active
joint witness uses the same thermal actuator whose action dependence, positive
heat and negative passive signed waste are proved under `Examples/`.

The first build failed on the regression specifications before the declarations
were implemented. The completed `lake build` has zero warnings; its default
axiom audit checks 2,320 declarations in 42 modules and accepts only `propext`,
`Classical.choice` and `Quot.sound`. Explicit headline axiom checks agree.
The prose, Table S1, figure, leaf and placeholder gates pass. No Python code or
simulation was added in this follow-up.

The article's diagram and edge table describe both branches. The supplement's
implementation account and Table S1 give their separate thermodynamic premises
and common downstream assumptions. Both PDFs were rebuilt with two passes;
the article is 38 pages and the supplement 31, with no LaTeX warnings or
overfull boxes. The two new bibliography links have explicit break opportunities.
The shared bibliography also prompted a two-pass primer rebuild (68 pages);
the user's pre-existing primer source edits were preserved.

`prepare_arxiv.sh` compiled the unpacked submission archive cleanly at 47 pages.
The archive freshness gate passes. In addition to the staged-PDF gate, a check
of the entire working-tree diff and dependency timestamps confirms that all
three tracked PDFs are current. `git diff --check` passes.

## Open physical questions

The budget allocation, the identification of register and controller, and the
coupling dynamics relating this process to a convergent energy sequence need a
physical model. They remain assumptions of the composition. Neither branch
derives a policy, objective, local-state compatibility or biological mechanism.
