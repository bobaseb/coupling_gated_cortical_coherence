# Agency extension — specification, 2026-09-13

## Intent

Make perception and action explicit and retain the passive information theorem
as a special case. Supply a finite physical feedback example with a declared
reservoir and a checked entropy balance. This is an extension of the supporting
thermodynamics, not a derivation of a cortical policy or an agent's goals.

## Constraints

- Reuse the KL-based mutual information in `Phase3_PredictiveThermodynamics`.
- Use real subtraction for signed information differences. Prove the
  nonnegativity of conditional information under explicit finiteness conditions.
- Specify policy, world, observation and memory-update channels. Do not assume
  a dissipation inequality as the conclusion of a new structure field.
- Keep physical transition/bath assumptions distinct from information identities.
- Add witnesses and regression checks before implementing their declarations.
- Keep the axiom audit and pinned Lean toolchain intact; add every module to
  the build. Update the manuscript and supplement and rebuild their PDFs.
- Preserve the primer edits already present at the start of this task.
- Introduce no simulation sweep or computed publication numerals.

## Reviewable changes and success criteria

1. Information and dynamics: build the feedback law, prove
   `I(X;S) - I(X;S') = I(X;S | S') - I(X;S' | S)`, prove both
   conditional terms nonnegative, recover the passive inequality, and check an
   action that increases mutual information. Exercise the observation/update
   portion of the loop as well as the actuator.
2. Thermodynamics: construct normalized forward and reverse laws for a finite
   environment update conditioned on the fixed agent state, derive their KL
   entropy-production balance, and witness it with an action-dependent noisy
   two-bit process. State reservoir/heat identification explicitly. Check a
   nonzero cost and the feedback information accounting on the same process.
3. Publication and validation: state these results and their scope consistently,
   verify new references online, rebuild PDFs (including the assembled arXiv
   submission if present), run the Lean build/audit and relevant publication gates.

## Execution

- [x] Red: regression declarations fail before implementation.
- [x] Information/dynamics proofs and witnesses pass.
- [x] Finite thermodynamic balance and physical witness pass.
- [x] Publications and PDFs agree with the verified results.
- [x] Build, axiom audit and publication gates pass.

## Completed result

`Phase3_Agency.lean` composes all four channels and proves the conditional
information identity, nonnegativity and passive recovery. The finite-measure
bridge in `Phase3_FiniteInformation.lean` reuses the existing `ProbDist` and
proves equality with Mathlib KL, as well as finite mutual information for every
finite discrete probability law, including zero atoms.

`Phase3_AgencyThermodynamics.lean` constructs normalized forward/reverse laws
and derives the entropy and first-law balances. `history_toAgency` identifies
these paths with the explicit policy-generated history. The reciprocal witness
uses an interaction energy difference of log 3 at k_B T = 1. Its actuation
creates correlations and releases heat from the initial nonequilibrium energy;
sensing changes individual internal states while preserving the equilibrium
joint law. The full cycle, signed information, heat, energy and work are checked.

The heat-budget interface is `Chain.active_entropy_budget`. The follow-up in
`tasks/agency_chain.md` carries it into `chain_active` through a named process,
physical budget allocation and an explicit coupling-convergence assumption.
The passive `chain` retains its predictive node. Neither branch supplies a
physical model connecting cortical coupling to an optimized policy.

Validation: `lake build` passes with zero warnings; `Audit` verifies 2,306
declarations across 42 modules with only propext, Classical.choice and Quot.sound.
Headline results were additionally checked with `#print axioms`. The 31 PDF,
arXiv-freshness and figure tests pass. Ruff, strict mypy (52 files), Bandit,
Vulture, Xenon and Tach pass for the changed Python tooling at its normal scope.
The prose, table, figure, leaf, placeholder and freshness gates pass.

Both publication PDFs were rebuilt twice with no warnings or overfull boxes.
The primer PDF was rebuilt from the pre-existing edited source because it shares
the bibliography; its source edits were preserved. `prepare_arxiv.sh` rebuilt
and verified the 46-page submission from the unpacked tarball. No simulation ran.

The additional bibliography entries exposed xr's citation import: the supplement
now uses its supported `[][nocite]` option to import labels only. A failing
regression test preceded the dependency parser's support for both optional
arguments, preserving PDF/arXiv freshness tracking of the external document.

References independently verified online on 2026-09-13:

- Jordan M. Horowitz and Massimiliano Esposito, *Thermodynamics with Continuous
  Information Flow*, Physical Review X **4**, 031015 (2014),
  https://doi.org/10.1103/PhysRevX.4.031015.
- Sosuke Ito and Takahiro Sagawa, *Information Thermodynamics on Causal Networks*,
  Physical Review Letters **111**, 180603 (2013),
  https://doi.org/10.1103/PhysRevLett.111.180603.

## Open modelling questions

The cortical memory readout, action readout, environmental state sufficient for
Markov dynamics, biological objective and reservoir calibration remain empirical
choices. The finite examples below will declare their own choices explicitly.
