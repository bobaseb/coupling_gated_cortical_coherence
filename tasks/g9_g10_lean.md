# G9 / G10 Lean specification — 2026-09-23

## Intent

Resolve the two hardest open Lean targets in the review ledger with sound
statements. G9 cannot infer positive dissipation from order alone: periodic
gradient equilibria have zero probability current. G10 cannot infer a rank
bound on softmax attention from query/key dimension: exponentiation changes
rank. These failures must be checked, not hidden in additional assumptions.

## Plan and success criteria

1. Add failing Lean specifications for ordered zero-dissipation states, a
   current-based dissipation bound, a spectral approximation bound for an
   explicitly rank-constrained operator, and a softmax rank counterexample.
2. Prove the G9 statements in `Phase8_FokkerPlanck`: positive self-consistent
   stationary order with zero dissipation; the sharp current bound
   `(integral J)^2 <= D * currentDissipation` for normalized positive densities.
   Order alone supplies no nonzero current or cortical power calibration.
3. Prove the finite-dimensional G10 bound in `Phase6_AttentionRank`: for an
   orthonormal eigenbasis with descending squared eigenvalues and any linear
   map of rank at most d, squared Hilbert--Schmidt error is at least the sum of
   the omitted squared eigenvalues. The rank hypothesis concerns the actual
   operator, not its logits. Check an explicit rank-one-logit/full-rank-softmax
   example and a sharp truncation example.
4. Integrate the modules and regression examples into the library and audit;
   update manuscript scope, Table S1, the ledger and lessons. Rebuild affected
   PDFs and the proof companion, and refresh an existing arXiv submission.
5. Run `lake build`, axiom and textual gates, publication gates, and companion
   freshness checks. Preserve all pre-existing workspace changes.

## Constraints

No axioms, sorry, toolchain changes, physical postulates disguised as proofs,
new Python, or new bibliographic references. Finite spectral truncation does
not construct a Mercer expansion. A current bound is dimensionless entropy
production until a physical thermal scale is supplied. No simulated bound
validation is needed where explicit analytic equality witnesses are checked.

## Open questions beyond this change

Which cortical drive enforces nonzero probability circulation, and how is its
entropy production converted to measured metabolic power? Which attention
implementation has a measured or enforced rank budget after softmax? Neither
question has data in the repository that would justify a universal answer.

## Lean-first continuation — 2026-09-23

The first full build passed: 5,769 declarations in 93 modules, only the three
permitted axioms, no Lean warnings. Main, supplement and primer compiled with
zero overfull boxes and undefined references. Companion refresh is deferred
until the remaining Lean work below is complete, following the user's steering.

1. G10(b): prove the existing KL-based mutual information of a finite joint law
   is at most its output entropy, hence at most log vocabulary size. Convert to
   bits and extend to fixed-length token sequences, without independence or
   positive-atom assumptions. Check a saturating binary copy and an independent
   output control.
2. G9(c): investigate the actual Fokker--Planck speed bound for the cosine
   moment, deriving it from current dissipation and the continuity operator.
   Keep a coupling ramp's externally specified speed separate; test whether a
   universal coupling-speed bound is false even for the uniform solution.
3. Write failing Lean specifications first, prove the valid statements, add
   witnesses and axiom checks, then perform one combined integration and
   publication/companion refresh. No new axioms or new Python code.

## Results

- G9: positive self-consistent equilibrium with zero dissipation; impossibility
  of a universally positive order-only lower bound; sharp integrated-current
  cost with a driven uniform equality witness.
- G10(a): arbitrary-rank-competitor spectral tail lower bound, attaining
  truncation, linear encoder/readout corollary, and a checked softmax rank
  counterexample. The theorem is finite-dimensional and needs a supplied
  orthonormal eigenbasis and actual rank budget.
- G10(b): the existing KL mutual information is bounded by output entropy and
  alphabet size; fixed-length sequences satisfy the bit ceiling without
  independent emissions. Binary copying saturates and independent output costs
  zero information; empty sequences convey exactly zero.
- G9(c): the cosine moment of the Fokker--Planck operator obeys the dissipation
  speed inequality. A nonzero-rate sinusoidal-drive witness exercises it. The
  uniform nonautonomous solution under positive exponential coupling proves
  that coupling slope itself can be arbitrary at zero phase-current cost.
  An ordered actuator-cost or cortical calibration remains a separate problem.

## Verification

- Both initial failing specifications and their typed witness regressions were
  observed failing on missing results, then passed after implementation.
- Combined axiom audit: 5,797 declarations in 94 modules, only `propext`,
  `Classical.choice`, `Quot.sound`; no Lean warnings or errors.
- Prose, claim-map status and coverage, leaf-module, sorry, figure-uniqueness and
  arXiv-freshness gates passed. No arxiv_submit directory exists.
- Main, supplement and primer rebuilt twice, each with zero overfull boxes and
  unresolved references. An existing unescaped underscore in main.tex's data
  path was repaired to allow the main document to compile.
- The clean HEAD supplement required the already-edited energy macro file to
  compile; no source references or physical values were invented to repair it.
