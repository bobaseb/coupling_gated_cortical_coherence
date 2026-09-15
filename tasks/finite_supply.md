# A finite source behind replenishment — 2026-09-15

## Intent and constraints

Continue the agency ledger's **Physical preparation and supply beyond the
finite model** item with one bounded change: account for the source that
replenishes a `PathwiseStore`. The source has an energy coordinate in the same
state, and the supplied work is its loss on each executed transition. Closing
this resource boundary must remove replenishment from the combined ledger.

Use the existing finite protocol and support predicates. No new physical
class, axiom, positivity assumption, dependency, Python, simulation or
reference is needed. Signed transfers admit energy returned to the source.
The source's nonnegative usable energy and the transfer identity are explicit
hypotheses; an energy-conserving finite witness must discharge them.

This is a finite source model, not preparation of that source, a continuing
external power source, a sensor-memory implementation, or a connection to the
learning agent's particular actuator. Keep those remaining tasks open.

## Model and success criteria

1. Given a store and a source energy `R`, declare `SourceLedgered R` on the
   protocol's reachable transitions: `R(t) = R(s) - supply(s,t)`. Construct
   `withSource R` with balance `balance + R`, unchanged draw and zero external
   supply. Derive its ledger from the two constituent ledgers.
2. Derive total supplied work as the source's initial mean energy minus its
   final mean energy. Derive the draw bound by the initial combined resources
   when both remain nonnegative. A uniformly positive draw before the chosen
   horizon bounds that horizon by the combined initial capacity. Reuse the
   existing pathwise/mean proofs.
3. Construct a finite source, buffer, output load and selector, all bits on
   one joint law. The three energy bits have levels zero and one; the selector
   has degenerate energy. A selector-controlled source/buffer swap is followed
   by a buffer/load swap. Both gates are permutations conserving total energy.
   The source starts charged, the buffer and load empty, the selector uniform.
   Supply is the source loss, and work drawn is the load gain on the same paths.
4. Prove the actual intermediate and final laws. Half the paths deliver a
   unit to the load and half deliver nothing while leaving the source charged.
   The store and source remain solvent and the combined capacity bounds all
   horizons. The protocol idles after its two gates: this is one attempted
   delivery, not a claim of recurrent random arrivals or unlimited work.
5. Regression checks: a claimed unit of work on every path contradicts the
   store ledger; an initially empty source delivers no work; the earlier
   charger with unbounded cumulative draw cannot have a nonnegative finite
   source satisfying this transfer identity. Available energy alone does not
   guarantee delivery, and a solvent idle state is not ongoing useful work.
6. Run failing Lean specifications before implementation and retain them in
   the witness file. Complete the zero-warning full build, axiom checks and
   applicable publication gates. Align the article, supplement, primer and
   their rebuilt PDFs; refresh the arXiv archive. Update the open item and
   append the dated execution record.

## Plan

- [x] Record the red regression run.
- [x] Prove the generic source accounting and exhaustion results.
- [x] Build the reversible finite witness and negative controls.
- [x] Align publications and rebuild all linked artifacts.
- [x] Complete the build, checks and ledger record.

## Stop rule

Stop at this finite supply and its obstructions. Do not add initial-law
preparation, sensor erasure, local content dynamics, an infinite reservoir,
continuous state spaces or optimal-policy convergence to this change.

## Execution

The working tree was clean at `fda1591`. Existing tracked-artifact logs show
zero overfull boxes, underfull counts 2/0/29 for article/supplement/primer, and
the already-recorded article Table 1 overflow of 36.46669 pt. Verify against
fresh baseline builds before finishing; repair no unrelated layout task here.

Ten retained specifications failed before the source declarations existed
(`/tmp/finite-supply-red.log`). The generic module and the complete witness
then compiled with zero warnings, passing those specifications.
The finite selector is sampled only in the initial law. The source and load
transfers are computed from energy differences on the executed gates, and
`law_eq_coin` derives the law at every horizon without resampling.

Fresh two-pass builds of the unchanged publication sources confirm the
baseline: 49/42/86 pages, zero overfull boxes, underfull counts 2/0/29 and the
36.46669 pt Table 1 overflow.

Review found a non-vacuity issue in the positive-cost horizon premise inherited
from `balance_le_of_net_cost`: a finite state coordinate cannot decrease by a
uniform positive amount at every natural-numbered stage. The source test was
strengthened to require cost only before `N`, a bounded-cost regression was
added for the existing horizon theorem, and three specifications require a
direct one-stage depletion that then idles. They failed before the correction
(`/tmp/finite-supply-horizon-red.log`). The existing induction is generalized
to `n < N` and reused by both horizon theorems. This is a weaker hypothesis,
not an additional resource assumption. The retained suite has 14 examples.

## Completed result and validation

The final `lake build` passes with zero warnings. The default axiom audit
covers 3,671 declarations in 58 modules using only `propext`,
`Classical.choice` and `Quot.sound`; explicit `#print axioms` checks on the
changed horizon results and the new headline results agree. All 14 retained
regression examples compile without warnings. Logs are in
`/tmp/finite-supply-build.log`, `/tmp/finite-supply-axioms.log` and
`/tmp/finite-supply-horizon-green.log`.

All applicable pre-commit hooks pass, including the staged-PDF freshness
check, the arXiv manifest, prose, hedging, Table S1, figures, leaves and
placeholder-proof checks. No Python changed, so its lint/type/security hooks
correctly skip this change. The complete report is
`/tmp/finite-supply-final-hooks.log`. `git diff --cached --check` passes.

The two-pass article, supplement and primer builds have 50/42/86 pages,
against the baseline's 49/42/86. All three have zero overfull boxes and
unchanged underfull counts 2/0/29. The E34 row's shorter resource summary
reduces the existing Table 1 overflow from 36.46669 pt to 22.86668 pt; that
separate P-item remains open and records the current measurement. The new
article passage, supplement passage and table row, and primer subsection
were visually checked. The 63-page arXiv submission compiles from its
unpacked tarball and passes freshness.

The source, tests, publication sources and rebuilt PDFs are kept together in
this change. Remaining work is initial-law/source preparation,
gate control and fabrication, external refuelling, sensor-memory
implementation/erasure and connecting this source to the learning agent's
actual channels. Local content agreement remains a separate agency task.
