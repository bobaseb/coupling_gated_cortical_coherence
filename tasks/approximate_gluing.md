# L4 — Approximate overlap agreement (2026-09-14)

## Intent and route

Implement **Route A, selection**, for finite spatial mass profiles. Choose the
uniform distance between site masses, the metric already realized by the
three-site cortex's `massEquivOn` and `gsMetric`. No content coefficients,
cohomology, new physical bridge or simulation are part of this change.

The hypotheses are a fixed finite cover `U`, nonnegative local profiles `s_i`,
and nonnegative weights `w_i(x)` supported on their patches and summing to one
at every site. These are a partition of unity on the finite discrete space.
Values of a profile outside its patch are bookkeeping and must have no effect.
Agreement means distance at most `epsilon` between the restrictions of **every
pair in the same supplied family** to its overlap. The distance is a genuine
uniform metric on functions on the overlap, including the empty overlap.

## Success criteria, before implementation

1. Construct `select w s (x) = sum_i w_i(x) s_i(x)` as a nonnegative profile.
   Prove it ignores off-patch values and is within `epsilon` of each patch on
   that patch.
2. Prove that any two such partitions select profiles at distance at most
   `epsilon`. The explicit constant is `C(N) = 1` for every finite cover
   multiplicity `N`: normalization should remove the multiplicity factor in
   this uniform metric. This is stronger than the suggested `N epsilon` bound,
   not a claim in total variation or an arbitrary sheaf metric. Prove also the
   `epsilon = 0` recovery of exact gluing and the `2 delta` diameter bound for
   arbitrary profiles fitting all patches to tolerance `delta`.
3. Witness the result on the existing three-site cortex with its three
   two-site patches (multiplicity two), positive nonuniform masses and two
   partitions that select states exactly `epsilon` apart. For every positive
   `epsilon`, prove that the same approximately compatible family has no exact
   global section in the actual probability sheaf.
4. Keep two regressions explicit. Approximate agreement on all pairs cannot
   be passed as exact compatibility. Agreement on just the pairs `(0,1)` and
   `(1,2)` does not check the remaining overlap `(0,2)`. Exact pairwise overlap
   agreement of a fixed family *is* the sheaf condition and must not be
   incorrectly rejected or conflated with matching probability marginals.
5. Prove that a feature with a supplied Lipschitz bound has correspondingly
   bounded selection dependence. This states the resolution condition needed
   for an interpretation; it neither chooses a cortical decoder nor proves
   that a conscious episode depends only on such features.

## Plan and constraints

1. [x] Run failing Lean specifications before adding the implementation. The
   scratch file `l4-spec.lean` failed on the missing witness declarations;
   the red and green runs are recorded in the session scratchpad.
2. [x] Add the finite selection theorems beside the exact gluing theorem
   (`Phase5_GlobalSection.lean`, namespace `ApproximateGluing`) and the
   witnesses in `Examples/Phase5.lean` §21, using the existing measure
   dictionary. Data (`select`, `pickW`) and properties (`Compatible`,
   `IsPartition`) are separate declarations.
3. [x] Align the article, supplement, Table S1 and companion primer with the
   exact theorem scope. No reference, macro or simulation claim was added.
4. [x] Run the full Lean build, axiom audit and explicit headline axiom checks;
   pass applicable repository gates. Rebuild tracked PDFs with two LaTeX passes,
   compare warnings with HEAD, and refresh the arXiv submission.
5. [x] Mark L4 complete and append its dated result, limitations and verification
   to the task ledger.

The finite mass-profile and partition assumptions are essential structure.
The exact `ThermodynamicCover` theorem and the chain retain their exact
agreement hypothesis. This work supplies no process that acquires agreement,
no cover-selection rule and no extension theorem for content marginals. Stop
after this route, its bound, negative companions and witness.

## Completed result and verification, 2026-09-14

The six general declarations are in `Phase5_GlobalSection.lean`
(`profileDist`, `Compatible`, `IsPartition`, `select`, with `select_close`,
`select_dist_le`, `approximate_diameter_le`, `select_glue_unique`,
`select_eq_of_eqOn` and `feature_dist_le`). The witness, its two regressions
and the Lipschitz readout are `Examples/Phase5.lean` §21. No new module,
import, dependency, Python source, reference or simulation was needed.

The constant is `C(N) = 1` at every multiplicity, in the uniform mass metric,
and it is attained: on the three two-site patches of §17.1 the two extreme
partitions select states at distance exactly `ε` (`apx_select_dist`). The
matching negative is stronger than "not controlled by `ε`": for every positive
`ε` the same family admits no exact global section at all
(`apx_no_global_section`), because two patches see `right` and disagree there.
The regressions keep the approximate family from being read as an exact one
(`apxW_not_compatible_zero`, `apxSection_overlap_fails`) and show that
agreement on the overlaps `(0,1)` and `(1,2)` does not bound the selections
(`chainW_not_compatible`, `chainW_select_dist_gt`, `2ε` apart). The exact
family of §17.1 satisfies the relaxed hypothesis at `ε = 0` and the selection
returns its glued profile (`trioW_compatible`, `trioW_glue_unique`).

`lake build` passes with zero warnings; the audit covers 2,662 declarations in
45 modules resting only on `propext`, `Classical.choice` and `Quot.sound`, and
sixteen explicit headline `#print axioms` checks report the same three. The
scratch specifications that failed before implementation now all pass. The
seven applicable gates (`check_prose`, `check_figures`, `check_pdf_freshness`,
`check_arxiv_freshness`, `check_leaves`, `check_sorry`, `check_tableS1`) pass,
`check_hedging` reports zero flagged statements, and the 39 publication and
macro tests pass. The tracked PDFs are rebuilt with two passes — article 40
pages, supplement 35, primer 78 — with zero warnings and zero overfull boxes,
matching the pre-change logs, and the changed pages were inspected. The arXiv
submission is rebuilt and compiles from its unpacked tarball at 52 pages.

Scope. Route A only: finite spatial mass profiles with the uniform metric,
selection by a supplied partition of unity. Nothing here produces overlap
agreement, selects the cover or the weights, or bears on matching marginals of
decoded contents. `sheaf_glue_unique`, the `ThermodynamicCover` instances and
the composed chain retain their exact agreement hypothesis. Route B, the
obstruction-theoretic version, still requires choosing a content state space
and is not started.
