# Stationary densities and linear stability — 2026-09-15

## Intent and scope

Finish the four unchecked Lean items in `tasks/todo.md`, excluding R items.
The model is the identical-frequency noisy mean-field Kuramoto equation in its
rotating frame, with positive diffusion. Its periodic current and differential
operator must be definitions of the named density and drift. Differentiability
must accompany every use of the totalized `deriv` operation.

## Plan and success criteria

1. Specify regression statements before implementation. Derive zero stationary
   current for a periodic gradient drift and classify the normalized stationary
   density as von Mises. Use a nonconstant witness and a nongradient control.
2. Connect the existing fixed-point existence and uniqueness results to this
   stationarity predicate, including the uniform solution.
3. Compute the linearized operator on the Fourier harmonics of the uniform
   solution, with first-mode rate `K / 2 - D` and higher-mode rates `-D n²`.
4. Prove linear stability of the coherent branch modulo its rotational mode.
   Derive the needed inequalities from the specified density; do not assume
   stability, a spectral gap, or a covariance inequality as a physical input.
   Keep nonlinear stability, solution construction and the finite-particle
   mean-field limit distinct from estimates for the limiting equation.
5. Run the complete warning-free Lean build and axiom audit, update the ledger
   and publication scope, rebuild tracked PDFs twice, and refresh the assembled
   arXiv submission if present. Run the applicable repository gates.

## Constraints

No new axioms, admitted proofs, toolchain changes, simulation sweeps, or R work.
Use separate modules for the stationary and stability proofs, with real
downstream consumers. Document hypotheses and non-degeneracy in Lean. The
squared-drift functional over substrate sites and current dissipation over phase
space have different domains; no identification of them is intended.

## Execution record

- Baseline: clean working tree; `lake build` passes, including the audit of
  4293 declarations in 69 modules.
- Regressions first. `Examples/Phase8.lean` §21 was written against declarations
  that did not exist and failed to compile; it compiles now. The nonconstant
  witness (`unitBranch_not_uniform`) and the nonzero rate
  (`unitBranch_rate_pos`) are the two hollowness checks the plan asked for, and
  the subcritical control `incoherent_stable_one_one` is the nongradient
  control's counterpart for the incoherent criterion.
- Criterion 1 — **the stationary equation and the classification.**
  `Phase8_FokkerPlanck.lean`. `current`, `operator` and `IsStationary` are
  definitions over named data; differentiability of the density and of its
  current are fields of the predicate, because `deriv` is totalized and an
  equation stated with it alone admits spurious solutions. The predicate binds
  every symbol it constrains, which is the soundness requirement the plan
  carried over from `AGENTS.md` §1. `integratingFactor_hasDerivAt`,
  `stationary_current_zero`, `stationary_gibbs`, `stationary_iff_vonMises`.
- Criterion 2 — **existence, connected.** `supercritical_stationary_existsUnique`
  transfers `supercritical_fixed_point_existsUnique` through the classification;
  it needed no new analysis. The uniform solution is the subcritical side of the
  same statement and is what `incoherent_instability_iff` linearizes about.
- Criterion 3 — **the incoherent linearization.** `Phase8_Linearization.lean`.
  `current_expansion` is an exact expansion of the current at `q + εu`, not a
  declared rate list; `incoherent_mode_rate` reads `K / 2 - D` at the first
  harmonic and `-D n²` above it off that expansion, on both the cosine and sine
  families; `incoherent_instability_iff` is the threshold. Per-mode: no
  completeness of the Fourier family is claimed.
- Criterion 4 — **the coherent branch, modulo rotation.** Four modules, in
  dependency order: `Phase8_StabilityMoments.lean` derives the strict moment
  inequality `cosine_variance_lt_sine` from the Riccati identity for `E`, so the
  covariance inequality is a theorem and not a physical input, as the plan
  required; `Phase8_CircleForm.lean` builds the quadratic form on continuous
  functions over the whole circle; `Phase8_WeightedPoincare.lean` supplies the
  weighted inequality with an explicit finite constant; `Phase8_CoherentStability.lean`
  proves `coherent_linear_stability` with a positive rate and exhibits the
  rotation direction as a nonzero element of rate zero (`rotation_generator_zero`),
  which forces the transversality rather than assuming it. Nonlinear stability,
  construction of solutions and the finite-`N` limit are untouched and are said
  to be untouched.
- Separation, as a theorem. `stationary_current_separation` evaluates current
  dissipation and the phase-averaged squared drift at the coherent stationary
  state: zero and positive. Both are functionals on phase space. The plan's
  constraint holds: nothing identifies either with `sigmaContinuum`, which is a
  functional of the coupling kernel over substrate sites, and no result records
  such an identification.
- Downstream consumers, as the constraints required. `Phase9_EMIdentification.IsEMFieldCoupling.coherent_phase_model`
  carries the stationary state and the gap to the identified field model at that
  model's own coupling and diffusion. `Phase8_CriticalExponent.lean` stops being
  a recorded leaf — `Phase8_StabilityMoments` consumes its moment derivatives —
  so its entry leaves `check_leaves.ALLOWED_LEAVES`.
- Criterion 5 — **verification.** `lake build` clean, zero warnings; axiom audit
  4521 declarations in 75 modules on `propext`, `Classical.choice`, `Quot.sound`
  only, from 4293 in 69. `check_prose`, `check_hedging`, `check_figures`,
  `check_tableS1`, `check_leaves`, `check_sorry`, `check_pdf_freshness` and
  `check_arxiv_freshness` pass; 143 Python tests pass. `main.tex`,
  `supplementary.tex`, `docs/primer.tex`, `CHANGELOG.md` and the ledger were
  updated in the same pass, the three tracked PDFs rebuilt with two passes each,
  and the assembled arXiv submission refreshed. No axiom, admitted proof,
  toolchain change or simulation sweep.

## Deviation from plan

`Phase8_FokkerPlanck.lean` was overwritten in the working tree by a heredoc
redirection during the pass, with no git history to restore from because the
file was untracked. It was rebuilt from its compiled `.olean`: declaration set,
signatures and doc-strings are the originals, read back from the artifact; the
proof terms are re-derived. The module is checked by the build like any other.
The recovery route and the rule that would have prevented it are recorded in
`tasks/lessons.md`.
