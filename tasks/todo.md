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

## M — Publication alignment, closed

**Eight sentences in the publication were waiting on measurements this repository
already had.** N7–N9 and N12–N13 each deferred their publication alignment, for
the same stated reason and on the same terms: a macro is required for every
numeral that *reaches* the publication, and none of theirs does yet, so
generating macros nobody cites would put dead entries into a generated file and
into its drift test. That reasoning is sound for each pass on its own and it
does not survive being repeated — two deferrals with nothing tracking them is
how a numeral that contradicts a published sentence stays published. This
section is what tracks them. Unlike the P-items below, nothing here is blocked
on anyone else.

The sentences, with the item that bears on each:

| From | Sentence |
| :--- | :--- |
| N7 | `supplementary.tex` on what a discriminating awakening experiment must span — the estimator as published cannot discriminate at the 100 sites the protocol permits at *any* concentration, and the first fix is a bin count of 24 or fewer |
| N7 | the same section's independent calibration, called optimistic for EEG — the requirement at the observed concentration rises from 3,000 to 31,000 sites between independence and full clustering |
| N8 | `K_c = 2D` is stated for a scalar coupling with no aggregation rule; N8 supplies the row-sum rule, the ±0.08 error bound over the declared decay range, and the measurement that frequency heterogeneity rather than spatial structure is what the identical-frequency restriction holds back |
| N9 | the compatibility clause is recorded as having no observable; N9 supplies one, its two required diagnostics, and the limit that no phase-derived statistic substitutes for it |
| N12 | `main.tex:182` motivates coupling that "evolves more slowly than phase dynamics" and quantifies nothing; N12 supplies the required time-scale ratio and the reading of the cited geometry against it |
| N12 | `supplementary.tex` reports `ΔK ∝ v^0.443` as "near the predicted exponent 1/2 at this resolution"; N12 supplies the deterministic threshold limit of the same measurement, `0.447` over four speeds and `0.418` over three |
| N12 | the recovery section reads a crossing of `K_c` as an onset; N12 shows the quasi-static residual on a leg symmetric about `K_c` is rate-independent, so branch tracking is unattainable exactly where that argument uses it |
| N13 | nothing says which statistic of a varying coupling `K_c` is read against; N13 supplies the mean in the fast limit, the quasi-static average in the slow non-crossing limit, and neither for a slow crossing drive |

**Acceptance rule.** Every numeral that reaches either publication file is a
generated macro read from a saved summary (AGENTS.md §3) — no hand-typed
numerals, and regenerating must not rerun a sweep. Withdrawn claims go to
`CHANGELOG.md`, which is the pass that earns the entry the four preceding passes
deliberately did not write. The three tracked PDFs are rebuilt in the same
commit as their sources (AGENTS.md §6), and `prepare_arxiv.sh` is re-run or
`arxiv_submit/` removed (AGENTS.md §7).

- [x] **M1 — Generate the macros.** Extend `simulations/simulation_tex.py` to
      read `collapse_design`, `spatial_reduction`, `compatibility_estimator`,
      `quasistatic_error` and `fluctuating_coupling` summaries, emit a macro for
      each numeral the rewritten sentences will cite, and extend
      `test_simulation_tex.py`'s drift test to cover them. Emit a macro only for
      a numeral a sentence actually uses: an unused macro is the dead entry this
      section exists to avoid creating.
- [x] **M2 — Rewrite the eight sentences**, in present tense and with no
      drafting-history narration (AGENTS.md §5, and `check_prose.py` enforces
      it). Three of them — the awakening-experiment span, the `v^0.443` reading
      and the onset crossing — are claims that become false or incomplete, so
      each needs its replacement written rather than deleted.
- [x] **M3 — Close the artifacts.** Rebuild `main.pdf`, `supplementary.pdf` and
      `docs/primer.pdf`, check the primer's explanation still matches what the
      manuscript now says, refresh or remove the built arXiv submission, and
      write the `CHANGELOG.md` entry naming the claims withdrawn.

**Closing record.** `simulation_tex.py` gained `_design_macros`,
`_reduction_macros`, `_compatibility_macros`, `_quasistatic_macros` and
`_fluctuating_macros`, reading the five summaries named in M1; the drift test
gained per-group assertions and a check that those five groups emit no macro the
publication does not cite. The eight sentences are rewritten in place, three of
them withdrawing a claim, and `CHANGELOG.md` carries those three. `main.pdf`,
`supplementary.pdf` and `docs/primer.pdf` are rebuilt; the primer's two
compatibility statements and its aggregation sentence are updated to match.

**Still open from the ledger `0505cac` truncated:** the R research programme
(R1-R12) is restored in `tasks/research_programme.md`. The P submission-readiness
items and the pass records remain in `dde1a36:tasks/todo.md`.

## W — The winding state, from measurement to theorem

**The sweep in `travelling_wave.py` establishes by simulation what the
development could state as theorems.** A field winding across the sheet has
global order zero while every patch of it stays locked, and the two sweeps place
the boundary that separates surviving windings from unwinding ones at
\waveBoundary~mm at identical frequencies and \waveSpreadBoundary~mm under the
spatial control's quenched spread — both inside the 0.1--0.3~mm band. The
publication says this in prose and cites the saved summaries. Nothing in Lean
says any of it.

**Why no refactor is owed.** The convergence results are not wrong here and do
not need relaxing. `velocity_tendsto_zero` assumes only `omega = 0` and holds of
a twist trivially, its velocity being zero throughout.
`kuramoto_tendsto_global_minimum` additionally requires the quarter-turn initial
spread `h_init : |theta 0 i - theta 0 j| <= pi/2`, which a twist spanning the
circle violates, so that theorem is silent on this regime by construction. The
gap is that nothing states what happens instead, not that anything overreaches.

**Integration cost to budget.** `check_leaves.py` fails a phase module whose
theorems nothing outside it consumes, so a new `Phase4_TwistedStates.lean` is a
leaf on arrival. W1--W3 belong inside `Phase4_RotatingFrame` or
`Phase4_KuramotoDynamics`, beside the results they qualify and inheriting their
consumers.

- [x] **W1 — The order parameter vanishes on a twist.** For `theta k = 2*pi*q*k/n`
      on `ZMod n`, prove `order_parameter_r_sq theta = 0` when `n` does not
      divide `q`, through the root-of-unity sum mathlib already carries
      (`IsPrimitiveRoot.geom_sum_eq_zero` or its neighbours). Cheap, and on its
      own it makes "the observable cannot see winding" a theorem.
- [x] **W2 — Patch order dominates global order.** Define a patch resultant over
      a uniform cover and prove it is never below the global resultant, from
      `|mean| <= mean |.|` over `Complex`. This is the exact content of the
      observable `travelling_wave.local_order` computes, which currently rests
      on prose and a property test. With W1 it gives a configuration whose patch
      order is one and whose global order is zero, with no dynamics needed.
- [x] **W3 — A twist is a stationary state.** Needs structure the development
      does not have: `KuramotoSystem.A` is a general `V -> V -> R`, so this
      wants a circulant coupling on `ZMod n` with `f (-d) = f d`. The drift then
      cancels by pairing `d` with `-d`. Medium rather than cheap, and the
      modelling addition is the real cost, not the proof. With W1 it yields the
      prize: two stationary states of one system with `r = 1` and `r = 0`, so
      that `K` does not determine `r` becomes a theorem.

**Out of scope, and worth recording as such.** Relaxing `omega = 0` to
heterogeneous frequencies costs the gradient-flow structure the Lojasiewicz
argument rests on; "where it stops" is then open, and no cheap version exists.

- [x] **W4 — Say "winding", not "travelling".** At identical frequencies with a
      symmetric kernel a twist has zero drift: it is a standing phase gradient,
      and the vanishing resultant follows from the winding rather than from any
      motion. The supplement's sentence on what the threshold's one number
      cannot separate says "travelling wave" where the demonstrated object is a
      winding field, which is the more general claim. Tighten that sentence; the
      module filename stays, being wired into `tach.toml`, `setup.cfg`, the
      figure paths and the supplement's `\includegraphics`.

**Closing record.** All four are done, in `Phase4_KuramotoDynamics.lean` §6 —
inside an already-consumed module, so no leaf arrives. `winding` and
`windingPhasor` carry the configuration; `winding_add` is the lemma everything
rests on, since `ZMod.val` is a residue rather than a homomorphism to `ℝ` and
the defect is exactly `2π`-periodic. W1 is `order_parameter_r_sq_winding`, proved
from shift invariance of the site sum rather than from a root-of-unity sum: the
shift `k ↦ k + 1` multiplies the sum by a phasor other than one whenever `n ∤ q`,
so the sum is zero. W2 is `patch_resultant`, `mean_patch_order` and
`IsUniformCover`, with `mean_patch_resultant` proving the patch resultants
average back to the global one — overlap allowed, a partition being `m = 1` and
`travelling_wave.local_order`'s sliding box being `m = c` — and
`norm_order_parameter_le_mean_patch_order` the domination. W3 is
`circulantSystem`, `circulant_drift_winding` and `winding_is_kuramoto_trajectory`.
`coupling_does_not_determine_order` is the prize: one system, two stationary
states, `r² = 1` and `r² = 0`.

Two results beyond the ledger, both cheap once the above is in place.
`le_norm_patch_resultant` bounds a patch resultant below by the concentration of
its phases, stated through `cos (θ i - a)` rather than `|θ i - a|` because the
bound has to survive the `2π` wrap. Against it,
`cos_le_mean_patch_order_winding` puts the winding's nearest-neighbour patch
order at or above `cos (2πq/n)`, which approaches one as the same winding is
spread over more sites. Without it the only witness available is the singleton
cover, where patch order is one for every configuration whatever — true, and
degenerate.

W4 tightened the sentence in both publication files rather than only the
supplement: `main.tex` carried the same "travelling wave" where a winding was
demonstrated. `CHANGELOG.md` carries the withdrawal, the supplement's
stationarity paragraph now cites the five theorem names, `main.tex` cites
`winding_is_kuramoto_trajectory`, and `docs/primer.tex` §"balanced
configurations can be equilibria too" cites it as well. All three PDFs and the
arXiv submission are rebuilt.

## X — An amplitude field, and what it would buy

**The diagnosis stands and the price does not.** A standing wave needs amplitude
nodes; the phase field carries none, since every oscillator sits on the unit
circle, so `u = cos(kx)cos(ωt)` has no representation in what the framework
integrates. Amplitude enters only in the measurement layer, where
`Phase5_PhaseLifts` reads singularities off the analytic signal `z = A e^{iφ}`,
and nothing connects the two layers. What is wrong is the estimate that closing
this is a research decision: the **real** Stuart--Landau layer keeps the
gradient-flow structure the whole convergence architecture rests on, so it is an
extension of the development rather than a replacement of it.

**The model.** State `z : V → ℂ` instead of `theta : V → ℝ`, in the rotating
frame `Phase4_RotatingFrame` already supplies, with

    ż i = (μ - |z i|²) * z i + ∑ j, A i j * (z j - z i).

This is a gradient flow of

    F z = ∑ i, (|z i|⁴/4 - μ * |z i|²/2) + (1/4) * ∑ i, ∑ j, A i j * |z i - z j|²

against the real inner product on `ℂ^V ≅ ℝ^(2V)`, so `dV_dt_le_zero` and the
Łojasiewicz argument transfer rather than being redone. Four results follow, each
cheap given §6, and each checked numerically at `n = 12` before being proposed:

- [x] **X1 — The phase equation of the amplitude model is Kuramoto.** Where `z i ≠ 0`,
  writing `z = r e^{iθ}` gives `θ̇ i = ∑ j, A i j * (r j / r i) * sin (θ j - θ i)`
  exactly, which is `is_kuramoto_trajectory` as soon as the amplitudes agree.
  This is the bridge, and it is what makes the two layers one object: the phase
  model is the amplitude model's phase equation with the amplitude ratios set to
  one. It also makes the loop winding of `Phase5_PhaseLifts` computable from a
  dynamical state rather than postulated from data.
- [x] **X2 — Windings are exact, and they carry an amplitude.** On the ring with the
  circulant kernel of §6, `z k = a * ξ^k` with `ξ = exp (2πiq/n)` is stationary
  exactly when `a² = μ + λ q`, where `λ q = ∑ d, f d * (cos (2πqd/n) - 1)` is
  real by the evenness of `f`. The proof is the §6 cancellation with the cubic
  term absorbed into the amplitude.
- [x] **X3 — An existence band the phase model cannot state.** That winding exists
  **iff** `μ + λ q > 0`. The phase model admits every winding number at every
  coupling; the amplitude model admits a band, and a winding outside it has
  nowhere to sit. This is a prediction rather than a restatement, and it is the
  first thing in this development that the extra degree of freedom buys.
- [x] **X4 — A standing wave.** The lab-frame reading of a stationary amplitude
  state is `u i t = Re (z i * exp (iΩt)) = |z i| * cos (Ωt + arg (z i))`. At
  `q = n/2` with `n` even, `ξ = -1`, so `z k = a * (-1)^k` is real and exact and
  `u k t = a * (-1)^k * cos (Ωt)` — `cos(kx)cos(ωt)` at `k = π`, in the
  framework's own integrated dynamics. The phase model has no such object,
  because there the observable is the phase and every site has unit modulus.

- [x] **X5 — The scope statement, written before the layer and not after.** A scope
  statement drafted once the results are in is shaped by the results; this one is
  specified first, and X1--X4 are answerable to it. Six limits, each with what it
  would take to remove:

  1. **A ring has no spiral.** What \cite{townsend2015} and \cite{xu2023}
     measure is a two-dimensional defect: a point of the sheet around which phase
     advances by a whole turn and at which amplitude vanishes. `ZMod n` has no
     interior, so X2--X4 reach a winding and not a spiral, and the exact
     one-dimensional solutions never have the defining feature — `|z k| = a` at
     every site, so no site is a zero. The extension to `ZMod n × ZMod n` is
     where the payoff sits and it is not a corollary. Until it is done the layer
     speaks about `Phase5_PhaseLifts`'s electrode loop and not about what the
     loop encircles.
  2. **Relaxational dynamics has no propagation speed.** Real coefficients mean
     no nonlinear dispersion, and §6 proves the drift is exactly zero, so nothing
     here travels. A cortical wave measurement always reports a speed; this model
     predicts none. Supplying one needs heterogeneous frequencies or complex
     coefficients, and both cost the gradient structure that makes the layer
     cheap. The layer buys standing structure and is silent on the one number the
     measurement leads with.
  3. **`|z|` is a normal-form radius; `A` is a signal envelope.**
     `Phase5_PhaseLifts` reads winding off an analytic signal `z = A e^{iφ}`
     derived from a recording. `|z|` in the layer is a distance from an unstable
     fixed point in a Hopf normal form. Identifying the two is a physical
     assumption of the same kind as the Landauer identification that
     `Phase3_LandauerBridge` keeps as a named hypothesis rather than deriving, and
     it should be a named hypothesis here too rather than a definition.
  4. **Stuart--Landau is local in parameter space, and nothing here places cortex
     in it.** The normal form is valid near a supercritical Hopf bifurcation,
     where the resting state has just lost stability. Much cortical wave
     phenomenology is excitable-medium behaviour instead — a stable rest state and
     a threshold that gets crossed — and the two produce similar-looking maps from
     different mechanisms. The layer models one of them and says nothing about
     which one applies.
  5. **`μ` has no cortical estimate in this repository.** X3's band
     `μ + λ q > 0` is structural: the distance from the bifurcation is not
     measured anywhere here, so the band predicts no numeral and discriminates no
     experiment. That belongs in the same sentence as the prediction, not in a
     later paragraph.
  6. **Nothing connects a winding sector to content.** Table S1's row stands
     unchanged. Making a defect computable from a dynamical state rather than
     postulated from data is not making it mean anything, and the layer's
     contribution to the content question is exactly zero.

  **Where it goes.** The publication's scope voice, which `check_hedging` counts,
  and the new module's docstring — the two destinations `AGENTS.md` §5 names for
  this kind of content. Limits 1, 2 and 4 are the ones a reader of the
  neuroscience will test the layer against first, so they are the ones that go in
  the article rather than only in the supplement.

**What does not come for free, and is not being proposed.**

- A cosine profile is *not* a stationary state: the cubic term does not preserve
  a single Fourier mode. Only the circularly polarised modes are exact, and the
  only real one among them is the alternating mode of X4. A standing wave with an
  interior amplitude node is a fixed point of a nonlinear system with no closed
  form, reached by bifurcation from `μ = -λ q`; that argument is the real cost
  here, and X1--X4 do not need it.
- The genuine complex Ginzburg--Landau equation — complex coefficients on the
  cubic and on the coupling — is **not** the thing to take. It is not a gradient
  flow, and every convergence result in the development rests on the fact that
  this one is. The real case is the one that inherits the architecture.
- Spirals stay out of reach on the ring, which is the first item of X5 and is
  recorded there rather than here, because it is a limit on what the layer
  measures and not on what it costs to build.

**Integration cost to budget.** X1 states a property of `is_kuramoto_trajectory`,
so it belongs in `Phase4_KuramotoDynamics` beside §6 and inherits its consumers.
X2--X4 in a separate `Phase4_AmplitudeField.lean` would arrive as a leaf unless
X1 is moved there and something outside consumes it; the cheap resolution is to
keep the whole layer in `Phase4_KuramotoDynamics`, which is already long, and the
honest alternative is a recorded `ALLOWED_LEAVES` entry. That is a decision, not
a task.

**Closing record.** All five are done, in `Phase4_KuramotoDynamics.lean` §7 —
the decision the budget note left open is taken the cheap way, the whole layer
sitting in the already-consumed module, so no leaf arrives and
`ALLOWED_LEAVES` gains nothing. `amplitudeField` and `is_amplitude_trajectory`
carry the model, stated componentwise exactly as `is_kuramoto_trajectory` is.

X1 is `deriv_phase_of_amplitude_trajectory`, and it is an identity rather than a
limit: the phase velocity is `Im (ż i * conj (z i)) / r i ²`, which
`im_amplitudeField_mul_conj` evaluates to the Kuramoto drift weighted by the
amplitude ratios. The cubic term drops out of it because it is a real multiple
of `z i`, which is why no slow-amplitude assumption is needed anywhere.
`amplitude_phase_is_kuramoto` is the bridge at equal amplitudes.

X2 is `windingState_is_amplitude_trajectory_iff`, resting on
`amplitudeField_windingState`: the field acts on `a * ξ^k` as the single real
scalar `μ - a² + windingLambda n q f`, the imaginary part of the kernel sum
cancelling by the same odd-against-even pairing as `circulant_drift_winding`.
X3 is `exists_windingState_iff`, and `phase_model_admits_winding_outside_band`
is the contrast that makes it a prediction: outside the band the phase model
still carries the winding, because `winding_is_kuramoto_trajectory` constrains
neither `q` nor `f`. X4 is `standing_wave_of_amplitude_band`, with
`winding_antipodal` and `windingState_antipodal` supplying the half turn and
`labField` the lab-frame reading.

All four were checked numerically at `n = 12` against a random even kernel
before being proposed, and the check is reproduced by the theorems rather than
committed: `lake build` runs the audit, which reports 5319 declarations resting
only on the permitted three.

X5's six limits are in §7's docstring in full; the supplement's new
`sec:supp-amplitude` states all six and the article states limits 1, 2 and 4,
each in the publication's scope voice. Limit 5 is written into the same sentence
as the band, not a later paragraph, so the prediction never stands unqualified.
The primer's phase-singularity scope gains the layer as a third limit — a ring
winding has constant modulus, so it is still not a spiral.

**No `CHANGELOG.md` entry, deliberately.** That file lists claims that were made
and are no longer made; nothing in either publication file said anything about
amplitude before this pass, so the layer withdraws nothing. The entry would be
an announcement of new work, which is what the file's own opening declines to
carry. `main.pdf`, `supplementary.pdf`, `docs/primer.pdf`, the proof companion
and the arXiv submission are all rebuilt.

## Y — What the winding rows say they do not reach

**Table S1's two new rows end on three scope limitations, and two of them are
reachable with the machinery already in the file.** The rows state that
stationarity of a character state needs no basin hypothesis but selects no
limit; that the existence band `mu + lambda > 0` is one of existence and not
stability; and that no theorem connects a winding sector to content. The second
is the cheapest result in this section and is what the sweep in
`travelling_wave.py` actually measures. Half of the third is nearly free and
improves a bound the article already complains about. The first is mostly out of
reach, and two negative corollaries are all that is honestly available.

**Why the stability half is cheap.** Linearising the phase model about a winding,
`theta i = W.psi i + u i`, gives

    d(u i)/dt = sum_d f d * sin (psi d + u (i+d) - u i)
              ~ sum_d f d * sin (psi d)                       -- vanishes
              + sum_d f d * cos (psi d) * (u (i+d) - u i)

The first sum is exactly `circulant_drift_char`. What is left is circulant with
kernel `g d = f d * cos (W.psi d)`, and `g` is even: `f` is even by hypothesis
and `cos . psi` is even from `chi_neg`. So `sum_kernel_chi` applies unchanged and
the spectrum is `charLambda W' g` ranging over the characters `W'` — the
definition already at `Phase4_KuramotoDynamics.lean:1399`, re-instantiated at a
twisted kernel. `charLambda`, `sum_kernel_chi` and `sum_eq_zero_of_odd` are all
generic in the kernel and require only evenness, so none of them is touched.

This is the mechanism the sweep measures. As the decay length grows the kernel
reaches separations at which the winding has advanced past a quarter turn,
`cos (psi d)` turns negative, `g d < 0`, and a mode crosses zero. It would make
the interpolated boundary `\waveBoundary` a computable quantity rather than a
measured one.

**Why the content half is nearly free.** `chord_le_of_coherence` and
`compatible_of_shared_coherence` are generic in the site type `V`. Instantiated
at the subtype of a patch they give the same bounds with `card P` for `card V`
and the patch's own resultant for the global one; the only bridge needed is
`patch_resultant theta P` against `order_parameter_complex` on that subtype,
which is `Finset.sum_coe_sort` and `Fintype.card_coe`.

**Integration cost to budget.** All of Y1--Y4 belong in the modules that already
carry what they qualify — Y1--Y3 in `Phase4_KuramotoDynamics` beside §6 and §7,
and Y4 split across both, its patch bridge in `Phase4_KuramotoDynamics` where
`patch_resultant` and `chord_le_of_coherence` are and its compatibility
instantiation in `Phase5_ContentDynamics` — so nothing arrives as a leaf and `ALLOWED_LEAVES` gains nothing. Anything that reaches
`main.tex` needs a Table S1 row in the same commit, which
`check_table_coverage.py` now enforces (AGENTS.md §9), and any `.lean` edit needs
`proof_companion/run.sh extract` then `pdf` before the commit hooks pass.

- [x] **Y1 — The twisted kernel.** Define
      `twistedKernel W f := fun d => f d * Real.cos (W.psi d)` and prove it even
      from `chi_neg`. Cheap, and on its own it says nothing; it is the object
      Y2 is stated about.
- [x] **Y2 — The linear criterion at a winding.** Prove the Jacobian of the
      phase model at `charState` is circulant with kernel `twistedKernel W f`,
      so its spectrum is `charLambda W' (twistedKernel W f)` over characters
      `W'`. Then the two halves: if `0 <= f d` and `|W.psi d| <= pi/2` on the
      kernel's support, every eigenvalue is at most zero, termwise from
      `(chi' d).re <= 1`; and a `W'` with `charLambda W' (twistedKernel W f) > 0`
      is a growing mode. This is the phase-layer analogue of
      `incoherent_mode_rate` and `incoherent_instability_iff`, which is a shape
      this development has already carried once.
- [x] **Y3 — A winding is not a minimum.** A nontrivial winding has `r^2 = 0`
      where a global minimum has `r^2 = 1`, so it is not one:
      `potential_min_iff_phase_locked`, `phase_locked_implies_r_sq_eq_one` and
      `order_parameter_r_sq_char` are all proved and this is close to an
      assembly. It upgrades "the convergence hypothesis excludes this state" to
      "it must, because the conclusion is false of it", which is the refutation
      shape `Axioms.lean` §5 prefers. With Y2 it extends to "not a local
      minimum either" wherever an eigenvalue is positive.
- [x] **Y4 — Content agreement on a patch.** Instantiate
      `chord_le_of_coherence` and `compatible_of_shared_coherence` at the
      subtype of a patch, with the bridge lemma above. Two payoffs, and the
      second is independent of windings: on a winding the global bound is
      `sqrt 2 * N` and vacuous while the patch bound stays finite, because
      `cos_le_mean_patch_order_char` holds patch order near one — which is the
      winding-to-content connection Table S1 records as absent; and a bound
      carrying `card P` rather than `card V` answers the article's own remark
      that the factor `N` makes the estimate weak in large populations.

**Closing record.** All four are done, in `Phase4_KuramotoDynamics.lean` §9 and
§10 — both inside the already-consumed module, so no leaf arrives and
`ALLOWED_LEAVES` gains nothing. `lake build` runs the audit, which reports 5412
declarations resting only on the permitted three.

Y1 is `twistedKernel` with `twistedKernel_even` and `twistedKernel_nonneg`. The
evenness rests on a new `WindingData.cos_psi_neg`, the companion of
`sin_psi_neg`: conjugation fixes the real part, so `cos ∘ psi` is even where
`sin ∘ psi` is odd, and that one fact is what lets every §6 cancellation run
again at the twisted kernel with nothing else touched.

Y2 is `hasDerivAt_charJacobian`, `charJacobian_chi_re`, `charLambda_nonpos`,
`charJacobian_stable_of_quarter_turn` and `charJacobian_growing_mode`. The
Jacobian is stated as the derivative of `kuramotoField` along the line
`W.psi + s • u` at `s = 0`, which is what a Jacobian is and needs no bundling of
the state space. The eigenvector is `Re ∘ chi'` rather than `chi'` itself, so the
statement stays inside the real field the phase model lives in; the imaginary
half cancels through `sum_kernel_chi_im`, extracted from `sum_kernel_chi` for
the purpose and now used by both. The growing mode is evaluated at the identity
site, where `chi' 0 = 1` makes it nonzero for every character — which is why no
hypothesis is needed to rule out a mode that vanishes where it is read.

Y3 is `char_not_potential_min` for the global half and
`char_not_local_min_of_charLambda_pos` for the local one, the second the
extension the ledger left as a remark. The local half needed the second
variation, so §9 carries `charLinePotential`, `charLineDeriv`, `charLineSecond`
and their two derivative lemmas: `charLineDeriv_zero` proves the first variation
vanishes in *every* direction, by an antisymmetry that reduces both halves of
the split to `circulant_drift_char`, and `charLineSecond_zero` identifies the
second variation with minus the Jacobian's quadratic form through
`sum_sq_diff_eq`. Negative curvature plus a vanishing first derivative gives
strict decrease to the right of zero, and `IsLocalMin.comp_continuous` lifts the
line statement to the state space.

Y4 is `order_parameter_complex_patch` — the bridge, and `Finset.sum_coe_sort`
with `Fintype.card_coe` are the whole of it — then `chord_le_of_patch_coherence`
in `Phase4_KuramotoDynamics` and `compatible_of_patch_coherence` in
`Phase5_ContentDynamics`, each a literal instantiation of the global statement at
the subtype of a patch rather than a second proof of it. `chord_le_of_char_patch`
is the winding payoff at `2√2|sin ψ_g|`, and `chord_bound_char_global` with
`chord_le_two` make "the global bound is vacuous there" a theorem rather than a
remark.

**Still not reached, and recorded where it matters.** Asymptotic stability
remains out of reach for the reason the ledger gives, and both publication files
and Table S1 say so in the same sentence as the criterion. The amplitude layer's
band is untouched: §9 linearises the *phase* model, and the amplitude field's
Jacobian at a character state mixes the amplitude and phase directions, so "the
band is one of existence and not of stability" stands as the amplitude row
states it.

**No `CHANGELOG.md` entry, deliberately**, on the reading the X pass set down:
that file lists claims that were made and are no longer made. Nothing here
denies anything either publication file asserted. The scope sentences that
tighten — which state a trajectory reaches, what the factor `N` costs, what a
winding sector connects to — tighten by gaining a theorem beside them, and each
keeps the part of itself that is still true.

**Where it landed in the publication.** `main.tex` §"A winding state leaves the
order parameter ambiguous" gains the criterion and the minimality paragraphs and
one paragraph on what a vanishing resultant does not mean for content;
§"When coherence does constrain content" gains the patchwise reading of the
factor `N`. `supplementary.tex` §"Global sections and the unity of
consciousness" gains Eq. (chord-bound-patch), and §"What the order parameter
reports for a winding state" gains four paragraphs. Table S1's winding row
carries every new identifier the article names, as `check_table_coverage`
requires. `docs/primer.tex` gains the forced-hypothesis reading in its scope
note on the convergence theorem.

**Out of scope, and worth recording as such.** Two things this section does not
reach, both for stated reasons rather than for want of effort.

- **Asymptotic stability.** Y2 is an eigenvalue statement about the Jacobian, not
  convergence of trajectories. Upgrading it needs a local Lojasiewicz estimate
  around a critical point that is not a minimum, and the existing chain —
  `lojasiewicz_estimate`, `excess_decay`, `velocity_abs_le_exp`, `phase_tendsto`
  — is built around the global minimum through `potentialExcess`, the pairwise
  quarter turn and `couplingTotal_pos`. Rebuilding it locally is a pass of its
  own, not a corollary of Y2, and the publication must keep saying that the
  states which persist occupy a strictly narrower range than the band allows.
- **The converse direction of Y4.** That a nonzero winding *obstructs* global
  compatibility does not follow from anything here.
  `loopWinding_eq_zero_of_hasGlobalLift` is the topological obstruction, but
  `Phase5_PhaseLifts.lean` is combinatorial throughout — integers around a loop,
  with no connection to the Kuramoto dynamics or to the content sheaf. Joining
  them means identifying the content sheaf with the phase-lift sheaf, which is
  the modelling commitment the publication declines to make. That is not a
  formalization gap but the open problem, and the `Frustration as memory
  capacity` row is right to record it as one.

## Z — From conditional to falsifiable

**The eight edges are supplied, and the article says so.** §4.3 states that the
composition establishes that the premises are consistent and *not* that
coherence follows from installed energy or self-representation from coherence.
That is accurate, and it is also the ceiling: a chain that transmits nothing
carries no prediction. The one prediction the article does make — a square-root
recovery onset at the `K_c` crossing — is defeated by its own §5.2, where none of
the scanned rates meets the declared tracking tolerance. This section lists what
would change that, separated into what is reachable and what is not.

**The finding that reorders the list.** The delay scaling is already measured and
already filed as a limitation. `supplementary.tex` §"Finite-ramp numerical check"
reports `ΔK ∝ v^0.443` against the predicted `1/2`, with the deterministic
mean-field limit returning `0.447` over four speeds and `0.418` over three, so
the shortfall belongs to the delay estimator rather than to finite-`N` sampling
— which is the hard half of that argument, and it is done.
`figures/DYNAMIC_RAMP_REPORT.md` adds the scale conversion: at `D_phys = 1.5`
rad/s a 100–1000 s crossing is `v ∈ [6.7e-4, 6.7e-3]`, inside the tested range. A
scaling law with a predicted exponent, a diagnosed bias and a physiologically
relevant range is a prediction. It is currently presented as a control.

**Acceptance rule.** Z1's extended sweep writes a saved summary, and its numerals
reach either publication file only as generated macros read from that summary
(AGENTS.md §3); regenerating the macros must not rerun the sweep. Z2 is prose
plus a script under `simulations/`, on the pattern of `fermi_estimate_check.py`.
Any publication edit rebuilds the three tracked PDFs in the same commit (§6) and
refreshes or removes `arxiv_submit/` (§7).

- [x] **Z1 — Extend the ramp sweep, and state the scaling as a prediction.** The
      delay fit uses three speeds; the fastest leg is right-censored at
      `rampFastEscaped/rampReplicas` replicas and excluded. Extend to six or
      eight speeds spanning the converted range, put an interval on the
      exponent, and check whether the estimator shortfall is stable across the
      wider span. Then state the prediction in the form that needs no absolute
      calibration: **onset delay scales as the square root of the emergence
      rate**. That requires only that `K̇` be monotonic in the drug offset rate,
      not its value, nor `κ`, nor `γ`, so it is a within-subject design an
      anaesthesia group can run by varying offset rate alone. The §5.2 protocol
      hazard — a fixed `r ≥ 0.2` criterion meeting a size-dependent fluctuation
      floor — is what such a design must avoid, and the article already says so.
      `D` itself is nearer than the EEG work suggests: §5.1 notes quadratic
      variation accumulates at rate `2D`, which is estimable from resolved phase
      traces and is a different quantity from the concentration `a` that the
      propofol analysis could not range over.

- [x] **Z2 — Read the installed-energy bound against a cortical energy budget.**
      The installed-energy row is the only conditional theorem in Table 1 and it
      carries no number. `fermi_params.tex` computes the *other* conversion
      already — and **none of it reaches either publication file**, which is the
      first thing this item has to fix. `fermi_estimate_check.py` emits 29 macros;
      exactly three are cited anywhere in `main.tex`, `supplementary.tex` or
      `docs/primer.tex` (`fermiFieldMin`, `fermiFieldMax`, `fermiShift`, all in the
      field-amplitude and spike-timing sentence of Table S1's E56 row). The whole
      coupling estimate — `fermiN`, `fermiK`, `fermiKGamma`, `fermiKGammaCons`,
      `fermiThreshold` and every band-specific `E` and `f` — is generated and
      unread. Recomputed: `N ≈ 1675` in a 0.2 mm sphere at `ρ = 5e4 mm^-3`, giving
      `K/γ ≈ 8.0` at theta (3.0 mV/mm, 6 Hz), `≈ 8.9` at gamma and `≈ 5.7` on the
      conservative parameter set, against the noiseless Lorentzian `K_c/γ = 2`.
      That estimate addresses the Lorentzian-heterogeneity threshold and **not**
      `K_c = 2D`; the fermi file says so in its own header and the distinction
      must survive into anything written here. Whether the estimate belongs in
      the publication at all is the decision this item forces: a cortical
      coupling a few times over its threshold is either the article's most
      concrete physical claim or a calculation too loose to print, and it is
      currently neither. Missing is the energy side:
      whether the metabolic cost of maintaining the currents that generate those
      fields clears `2D/κ` for any defensible `κ`. Attwell & Laughlin (2001) and
      Harris, Jolivet & Attwell (2012) give the budget. Expect it to clear by
      orders of magnitude and to discriminate nothing for cortex — worth one
      paragraph rather than none, because it says what the installed-energy
      result is *for*: it bites on energy-limited substrates, which makes it a
      sharper instrument in §6.3 than in §6.2.

- [x] **Z3 — Characterize when restriction resonance fails.** The reachable half
      of the contraction question, and the one that fits what §5 already does.
      The ingredients are present: the constant-readout counterexample, the
      code-separation criterion of §3.2, and the causal-past obstruction of §3.3.
      A theorem naming conditions under which restriction resonance *fails* would
      constrain E89 from below in the way the winding results constrain the
      resultant. A pass of its own, not a corollary of Z1 or Z2.

- [x] **Z4 — Two defects in the Fermi macros, found while scoping Z2.**
      `\fermiKGammaCons` hardcodes the shift `0.4` while `\fermiConsShift = 0.3`
      is defined beside it and used nowhere, so the macro named for the
      conservative parameter set is not conservative in that parameter: it
      returns `5.7` where the declared conservative shift gives `4.2`. Both
      clear the threshold of `2`, so nothing published is wrong — nothing
      published cites it. Second, 26 of the 29 fermi macros are uncited. The M
      pass added an unused-macro assertion to `test_simulation_tex.py`, but only
      over the five summary groups it introduced; `fermi_params.tex` has no such
      check, which is why this went unnoticed. Extend the assertion to cover it,
      then either cite the coupling estimate (Z2) or stop generating it.

**Pass record.**

- **Z3, done first.** `Resonates E ρ` names restriction resonance on bare maps
  in `Phase6_Reconstruction.lean`, and `isRestrictionResonance_iff_resonates`
  identifies the boundary's predicate with it. Failure has two criteria that
  evaluate neither map — a pair the encoder confuses and the reference separates
  (`not_resonates_of_confuses`), and the mirror image
  (`not_resonates_of_splits`) — and they generalize
  `constResonance_not_isRestrictionResonance` from a constructed boundary to a
  hypothesis about any boundary (`not_isRestrictionResonance_of_const_avatar`).
  The one that constrains E89 is
  `not_isRestrictionResonance_of_reconstructs`: accuracy on two relevant states
  the avatar region reads identically refutes resonance, so under resonance
  `restrictToAvatar` must be injective on any separated reconstructed family
  (`restrictToAvatar_injOn_of_isRestrictionResonance`). That is a demand on the
  region, fixed before any encoding is chosen. `Phase6_Locality.lean` adds the
  deadline form from the causal past. Witnessed both ways on the one-site
  avatar and on the delay line; supplement §"When restriction resonance fails"
  and one Table S1 row.

- **Z4, and the decision it forced.** The conservative-shift defect is gone with
  the macro: the whole coupling estimate is no longer emitted. `K` there is a
  neuron count times a time times a frequency, so it is a pure number, while a
  coupling in the stochastic model is an inverse time; the rate closing that gap
  is the persistence of a field-induced timing shift, which the supplement's
  own rate-calibration subsection shows the field measurement does not fix.
  Emitting `K/γ` would have published one choice of it silently. The calculator
  keeps computing and printing the estimate, and now prints `4.2` for the
  conservative bound because the script's own scenario always used
  `CONS_SHIFT`; only the TeX path had `0.4` hardcoded. `fermi_params.tex` is
  down to the three measured quantities the publication states.
  `test_generated_macros.py` now gates every generated macro file both ways —
  drift against its generator, and citation by the publication — with the
  citation match anchored so that `\fermiK` is not certified live by
  `\fermiKGamma`.

- **Z2.** `energy_budget_check.py` (theory layer, `energy_budget.tex`) reads the
  installed-energy bound against Attwell & Laughlin's grey-matter budget. It
  cannot evaluate the condition, because the conversion factor is declined;
  what it does is invert it, and report the factor the identification would have
  to deliver. The expectation that it "clears by orders of magnitude" holds for
  the *energy* and not for the condition: the decay sphere's installed energy is
  fourteen orders of magnitude above `kT` at body temperature, so the condition
  can fail for cortex only through the conversion factor. Supplement
  §"The bound against a cortical energy budget", and one sentence in §6.3 saying
  the same of a processor.

- **Z1.** The delay sweep runs eight speeds, `0.1` down to `1e-4` on a 1--2--5
  ladder, with three inside the converted window; the per-leg onset and collapse
  fits stay on the four decade-spaced legs, which is what their paragraphs can
  carry. `fit_power_law` returns a 95% Student-`t` interval on the slope and
  `split_span_exponents` fits the halves of the span apart, which is the check
  that the shortfall is the estimator's rather than a drift with rate. The
  prediction is stated in §5.2 in the form that needs no absolute calibration.

**Declined, with reasons**, so that neither returns as an open item.

- **Deriving `κ` from the mode hardware.** A mode is a priced rank-one
  contribution to the kernel. Cortical extracellular field generation has no
  canonical decomposition into priced modes — the field is the summed
  transmembrane current of everything present — so choosing the basis is
  choosing the answer. This is not a formalization gap but the absence of the
  physical object the formalism quantifies over. Z2 is the consistency check
  that remains available without it.
- **Deriving E89's contraction from dynamics.** Restriction resonance, that a
  sub-region's encoding recovers the whole state, is the substantive commitment
  of the reflexive construction rather than a lemma in front of it. The witnesses
  construct models where it holds; deriving it for a physical system is the
  framework's problem restated. Z3 is the half that is reachable.
