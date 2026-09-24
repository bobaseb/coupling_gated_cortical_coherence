# G16 manuscript outline

## Intent and acceptance checks

The article should make one argument: collective phase order is a candidate
coordination mechanism, while shared content and accurate reconstruction require
additional, independently testable conditions. The cortical field identification
is a physical hypothesis. The association of the resulting state with experience
is an interpretation that needs an independent experiential measure.

An edit is ready for the final audit when each main section answers a distinct
question, every headline states its assumptions and limit, and the article's
prose is roughly 8,000--9,000 words under one recorded counting method. The
initial abstract target was 200--250 words. The first 203-word draft ran onto
page two under the article's title layout, so the current 155-word abstract is
a deliberate exception that fits on page one. These are editorial targets, not
journal requirements. G15 must settle the finite-ramp wording before the final
abstract and conclusion are fixed.

## Article structure and prose budget

| Destination | Purpose | Words |
| --- | --- | ---: |
| Abstract | Central distinction, conditional result, empirical test and limitation | 155 |
| Introduction | Cup example, question, contributions and evidential status | 700 |
| Coherence and physical coupling | Inherited stationary threshold, winding counterexample, installed-energy necessity | 1,050 |
| Compatibility | Shared decoders, patch limit, overlap and global gluing; state what each measurement must resolve | 1,450 |
| Reconstruction | Fixed-point control, family separation, causal reach and fidelity | 1,100 |
| Observables and controls | Stationary identifiability, finite onset, winding, adaptation and decoder controls; distinguish numerical results from theorem | 1,150 |
| Cortical hypothesis and test | Physical calibration, spatial comparator, endpoints, held-out score and failure conditions | 1,200 |
| Resource and composition limits | Current cost, ordered equilibrium, conditional heat ledger and eight connecting premises; explain why each matters | 650 |
| Discussion | What the results establish, interpretive identification, empirical gaps | 550 |
| **Total** | | **8,005** |

The current standalone landscape inventory should dissolve into the sections
where its counterexamples do work. The abstract, introduction and discussion
should each state the argument once at their own level, without repeating the
five-result list. Figures and the notation and claim tables sit outside the
prose budget.

The main-text pass now measures 8,141 words against 12,576 words at
`7d8c5ba21e3b25b8f9459cc67aff9b8da6f55752` (35.3% less). The count begins at
`\begin{abstract}`, stops before `\section*{Notation}`, omits complete `figure`
and `longtable` environments, and runs the remaining TeX through `detex -n`
then `wc -w`. It includes headings and equation text, so it is a stable working
measure rather than a publisher's prose count. The 8,005-word allocation remains
a planning budget; the measured article is within its 8,000--9,000-word target.

## Migration map

| Current material | Primary destination | Article treatment |
| --- | --- | --- |
| Stationary threshold and phase dynamics | Coherence; full derivation in supplement | State the ideal model and threshold with its assumptions. |
| Uniform patch estimate and alternative bounds | Compatibility; derivations already in supplement | State the patch limit and what extra cover or graph data each alternative needs. |
| Winding and resultant controls | Coherence counterexample, then observables | Explain why order alone cannot identify a state; place numerical details with the observable. |
| Gluing, approximation and decoder requirements | Compatibility | Pair each mathematical implication with an independently identified shared quantity. |
| Fixed point, family capacity and causal reach | Reconstruction | Use the constant-map control before the positive construction. |
| Linear-rank bound, softmax control and finite token information | Existing supplement sections on reconstruction and digital candidates | Keep a short pointer in the article only if needed to explain a measurement; preserve the linear-rank premise and finite-output channel scope. |
| Passive/active feedback, learning and repeated supply | Existing supplement thermodynamics and learning sections | Keep the eight premises and one short explanation of why a heat budget does not supply compatibility. |
| Installed actuator energy and cortical estimates | Coherence; detailed calculation in supplement | State necessity, unidentified mode prices and supply-to-occupancy calibration. |
| Probability current and density-change bound | Resource and composition limits; proof in supplement | State ordered zero-current equilibrium and that an actuator cost needs a separate physical law. |
| EEG calibration and synthetic decoders | Observables | Preserve their calibration/control status; no evidence claim for nonlinear Bessel behaviour or cortical content. |
| Field/connectivity onset comparator | Cortical hypothesis and test; detailed protocol in supplement | Treat held-out advantage as support for a specified predictor, not field causation or an experiential endpoint. |

Formal verification assures the stated mathematical implications. Joint
witnesses show that their hypotheses can hold together in a specified model;
they do not establish cortical realization. The biological question is whether
measured coupling, decoders and reconstruction meet those hypotheses in cortex.

## Main-text compression audit

| Material shortened in the article | Where its substantive content now lives |
| --- | --- |
| Five-result landscape inventory and repeated introduction/discussion lists | The brief limits section introduces the problem; each counterexample and condition appears at its point of use in the article, with theorem scope in Supplemental Material Table S1. Repeated narration was removed rather than copied. |
| Winding stability, amplitude band, defect and phase-lift derivations | Article's winding subsection retains the result and measurement limit; Supplemental Material's spatial-wave, amplitude and phase-lift sections retain the technical results and controls. |
| Machine capacity, support and philosophical comparisons | Article retains the linear-rank premise, token ceiling and test obligations; Supplemental Material carries the proofs, capacity and hardware comparisons, and relationship to other theories. |
| Feedback, learning and supply detail | Article retains the named resource premises and scope; Supplemental Material's feedback, learning and repeated-operation sections retain their distinct models. |
| Hand/viewpoint perturbation from the earlier discussion | Added to Supplemental Material's interpretive-scope section as a conditional test of the specified reconstruction readout. |

The article and supplement do not divide by age of material: the article carries
the argument and measurements, while the supplement carries methods, proofs and
long controls. Removed repetition was not moved verbatim.
