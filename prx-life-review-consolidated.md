# Referee Report — PRX Life (Consolidated)

**Manuscript:** "Coupling-gated cortical coherence: a conditional framework for unity and self-representation" (main.tex, ~14,300 words; supplementary.tex, ~33,400 words)

**Reviewers:** anthropic/claude-fable-5.1 + openai/gpt-astra-latest via OpenRouter

**Date:** 2026-09-22

---

## SUMMARY

The manuscript proposes three formal requirements for a distributed cortical state to constitute "one experienced situation": coherence (Kuramoto phase order), compatibility (sheaf-theoretic gluing of local descriptions), and self-representation (the glued state as the unique fixed point of a contracting reconstruction map). It connects these through eight named hypotheses, machine-checks the composition in Lean 4 with an audited axiom footprint, and adds a sequence of theoretical bounds, numerical controls, and one experimental prediction — onset delay scaling as v^{1/2} in anaesthesia emergence. The Lean formalization and the candour about the framework's own limitations are genuine strengths. However, the physical and biological content that is new, testable, and specific to the proposed mechanism is thin relative to the manuscript's length. The five "unconditional results" are largely elementary observations. The single prediction is generic to any supercritical bifurcation crossed at finite rate and does not discriminate the field hypothesis from alternatives. The installed-energy bound is internally inconsistent as evaluated. The EEG exercise agrees with a line through the origin. And the exposition is so hedged and self-referential that a PRX Life reader will struggle to extract a positive claim. The manuscript also needs to demonstrate a clearer path from abstract mathematics to empirically testable neurobiological phenomena.

**Recommendation: Major revision** — the revision required is a restructuring, not a patch. A lightly edited resubmission should not be accepted.

---

## MAJOR CONCERNS

1. **The prediction does not test the mechanism and is not yet a protocol.** Delay scaling as v^{1/2} for a slow passage through a supercritical bifurcation is the classic delayed-bifurcation result (Baer, Erneux & Rinzel 1989; Berglund & Gentz 2002). It holds for *any* control parameter crossing *any* pitchfork/Hopf threshold at finite rate, so a positive outcome is equally consistent with synaptic, thalamocortical or neuromodulatory coupling, and does not test the installed-energy or field-geometry content of the framework. Moreover, ΔK is not observable — only time is — and t₀ (the moment K crosses K_c) is unobserved. The paper does not specify how the rate of emergence would be manipulated within subject, how many subjects/rates give power to distinguish an exponent of 0.5 from 0.44 or from 0, or what the competing null exponent is. Without this, the "prediction" is not yet a protocol. Relevant literature on emergence hysteresis / "neural inertia" (Friedman et al. 2010; Hudson et al. PNAS 2014; Proekt & Hudson 2018) is directly on point and uncited. The Sec. 9.3 six-item list is a wish list, not a design.

2. **The installed-energy bound has no discriminating power and its cortical evaluation is internally inconsistent.** The paper states the bound "excludes no macroscopic candidate" and "binds through κ", with κ being "hardware data" that has no canonical cortical decomposition — so "choosing the basis would choose the answer." A necessary condition with one free parameter that absorbs all the physics is not a constraint. Furthermore, the cortical number U_inst = 1.0×10⁻⁶ J is obtained by multiplying metabolic signalling power (Attwell & Laughlin) by 1/D = 2 s — i.e. dissipated energy over an interval — while the same section insists installed energy "is not heat" and is stored energy in field modes. The quantity computed is not the quantity the theorem bounds. Either derive a stored field energy (e.g. from measured LFP amplitudes and tissue permittivity/conductivity) or drop the numerical evaluation.

3. **The five "unconditional results" overstate their novelty.** The results presented as the article's fixed points are: (a) same phase, different mass profiles → no gluing (a one-line counterexample); (b) winding states are stationary with r = 0 (known since Wiley, Strogatz & Girnyk 2006); (c) M states pairwise > 2ε apart need M distinct codes (pigeonhole); (d) an encoding that is a restriction cannot resolve states the region reads identically (tautological); (e) causal-cone locality in synchronous networks (standard). None is wrong, but presenting them as five results "any account reading unity off coherence has to meet" overstates their content. The relevant Kuramoto literature (Strogatz 2000; Acebrón et al. 2005; Ott & Antonsen 2008; Dörfler & Bullo 2014) is largely uncited.

4. **Statistical treatment of the delay exponent is insufficient.** The 95% interval [0.394, 0.494] is an OLS interval on a 6-point log-log fit of ensemble means, not an interval over seeds. The supplement admits this (supp:1208-1211). The exclusion of 1/2 is attributed to the escape criterion via a deterministic mean-field reference that returns 0.425 at r ≥ 0.2 and 0.490 at r ≥ 0.05 — but the stochastic ensemble was never rerun at the tightened criterion. A clean demonstration would use an ensemble at larger N (floor ~1/√N) with a bootstrap over replicas. As it stands, the headline prediction is supported by a fit whose point estimate contradicts it and whose interval is not the relevant one.

5. **Hypothesis E78 undermines the compatibility route as stated.** "Patches and oscillators carry one index, so one oscillator carries exactly one content patch" is acknowledged as "not an innocent one." Together with the vacuity of the uniform bound beyond 3 sites at the sheet's own patch order (wavePatchInformativeSites = 3) and the chained bound saturating at ~0.2 mm, the article spends ~2,000 words establishing that the coherence-to-content estimate is useless at the scale the unity claim concerns, then keeps it as a "non-standard ingredient." This should be compressed to a paragraph and its conclusion stated once.

6. **The thermodynamic chain (Sec. 6) and GPU/LLM section (Sec. 5) should be removed from the main text.** The former states its own regime is "two-bit systems with interaction energies of order k_BT", that "cortex is not in it," that the bound "is satisfied by any macroscopic candidate and excludes none of them," and that "no result of Section 3 passes through it." The latter rests on trivial counts (token-vocabulary cardinality; the causal mask). Sections whose own conclusions are that they constrain nothing relevant do not belong in a PRX Life article.

7. **The EEG exercise is null and should be presented as such.** Mean a = 0.104, r = 0.052: for a < 0.15, I₁/I₀(a) = a/2 to within 10⁻³, so agreement with the Bessel relation is agreement with a straight line through the origin. The pooled estimand (62 channels × 500 samples) is not the spatial order parameter of the theory, and the bootstrap over time bins ignores autocorrelation (acknowledged). This is at most an estimator calibration and cannot be described as data "compatible with the Bessel relation" without adding "and with any monotone alternative."

8. **The consciousness identification is not empirically anchored.** The glued state and its reconstruction are proposed as correlates of unity and a minimal self, but no independent measurement for "experience" is offered, and the supplement concedes "absence of report cannot define absence of experience." PRX Life publishes quantitative biology; a correlate whose experiential side has no proposed measurement is philosophy, and should be labelled as motivation rather than as a scientific proposal. The eight hypotheses also do not contain the identification, so the Lean composition does not bear on the paper's title claim.

9. **Biological realism of the phase model.** All threshold results assume identical frequencies, mean-field sinusoidal coupling, no delays, and positive couplings (supp:72 notes positivity is "not free" and excludes frustration). Cortical oscillators have heterogeneous frequencies, conduction delays, inhibitory interactions, and non-sinusoidal phase-response curves. The only heterogeneity control moves the operational threshold by ~50% (supp:1704). Either add a heterogeneous/delayed control for the delay-scaling prediction or restrict the claim explicitly to the mean-field idealisation.

10. **Length and clarity.** Main text ~14k words plus a 33k-word supplement with ~50 table rows of Lean identifiers is well beyond PRX Life norms. The prose is nearly opaque: the abstract contains sentences such as "That grain is the uniform bound's, not phase order's" and "for a κ derived here for neither cortex nor a processor"; several paragraphs run 200+ words carrying inline Lean names. Almost every paragraph ends by retracting part of what it began with. Rewrite for a reader who has not seen the Lean code: state each result, its hypotheses and its scope in one place, and move Lean identifiers to the supplement table.

11. **Assumptions on cortical implementation are not empirically substantiated.** The identification of the kernel with a cortical field, the specific mode profiles and prices, and the assumption of a specific physical field mediating coupling are crucial but presented as modelling commitments rather than derived results. This leaves direct applicability to cortex as a speculative leap rather than a demonstrated consequence.

---

## MINOR CONCERNS

1. **Notation collisions:** E is both encoder (Eq. 10) and field amplitude (Eq. 13); λ is both a kernel eigenvalue and tortuosity; U is both stored energy and a patch; T is rounds to deadline while k_BT uses T as temperature and script-T is timing sensitivity; D is diffusion in the main text and the phase spread in supp:148.

2. **main.tex:150** attributes K_c = 2D to Sakaguchi 1988; the result is correct, but Strogatz & Mirollo 1991 and the Acebrón 2005 review should accompany it.

3. **Propagation of chaos** for the noisy Kuramoto model is in fact established (Dai Pra & den Hollander 1996; Bertini, Giacomin & Pakdaman 2010). The supplement's statement that it "is a research programme rather than a lemma" (supp:124) is out of date; cite and scope correctly.

4. **Plasticity controls (main.tex:477):** three seeds is too few for the reported ranges; either add seeds or report as illustrative.

5. **Compatibility estimator AUC = 0.986** (main.tex:492) is on constructed data with a known generative model. The main text should say "on synthetic data."

6. **Reference verification:** "Barbour 2017" for cortical conductivity 0.3-0.6 S/m should be verified against Logothetis et al. 2007 and Miceli et al. 2017. Per the author's own anti-hallucination gate, all 2026 references should be re-verified at submission.

7. **main.tex:190:** the falsification condition "the first identification delivering less refutes the coupling-gated account" is not operational since κ is not measurable without choosing a mode basis.

8. **Eq. (14)** r_ss ~ √(K̇/D)(t - t₀)^{1/2} is stated as a "benchmark" but the paper's own Sec. 7.2 shows the tracking approximation fails at onset.

9. **Sec. 9.1, columns:** the objections to columns as a content cover are well made, but no alternative cover candidate is offered.

10. **Fig. 3 (ramp)** shows ±1 SE bands over 32 replicas; the delay exponent fit should show per-replica points or a bootstrap band, not only the ensemble mean.

11. **Data availability:** state the ds005620 subject/run list and preprocessing code path explicitly, and give the Lean toolchain and Mathlib commit hash.

12. **"Supplemental Material"** vs. "supplementary.tex" — harmonise.

13. **Typographic:** repeated `\allowbreak` Lean identifiers render awkwardly in 12 pt; several tables will need landscape or smaller fonts.

14. **Limited discussion of alternative frameworks:** a more thorough comparison with IIT, GWT, and predictive processing would strengthen the manuscript's positioning.

---

## APPRAISAL

The Lean-verified composition with an audited axiom footprint is a genuine methodological contribution. The winding/amplitude-layer analysis (Sec. 7.3) and the synthetic compatibility estimator are worth publishing. The mathematical architecture is internally coherent and the candour about limitations is unusual and refreshing. However, in its present form the manuscript is a very long catalogue of conditional statements whose physical content is either textbook, vacuous by the author's own admission (installed energy, thermodynamic chain, uniform content bound), or generic (the v^{1/2} delay). The gap between abstract mathematics and measurable neurobiology remains unbridged.

A publishable version for PRX Life would:
- Cut Secs. 5 and 6 and most of Sec. 4.2 to a paragraph each
- Recast the "unconditional results" as motivation with proper citations to the extensive Kuramoto literature
- Turn the emergence prediction into an actual design with a discriminating alternative, calibrated observables, and per-replicate uncertainty on the exponent
- Either derive a genuine stored-field energy or drop the cortical evaluation of the installed-energy bound
- Present the consciousness identification as interpretive framing rather than as a testable proposal
- Rewrite the exposition for a reader who has not seen the Lean code

---

## RECOMMENDATION

**Major revision.** A substantially restructured resubmission would be considered; acceptance of a lightly edited version is not recommended.