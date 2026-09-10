<div align="center">
  
# 🌌 Coupling-gated cortical coherence
**What a field theory of conscious unity must assume, and what it predicts**

<br />

[![Lean 4 Verified](https://img.shields.io/badge/Lean_4-Verified-27ae60?style=for-the-badge&logo=lean)](https://leanprover.github.io/)
[![Checks](https://img.shields.io/github/actions/workflow/status/bobaseb/coupling_gated_cortical_coherence/ci.yml?branch=master&style=for-the-badge&label=checks&logo=githubactions&logoColor=white)](https://github.com/bobaseb/coupling_gated_cortical_coherence/actions/workflows/ci.yml)
[![Status: Preprint](https://img.shields.io/badge/Status-Preprint-f39c12?style=for-the-badge&logo=open-access)](main.pdf)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue?style=for-the-badge)](LICENSE)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC_BY_4.0-lightgrey?style=for-the-badge)](https://creativecommons.org/licenses/by/4.0/)

*A conditional field model of cortical coherence, with a machine-checked composition, a testable recovery prediction, and its assumptions named.*

[**Read the Paper**](main.pdf) | [**Math Supplement**](supplementary.pdf) | [**Maths Primer**](docs/primer.pdf) | [**Project Website**](https://bobaseb.github.io/coupling_gated_cortical_coherence/)

</div>

<hr />

## 🧠 Overview

A field account of cortical coordination holds that distributed neural processes are coupled in part through the endogenous extracellular electromagnetic field. This repository asks what such an account must assume in order to reach a globally consistent, self-referential state, and what it predicts before it gets there.

Nothing here derives consciousness from first principles. The physical core is a noisy mean-field phase model whose coupling drifts through a synchronization threshold; the resulting **coupling-gated recovery hypothesis** is the article's testable content. A Lean 4 development composes the established ingredients into one conditional theorem and isolates the **eight hypotheses** that composition consumes. The identification of the resulting mathematical object with the unity of a conscious episode is stated and argued for as a philosophical commitment, not proved.

## ⚡ The conditional chain

Nine nodes; the eight arrows between them are the assumptions, not results:

1. **Finite capacity** — a finite phase space has bounded information capacity.
2. **Boundary** — a broken symmetry forces the field to leave its vacuum manifold.
3. **Erasure** — the boundary erases, and erasure costs Landauer heat.
4. **Predictive bound** — dissipation bounds nonpredictive memory.
5. **Continuum limit** — discrete couplings coarse-grain to a scalar continuum energy.
6. **Field identification** — a specified physical field realizes that coupling (*empirical commitment*).
7. **Coherence** — above `K_c = 2D` the field carries a unique coherent order parameter.
8. **Unity** — compatible local states glue to a unique global section.
9. **Self** — that section is the unique fixed point of a self-prediction map.

Table 1 of the manuscript classifies the eight connecting hypotheses: one independent physical premise, three formalization gaps, two modelling assumptions and two physical commitments. A common toy witness satisfies all eight, so their conjunction is not empty; that is consistency, not cortex.

## 🧪 What the simulations show

The numerical controls restrict the hypothesis rather than confirm it, and two results transfer beyond this framework:

- **Ramp speed sets the apparent onset exponent.** An exponent fitted to a driven recovery trace reports the drive at least as much as the mechanism.
- **Squared-drift plasticity does not learn structure.** Coupling updates that descend the objective remove about two thirds of the objective available to them and preserve coherence, while driving within-cluster coupling to a fraction of between-cluster coupling — *away* from the generating structure, and further from it than from almost every node relabelling. A matched random update of the same step size does neither. Descending that functional does not produce representational learning, and the direction of the failure follows from a conservation law: symmetric coupling fixes the mean drift, so the objective can only equalize drift, which rewards exactly the coupling the template penalizes.

The exploratory EEG analysis is a demonstration of the estimation protocol on public data, over a concentration range too narrow to be informative about the relation itself.

---

## 🛠️ Formal Verification in Lean 4

To ensure our derivations are mathematically rigorous and avoid "math theatre," the core physical claims have been fully formalized in **Lean 4**. 

| Phase | Module | Status |
| :--- | :--- | :---: |
| 🔹 **Phase 1** | `Phase1_Primitives.lean` | ✅ Verified |
| 🔹 **Phase 2** | `Phase2_SimplicialBridge.lean` | ✅ Verified |
| 🔹 **Phase 3** | `Phase3_CombinatorialThermodynamics.lean` | ✅ Verified |
| 🔹 **Phase 4** | `Phase4_KuramotoDynamics.lean` | ✅ Verified |
| 🔹 **Phase 5** | `Phase5_GlobalSection.lean` | ✅ Verified |
| 🔹 **Phase 6** | `Phase6_ReflexiveTopology.lean` | ✅ Verified |
| 🔹 **Phase 7** | `Phase7_HardwareComparison.lean` | ✅ Verified |
| 🔹 **Phase 8** | `Phase8_ContinuousField.lean` | ✅ Verified |
| 🔹 **Phase 9** | `Phase9_EMIdentification.lean` | ✅ Verified |
| ⛓️ **Composition** | `Chain.lean` | ✅ Verified |

The table names one representative module per phase; the development is 37
modules in total, and `Chain.lean` is the one that matters most — it imports all
nine phases and states the single conditional theorem, with the eight
connecting hypotheses as explicit arguments. It also discharges all eight at
once, on the three-site cortex the witnesses under `Examples/` build, which is
what makes the conjunction non-empty rather than vacuous.

### 🚀 Building the Proofs

Ensure you have [elan](https://github.com/leanprover/elan) installed, which manages Lean versions.

```bash
# Clone the repository
git clone https://github.com/bobaseb/coupling_gated_cortical_coherence.git
cd coupling_gated_cortical_coherence

# Build the Lean 4 project
lake build
```

### 🐍 Simulations and tests

The numerical controls, the exploratory EEG analysis and the repository's own
gate scripts live under `simulations/`, managed with
[uv](https://docs.astral.sh/uv/):

```bash
cd simulations
uv sync --group dev
uv run pytest
```

Published values are not recomputed at build time: each simulation writes a
saved summary, and the manuscript reads only the LaTeX macros generated from
those summaries, so a quoted number cannot drift from the run that produced it.
See [`simulations/README.md`](simulations/README.md) for the gate scripts and
the data policy.

### 🔁 Off this machine

Both halves are checked on someone else's computer as well as the author's.
[`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs the test suite and
the whole `pre-commit` gate set on every push, and `lake build` against
Mathlib's prebuilt cache on an x86 runner. The twelve gates are otherwise
enforced on one machine only, where `git commit -n` can skip every one of
them.

## 📝 Manuscript

The manuscript and supplementary materials are written in LaTeX and compiled using `pdflatex`:

- `main.tex`: The main manuscript.
- `supplementary.tex`: The mathematical appendix detailing the Lean 4 formalisms.

A third document is a companion rather than part of the publication:

- `docs/primer.tex`: a plain-English primer on the advanced mathematics and physics used in both, for readers coming from cognitive neuroscience, machine learning or philosophy of mind. It works through each object in turn — what it is, why the framework needs it, what is actually proved, and what is not — and covers the topology, thermodynamics, operator theory, Kuramoto dynamics, bifurcation theory, sheaf theory, fixed-point theory, circular statistics and formal methodology that the two papers use. It reads the manuscript's generated numerical macros, so its figures cannot drift from the saved simulation summaries. Where it differs from `main.tex` or `supplementary.tex`, those are authoritative.

## 🤖 AI Assistance

This project was heavily AI-assisted, across the Lean 4 development, the simulation and analysis code, and the drafting and revision of the manuscript and supplement. Several assistants were used in an interleaved way throughout:

- **Google Antigravity CLI** — Gemini 3.1, Claude 4.6 Opus, Claude 4.6 Sonnet
- **OpenAI Codex CLI** — Astra, Terra, Luna, Sol
- **Claude Code** — Claude Opus 5
- **Gemini Pro**, through its web interface
- **Fable (Claude Opus 4)** — through OpenRouter, accessed with the Hermes CLI

Because they were used in combination and in alternation, no file, proof, figure or result is attributable to any one of them, and none is claimed to be. The author is responsible for all content, including everything a tool produced. Machine checking establishes the stated Lean results under their hypotheses; it does not validate the biological interpretation, and it does not replace scientific review of generated code and prose.

## 📄 License

This repository is dual-licensed:
- **Code (Lean 4 scripts, Python scripts, etc.):** [MIT License](LICENSE)
- **Text & Manuscripts (LaTeX source, PDFs, HTML):** [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/)

## 🏷️ Tech Stack

<div align="center">
  <img src="https://img.shields.io/badge/LaTeX-47A141?style=for-the-badge&logo=LaTeX&logoColor=white" alt="LaTeX" />
  <img src="https://img.shields.io/badge/Python-3776AB?style=for-the-badge&logo=python&logoColor=white" alt="Python" />
  <img src="https://img.shields.io/badge/Lean_4-2B2B2B?style=for-the-badge&logo=lean&logoColor=white" alt="Lean 4" />
</div>

<br/>

<div align="center">
  <img src="https://raw.githubusercontent.com/andreasbm/readme/master/assets/lines/rainbow.png" width="100%" alt="Divider" />
</div>