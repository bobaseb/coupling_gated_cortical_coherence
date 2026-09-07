<div align="center">
  
# 🌌 Physical Primitives of Mind
**Coupling-gated cortical coherence: what a field theory of conscious unity must assume, and what it predicts**

<br />

[![Lean 4 Verified](https://img.shields.io/badge/Lean_4-Verified-27ae60?style=for-the-badge&logo=lean)](https://leanprover.github.io/)
[![Status: Preprint](https://img.shields.io/badge/Status-Preprint-f39c12?style=for-the-badge&logo=open-access)](main.pdf)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue?style=for-the-badge)](LICENSE)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC_BY_4.0-lightgrey?style=for-the-badge)](https://creativecommons.org/licenses/by/4.0/)

*A conditional field model of cortical coherence, with a machine-checked composition, a testable recovery prediction, and its assumptions named.*

[**Read the Paper**](main.pdf) | [**Math Supplement**](supplementary.pdf) | [**Maths Primer**](docs/primer.pdf) | [**Project Website**](https://bobaseb.github.io/physical_primitives_of_mind/)

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
- **Squared-drift plasticity does not learn structure.** Coupling updates that descend the objective preserve coherence while moving *away* from the generating structure, below a shuffled-label comparison. Dissipation minimization does not imply representational learning.

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

### 🚀 Building the Proofs

Ensure you have [elan](https://github.com/leanprover/elan) installed, which manages Lean versions.

```bash
# Clone the repository
git clone https://github.com/bobaseb/physical_primitives_of_mind.git
cd physical_primitives_of_mind

# Build the Lean 4 project
lake build
```

## 📝 Manuscript

The manuscript and supplementary materials are written in LaTeX and compiled using `pdflatex`:

- `main.tex`: The main manuscript.
- `supplementary.tex`: The mathematical appendix detailing the Lean 4 formalisms.

A third document is a companion rather than part of the publication:

- `docs/primer.tex`: a plain-English primer on the advanced mathematics and physics used in both, for readers coming from cognitive neuroscience, machine learning or philosophy of mind. It works through each object in turn — what it is, why the framework needs it, what is actually proved, and what is not — and covers the topology, thermodynamics, operator theory, Kuramoto dynamics, bifurcation theory, sheaf theory, fixed-point theory, circular statistics and formal methodology that the two papers use. It reads the manuscript's generated numerical macros, so its figures cannot drift from the saved simulation summaries. Where it differs from `main.tex` or `supplementary.tex`, those are authoritative.

## 🤖 AI Assistance

The conceptualization, manuscript drafting, and Lean 4 formalizations in this project were heavily AI-assisted. We gratefully acknowledge the use of **the Google Antigravity CLI**, specifically utilizing **Gemini 3.1**, **Claude 4.6 Opus**, and **Claude 4.6 Sonnet** as pair-programming and reasoning partners throughout the research process.

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