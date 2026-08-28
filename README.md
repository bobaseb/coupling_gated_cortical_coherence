<div align="center">
  
# 🌌 Physical Primitives of Mind
**Modeling Consciousness via Symmetries and Landauer Erasure**

<br />

[![Lean 4 Verified](https://img.shields.io/badge/Lean_4-Verified-27ae60?style=for-the-badge&logo=lean)](https://leanprover.github.io/)
[![Status: Under Review](https://img.shields.io/badge/Status-Under_Review-f39c12?style=for-the-badge&logo=open-access)](https://direct.mit.edu/opmi)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue?style=for-the-badge)](LICENSE)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC_BY_4.0-lightgrey?style=for-the-badge)](https://creativecommons.org/licenses/by/4.0/)

*A rigorous physical framework demonstrating how cognitive architectures emerge as attractor states from fundamental physical primitives.*

[**Read the Paper**](main.pdf) | [**Math Supplement**](supplementary.pdf) | [**Project Website**](index.html)

</div>

<hr />

## 🧠 Overview

The pursuit of a physical theory of consciousness typically searches for biological correlates or treats subjective experience as an abstract algorithm. This repository asks a more fundamental question:

> *If we assume nothing but the most basic physical primitives—continuous symmetries (the Poincaré group), geometry, and thermodynamics—is the emergence of a unified, perceiving entity a natural physical attractor?*

We demonstrate that the structural hallmarks of consciousness can be derived as physical attractor states. By establishing a deductive chain starting from absolute first principles, we show how continuous symmetries break to form boundaries, how those boundaries dissipate free energy as non-equilibrium steady states, and how their evolution along paths of least action results in physical resonance with their environment.

## ⚡ Core Framework

The deductive chain mapping physical primitives to cognitive properties:

1. **Symmetry Breaking ➔ Boundaries:** Spontaneous symmetry breaking generates necessary topological boundaries between an "inside" and "outside".
2. **Landauer's Principle ➔ Dissipation:** Because phase space is finite, the boundary is subjected to thermodynamic erasure, acting as a dissipative structure.
3. **Least Action ➔ Structural Resonance:** To minimize entropy production, the internal topology morphs to mirror the environment (Predictive Processing).
4. **Thermodynamic Noise ➔ Phase Synchronization:** Macroscopic scaling triggers a Kuramoto phase transition.
5. **Phase Synchronization ➔ Global Sections:** Local fields mathematically glue into a unified topological space (Unity of Consciousness).
6. **Auto-Resonance ➔ The Self:** The field must predict itself to reach the absolute minimal dissipation state.

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
git clone https://github.com/your-username/physics_of_consciousness.git
cd physics_of_consciousness

# Build the Lean 4 project
lake build
```

## 📝 Manuscript

The manuscript and supplementary materials are written in LaTeX and compiled using `pdflatex`:

- `main.tex`: The main manuscript formatted for submission to *Open Mind*.
- `supplementary.tex`: The mathematical appendix detailing the Lean 4 formalisms.

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