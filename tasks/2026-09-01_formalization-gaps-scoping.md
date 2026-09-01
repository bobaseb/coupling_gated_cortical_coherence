# Formalization Gaps: Complete Scoping

**What Gemini's "interface isolation / SymPy / SMT" suggestion translates to in this repo, and what each strategy buys.**

---

## 1. What gaps exist, and where they live

The project distinguishes **four gap kinds**, and Gemini's feedback is about fixing two of them. Being precise about which is which matters because the strategies that work for one don't work for another.

### 1a. Chain gaps (the eight named hypotheses in `Chain.lean`)

| Label | Kind | What it asserts |
|---|---|---|
| `E12` n1→n2 | Formalization gap | Not really an edge — logically equivalent to its conclusion |
| `E23` n2→n3 | Formalization gap | Defect locus not related to a state space |
| `E34` n3→n4 | Formalization gap | Landauer heat ≠ Still's dissipated work; no identification |
| `E45` n4→n5 | Modelling assumption | Dissipation constrains coupling; no formal relation exists |
| `E56` n5→n6 | Physical commitment | The coarse-graining limit *is* the mean-field coupling constant |
| `E67` n6→n7 | Physical commitment | Cortex operates above threshold |
| `E78` n7→n8 | Formalization gap | Coherent order parameter → ThermodynamicCover on the substrate |
| `E89` n8→n9 | Modelling assumption | Self-prediction contracts at the Kuramoto linear relaxation rate |

**Gemini's interface isolation strategy is already the pattern here.** Every `E..` is a typed `Prop` with a docstring stating its kind, its physical content, and what would discharge it. Adding another one (say `E_FP` for the stationary density) would be trivial but raises the count to 9. More importantly: **the chain doesn't consume the stationary density.** The chain starts at n7 (coherent order parameter exists) and reasons forward. The density is an input *to* n7, not something `chain`'s correctness depends on. See §2 below.

### 1b. Pre-chain gaps (external to `chain` — the gap Gemini actually means)

These are the two gaps the manuscript marks as "open problems" and "standard ansätze":

1. **Fokker-Planck → von Mises stationary density** (O13, closed as decided-not-doing). The manuscript states at `main.tex:157`: *"Von Mises stationary density assumed rather than derived from the Fokker-Planck operator."* The Lean docstring at `Phase8_SelfConsistency.lean:15` says the same. **This is not hidden; it's the paper's position.**

2. **Propagation of chaos / McKean-Vlasov limit** (O14(B), closed as decided-not-doing). `main.tex:219`: *"the dynamical mean-field limit — propagation of chaos for the Kuramoto system — is the missing link."* The Lean file at `Phase8_ContinuousField.lean:787` records it as untouched. **Also not hidden.**

These are not in `Chain.lean` because `chain` doesn't need them. The chain is a composition of *consequences*: given a coherent order parameter (n7), the Self follows. How the order parameter arises is domain theory, not something the chain's correctness depends on.

---

## 2. Assessment of Gemini's three strategies

### 2a. Interface isolation — "typed assumption in Lean"

**Status: Already implemented. No new code needed.**

Gemini suggests adding an explicit `Prop`-valued hypothesis to `chain` for the Fokker-Planck → von Mises step. This would look like:

```lean
def E_FP (K D : ℝ) : Prop :=
  -- "the stationary density of the mean-field Kuramoto SDE at coupling K,
  --  noise D and order parameter r is von Mises at concentration a = Kr/D"
  ∀ r : ℝ, vonMisesDensity (K * r / D) = stationaryDensity (kuramotoSDE K D) r
```

**Why not do it:** It would make the paper's formal story *weaker*, not stronger. Currently the von Mises density is a **declared modelling input** — we say "we assume this, it's standard in the literature." Under interface isolation, it becomes a **hypothesis of the chain theorem** — and the chain then proves the Self *only if this holds*. That changes the honest status of the density from "we're comfortable with this assumption" to "we can't discharge this hypothesis, so the chain is conditional on it." 

The count of named hypotheses would go from 8 to 9, but one of the 8 (E12) is already not a real edge, so the effective count is 7. Adding E_FP would make it 8 again without closing any existing gap.

**Verdict: Skip for `chain`. Do not add E_FP.**

**When it would make sense:** If a referee specifically asks "is your chain theorem conditional on the stationary density being von Mises?" — at which point we add the assumption to the chain and concede the count goes up. Currently the density is upstream of the chain, which is a stronger position.

### 2b. SymPy algebraic verification — "mechanically verify the Fokker-Planck expansion step by step"

**Status: Worth doing as a supplement. Low effort, high-return for reviewer confidence.**

The Fokker-Planck → von Mises derivation for the mean-field Kuramoto model is standard (Sakaguchi 1988, Strogatz 2000). The steps:

1. Write the Fokker-Planck equation for the N-oscillator system
2. Take the mean-field limit (N → ∞, McKean-Vlasov)
3. Show the stationary solution is the von Mises density `ρ(θ) ∝ exp((Kr/D) cos(θ - ψ))`
4. Self-consistency gives `r = R(a)`

Step 2 is the hard one (propagation of chaos). Step 3 is the algebraic one: solving the stationary Fokker-Planck equation `∂_θ(ωρ) + ∂_θ(Kr sin(θ - ψ)ρ) = D ∂_θ²ρ` gives the von Mises. **This is ODE solving, not PDE analysis** — the mean-field reduction makes it one-dimensional.

A SymPy notebook verifying step 3 would:
- Set up the stationary Fokker-Planck ODE symbolically: `D · ρ''(θ) - d/dθ[(ω + Kr sin(θ - ψ)) ρ(θ)] = 0`
- Solve for ρ(θ): the first integral gives `D ρ' = (ω + Kr sin(θ - ψ)) ρ + C`
- The periodic boundary condition `ρ(-π) = ρ(π)` and normalization fix the constants
- Show the solution is `ρ(θ) ∝ exp((Kr/D) cos(θ - ψ))` (von Mises) up to the phase shift

**This doesn't prove the PDE → ODE reduction or the mean-field limit** (that's propagation of chaos, a research programme). It proves: *if you accept the mean-field Fokker-Planck equation, its stationary solution is the von Mises.* That's the algebraic step that should be mechanically checked.

**What exists in Lean already:** The Lean development doesn't need this — it takes the von Mises density as input. The notebook is for the manuscript's supplement, to show a reader "here is the algebra that connects the SDE to the density we assume."

**Cost:** 200-300 lines of SymPy. A single Python script + printed notebook PDF for the supplement. 2-4 hours.

**Verdict: Do it. Low cost, strengthens the supplement, eliminates an algebraic-error attack vector a referee could exploit.**

**What it does NOT provide:**
- No Lean integration (SymPy ≠ Lean)
- No proof of the mean-field limit (that's propagation of chaos)
- No proof of dynamical stability (the stationary solution could be unstable)

### 2c. SMT bounded checking (Z3) — "discretize the Fokker-Planck operator and prove invariant regions"

**Status: Skip. Wrong tool for the problem.**

Z3's bounded model checking works on discrete transition systems — finite-state or quantifier-free theories. The Fokker-Planck operator is a continuous PDE on an infinite-dimensional function space. To discretize it enough for Z3, you'd:

1. Discretize the domain `[-π, π]` into N grid points
2. Discretize the Fokker-Planck equation into a system of ODEs (method of lines)
3. Discretize time into steps
4. Bound the state space to a finite range of densities
5. Assert: "for all time steps up to T, the density stays within ε of the von Mises"

Every discretization step introduces errors that need their own bounding arguments, and the result is about the discretization, not the PDE. The analytic proofs already in Lean (continuity, strict monotonicity, uniqueness of the fixed point) do more for stochastic stability than a Z3 bounded check on a discretized surrogate could.

**When would SMT help?** If there were discrete invariants to verify — e.g., "the winding number around a phase singularity remains integer-valued" or "the rank of a coupling matrix stays positive." Those are genuinely in Z3's wheelhouse. None of the current gaps have that shape.

**Verdict: Skip. Zero net gain for this paper.**

---

## 3. What the paper currently says about these gaps, and what could change

| Gap | Current manuscript position | What changes if we add SymPy verification |
|---|---|---|
| Fokker-Planck → von Mises | "Assumed rather than derived" (supplementary §1) | "Verified algebraically in supplement §X" — stronger claim, same logical status |
| Propagation of chaos | "Missing link" (main §2) | Unchanged — SymPy doesn't touch this |
| Chain gaps (E12–E89) | 8 named hypotheses, labelled by kind | Unchanged — SymPy is orthogonal to Lean formalization |

**The paper's claim is honest either way.** The SymPy notebook changes nothing about the Lean chain. It changes the supplement from "here's a cited derivation" to "here's a mechanically-checked algebraic verification." That is a real improvement for a referee who might otherwise say "show me the algebra."

---

## 4. Recommendation summary

| Strategy | Gap addressed | Cost | Value | Do it? |
|---|---|---|---|---|
| Interface isolation for FP gap | Already the pattern; would *weaken* the chain | Zero lines | Negative | **No** |
| SymPy Fokker-Planck → von Mises | Algebraic verification of standard derivation | 2-4 hours | Medium — supplement strength, eliminates algebraic error vector | **Yes** |
| SMT/Z3 bounded checking | Dynamical stability of continuum limit | 2-3 days | Low — analytic proofs already cover this better | **No** |
| SymPy expansion check | E(a) second-order coefficients for S2 | 1 hour | Medium — catches sign errors in the exponent derivation | **Yes** (add to S2 scope) |

**The highest-leverage formal gap work remains what's already in the todo file:**
- **T2** — Close E34 (Landauer = Still's dissipated work) — actual Lean proof
- **T2** — Close E78 first half (ofConvergentTrajectory → ThermodynamicCover) — actual Lean proof
- **F2** — Frustration gluing (H¹ obstruction) — actual Lean proof

These close gaps in the chain. SymPy doesn't close gaps; it checks algebra in the supplement.

---

## 5. Open question for you

The SymPy notebook would verify the stationary Fokker-Planck → von Mises algebra. It's the kind of thing that takes 2-4 hours and produces a printable notebook. Worth scheduling it as a task alongside the Bastos data pipeline (S1) and the Fermi estimate (E67), or should I just note it for later?