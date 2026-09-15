import Mathlib
import PhysicsOfConsciousness.Phase8_ContinuousField
import PhysicsOfConsciousness.Phase8_CoherentStability

/-!
# Phase 9 — EM field identification predicate

The identification of the posited continuum coupling kernel with the cortical
endogenous EM field is the framework's central empirical commitment. Before this
module it lived entirely in prose. `IsEMFieldCoupling` makes it a `Prop` whose
fields are the conditions the framework places on the kernel:

1. **Joint continuity** — the kernel is a continuous function `M × M → ℝ`, which
   is what the continuum theorems (`fieldCorrelation`, `structural_resonance`,
   etc.) need for the integration and differentiation steps.
2. **A probability substrate** — `volume` is a probability measure. This is not
   decoration: `mean_field_coupling` integrates the kernel against `volume`
   twice, so without the normalization a constant kernel's mean-field strength
   scales with the substrate's total mass and the threshold `K_c = 2D` compares
   a coupling against a size. `exhibits_phase_transition` requires exactly the
   same hypothesis, for exactly this reason.
3. **`K` is the kernel's mean-field strength** — `mean_field_coupling sys = K`.
   This is the field that stops the predicate from being about a free scalar
   sitting next to an unconstrained kernel.
4. **No single site carries the coupling** — the EM field is *modulatory*: the
   coupling any one site contributes is at most half the mean-field strength.
   On a nonatomic substrate this is automatic; on a finite one it is a real
   constraint, and it is what rules out a kernel that is a delta at one vertex
   (the shape `vertexKernel` in `Chain.lean` exhibits).
5. **`D` is the field's own noise** — `sys.D = D`, so the noise the threshold is
   stated against is the noise of the field named here, not a second free
   scalar. Positivity is then inherited from `StochasticNeuralField.h_D_pos`
   rather than assumed again (`IsEMFieldCoupling.noise_pos`).

`isEMFieldCoupling_const` is the general construction: any probability substrate
whose singletons carry at most half the mass supports a constant kernel of any
non-negative strength. `em_unitInterval_isEMFieldCoupling` instantiates it on a
continuum (the unit interval with Lebesgue measure); `Chain.lean` instantiates it
on the finite `Cortex` witness, where the site condition has content.

## What this does not establish

* Not that cortex satisfies any of the conditions. No object in this development
  denotes cortex; the witnesses are a unit interval and a three-site toy. That
  the *physical* kernel is the endogenous EM field is the empirical question,
  and the predicate's role is to say what a future model must exhibit, not to
  settle it.
* Not that the field is electromagnetic. Nothing here distinguishes an EM kernel
  from any other continuous mean-field kernel; the conditions are necessary, not
  sufficient, and the name records the intended referent.
* Not the supercriticality of `K`. That is `Chain.lean`'s `E67` — a separate
  node, deliberately, because `E56` says *which field realizes the kernel* and
  `E67` says *which regime that field is in*.
  `exhibits_phase_transition_of_isEMFieldCoupling` is where the two meet.
-/

open Set MeasureTheory Topology

namespace PhysicsOfConsciousness

variable {M : Type*} [MeasureSpace M] [TopologicalSpace M]

/-- The conditions the continuum coupling kernel must satisfy if it is to be
identified with the endogenous EM field.

Unlike `Chain.FieldRealizes`, which relates three real numbers, this predicate is
stated about a concrete `StochasticNeuralField M`: fields 3 and 5 pin `K` and `D`
to that field rather than leaving them free. -/
structure IsEMFieldCoupling (sys : StochasticNeuralField M) (K D : ℝ) : Prop where
  /-- The kernel `sys.K : M → M → ℝ` is jointly continuous. -/
  kernel_continuous : Continuous (Function.uncurry sys.K)
  /-- The substrate is normalized: `volume` is a probability measure. This is the
  normalization in which the mean-field derivation of `K_c = 2D` is carried out. -/
  domain_probability : IsProbabilityMeasure (volume : Measure M)
  /-- `K` is the kernel averaged over both arguments, not a free scalar. -/
  coupling_is_mean_field : mean_field_coupling sys = K
  /-- The field is *modulatory*: no single site contributes more than half the
  mean-field coupling. Vacuous on a nonatomic substrate, a real constraint on a
  finite one. -/
  no_site_dominates : ∀ x y : M, sys.K x y * ((volume : Measure M) {y}).toReal ≤ K / 2
  /-- The mean-field coupling constant is non-negative. -/
  coupling_nonneg : 0 ≤ K
  /-- `D` is the field's own phase noise. -/
  noise_is_field_noise : sys.D = D

namespace IsEMFieldCoupling

variable {sys : StochasticNeuralField M} {K D : ℝ}

/-- The phase noise is positive — inherited from the field, not assumed. -/
theorem noise_pos (h : IsEMFieldCoupling sys K D) : 0 < D :=
  h.noise_is_field_noise ▸ sys.h_D_pos

/-- The domain carries positive measure: the field is spatially extended. -/
theorem domain_positive_measure (h : IsEMFieldCoupling sys K D) :
    0 < (volume : Measure M) (Set.univ) := by
  have := h.domain_probability
  simp [measure_univ]

end IsEMFieldCoupling

/-- The threshold node and the identification node meet here: a field satisfying
`IsEMFieldCoupling` at a supercritical `K` is a field that
`Phase8_ContinuousField`'s `exhibits_phase_transition` applies to.

This is what stops the predicate from being inert in `Chain.lean`: the second
conjunct of `E56` is not decoration, it is the hypothesis that converts `E67`'s
numerical claim about two reals into a statement about the substrate. -/
theorem exhibits_phase_transition_of_isEMFieldCoupling
    [IsProbabilityMeasure (volume : Measure M)]
    {sys : StochasticNeuralField M} {K D : ℝ}
    (h : IsEMFieldCoupling sys K D) (hK : critical_coupling D < K) :
    exhibits_phase_transition sys := by
  rw [exhibits_phase_transition, h.coupling_is_mean_field, h.noise_is_field_noise]
  exact hK

/-- The identified scalar mean-field model above threshold has a coherent
stationary density with a proved classical linear gap modulo rotation. The
coupling and diffusion are those of the named field. This does not transfer
the scalar equation's stability to a heterogeneous spatial kernel or establish
an electromagnetic or cortical identification; those remain model inputs. -/
theorem IsEMFieldCoupling.coherent_phase_model
    {sys : StochasticNeuralField M} {K D : ℝ}
    (h : IsEMFieldCoupling sys K D) (hK : critical_coupling D < K) :
    ∃ a : ℝ, 0 < a ∧
      FokkerPlanck.IsStationary sys.D
        (FokkerPlanck.meanDrift (mean_field_coupling sys) (vonMisesDensity a))
        (vonMisesDensity a) ∧
      FokkerPlanck.HasCoherentLinearGap sys.D (mean_field_coupling sys) a := by
  have hD := h.noise_pos
  have hKpos : 0 < K := by unfold critical_coupling at hK; linarith
  obtain ⟨r, hr, _, hf⟩ := supercritical_fixed_point_exists hD hK
  have ha : 0 < K * r / D := div_pos (mul_pos hKpos hr) hD
  have he : FokkerPlanck.branchCoupling D (K * r / D) = K := by
    rw [FokkerPlanck.branchCoupling, (coherent_iff_sRatio_eq hD hKpos hr.ne').mp hf]
    field_simp
  rw [h.coupling_is_mean_field, h.noise_is_field_noise]
  refine ⟨K * r / D, ha, ?_, ?_⟩
  · simpa only [he] using FokkerPlanck.branch_stationary hD ha
  · simpa only [he] using FokkerPlanck.branch_hasLinearGap hD ha

#print axioms IsEMFieldCoupling.coherent_phase_model

/-! ## Witnesses -/

/-- The constant-kernel field of strength `c` and noise `D` on a substrate `M`. -/
noncomputable def constField (c D : ℝ) (hD : 0 < D) : StochasticNeuralField M :=
  ⟨⟨fun _ => (0 : ℝ), fun _ _ => c, (0 : ℝ)⟩, D, hD, (0 : ℝ)⟩

/-- **The general construction.** On any probability substrate whose singletons
carry at most half the total mass, the constant kernel of any non-negative
strength `c` is an `IsEMFieldCoupling` at `K = c`.

The singleton hypothesis is where the *modulatory* condition bites: it holds
vacuously when `volume` has no atoms, and on a finite substrate it says the
substrate has at least two sites of equal weight. It is not a way of making the
predicate trivial — a kernel concentrated on one vertex fails it. -/
theorem isEMFieldCoupling_const [IsProbabilityMeasure (volume : Measure M)]
    {c D : ℝ} (hc : 0 ≤ c) (hD : 0 < D)
    (hsite : ∀ y : M, ((volume : Measure M) {y}).toReal ≤ 1 / 2) :
    IsEMFieldCoupling (constField (M := M) c D hD) c D := by
  refine ⟨?_, inferInstance, ?_, ?_, hc, rfl⟩
  · -- a constant kernel is jointly continuous
    have h : (Function.uncurry fun (_ _ : M) => c) = fun _ : M × M => c := by
      ext ⟨x, y⟩; rfl
    rw [show (constField (M := M) c D hD).K = fun _ _ : M => c from rfl, h]
    exact continuous_const
  · -- on a probability substrate a constant kernel has mean-field strength `c`
    exact mean_field_coupling_const (constField (M := M) c D hD) c rfl
  · -- no single site carries more than half the coupling
    intro x y
    have hmul : c * ((volume : Measure M) {y}).toReal ≤ c * (1 / 2) :=
      mul_le_mul_of_nonneg_left (hsite y) hc
    simpa [constField] using hmul.trans_eq (by ring)

/-- **A continuum witness.** The unit interval with Lebesgue measure is a
probability substrate with no atoms, so the constant kernel of strength `1` and
noise `1` satisfies every condition.

This is a *mathematical* witness: it shows the predicate is not vacuous on a
continuum, where the modulatory condition is automatic. It says nothing about
cortex. -/
theorem em_unitInterval_isEMFieldCoupling :
    IsEMFieldCoupling (constField (M := unitInterval) 1 1 one_pos) 1 1 :=
  isEMFieldCoupling_const zero_le_one one_pos (fun y => by simp)

end PhysicsOfConsciousness
