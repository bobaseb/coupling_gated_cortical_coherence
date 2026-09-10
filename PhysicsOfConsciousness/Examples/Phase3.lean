/-
  Examples/Phase3.lean — heat, resonance, and what dissipation pays for

  §2 inhabits `StructuralResonance` twice: a perfectly resonant system at KL = 0
  and a detuned one that attains the bound with equality. §18 inhabits
  `PredictiveDissipation` twice over one correlated two-bit law — a frozen
  signal permitted to dissipate nothing, and a scrambled one forced to dissipate
  its whole mutual information — and §18.4 refutes the postulate's `axiom` form.
-/

import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_KLBound
import PhysicsOfConsciousness.Phase3_LandauerBridge
import PhysicsOfConsciousness.Phase3_PredictiveThermodynamics
import PhysicsOfConsciousness.Examples.Bit

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 2. Structural resonance: a perfectly resonant system, and a detuned one

The first witness below has `KL = 0`, so it discharges `StructuralResonance.kl_bound`
trivially — `σ ≥ 0` is all that is being asked of it, and any system whatever would do. A
witness like that shows the class is inhabited and nothing else.

The second is the same one-bit eraser of §1 driven by an environment that is *not* matched
to it: the perturbation statistics are a point mass while the system's internal transition
statistics are uniform. There `KL = log 2 > 0`, the entropy production rate is
`log 2 > 0`, and the postulate is satisfied with **equality** (`boolDetuned_tight`). So the
bound is not merely consistent, it is attained: it cannot be strengthened to a strict
inequality, and it is doing real work rather than comparing a positive number to zero.

`boolDetuned` is a `def` rather than an `instance` because `boolResonance` already occupies
`StructuralResonance Bool`; the theorems are applied to it explicitly. -/

/-- Uniform internal statistics matched to uniform external statistics: the
    system has reached structural resonance, so KL = 0 and the postulate holds
    with room to spare. -/
noncomputable def uniformBool : ProbDist Bool where
  p := fun _ => 1/2
  nonneg := by intro i; norm_num
  sum_one := by simp

noncomputable instance boolResonance : StructuralResonance Bool where
  P_ext := uniformBool
  Q_int := uniformBool
  Q_int_pos := by intro i; norm_num [uniformBool]
  transition := id
  dt := 1
  dt_pos := one_pos
  kl_bound := by
    have hKL : KL uniformBool uniformBool = 0 := by
      unfold KL uniformBool
      simp
    show discrete_entropy_rate (σ := Bool) id ≥ KL uniformBool uniformBool / 1
    rw [hKL]
    rw [zero_div]
    have h : discrete_entropy_rate (σ := Bool) id = Real.log 2 / 1 := rfl
    rw [h, div_one]
    positivity

/-- A point mass at `true`: an environment that only ever presents one perturbation,
against internal statistics that are uniform. -/
noncomputable def diracTrue : ProbDist Bool where
  p := fun b => if b then 1 else 0
  nonneg := by intro i; cases i <;> norm_num
  sum_one := by rw [Fintype.sum_bool]; norm_num

theorem KL_diracTrue_uniform : KL diracTrue uniformBool = Real.log 2 := by
  unfold KL diracTrue uniformBool
  rw [Fintype.sum_bool]
  norm_num

/-- The one-bit eraser of §1 against a mismatched environment. Not an `instance`: `Bool`
already carries `boolResonance`. -/
@[instance_reducible] noncomputable def boolDetuned : StructuralResonance Bool where
  P_ext := diracTrue
  Q_int := uniformBool
  Q_int_pos := by intro i; norm_num [uniformBool]
  transition := fun _ => false
  dt := 1
  dt_pos := one_pos
  kl_bound := by
    show discrete_entropy_rate (σ := Bool) (fun _ => false) ≥ KL diracTrue uniformBool / 1
    rw [KL_diracTrue_uniform, div_one]
    have h : discrete_entropy_rate (σ := Bool) (fun _ => false) = Real.log 2 / 1 := rfl
    rw [h, div_one]

/-- The divergence is strictly positive: the environment and the system genuinely disagree. -/
theorem boolDetuned_KL_pos : 0 < KL boolDetuned.P_ext boolDetuned.Q_int := by
  show 0 < KL diracTrue uniformBool
  rw [KL_diracTrue_uniform]
  exact Real.log_pos one_lt_two

/-- And so is the entropy production rate it is being compared against. -/
theorem boolDetuned_sigma_pos :
    0 < discrete_entropy_rate (σ := Bool) boolDetuned.transition := by
  have h : discrete_entropy_rate (σ := Bool) boolDetuned.transition = Real.log 2 / 1 := rfl
  rw [h, div_one]
  exact Real.log_pos one_lt_two

/-- **The postulate is tight.** `KL = Δt · σ` exactly, so `StructuralResonance.kl_bound`
cannot be strengthened to a strict inequality — a one-bit erasure dissipating `log 2`
against a point-mass environment sits precisely on the bound. -/
theorem boolDetuned_tight :
    KL boolDetuned.P_ext boolDetuned.Q_int
      = boolDetuned.dt * discrete_entropy_rate (σ := Bool) boolDetuned.transition := by
  show KL diracTrue uniformBool = 1 * discrete_entropy_rate (σ := Bool) (fun _ => false)
  have h : discrete_entropy_rate (σ := Bool) (fun _ => false) = Real.log 2 / 1 := rfl
  rw [KL_diracTrue_uniform, h, div_one, one_mul]

/-- Derivation 3's bound, on the non-degenerate witness. -/
example : KL boolDetuned.P_ext boolDetuned.Q_int
    ≤ boolDetuned.dt * discrete_entropy_rate (σ := Bool) boolDetuned.transition :=
  @structural_resonance_bound Bool _ _ _ boolDetuned

/-- The discrete second law, on the same witness. -/
example : 0 ≤ discrete_entropy_rate (σ := Bool) boolDetuned.transition :=
  @discrete_entropy_rate_nonneg Bool _ _ _ boolDetuned

/-! ## 18. Prediction, memory, and what dissipation pays for

Witnesses `Phase3_PredictiveThermodynamics`. Three obligations are discharged
here and they are different in kind.

**(a) The class is inhabited, twice, on the same joint law.** `PredictiveDissipation`
carries Still, Sivak, Bell and Crooks' bound as a field, exactly as
`StructuralResonance` carries its own postulate. Two instances are built over the
same two-bit joint law and differ only in the signal's dynamics: in
`frozenSystem` the signal does not move, in `scrambledSystem` it is redrawn from
its stationary law at every step. The first dissipates nothing and is allowed to;
the second is *forced* to dissipate, and the amount is computed.

**(b) The informations are not zero, and not infinite.** A witness whose mutual
information were `0` would satisfy every bound in the file vacuously, and one
whose mutual information were `⊤` would make `dissipatedWork` say nothing. Both
are excluded here by direct computation on the two-bit law
(`memory_ne_zero`, `memory_ne_top`), and the second needs real work: absolute
continuity of the joint against the product of its marginals, established by
showing that the product charges every singleton with mass `1/4`.

**(c) The data processing inequality is fenced.** `predictiveInfo_le_mutualInfo`
holds because the evolution has the form `id ∥ₖ κ` — the system cannot write to
its environment. `writeKernel_increases_mutualInfo` exhibits a Markov kernel on
the *pair* that raises mutual information from `0` to something positive, so the
restriction on the kernel's shape is load-bearing and not decoration. This is the
same service `§16`'s one-way kernel performs for the symmetric-kernel theorems.

Finally, `still_bound_is_not_an_axiom` proves the claim the class docstring makes
in prose: the `axiom` formulation of Still's bound, quantified over all joint laws
and all signal dynamics with `dissipatedWork` a fixed field, is refuted by
`frozenSystem`'s own data read against `scrambledSystem`'s signal. -/

section PredictiveThermodynamicsWitness

open ProbabilityTheory InformationTheory

/-! ### The two-bit law

`Bool` for the system state, `Bool` for the signal. The joint law is the
perfectly correlated pair: the system's bit *is* the signal's bit. This is the
smallest law with non-zero mutual information, and everything below is computed
against it. -/

/-- The uniform law on one bit. -/
noncomputable def unifBool : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

/-- **The system remembers the signal exactly.** The joint law of `(X_t, S_t)`
puts mass `1/2` on each of the two agreeing configurations and nothing on the
two disagreeing ones. -/
noncomputable def corrJoint : Measure (Bool × Bool) :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (true, true) + Measure.dirac (false, false))

/-- The same marginals, made independent. This is the reference law mutual
information is measured against, and — in `§18.3` — a joint law in its own
right, the one a system that has forgotten the signal would carry. -/
noncomputable def indepJoint : Measure (Bool × Bool) := unifBool.prod unifBool

instance : IsProbabilityMeasure unifBool :=
  ⟨by simp [unifBool, ENNReal.inv_two_add_inv_two]⟩

instance : IsProbabilityMeasure corrJoint :=
  ⟨by simp [corrJoint, ENNReal.inv_two_add_inv_two]⟩

instance : IsProbabilityMeasure indepJoint := by unfold indepJoint; infer_instance

/-- Both marginals of the correlated law are uniform: the correlation is in the
joint alone, not in either coordinate. -/
theorem corrJoint_fst : corrJoint.fst = unifBool := by
  ext s hs
  rw [Measure.fst_apply hs]
  simp only [corrJoint, unifBool, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (measurable_fst hs)]
  rfl

theorem corrJoint_snd : corrJoint.snd = unifBool := by
  ext s hs
  rw [Measure.snd_apply hs]
  simp only [corrJoint, unifBool, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (measurable_snd hs)]
  rfl

/-- Mutual information for this law is the divergence of the correlated joint
from the independent one. -/
theorem mutualInfo_corrJoint : mutualInfo corrJoint = klDiv corrJoint indepJoint := by
  rw [mutualInfo, corrJoint_fst, corrJoint_snd, indepJoint]

/-! ### The memory is real: neither zero nor infinite -/

theorem unifBool_singleton (b : Bool) : unifBool {b} = (2 : ℝ≥0∞)⁻¹ := by
  simp only [unifBool, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton b)]
  cases b <;> simp

/-- The independent law charges every configuration with mass `1/4`. This is what
makes it a legitimate reference: nothing is invisible to it. -/
theorem indepJoint_singleton (p : Bool × Bool) : indepJoint {p} = (4 : ℝ≥0∞)⁻¹ := by
  have hs : ({p} : Set (Bool × Bool)) = ({p.1} : Set Bool) ×ˢ ({p.2} : Set Bool) := by
    ext q; simp [Prod.ext_iff]
  rw [indepJoint, hs, Measure.prod_prod, unifBool_singleton, unifBool_singleton,
    ← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num

theorem corrJoint_singleton_tt : corrJoint {((true, true) : Bool × Bool)} = (2 : ℝ≥0∞)⁻¹ := by
  simp only [corrJoint, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton ((true, true) : Bool × Bool))]
  simp

/-- **The pair is genuinely dependent**: the joint charges the agreeing
configuration with `1/2` where independence would charge `1/4`. -/
theorem corrJoint_ne_indepJoint : corrJoint ≠ indepJoint := by
  intro h
  have h1 : corrJoint {((true, true) : Bool × Bool)}
      = indepJoint {((true, true) : Bool × Bool)} := by rw [h]
  rw [corrJoint_singleton_tt, indepJoint_singleton] at h1
  revert h1
  norm_num

/-- Absolute continuity, from the fact that the reference law has no null
singletons: a set the product ignores is empty. -/
theorem corrJoint_ac : corrJoint ≪ indepJoint := by
  intro s hs
  have hmem : ∀ p : Bool × Bool, p ∉ s := by
    intro p hp
    have hle : indepJoint {p} ≤ indepJoint s := measure_mono (Set.singleton_subset_iff.2 hp)
    rw [indepJoint_singleton, hs] at hle
    revert hle
    norm_num
  rw [Set.eq_empty_iff_forall_notMem.2 hmem, measure_empty]

/-- **The memory is finite**, so `PredictiveDissipation.memory_ne_top` is
dischargeable and the real number `dissipatedWork` says something. -/
theorem memory_ne_top : mutualInfo corrJoint ≠ ⊤ := by
  rw [mutualInfo_corrJoint]
  exact klDiv_ne_top corrJoint_ac Integrable.of_finite

/-- **The memory is non-zero.** Without this every bound in
`Phase3_PredictiveThermodynamics` would hold of this witness vacuously. -/
theorem memory_ne_zero : mutualInfo corrJoint ≠ 0 := by
  rw [mutualInfo_corrJoint]
  exact fun h => corrJoint_ne_indepJoint (klDiv_eq_zero_iff.1 h)

theorem memory_pos : 0 < (mutualInfo corrJoint).toReal :=
  ENNReal.toReal_pos memory_ne_zero memory_ne_top

/-! ### 18.1 A frozen signal: the memory is entirely predictive

The signal does not move, so what the system remembers about `S_t` is exactly
what it knows about `S_{t+1}`. Nonpredictive information is zero and the instance
is permitted to dissipate nothing. -/

/-- A system whose environment is static. `dissipatedWork := 0` is *allowed* here,
not assumed: `still_bound` has to be checked, and it is checked by
`predictiveInfo_id`. -/
@[instance_reducible]
noncomputable def frozenSystem : PredictiveDissipation Bool Bool Bool where
  joint := corrJoint
  joint_isProb := inferInstance
  signal := Kernel.id
  signal_isMarkov := inferInstance
  memory_ne_top := memory_ne_top
  thermalEnergy := 1
  thermalEnergy_pos := one_pos
  dissipatedWork := 0
  still_bound := by rw [predictiveInfo_id, tsub_self]; simp

/-- Every bit the frozen system holds is a predictive bit. -/
theorem frozenSystem_predictive : frozenSystem.predictive = mutualInfo corrJoint :=
  predictiveInfo_id corrJoint

theorem frozenSystem_nonpredictive : frozenSystem.nonpredictive = 0 := by
  show mutualInfo corrJoint - predictiveInfo corrJoint (Kernel.id : Kernel Bool Bool) = 0
  rw [predictiveInfo_id, tsub_self]

/-- **The zero-dissipation theorem, fired.** `predictive_eq_of_no_dissipation`
returns the equality of the two informations on this instance — and by
`memory_pos` the common value is strictly positive, so the conclusion is about a
system that actually remembers something. -/
theorem frozenSystem_all_memory_predictive :
    frozenSystem.predictive = mutualInfo corrJoint ∧ 0 < (frozenSystem.predictive).toReal :=
  ⟨frozenSystem.predictive_eq_of_no_dissipation rfl,
    by rw [frozenSystem.predictive_eq_of_no_dissipation rfl]; exact memory_pos⟩

/-! ### 18.2 A scrambled signal: the memory is entirely wasted

The signal is redrawn from the uniform law at every step, independently of its
own past. The system's memory of `S_t` therefore says nothing whatever about
`S_{t+1}`, and Still's bound charges the *whole* of it against dissipated work.
This is the regime the phrase "memory that does not predict is thermodynamic
waste" names, and here the waste is computed rather than asserted. -/

/-- A system whose environment has no memory of its own. -/
@[instance_reducible]
noncomputable def scrambledSystem : PredictiveDissipation Bool Bool Bool where
  joint := corrJoint
  joint_isProb := inferInstance
  signal := Kernel.const Bool unifBool
  signal_isMarkov := inferInstance
  memory_ne_top := memory_ne_top
  thermalEnergy := 1
  thermalEnergy_pos := one_pos
  dissipatedWork := (mutualInfo corrJoint).toReal
  still_bound := by rw [predictiveInfo_const, tsub_zero]; simp

/-- Nothing the scrambled system remembers predicts anything. -/
theorem scrambledSystem_predictive : scrambledSystem.predictive = 0 :=
  predictiveInfo_const corrJoint unifBool

theorem scrambledSystem_nonpredictive : scrambledSystem.nonpredictive = mutualInfo corrJoint :=
  nonpredictiveInfo_const corrJoint unifBool

/-- **The instance is forced to dissipate.** This is the content of the witness:
the bound is not satisfiable at zero cost once the signal stops being
predictable, and the floor is the system's entire memory. -/
theorem scrambledSystem_dissipates : 0 < scrambledSystem.dissipatedWork := memory_pos

/-- The data processing inequality is *strict* on this instance: `0 = I_pred <
I_mem`. Together with `§18.1`, where it is an equality, this shows the inequality
is not secretly one or the other. -/
theorem scrambledSystem_dpi_strict : scrambledSystem.predictive < mutualInfo corrJoint := by
  rw [scrambledSystem_predictive]
  exact pos_iff_ne_zero.2 memory_ne_zero

/-- **The Kawai–Parrondo–Van den Broeck predicate, discharged.** The forward
ensemble is the correlated law, the reversed one is the product of its marginals,
and the dissipated work is `k_B T` times the divergence between them — with
equality, so the instance saturates both postulates at once.

Read physically, the identification is the sharp case: the only distinguishable
consequence of running this system's film backwards is the correlation it holds,
so the arrow of time and the wasted memory coincide. A physical instance would
carry path ensembles with structure of their own and the inequality of
`nonpredictive_le_arrow` would be slack. -/
theorem scrambledSystem_kpv : IsKPVDissipation scrambledSystem corrJoint indepJoint := by
  show (mutualInfo corrJoint).toReal = 1 * (klDiv corrJoint indepJoint).toReal
  rw [one_mul, mutualInfo_corrJoint]

/-- The arrow-of-time bound, fired on the instance. -/
theorem scrambledSystem_arrow :
    (scrambledSystem.nonpredictive).toReal ≤ (klDiv corrJoint indepJoint).toReal :=
  nonpredictive_le_arrow scrambledSystem corrJoint indepJoint scrambledSystem_kpv

/-- The second law, read off the instance rather than assumed of it. -/
theorem scrambledSystem_second_law : 0 ≤ scrambledSystem.dissipatedWork :=
  scrambledSystem.dissipatedWork_nonneg

/-! ### 18.3 Why the kernel must have the form `id ∥ₖ κ`

`predictiveInfo_le_mutualInfo` is the data processing inequality for the Markov
chain `X_t → S_t → S_{t+1}`, and the chain is enforced by the *shape* of the
evolution: `Kernel.id ∥ₖ κ` leaves the system coordinate alone and acts on the
signal coordinate through `κ` only. Drop that shape and the theorem is false, not
merely unproved. The kernel below is the system writing its own state into the
environment, and it takes an independent pair to a perfectly correlated one. -/

/-- The system stamps its state onto the signal. A perfectly good Markov kernel
on the pair — and not of the form `id ∥ₖ κ`. -/
noncomputable def writeKernel : Kernel (Bool × Bool) (Bool × Bool) :=
  Kernel.deterministic (fun p => (p.1, p.1)) (by fun_prop)

theorem writeKernel_comp : writeKernel ∘ₘ indepJoint = corrJoint := by
  have hcomp : (fun p : Bool × Bool => (p.1, p.1))
      = (fun x : Bool => (x, x)) ∘ Prod.fst := rfl
  rw [writeKernel, Measure.deterministic_comp_eq_map, hcomp,
    ← Measure.map_map (by fun_prop) measurable_fst]
  have hfst : indepJoint.map Prod.fst = unifBool := by
    rw [indepJoint, ← Measure.fst, Measure.fst_prod]
  rw [hfst]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  simp only [corrJoint, unifBool, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ ((by fun_prop : Measurable fun x : Bool => (x, x)) hs)]
  rfl

/-- An independent pair carries no mutual information. -/
theorem mutualInfo_indepJoint : mutualInfo indepJoint = 0 := by
  rw [indepJoint, mutualInfo_prod]

/-- **The system that writes to its environment breaks the bound.** Mutual
information rises from `0` to a strictly positive value under one application of
a Markov kernel on the pair. So `predictiveInfo_le_mutualInfo` is not a fact about
Markov kernels in general, and the parallel form in `evolvedJoint` is carrying the
physical hypothesis rather than decorating it. -/
theorem writeKernel_increases_mutualInfo :
    mutualInfo indepJoint < mutualInfo (writeKernel ∘ₘ indepJoint) := by
  rw [mutualInfo_indepJoint, writeKernel_comp]
  exact pos_iff_ne_zero.2 memory_ne_zero

/-! ### 18.4 Why Still's bound is a class field and not an axiom -/

/-- **The `axiom` form of Still's bound is inconsistent**, and this is the
refutation the class docstring describes rather than a restatement of it.

`frozenSystem` fixes `dissipatedWork = 0` and `thermalEnergy = 1`. Had
`still_bound` been declared as a free-standing axiom quantified over all joint
laws and all signal dynamics, it would apply to that instance's fields with
`scrambledSystem`'s signal, and assert `1 * (mutualInfo corrJoint).toReal ≤ 0` —
which `memory_pos` refutes. Bundling the joint law and the signal dynamics as
*data of one system* is what makes the postulate a constraint on that system
instead of a false claim about every pair.

This is the same failure that made three of the development's five original
axioms provably `False` (`Axioms.lean` §5). -/
theorem still_bound_is_not_an_axiom :
    ¬ ((1 : ℝ) * (mutualInfo corrJoint
          - predictiveInfo corrJoint (Kernel.const Bool unifBool)).toReal ≤ 0) := by
  rw [predictiveInfo_const, tsub_zero, one_mul]
  exact not_le.2 memory_pos

/-! ### 18.5 The two-bit law, charged to Landauer's bill

`§18.2` computes the wasted memory of a system whose signal is unpredictable and
declares a `dissipatedWork` equal to it. That is legitimate — the class field is
an obligation and the instance meets it — but the number stands beside the
system rather than coming out of it, exactly as `K` and `D` once stood beside
the field in `Phase9_EMIdentification`.

`landauerSystem` is the same two-bit law with the number produced instead.
`PredictiveDissipation.ofLandauer` (`Phase3_LandauerBridge.lean`) takes the
one-bit eraser of `§1` — the register `fun _ => true`, whose Landauer heat
`§1`'s bath fixes at `log 2` — and returns a predictive structure whose
`dissipatedWork` *is* that heat and whose `still_bound` is derived from
`landauer_bound`. Nothing is postulated twice.

The arithmetic is the sharp case and is worth stating plainly: the register
erases one bit, `log 2` of entropy; the correlated law wastes one bit, `log 2`
of memory; and the bound is met with **equality** (`landauerSystem_tight`). A
witness in which the erased entropy exceeded the waste would show the
construction runs; this one shows it runs with nothing to spare. -/

/-- The density of the correlated law against the independent one: `2` on the
diagonal, `0` off it. The mutual information of `§18` is computed from it. -/
noncomputable def corrDensity : Bool × Bool → ℝ≥0∞ := fun p => if p.1 = p.2 then 2 else 0

lemma measurable_corrDensity : Measurable corrDensity := measurable_of_countable _

theorem corrJoint_singleton (p : Bool × Bool) :
    corrJoint {p} = if p.1 = p.2 then (2 : ℝ≥0∞)⁻¹ else 0 := by
  simp only [corrJoint, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton p)]
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> simp

theorem corrJoint_eq_withDensity : corrJoint = indepJoint.withDensity corrDensity := by
  refine Measure.ext_of_singleton fun p => ?_
  rw [withDensity_apply _ (measurableSet_singleton p), lintegral_singleton,
    indepJoint_singleton, corrJoint_singleton]
  by_cases h : p.1 = p.2 <;> simp [corrDensity, h]
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

lemma rnDeriv_corrJoint : corrJoint.rnDeriv indepJoint =ᵐ[indepJoint] corrDensity := by
  rw [corrJoint_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ measurable_corrDensity

lemma llr_corrJoint :
    llr corrJoint indepJoint =ᵐ[corrJoint] fun p => Real.log (corrDensity p).toReal := by
  filter_upwards [corrJoint_ac.ae_le rnDeriv_corrJoint] with p hp
  simp only [llr_def, hp]

/-- **The memory is exactly one bit.** `§18` proves the mutual information of the
correlated law is neither `0` nor `⊤`; this computes it. The Radon–Nikodym
derivative against the product law is `2` on the diagonal and `0` off it, so the
log-likelihood ratio is `log 2` wherever the law charges anything. -/
theorem klDiv_corrJoint : klDiv corrJoint indepJoint = ENNReal.ofReal (Real.log 2) := by
  rw [klDiv_of_ac_of_integrable corrJoint_ac Integrable.of_finite]
  have hint : ∫ p, llr corrJoint indepJoint p ∂corrJoint = Real.log 2 := by
    rw [integral_congr_ae llr_corrJoint, integral_fintype Integrable.of_finite]
    simp only [corrDensity, Measure.real, corrJoint_singleton, Fintype.sum_prod_type,
      Fintype.sum_bool]
    norm_num
    ring
  rw [hint]
  simp

theorem mutualInfo_corrJoint_eq : mutualInfo corrJoint = ENNReal.ofReal (Real.log 2) := by
  rw [mutualInfo_corrJoint, klDiv_corrJoint]

theorem memory_toReal : (mutualInfo corrJoint).toReal = Real.log 2 := by
  rw [mutualInfo_corrJoint_eq, ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num))]

/-- **The register of `§1`, and what it erases.** `fun _ => true` collapses two
states onto one: `log 2 − log 1` of entropy, which is one bit. -/
theorem erasedEntropy_boolEraser : erasedEntropy (fun _ : Bool => true) = Real.log 2 := by
  simp [erasedEntropy, entropy, boltzmann_entropy]

/-- The identification the bridge asks for, discharged by computation: the memory
this law wastes is exactly the entropy that register destroys. -/
theorem boolEraser_waste :
    (nonpredictiveInfo corrJoint (Kernel.const Bool unifBool)).toReal
      ≤ erasedEntropy (fun _ : Bool => true) := by
  rw [nonpredictiveInfo_const, erasedEntropy_boolEraser, memory_toReal]

/-- **The predictive structure of the one-bit eraser.** Same joint law as
`§18.1` and `§18.2`; the thermal scale and the dissipated work are now `§1`'s
temperature and `§1`'s Landauer heat, and `still_bound` is discharged by
`landauer_bound` rather than by a declaration. -/
@[instance_reducible]
noncomputable def landauerSystem : PredictiveDissipation Bool Bool Bool :=
  PredictiveDissipation.ofLandauer (sys := Bool) (fun _ => true) corrJoint
    (Kernel.const Bool unifBool) memory_ne_top boolEraser_waste

theorem landauerSystem_dissipatedWork :
    landauerSystem.dissipatedWork = heat_dissipation (fun _ : Bool => true) := rfl

theorem landauerSystem_thermalEnergy :
    landauerSystem.thermalEnergy = Thermodynamics.temperature (sys := Bool) := rfl

theorem landauerSystem_nonpredictive :
    landauerSystem.nonpredictive = mutualInfo corrJoint :=
  nonpredictiveInfo_const corrJoint unifBool

/-- The waste is real: the instance is not one of those that satisfy every bound
by holding no memory. -/
theorem landauerSystem_nonpredictive_pos : 0 < (landauerSystem.nonpredictive).toReal := by
  rw [landauerSystem_nonpredictive]; exact memory_pos

/-- **The bound is attained.** `k_B T · I_nonpred = W_diss`: the bit the register
erases is the bit the memory wastes, and Landauer's heat pays for it exactly.
Nothing is left over, so the inequality of `still_bound` cannot be strengthened
on this witness. -/
theorem landauerSystem_tight :
    landauerSystem.thermalEnergy * (landauerSystem.nonpredictive).toReal
      = landauerSystem.dissipatedWork := by
  rw [landauerSystem_nonpredictive, memory_toReal]
  show (1 : ℝ) * Real.log 2 = Real.log 2
  rw [one_mul]

/-- **The regression.** `frozenSystem` is a legitimate `PredictiveDissipation`
and it is *not* a predictive structure of the erasing register: its dissipated
work is zero where the register's Landauer heat is `log 2`, and it wastes no
memory at all. An edge asking only for `Nonempty (PredictiveDissipation _ _ _)`
is discharged by it; the edge `Chain.E34` asks for more, and this is what "more"
excludes. -/
theorem frozenSystem_not_of_eraser :
    frozenSystem.dissipatedWork ≠ heat_dissipation (fun _ : Bool => true)
      ∧ (frozenSystem.nonpredictive).toReal = 0 := by
  constructor
  · show (0 : ℝ) ≠ Real.log 2
    exact ne_of_lt (Real.log_pos (by norm_num))
  · rw [frozenSystem_nonpredictive, ENNReal.toReal_zero]

end PredictiveThermodynamicsWitness

end Examples
end PhysicsOfConsciousness
