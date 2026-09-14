import PhysicsOfConsciousness.Phase2_KernelMesh
import PhysicsOfConsciousness.Phase3_AgencyThermodynamics

/-!
# A finite microscopic actuator with spatial response modes

Each physical configuration sets finitely many mode occupancies. The same
occupancies determine a reciprocal product-space kernel and the stored
installation energy. The feedback step changes configurations, so its kernel
update and installation work are computed on its actual paths. Spatial mode
profiles, occupancy readout, prices and reservoir conventions are declared
hardware data; neither a heat bound nor an entropy difference supplies them.

The thermal-switch witness pays positive work to close a mode. The fixed
substrate and initial configuration law are prepared inputs, not a continuing
energy source. No electromagnetic or cortical identification is established.
-/

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness

/-- Bare finite hardware data. `I` indexes physical modes; a local change is a
change of an occupancy. Nonnegativity and spatial continuity are properties of
a chosen arrangement, not additional unconstrained laws of the structure. -/
structure LocalActuator (M X S I : Type*) where
  occupancy : X × S → I → ℝ
  profile : I → M → ℝ
  price : I → ℝ

namespace LocalActuator

variable {M X S I : Type*} [Fintype I]

/-- The state of the actuator selects weights on spatial mode products. -/
noncomputable def kernel (A : LocalActuator M X S I) (z : X × S) (x y : M) : ℝ :=
  ∑ i, A.occupancy z i * A.profile i x * A.profile i y

/-- Stored energy of the installed mode occupancies, using declared prices. -/
noncomputable def storedEnergy (A : LocalActuator M X S I) (z : X × S) : ℝ :=
  ∑ i, A.price i * A.occupancy z i

/-- External work includes the change in installed hardware energy and heat
delivered to the reservoir. This fixes the required work in the declared
energy/reservoir model; it does not construct an external power supply. -/
noncomputable def pathWork (A : LocalActuator M X S I) (q : X → S → S → ℝ)
    (c : X) (s t : S) : ℝ :=
  A.storedEnergy (c, t) - A.storedEnergy (c, s) + q c s t

/-- Actual microscopic transitions change the kernel by the changed mode
occupancies. Profiles are fixed hardware; no entropy-to-gain law is assumed. -/
theorem kernel_update (A : LocalActuator M X S I) (c : X) (s t : S) (x y : M) :
    A.kernel (c, t) x y - A.kernel (c, s) x y =
      ∑ i, (A.occupancy (c, t) i - A.occupancy (c, s) i) * A.profile i x * A.profile i y := by
  simp [kernel, sub_mul, Finset.sum_sub_distrib]

/-- A transition changes no pair outside the response of its changed modes.
This is a spatial locality statement conditional on the supplied profiles,
not a derivation of their support from electromagnetism. -/
theorem kernel_update_local (A : LocalActuator M X S I) (c : X) (s t : S) (x y : M)
    (h : ∀ i, A.occupancy (c, t) i = A.occupancy (c, s) i ∨
      A.profile i x = 0 ∨ A.profile i y = 0) :
    A.kernel (c, t) x y = A.kernel (c, s) x y := by
  apply sub_eq_zero.mp
  rw [kernel_update]
  apply Finset.sum_eq_zero
  intro i _
  rcases h i with hi | hi | hi <;> simp [hi]

theorem kernel_symmetric (A : LocalActuator M X S I) (z : X × S) (x y : M) :
    A.kernel z x y = A.kernel z y x := by
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem kernel_nonneg (A : LocalActuator M X S I) (z : X × S)
    (ha : ∀ i, 0 ≤ A.occupancy z i) (hb : ∀ i x, 0 ≤ A.profile i x) (x y : M) :
    0 ≤ A.kernel z x y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (ha i) (hb i x)) (hb i y)

variable [Fintype X] [Fintype S]

noncomputable def expectedKernel (A : LocalActuator M X S I) (p : ProbDist (X × S))
    (x y : M) : ℝ := ∑ z, p.p z * A.kernel z x y

/-- The ensemble kernel follows the executed path law. This forbids silently
substituting an unrelated final law or a prospective policy evaluation. -/
theorem expected_kernel_update (A : LocalActuator M X S I) (P : FiniteFeedbackStep X S)
    (x y : M) :
    A.expectedKernel P.final x y - A.expectedKernel P.initial x y =
      P.meanHeat (fun c s t => ∑ i,
        (A.occupancy (c, t) i - A.occupancy (c, s) i) * A.profile i x * A.profile i y) := by
  simp_rw [← kernel_update]
  simp only [FiniteFeedbackStep.meanHeat, mul_sub, Finset.sum_sub_distrib,
    P.forward_expect_final (fun z => A.kernel z x y),
    P.forward_expect_initial (fun z => A.kernel z x y), expectedKernel]

/-- Mean installation work and heat use the very same paths that install the
kernel. The initial energy and external work source remain model inputs. -/
theorem installation_first_law (A : LocalActuator M X S I) (P : FiniteFeedbackStep X S)
    (q : X → S → S → ℝ) :
    P.meanHeat (A.pathWork q) =
      (∑ z, P.final.p z * A.storedEnergy z) -
      (∑ z, P.initial.p z * A.storedEnergy z) + P.meanHeat q :=
  P.mean_first_law A.storedEnergy q (A.pathWork q) (fun _ _ _ => rfl)

theorem expectedKernel_continuous [TopologicalSpace M] (A : LocalActuator M X S I)
    (p : ProbDist (X × S)) (hb : ∀ i, Continuous (A.profile i)) :
    Continuous (Function.uncurry (A.expectedKernel p)) := by
  apply continuous_finsetSum
  intro z _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  exact (continuous_const.mul ((hb i).comp continuous_fst)).mul ((hb i).comp continuous_snd)

/-- Spatial refinement of the installed ensemble kernel. This applies at any
fixed execution time and also to a supplied passive configuration law; there
is no interchange of learning-time and spatial limits. -/
theorem energy_tendsto [TopologicalSpace M] [CompactSpace M] [MeasurableSpace M]
    [BorelSpace M] [SecondCountableTopology M]
    (A : LocalActuator M X S I) (p : ProbDist (X × S))
    (hb : ∀ i, Continuous (A.profile i)) (G : ℕ → KernelMesh M)
    (μ : Measure M) [IsFiniteMeasure μ]
    (hG : ∀ x, Tendsto (fun n => (G n).snap x) atTop (𝓝 x)) :
    Tendsto (fun n => (G n).energy μ (A.expectedKernel p)) atTop
      (𝓝 (∫ z, A.expectedKernel p z.1 z.2 ∂μ.prod μ)) :=
  KernelMesh.energy_tendsto G μ _ (A.expectedKernel_continuous p hb) hG

end LocalActuator

/--
**One microscopic arrangement**: the hardware, the configuration law its modes
actually sit in, the substrate measure and a spatial refinement sequence.

The fields divide into three groups, as in `ActuatedCoupling`.

* The hardware — `actuator`, and the spatial continuity of its response
  profiles. Occupancies, profiles and prices are declared physical data.
* The configuration law — `law`, the actual joint law of the hardware's
  degrees of freedom. `Chain.e45Active_of_localActuator` names an executed
  feedback step whose final law it is, and `Chain.e45_of_localActuator` names a
  declared predictive system whose joint law it is. Neither derives it.
* The refinement data — a finite substrate measure and a sequence of finite
  measurable partitions whose samples converge. The index of that sequence is
  spatial; it is not a count of executed control updates, and convergence in
  one is not convergence in the other.

The kernel this arrangement installs lives on `M × M`. Its limit is the
integral of the arrangement's own kernel, not a quantity read off a heat
allowance: no field of this structure is a budget.
-/
structure KernelArrangement (M X S I : Type*) [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [Fintype X] [Fintype S] [Fintype I] where
  /-- The finite hardware whose mode occupancies carry the kernel. -/
  actuator : LocalActuator M X S I
  /-- Spatial continuity of the declared response profiles. -/
  profile_continuous : ∀ i, Continuous (actuator.profile i)
  /-- The actual joint law of the hardware's configuration. -/
  law : ProbDist (X × S)
  /-- The substrate measure. -/
  volume : Measure M
  /-- Finiteness of the substrate mass. Carried as a field because it is a
  property of the `volume` field rather than of the substrate type. -/
  [volume_finite : IsFiniteMeasure volume]
  /-- The refining sequence of finite partitions. Its index is spatial. -/
  grid : ℕ → KernelMesh M
  /-- Each point's sample converges to it: the spatial error shrinks. -/
  refines : ∀ x, Tendsto (fun n => (grid n).snap x) atTop (𝓝 x)

namespace KernelArrangement

variable {M X S I : Type*} [TopologicalSpace M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [SecondCountableTopology M] [Fintype X] [Fintype S] [Fintype I]

/-- **The kernel the arrangement installs**, on the product space. -/
noncomputable def kernel (A : KernelArrangement M X S I) : M → M → ℝ :=
  A.actuator.expectedKernel A.law

/-- **The finite cell-pair coupling energy at refinement level `n`.** -/
noncomputable def energy (A : KernelArrangement M X S I) (n : ℕ) : ℝ :=
  (A.grid n).energy A.volume A.kernel

/-- **The continuum coupling energy of the same installed kernel.** -/
noncomputable def continuumEnergy (A : KernelArrangement M X S I) : ℝ :=
  ∫ z, A.kernel z.1 z.2 ∂A.volume.prod A.volume

theorem kernel_continuous (A : KernelArrangement M X S I) :
    Continuous (Function.uncurry A.kernel) :=
  A.actuator.expectedKernel_continuous A.law A.profile_continuous

theorem kernel_symmetric (A : KernelArrangement M X S I) (x y : M) :
    A.kernel x y = A.kernel y x := by
  exact Finset.sum_congr rfl fun z _ => by rw [A.actuator.kernel_symmetric z x y]

/--
**The installed kernel's energies converge under spatial refinement.**

This is `LocalActuator.energy_tendsto` at the arrangement's own data. The
hypotheses used are the profiles' continuity, the substrate's compactness and
finite mass, and the shrinking sample error — all spatial. No heat budget,
entropy difference or learning-time limit appears, and supplying one would not
replace any of them.
-/
theorem coarseGrains (A : KernelArrangement M X S I) :
    Tendsto A.energy atTop (𝓝 A.continuumEnergy) :=
  haveI := A.volume_finite
  A.actuator.energy_tendsto A.law A.profile_continuous A.grid A.volume A.refines

end KernelArrangement

end PhysicsOfConsciousness
