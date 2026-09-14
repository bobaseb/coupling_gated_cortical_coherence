import PhysicsOfConsciousness.Phase3_LocalActuator
import PhysicsOfConsciousness.Examples.AgencyThermodynamics
import PhysicsOfConsciousness.Examples.Phase3

/-!
# A thermal switch installs a spatial coupling mode

The controller and switch are physical bits. Agreement closes the mode, with
stored installation energy one. The noisy channel favours closure with odds
three; the external work source pays the installation energy plus the heat
required by that channel. One prepared update is accounted for, not hardware
fabrication or indefinite operation. The response profile and price are
declared hardware choices. Uniform cell partitions of an atomless interval
exercise spatial refinement independently of the action clock.
-/

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness.Examples.MicroscopicCoupling

open ThermalAgency

noncomputable def hardware : LocalActuator unitInterval Bool Bool Unit where
  occupancy z _ := if z.1 = z.2 then 1 else 0
  profile _ x := 4 / 3 * (1 + (x : ℝ))
  price _ := 1

theorem profile_continuous (i : Unit) : Continuous (hardware.profile i) :=
  continuous_const.mul (continuous_const.add continuous_subtype_val)

noncomputable def before : unitInterval → unitInterval → ℝ :=
  hardware.expectedKernel actuation.initial

noncomputable def after : unitInterval → unitInterval → ℝ :=
  hardware.expectedKernel actuation.final

theorem before_formula (x y : unitInterval) :
    before x y = 8 / 9 * (1 + (x : ℝ)) * (1 + (y : ℝ)) := by
  norm_num [before, LocalActuator.expectedKernel, LocalActuator.kernel, hardware,
    actuation, independent, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

theorem after_formula (x y : unitInterval) :
    after x y = 4 / 3 * (1 + (x : ℝ)) * (1 + (y : ℝ)) := by
  rw [after, actuation_final]
  norm_num [LocalActuator.expectedKernel, LocalActuator.kernel, hardware,
    correlated, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- Executing this channel strengthens an actual pairwise kernel; its value
comes from the final configuration law, not an entropy-to-amplitude rule. -/
theorem action_changes_kernel : before (0 : unitInterval) 0 < after 0 0 := by
  rw [before_formula, after_formula]
  norm_num

/-- A local switch closure changes a kernel value. This is a pathwise action,
not just a change in a statistic of the ensemble. -/
theorem closure_changes_kernel :
    hardware.kernel (false, true) (0 : unitInterval) 0 = 0 ∧
    hardware.kernel (false, false) (0 : unitInterval) 0 = 16 / 9 := by
  norm_num [LocalActuator.kernel, hardware]

theorem work_formula : actuation.meanHeat (hardware.pathWork heat) =
    (1 + Real.log 3) / 4 := by
  rw [hardware.installation_first_law, actuation_final, actuation_heat]
  norm_num [LocalActuator.storedEnergy, hardware, correlated, actuation, independent,
    Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- Positive external work includes both the installed energy increase and
the channel's heat; no uncharged installation is hidden in the coupling law. -/
theorem installation_work_positive : 0 < actuation.meanHeat (hardware.pathWork heat) := by
  rw [work_formula]
  have := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  positivity

theorem zero_work_rejected : ¬ (∀ x s t, hardware.pathWork heat x s t = 0) := by
  intro h
  have hw := installation_work_positive
  simp [FiniteFeedbackStep.meanHeat, h] at hw

/-- Clamped left-endpoint samples give n+1 cells, including the endpoint one
in the last cell. Endpoint choices have zero volume but remain well-defined. -/
noncomputable def mesh (n : ℕ) : KernelMesh unitInterval where
  size := n + 1
  locate x := ⟨min ⌊(x : ℝ) * (n + 1)⌋₊ n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  locate_measurable := by
    exact (measurable_of_countable (fun k : ℕ =>
      (⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (n + 1)))).comp
      ((measurable_subtype_coe.mul_const ((n : ℝ) + 1)).nat_floor)
  sample i := ⟨(i : ℕ) / ((n : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
      exact_mod_cast (Nat.le_of_lt i.isLt)⟩

/-- Quantitative spatial fineness for every point, including the right endpoint.
This theorem refers to no feedback iteration. -/
theorem mesh_error (n : ℕ) (x : unitInterval) :
    dist ((mesh n).snap x) x ≤ 1 / ((n : ℝ) + 1) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hxN : 0 ≤ (x : ℝ) * (n + 1) := mul_nonneg x.property.1 hN.le
  have hmin : ((min ⌊(x : ℝ) * (n + 1)⌋₊ n : ℕ) : ℝ) ≤ (⌊(x : ℝ) * (n + 1)⌋₊ : ℕ) := by
    exact_mod_cast min_le_left ⌊(x : ℝ) * (n + 1)⌋₊ n
  have hlo : ((min ⌊(x : ℝ) * (n + 1)⌋₊ n : ℕ) : ℝ) ≤ (x : ℝ) * (n + 1) :=
    hmin.trans (Nat.floor_le hxN)
  have hhi : (x : ℝ) * (n + 1) ≤ (min ⌊(x : ℝ) * (n + 1)⌋₊ n : ℕ) + 1 := by
    by_cases h : ⌊(x : ℝ) * (n + 1)⌋₊ ≤ n
    · rw [min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [min_eq_right (le_of_not_ge h)]
      nlinarith [x.property.2]
  change |((min ⌊(x : ℝ) * (n + 1)⌋₊ n : ℕ) : ℝ) / (n + 1) - (x : ℝ)| ≤ _
  rw [abs_of_nonpos (sub_nonpos.mpr ((div_le_iff₀ hN).mpr hlo))]
  have hh := (le_div_iff₀ hN).mpr hhi
  rw [add_div] at hh
  linarith

theorem mesh_refines (x : unitInterval) :
    Tendsto (fun n => (mesh n).snap x) atTop (𝓝 x) :=
  KernelMesh.snap_tendsto_of_dist mesh _ tendsto_one_div_add_atTop_nhds_zero_nat mesh_error x

/-- **The whole arrangement**: this hardware, the law the executed channel
actually left it in, the substrate and its refining partitions. -/
noncomputable def installed : KernelArrangement unitInterval Bool Bool Unit where
  actuator := hardware
  profile_continuous := profile_continuous
  law := actuation.final
  volume := volume
  grid := mesh
  refines := mesh_refines

theorem installed_kernel : installed.kernel = after := rfl

noncomputable def meshEnergy (n : ℕ) : ℝ := installed.energy n

noncomputable def continuumEnergy : ℝ := installed.continuumEnergy

/-- Spatial convergence of this channel's installed kernel energy. The process
has already executed once; increasing n refines only its spatial description. -/
theorem spatial_limit : Tendsto meshEnergy atTop (𝓝 continuumEnergy) :=
  installed.coarseGrains

/-- The installed coupling is jointly continuous and strictly positive, so the
refinement limit is not the limit of a degenerate kernel. -/
theorem after_continuous : Continuous (Function.uncurry after) :=
  installed.kernel_continuous

theorem after_pos (x y : unitInterval) : 0 < after x y := by
  rw [after_formula]
  have hx := x.property.1
  have hy := y.property.1
  positivity

/-- Every substrate integral of this witness is an interval integral. The
substrate is atomless, so the finite meshes are not a vertex sum in disguise. -/
theorem integral_unitInterval (f : ℝ → ℝ) :
    ∫ x : unitInterval, f (x : ℝ) = ∫ x in (0 : ℝ)..1, f x := by
  rw [unitInterval.volume_def,
    integral_subtype_comap (s := unitInterval) measurableSet_Icc f,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]

theorem integral_one_add : ∫ x : unitInterval, (1 + (x : ℝ)) = 3 / 2 := by
  rw [integral_unitInterval (fun x => 1 + x),
    intervalIntegral.integral_add intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
  norm_num [integral_id]

theorem continuumEnergy_eq : continuumEnergy = 3 := by
  show (∫ z : unitInterval × unitInterval, after z.1 z.2 ∂volume.prod volume) = 3
  simp_rw [after_formula, mul_assoc]
  rw [integral_const_mul,
    integral_prod_mul (fun x : unitInterval => 1 + (x : ℝ)) (fun y : unitInterval => 1 + (y : ℝ)),
    integral_one_add]
  norm_num

theorem installed_energy : installed.energy = meshEnergy := rfl

theorem installed_continuumEnergy : installed.continuumEnergy = 3 := continuumEnergy_eq

/-- The cell count is the refinement level plus one, so the energy is a sum
over that many cells in each factor. -/
theorem meshEnergy_eq (n : ℕ) :
    meshEnergy n = ∑ ij : Fin (n + 1) × Fin (n + 1),
      volume.real ((mesh n).cell ij.1) * volume.real ((mesh n).cell ij.2) *
        after ((mesh n).sample ij.1) ((mesh n).sample ij.2) := rfl

theorem mesh_mem_cell (n : ℕ) (i : Fin (n + 1)) (x : unitInterval) :
    x ∈ (mesh n).cell i ↔ min ⌊(x : ℝ) * ((n : ℝ) + 1)⌋₊ n = (i : ℕ) :=
  Fin.ext_iff

theorem mesh_sample_val (n : ℕ) (i : Fin (n + 1)) :
    ((mesh n).sample i : ℝ) = (i : ℕ) / ((n : ℝ) + 1) := rfl

theorem mesh_cell_one : (mesh 0).cell (0 : Fin 1) = Set.univ := by
  ext x
  simp [mesh_mem_cell]

theorem mesh_cell_two_zero : (mesh 1).cell (0 : Fin 2) =
    Set.Iio (⟨1 / 2, by norm_num⟩ : unitInterval) := by
  ext x
  rw [mesh_mem_cell, Set.mem_Iio, ← Subtype.coe_lt_coe]
  simp only [Fin.val_zero, Nat.cast_one, Nat.min_eq_zero_iff, Nat.floor_eq_zero]
  norm_num
  constructor <;> intro h <;> linarith

theorem mesh_cell_two_one : (mesh 1).cell (1 : Fin 2) =
    Set.Ici (⟨1 / 2, by norm_num⟩ : unitInterval) := by
  have h : (mesh 1).cell (1 : Fin 2) = ((mesh 1).cell (0 : Fin 2))ᶜ := by
    ext x
    rw [Set.mem_compl_iff, mesh_mem_cell, mesh_mem_cell]
    simp only [Fin.val_zero, Fin.val_one]
    omega
  rw [h, mesh_cell_two_zero, Set.compl_Iio]

theorem mesh_energy_zero : meshEnergy 0 = 4 / 3 := by
  show ∑ ij : Fin 1 × Fin 1,
      volume.real ((mesh 0).cell ij.1) * volume.real ((mesh 0).cell ij.2) *
        after ((mesh 0).sample ij.1) ((mesh 0).sample ij.2) = 4 / 3
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, mesh_cell_one, after_formula,
    mesh_sample_val, Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
  norm_num

theorem mesh_energy_one : meshEnergy 1 = 25 / 12 := by
  show ∑ ij : Fin 2 × Fin 2,
      volume.real ((mesh 1).cell ij.1) * volume.real ((mesh 1).cell ij.2) *
        after ((mesh 1).sample ij.1) ((mesh 1).sample ij.2) = 25 / 12
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, mesh_cell_two_zero, mesh_cell_two_one,
    after_formula, mesh_sample_val, Measure.real, unitInterval.volume_Iio,
    unitInterval.volume_Ici]
  norm_num

/-- The first two energies differ, fencing a vacuous constant approximation. -/
theorem mesh_energy_changes : meshEnergy 0 ≠ meshEnergy 1 := by
  rw [mesh_energy_zero, mesh_energy_one]
  norm_num

/-! ### The passive branch, on the same hardware

`Examples/Phase3.lean` §18 declares two predictive systems over one joint law of
a system bit and a signal bit. Reading that law as this hardware's configuration
installs a kernel in exactly the way the executed channel does. The two systems
differ by their whole dissipated work and agree on every object below, which is
the regression: predictive efficiency selects no hardware, no law and no mesh.
-/

/-- §18's joint law, written as a configuration law for the same hardware. -/
noncomputable def agreeing : ProbDist (Bool × Bool) where
  p z := if z.1 = z.2 then 1 / 2 else 0
  nonneg z := by split <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

theorem agreeing_toMeasure : agreeing.toMeasure = corrJoint := by
  refine Measure.ext_iff_singleton.mpr fun z => ?_
  have hz : MeasurableSet ({z} : Set (Bool × Bool)) := measurableSet_singleton z
  rw [ProbDist.toMeasure_singleton]
  simp only [corrJoint, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ hz]
  rcases z with ⟨x, s⟩
  cases x <;> cases s <;> simp [agreeing]

/-- The same hardware, substrate and partitions, holding the declared
predictive system's own joint law instead of the executed channel's. -/
noncomputable def remembered : KernelArrangement unitInterval Bool Bool Unit :=
  { installed with law := agreeing }

theorem frozen_law : frozenSystem.joint = remembered.law.toMeasure :=
  agreeing_toMeasure.symm

theorem scrambled_law : scrambledSystem.joint = remembered.law.toMeasure :=
  agreeing_toMeasure.symm

theorem remembered_formula (x y : unitInterval) :
    remembered.kernel x y = 16 / 9 * (1 + (x : ℝ)) * (1 + (y : ℝ)) := by
  show hardware.expectedKernel agreeing x y = _
  norm_num [LocalActuator.expectedKernel, LocalActuator.kernel, hardware, agreeing,
    Fintype.sum_prod_type, Fintype.sum_bool]
  ring

theorem remembered_continuumEnergy : remembered.continuumEnergy = 4 := by
  show (∫ z : unitInterval × unitInterval, remembered.kernel z.1 z.2 ∂volume.prod volume) = 4
  simp_rw [remembered_formula, mul_assoc]
  rw [integral_const_mul,
    integral_prod_mul (fun x : unitInterval => 1 + (x : ℝ)) (fun y : unitInterval => 1 + (y : ℝ)),
    integral_one_add]
  norm_num

/-- The passive arrangement refines in exactly the same spatial sense. -/
theorem remembered_limit : Tendsto remembered.energy atTop (𝓝 4) :=
  remembered_continuumEnergy ▸ remembered.coarseGrains

/-- The configuration law is not inert: reading a different actual law on the
same hardware installs a different kernel with a different continuum energy. -/
theorem law_matters : remembered.continuumEnergy ≠ continuumEnergy := by
  rw [remembered_continuumEnergy, continuumEnergy_eq]
  norm_num

/-- The two declared systems dissipate differently and install the same kernel.
Efficiency is therefore not what chose the hardware, the law or the mesh. -/
theorem efficiency_selects_nothing :
    frozenSystem.dissipatedWork < scrambledSystem.dissipatedWork ∧
    frozenSystem.joint = scrambledSystem.joint :=
  ⟨scrambledSystem_dissipates, rfl⟩

end PhysicsOfConsciousness.Examples.MicroscopicCoupling
