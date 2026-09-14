import PhysicsOfConsciousness.Phase3_ActuatedCoupling
import PhysicsOfConsciousness.Examples.AgencyThermodynamics
import PhysicsOfConsciousness.Examples.Phase2

/-!
# A noisy actuator on a genuinely refining spatial mesh

The same thermal channel is paired with different gains and density profiles.
The resulting differences fence the constitutive inputs: the channel and its
heat do not determine either of them. The model uses ensemble entropy loss as
a signed drive, not a pathwise action or a microscopic actuator work account.
-/

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness.Examples.ActuatedField

open ThermalAgency

/-- A positive, nonconstant spatial profile; its choice is a model input. -/
noncomputable def profile (x : ℝ) : ℝ := 1 + |x - 1 / 2|

theorem profile_uniformContinuous : UniformContinuous profile :=
  uniformContinuous_const.add tent_uniformContinuous

theorem profile_integrable : IntegrableOn profile (Set.Ico (0 : ℝ) 1) volume :=
  (profile_uniformContinuous.continuous.integrableOn_Icc (a := 0) (b := 1)).mono_set
    Set.Ico_subset_Icc_self

/-- The total profile is retained symbolically; no numerical quadrature enters Lean. -/
noncomputable def profileMass : ℝ := ∫ x in Set.Ico (0 : ℝ) 1, profile x

theorem profileMass_pos : 0 < profileMass := by
  have h : (1 : ℝ) ≤ profileMass := calc
    1 = ∫ _x in Set.Ico (0 : ℝ) 1, (1 : ℝ) := by simp
    _ ≤ profileMass := integral_mono (by simp) profile_integrable
      (fun x => le_add_of_nonneg_right (abs_nonneg (x - 1 / 2)))
  linarith

/-- The thermal actuator sets the profile amplitude at a specified nonnegative
gain. Regular grids supply refinement independently of that physical input. -/
noncomputable def coupling (g : ℝ) (hg : 0 ≤ g) : ActuatedCoupling ℝ Bool Bool where
  step := actuation
  temperature := 1
  heat := heat
  base := profile
  gain := g
  gain_nonneg := hg
  volume := volume
  region := Set.Ico 0 1
  mesh := fun n => gridTriangulation (n + 1)
  meshFintype := fun _ => inferInstance
  meshOrder := fun _ => inferInstance
  regular := fun n => gridRegular (n + 1) n.succ_pos
  fineness := fun n => 1 / ((n : ℝ) + 1)
  fineness_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  fine := by
    intro n u v x hx y hy
    simpa only [Nat.cast_add, Nat.cast_one] using grid_fine (n + 1) u v hx hy
  base_uniformContinuous := profile_uniformContinuous
  region_ne_top := by simp
  base_integrable := profile_integrable

/-- The drive is computed from the actual initial and final joint laws. -/
theorem drive_eq (g : ℝ) (hg : 0 ≤ g) :
    (coupling g hg).drive = 3 / 4 * Real.log 3 - Real.log 2 := by
  change shannon_entropy independent.p - shannon_entropy actuation.final.p = _
  rw [actuation_final, entropy_independent, entropy_correlated]
  ring

/-- Positive heat alone need not imply positive drive; this actuator's entropy
loss is strictly positive by its explicit laws. -/
theorem drive_pos : 0 < (coupling 1 one_pos.le).drive := by
  rw [drive_eq]
  have h := Real.log_lt_log (show (0 : ℝ) < 16 by norm_num)
    (show (16 : ℝ) < 27 by norm_num)
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [h16, h27] at h
  linarith

theorem profile_energy_one : discreteEnergy (gridTriangulation 1) volume profile = 3 / 2 := by
  simp [discreteEnergy, profile, Fin.sum_univ_two, grid_edge_region, grid_embedding, gridCell]
  norm_num

theorem profile_energy_two : discreteEnergy (gridTriangulation 2) volume profile = 5 / 4 := by
  simp [discreteEnergy, profile, Fin.sum_univ_three, grid_edge_region, grid_embedding, gridCell]
  norm_num

/-- Refinement changes the energy even though the process and gain are fixed.
This exercises spatial convergence rather than a constant-sequence witness. -/
theorem energy_moves : (coupling 1 one_pos.le).energy 0 ≠
    (coupling 1 one_pos.le).energy 1 := by
  intro h
  change discreteEnergy (gridTriangulation 1) volume
    (fun x => 1 * (coupling 1 one_pos.le).drive * profile x) =
    discreteEnergy (gridTriangulation 2) volume
      (fun x => 1 * (coupling 1 one_pos.le).drive * profile x) at h
  rw [discreteEnergy_const_mul, discreteEnergy_const_mul,
    profile_energy_one, profile_energy_two] at h
  have hp := drive_pos
  nlinarith

/-- The stationary step of the same channel establishes no new joint order. -/
noncomputable def idle : ActuatedCoupling ℝ Bool Bool :=
  { coupling 1 one_pos.le with step := sensing }

/-- Process dependence: replacing the executed step with its stationary version
removes the density. The gain, profile and meshes stay fixed. -/
theorem idle_density : idle.density = fun _ => 0 := by
  have hd : idle.drive = 0 := by
    change shannon_entropy correlated.p - shannon_entropy sensing.final.p = 0
    rw [sensing_final, sub_self]
  funext x
  simp [ActuatedCoupling.density, hd]

/-- Gain dependence at an unchanged process and heat: doubling the gain strictly
increases the limit. Thus the gain cannot be inferred from that heat. -/
theorem gain_matters : (coupling 1 one_pos.le).continuumLimit <
    (coupling 2 (by norm_num)).continuumLimit := by
  change 1 * (coupling 1 one_pos.le).drive * profileMass <
    2 * (coupling 1 one_pos.le).drive * profileMass
  have hp := mul_pos drive_pos profileMass_pos
  nlinarith

/-- A different supplied profile on the same substrate and process. -/
noncomputable def flat : ActuatedCoupling ℝ Bool Bool :=
  { coupling 1 one_pos.le with
    base := fun _ => 1
    base_uniformContinuous := uniformContinuous_const
    base_integrable := by
      change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ico 0 1) volume
      simp }

/-- Profile dependence: the thermal data and gain permit different spatial
energies. Choosing the spatial profile is additional constitutive content. -/
theorem profile_matters : flat.energy 0 ≠ (coupling 1 one_pos.le).energy 0 := by
  intro h
  change discreteEnergy (gridTriangulation 1) volume
    (fun _ => 1 * (coupling 1 one_pos.le).drive * 1) =
    discreteEnergy (gridTriangulation 1) volume
      (fun x => 1 * (coupling 1 one_pos.le).drive * profile x) at h
  rw [discreteEnergy_const_mul, discreteEnergy_const_mul, profile_energy_one] at h
  simp [grid_energy_const _ (by norm_num : 0 < 1)] at h
  have hp := drive_pos
  linarith

/-- Choose the gain to match the existing field witness's limit. This is a
calibration input, not a prediction of that field strength from a heat budget. -/
noncomputable def normalized : ActuatedCoupling ℝ Bool Bool :=
  coupling (3 / ((coupling 1 one_pos.le).drive * profileMass))
    (div_nonneg (by norm_num) (mul_pos drive_pos profileMass_pos).le)

theorem normalized_limit : normalized.continuumLimit = 3 := by
  change 3 / ((coupling 1 one_pos.le).drive * profileMass) *
    (coupling 1 one_pos.le).drive * profileMass = 3
  field_simp [ne_of_gt drive_pos, ne_of_gt profileMass_pos]

/-! Regression specifications, first run before the declarations existed. -/

example : 0 < (coupling 1 one_pos.le).drive := drive_pos
example : (coupling 1 one_pos.le).energy 0 ≠ (coupling 1 one_pos.le).energy 1 := energy_moves
example : idle.density = fun _ => 0 := idle_density
example : (coupling 1 one_pos.le).continuumLimit <
    (coupling 2 (by norm_num)).continuumLimit := gain_matters
example : flat.energy 0 ≠ (coupling 1 one_pos.le).energy 0 := profile_matters
example : normalized.continuumLimit = 3 := normalized_limit

#print axioms ActuatedCoupling.actuated_coarseGrains
#print axioms ActuatedCoupling.actuated_limit_le_of_drive_le
#print axioms drive_pos
#print axioms energy_moves
#print axioms idle_density
#print axioms gain_matters
#print axioms profile_matters
#print axioms normalized_limit

end PhysicsOfConsciousness.Examples.ActuatedField
