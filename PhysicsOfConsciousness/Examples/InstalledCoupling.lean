import PhysicsOfConsciousness.Phase9_InstalledCoupling
import PhysicsOfConsciousness.Examples.MicroscopicCoupling

/-!
# Pricing the thermal switch's installed mode

The existing profile has mass 2 and unit price, fixing the sharp conversion
factor κ = 4 independently of the unit diffusion. Configuration laws with
agreement probabilities 1/4, 1/2 and 3/4 give coupling strengths 1, 2 and 3.
The first two are excluded by K3, including its boundary. A dearer half-filled
mode rejects the converse. Negative prices, an underpriced spatial mode,
threshold-fitted conversion and signed occupancies fence the hypotheses.

These are declared hardware and scalar mean-field witnesses, not simulations
or a physical field identification.
-/

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness.Examples.InstalledCoupling

open ThermalAgency MicroscopicCoupling

/-- The declared response profile's substrate mass. Profile and substrate only. -/
theorem profileMass : (∫ x : unitInterval, 4 / 3 * (1 + (x : ℝ))) = 2 := by
  rw [integral_const_mul, integral_one_add]
  norm_num

theorem modeMass_installed : installed.modeMass () = 2 := profileMass

/-- κ = 4, read off the profile's mass and the mode's price. -/
noncomputable def priced : PricedArrangement unitInterval Bool Bool Unit where
  toKernelArrangement := installed
  couplingPerEnergy := 4
  couplingPerEnergy_pos := by norm_num
  occupancy_nonneg z _ := by
    show (0 : ℝ) ≤ if z.1 = z.2 then 1 else 0
    split <;> norm_num
  mode_priced _ := by
    show installed.modeMass () ^ 2 ≤ 4 * hardware.price ()
    rw [modeMass_installed]; norm_num [hardware]

/-- The same hardware, holding the law it sat in *before* the channel executed. -/
noncomputable def unpowered : PricedArrangement unitInterval Bool Bool Unit where
  toKernelArrangement := { installed with law := actuation.initial }
  couplingPerEnergy := 4
  couplingPerEnergy_pos := by norm_num
  occupancy_nonneg z _ := by
    show (0 : ℝ) ≤ if z.1 = z.2 then 1 else 0
    split <;> norm_num
  mode_priced _ := by
    show installed.modeMass () ^ 2 ≤ 4 * hardware.price ()
    rw [modeMass_installed]; norm_num [hardware]

theorem installedEnergy_priced : priced.installedEnergy = 3 / 4 := by
  show (∑ z, actuation.final.p z * hardware.storedEnergy z) = 3 / 4
  rw [actuation_final]
  norm_num [LocalActuator.storedEnergy, hardware, correlated,
    Fintype.sum_prod_type, Fintype.sum_bool]

theorem installedEnergy_unpowered : unpowered.installedEnergy = 1 / 2 := by
  show (∑ z, actuation.initial.p z * hardware.storedEnergy z) = 1 / 2
  norm_num [LocalActuator.storedEnergy, hardware, actuation, independent,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- A phase field of unit noise carrying a supplied kernel. -/
noncomputable def fieldOf (K : unitInterval → unitInterval → ℝ) :
    StochasticNeuralField unitInterval :=
  ⟨⟨fun _ => (0 : ℝ), K, (0 : ℝ)⟩, 1, one_pos, (0 : ℝ)⟩

/-- The field whose kernel is the one the hardware carried before the channel. -/
noncomputable def subcriticalField : StochasticNeuralField unitInterval :=
  fieldOf unpowered.kernel

/-- The field whose kernel is the one the executed channel installed. -/
noncomputable def installedField : StochasticNeuralField unitInterval :=
  fieldOf priced.kernel

/-- K3 at the threshold itself: no growing Fourier mode or nonzero stationary
mean. Marginality of the first harmonic does not imply strict decay. -/
theorem unpowered_no_coherence :
    ¬ exhibits_phase_transition subcriticalField ∧
    (∀ r : ℝ, 0 ≤ r → r = selfConsistency (mean_field_coupling subcriticalField)
        subcriticalField.D r → r = 0) ∧
    ¬ ∃ n : ℕ, 0 < n ∧
      0 < FokkerPlanck.incoherentRate subcriticalField.D
        (mean_field_coupling subcriticalField) n := by
  refine unpowered.no_coherence_of_installedEnergy subcriticalField rfl rfl ?_
  rw [installedEnergy_unpowered]
  show (4 : ℝ) * (1 / 2) ≤ critical_coupling 1
  rw [critical_coupling]; norm_num

/-- A prepared law with agreement probability 1/4; no preparation mechanism
or preparation cost is inferred from the probability law. -/
noncomputable def belowLaw : ProbDist (Bool × Bool) where
  p z := if z.1 = z.2 then 1 / 8 else 3 / 8
  nonneg _ := by split <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- Strictly below threshold on the original hardware, changing only its law. -/
noncomputable def below : PricedArrangement unitInterval Bool Bool Unit :=
  { priced with law := belowLaw }

noncomputable def belowField : StochasticNeuralField unitInterval := fieldOf below.kernel

theorem below_installedEnergy : below.installedEnergy = 1 / 4 := by
  norm_num [KernelArrangement.installedEnergy, below, priced, installed,
    LocalActuator.storedEnergy, hardware, belowLaw, Fintype.sum_prod_type, Fintype.sum_bool]

theorem below_line : below.couplingPerEnergy * below.installedEnergy < critical_coupling 1 := by
  rw [below_installedEnergy]
  norm_num [below, priced, critical_coupling]

theorem below_no_coherence : ¬ exhibits_phase_transition belowField :=
  (below.no_coherence_of_installedEnergy belowField rfl rfl below_line.le).1

/-! ### The other side of the line, where the theorem is silent -/

theorem meanField_installedField : mean_field_coupling installedField = 3 := by
  rw [← installed.continuumEnergy_eq_mean_field_coupling installedField rfl rfl]
  exact installed_continuumEnergy

theorem installed_above_line :
    critical_coupling installedField.D < priced.couplingPerEnergy * priced.installedEnergy := by
  rw [installedEnergy_priced]
  show critical_coupling (1 : ℝ) < 4 * (3 / 4)
  rw [critical_coupling]; norm_num

theorem installed_exhibits : exhibits_phase_transition installedField := by
  rw [exhibits_phase_transition, meanField_installedField]
  show (3 : ℝ) > critical_coupling 1
  rw [critical_coupling]; norm_num

/-! ### Rejections -/

/-- An arrangement with the same profile, a dearer mode and a half occupancy. -/
noncomputable def slackHardware : LocalActuator unitInterval Bool Bool Unit where
  occupancy _ _ := 1 / 2
  profile _ x := 4 / 3 * (1 + (x : ℝ))
  price _ := 2

noncomputable def slack : PricedArrangement unitInterval Bool Bool Unit where
  toKernelArrangement :=
    { actuator := slackHardware
      profile_continuous := fun _ =>
        continuous_const.mul (continuous_const.add continuous_subtype_val)
      law := actuation.final
      volume := volume
      grid := mesh
      refines := mesh_refines }
  couplingPerEnergy := 4
  couplingPerEnergy_pos := by norm_num
  occupancy_nonneg _ _ := by norm_num [slackHardware]
  mode_priced _ := by
    show (∫ x : unitInterval, 4 / 3 * (1 + (x : ℝ))) ^ 2 ≤ 4 * (2 : ℝ)
    rw [profileMass]; norm_num

theorem slack_modeMass : ∀ i, slack.toKernelArrangement.modeMass i = 2 :=
  fun _ => profileMass

theorem slack_continuumEnergy : slack.toKernelArrangement.continuumEnergy = 2 := by
  rw [KernelArrangement.continuumEnergy_eq_modes]
  simp only [slack_modeMass]
  show (∑ z, actuation.final.p z *
    ∑ i, slackHardware.occupancy z i * (2 : ℝ) ^ 2) = 2
  rw [actuation_final]
  norm_num [slackHardware, correlated, Fintype.sum_prod_type, Fintype.sum_bool]

theorem slack_installedEnergy : slack.installedEnergy = 1 := by
  show (∑ z, actuation.final.p z * slackHardware.storedEnergy z) = 1
  rw [actuation_final]
  norm_num [LocalActuator.storedEnergy, slackHardware, correlated,
    Fintype.sum_prod_type, Fintype.sum_bool]

noncomputable def slackField : StochasticNeuralField unitInterval := fieldOf slack.kernel

/-- **The converse is rejected.** -/
theorem converse_rejected :
    critical_coupling slackField.D < slack.couplingPerEnergy * slack.installedEnergy ∧
    ¬ exhibits_phase_transition slackField := by
  constructor
  · rw [slack_installedEnergy]
    show critical_coupling (1 : ℝ) < 4 * 1
    rw [critical_coupling]; norm_num
  · rw [exhibits_phase_transition,
      ← slack.toKernelArrangement.continuumEnergy_eq_mean_field_coupling slackField rfl rfl,
      slack_continuumEnergy]
    show ¬ ((2 : ℝ) > critical_coupling 1)
    rw [critical_coupling]; norm_num

/-- A conversion factor forcing exclusion of the executed arrangement fails
the mode condition. This does not enforce the time at which κ was chosen. -/
theorem fitted_couplingPerEnergy_rejected {κ : ℝ}
    (h : ∀ i, installed.modeMass i ^ 2 ≤ κ * hardware.price i) :
    critical_coupling installedField.D < κ * priced.installedEnergy := by
  have h4 : (4 : ℝ) ≤ κ := by
    have hi := h ()
    rw [modeMass_installed] at hi
    norm_num [hardware] at hi; linarith
  rw [installedEnergy_priced]
  show critical_coupling (1 : ℝ) < κ * (3 / 4)
  rw [critical_coupling]; linarith

/-- The spatial mass of the existing mode exceeds the share allowed by κ = 3.
This directly rejects a factor smaller than the hardware permits. -/
theorem underpriced_mode_rejected :
    ¬ (installed.modeMass () ^ 2 ≤ (3 : ℝ) * hardware.price ()) := by
  rw [modeMass_installed]
  norm_num [hardware]

/-- **A negative price is rejected**: no nonnegative κ prices a mode of positive
spatial mass against it. -/
theorem negative_price_rejected {κ : ℝ} (hκ : 0 ≤ κ) :
    ¬ (installed.modeMass () ^ 2 ≤ κ * (-1 : ℝ)) := by
  rw [modeMass_installed]
  intro h
  nlinarith

/-- The original mode plus a zero-response mode with negative occupancy.
The extra mode subtracts stored energy without subtracting coupling. -/
noncomputable def negativeHardware : LocalActuator unitInterval Bool Bool Bool where
  occupancy _ i := if i then -1 else 1
  profile i x := if i then 0 else 4 / 3 * (1 + (x : ℝ))
  price _ := 1

noncomputable def negative : KernelArrangement unitInterval Bool Bool Bool where
  actuator := negativeHardware
  profile_continuous i := by
    cases i
    · exact continuous_const.mul (continuous_const.add continuous_subtype_val)
    · exact continuous_const
  law := actuation.final
  volume := volume
  grid := mesh
  refines := mesh_refines

theorem negative_modeMass (i : Bool) : negative.modeMass i = if i then 0 else 2 := by
  cases i
  · exact profileMass
  · simp [KernelArrangement.modeMass, negative, negativeHardware]

theorem negative_continuumEnergy : negative.continuumEnergy = 4 := by
  rw [KernelArrangement.continuumEnergy_eq_modes]
  simp only [negative_modeMass]
  show (∑ z, actuation.final.p z *
    ∑ i, negativeHardware.occupancy z i * (if i then 0 else (2 : ℝ)) ^ 2) = 4
  rw [actuation_final]
  norm_num [negativeHardware, correlated, Fintype.sum_prod_type, Fintype.sum_bool]

theorem negative_installedEnergy : negative.installedEnergy = 0 := by
  show (∑ z, actuation.final.p z * negativeHardware.storedEnergy z) = 0
  simp [LocalActuator.storedEnergy, negativeHardware]

/-- **A negative occupancy is rejected**: the mode condition still holds at the
declared κ, and the bound of K2 is false. -/
theorem negative_occupancy_rejected :
    (∀ i, negative.modeMass i ^ 2 ≤ 4 * negativeHardware.price i) ∧
    4 * negative.installedEnergy < negative.continuumEnergy := by
  constructor
  · intro i
    rw [negative_modeMass i]
    cases i <;> norm_num [negativeHardware]
  · rw [negative_continuumEnergy, negative_installedEnergy]
    norm_num

/-- Dropping nonnegative occupancies invalidates the no-go itself: the energy
test passes at zero stored energy, but the same kernel has supercritical mean 4.
The mode-price condition still holds, as `negative_occupancy_rejected` records. -/
theorem negative_occupancy_no_go_rejected :
    (¬ ∀ z i, 0 ≤ negativeHardware.occupancy z i) ∧
    4 * negative.installedEnergy ≤ critical_coupling 1 ∧
    exhibits_phase_transition (fieldOf negative.kernel) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := h (false, false) true
    norm_num [negativeHardware] at this
  · rw [negative_installedEnergy, critical_coupling]
    norm_num
  · rw [exhibits_phase_transition,
      ← negative.continuumEnergy_eq_mean_field_coupling (fieldOf negative.kernel) rfl rfl,
      negative_continuumEnergy]
    norm_num [fieldOf, critical_coupling]

/-- The bound of K2 is attained on the executed arrangement: with one mode, a κ
declared from the profile's mass and the mode's price leaves no slack. -/
theorem installed_bound_tight :
    priced.toKernelArrangement.continuumEnergy =
      priced.couplingPerEnergy * priced.installedEnergy := by
  rw [installedEnergy_priced]
  show installed.continuumEnergy = 4 * (3 / 4)
  rw [installed_continuumEnergy]
  norm_num

#print axioms unpowered_no_coherence
#print axioms below_no_coherence
#print axioms converse_rejected
#print axioms negative_occupancy_no_go_rejected

end PhysicsOfConsciousness.Examples.InstalledCoupling

open MeasureTheory
open PhysicsOfConsciousness PhysicsOfConsciousness.Examples.MicroscopicCoupling

-- Retained specification: K1's Fubini identity on the existing hardware.
example (sys : StochasticNeuralField unitInterval) (hker : sys.K = installed.kernel) :
    installed.continuumEnergy = mean_field_coupling sys := by
  exact installed.continuumEnergy_eq_mean_field_coupling sys rfl hker

-- K2 must price the arrangement's actual expected stored energy.
example (A : PricedArrangement unitInterval Bool Bool Unit) :
    A.toKernelArrangement.continuumEnergy ≤ A.couplingPerEnergy * A.installedEnergy :=
  A.continuumEnergy_le_installedEnergy

example (A : PricedArrangement unitInterval Bool Bool Unit) :
    0 < A.couplingPerEnergy := A.couplingPerEnergy_pos

-- K3 carries the no-go to an actual self-consistent stationary density.
example (A : PricedArrangement unitInterval Bool Bool Unit)
    (sys : StochasticNeuralField unitInterval) (hvol : A.volume = volume)
    (hker : sys.K = A.kernel)
    (hU : A.couplingPerEnergy * A.installedEnergy ≤ critical_coupling sys.D)
    {r : ℝ} (hr : 0 ≤ r) {ρ : ℝ → ℝ}
    (hstat : FokkerPlanck.IsStationary sys.D
      (FokkerPlanck.drift (mean_field_coupling sys) r) ρ)
    (hmean : circularOrderParameter ρ = (r : ℂ)) :
    r = 0 ∧ ρ = vonMisesDensity 0 :=
  A.stationary_eq_incoherent_of_installedEnergy sys hvol hker hU hr hstat hmean

-- K4 must cover strict subcriticality as well as the boundary and converse.
example : Examples.InstalledCoupling.below.couplingPerEnergy *
    Examples.InstalledCoupling.below.installedEnergy < critical_coupling 1 :=
  Examples.InstalledCoupling.below_line

example : ¬ exhibits_phase_transition Examples.InstalledCoupling.belowField :=
  Examples.InstalledCoupling.below_no_coherence

example : ¬ (installed.modeMass () ^ 2 ≤ (3 : ℝ) * hardware.price ()) :=
  Examples.InstalledCoupling.underpriced_mode_rejected

example : critical_coupling Examples.InstalledCoupling.slackField.D <
    Examples.InstalledCoupling.slack.couplingPerEnergy *
      Examples.InstalledCoupling.slack.installedEnergy ∧
    ¬ exhibits_phase_transition Examples.InstalledCoupling.slackField :=
  Examples.InstalledCoupling.converse_rejected
