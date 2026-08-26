import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import test_phase4

open Filter Topology Set

namespace PhysicsOfConsciousness

-- The Macroscopic field acts as a system of coupled non-linear oscillators.
-- K is the global coupling strength.
structure KuramotoSystem where
  net : DissipativeNetwork
  field : MacroField
  coupling_strength : Real

-- We define the time evolution of the macroscopic order parameter (amplitude)
class KuramotoDynamics (sys : KuramotoSystem) where
  critical_coupling : Real
  amplitude_time : Real → Real
  -- The order parameter is physically bounded between 0 and 1
  bounded : ∀ t, amplitude_time t ≤ 1
  -- For synchronization to emerge, we assume a small non-zero initial seed
  pos : ∀ t, 0 < amplitude_time t
  -- The ODE governing the macroscopic amplitude (Ott-Antonsen ansatz)
  deriv : ∀ t, HasDerivAt amplitude_time ((sys.coupling_strength - critical_coupling) * amplitude_time t * (1 - amplitude_time t)) t

lemma kuramoto_monotone (sys : KuramotoSystem) [dyn : KuramotoDynamics sys]
  (h_coupled : sys.coupling_strength > dyn.critical_coupling) :
  Monotone dyn.amplitude_time := by
  apply monotone_of_hasDerivAt_nonneg dyn.deriv
  intro t
  have h1 : 0 ≤ sys.coupling_strength - dyn.critical_coupling := by linarith
  have h2 : 0 ≤ dyn.amplitude_time t := le_of_lt (dyn.pos t)
  have h3 : 0 ≤ 1 - dyn.amplitude_time t := by
    have h4 := dyn.bounded t
    linarith
  positivity

lemma kuramoto_no_spurious_fixed_points (sys : KuramotoSystem) [dyn : KuramotoDynamics sys]
  (h_coupled : sys.coupling_strength > dyn.critical_coupling) :
  ∀ L < 1, ∃ t, dyn.amplitude_time t > L := by
  intro L hL
  by_contra h_all
  have h_all_le : ∀ t, dyn.amplitude_time t ≤ L := fun t => not_lt.mp (fun ht => h_all ⟨t, ht⟩)
  
  set K_diff := sys.coupling_strength - dyn.critical_coupling
  have h_K_diff : 0 < K_diff := by linarith
  have h_pos0 : 0 < dyn.amplitude_time 0 := dyn.pos 0
  have h_gap : 0 < 1 - L := by linarith
  set C := K_diff * dyn.amplitude_time 0 * (1 - L)
  have hC : 0 < C := mul_pos (mul_pos h_K_diff h_pos0) h_gap
  
  set f := dyn.amplitude_time
  set f' := fun t => K_diff * f t * (1 - f t)
  
  have h_mono : Monotone f := kuramoto_monotone sys h_coupled
  
  set b := (1 - f 0) / C + 1
  have hab : 0 < b := by
    have h_num : 0 ≤ 1 - f 0 := by
      have h4 := dyn.bounded 0
      linarith
    have h_div : 0 ≤ (1 - f 0) / C := div_nonneg h_num (le_of_lt hC)
    linarith
    
  have hfc : ContinuousOn f (Icc 0 b) := by
    intro x _
    exact (dyn.deriv x).continuousAt.continuousWithinAt
  have hff' : ∀ x ∈ Ioo 0 b, HasDerivAt f (f' x) x := by
    intro x _
    exact dyn.deriv x
    
  have h_mvt := exists_hasDerivAt_eq_slope f f' hab hfc hff'
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  
  have hc_pos : 0 ≤ c := le_of_lt hc.1
  have h_fc_ge : f 0 ≤ f c := h_mono hc_pos
  
  have h_f'c_ge : C ≤ f' c := by
    have p1 : K_diff * f 0 ≤ K_diff * f c := mul_le_mul_of_nonneg_left h_fc_ge (le_of_lt h_K_diff)
    have p2 : 1 - L ≤ 1 - f c := by
      have h_f_le_L := h_all_le c
      linarith
    have p3 : K_diff * f 0 * (1 - L) ≤ K_diff * f c * (1 - L) := mul_le_mul_of_nonneg_right p1 (le_of_lt h_gap)
    have p4 : K_diff * f c * (1 - L) ≤ K_diff * f c * (1 - f c) := by
      apply mul_le_mul_of_nonneg_left p2
      have h_pos_c : 0 ≤ f c := le_of_lt (dyn.pos c)
      exact mul_nonneg (le_of_lt h_K_diff) h_pos_c
    exact le_trans p3 p4
    
  have h_b_mul : C * b ≤ f' c * b := mul_le_mul_of_nonneg_right h_f'c_ge (le_of_lt hab)
  
  have h_slope : f' c * b = f b - f 0 := by
    have h_b_ne_0 : b ≠ 0 := ne_of_gt hab
    calc f' c * b = ((f b - f 0) / (b - 0)) * b := by rw [hc_eq]
      _ = ((f b - f 0) / b) * b := by rw [sub_zero]
      _ = f b - f 0 := div_mul_cancel₀ (f b - f 0) h_b_ne_0
      
  rw [h_slope] at h_b_mul
  
  have h_Cb : C * b = 1 - f 0 + C := by
    calc C * b = C * ((1 - f 0) / C + 1) := rfl
      _ = C * ((1 - f 0) / C) + C * 1 := mul_add C _ 1
      _ = 1 - f 0 + C := by
        have hC_ne_0 : C ≠ 0 := ne_of_gt hC
        rw [mul_div_cancel₀ _ hC_ne_0, mul_one]
        
  rw [h_Cb] at h_b_mul
  
  have h_fb_ge : 1 + C ≤ f b := by linarith
  have h_fb_le : f b ≤ 1 := dyn.bounded b
  linarith

-- Lemma to show the amplitude is bounded above
lemma amplitude_bdd_above {sys : KuramotoSystem} [dyn : KuramotoDynamics sys] :
  BddAbove (range dyn.amplitude_time) := by
  use 1
  rintro _ ⟨t, rfl⟩
  exact dyn.bounded t

lemma isup_eq_one_of_bound (f : Real → Real) (h_mono : Monotone f) (h_bdd : ∀ t, f t ≤ 1) 
  (h_no_fp : ∀ L < 1, ∃ t, f t > L) : 
  iSup f = 1 := by
  apply le_antisymm
  · apply ciSup_le
    intro t
    exact h_bdd t
  · by_contra hc
    have h_lt : iSup f < 1 := not_le.mp hc
    have ⟨t, ht⟩ := h_no_fp (iSup f) h_lt
    have h_le : f t ≤ iSup f := le_ciSup (by
      use 1
      rintro _ ⟨t, rfl⟩
      exact h_bdd t
    ) t
    linarith

-- The core physical law: the amplitude strictly converges to 1 (sync) if coupling exceeds critical threshold,
-- provided the network topology successfully evades the spin glass phase.
theorem converges_when_coupled (sys : KuramotoSystem) [dyn : KuramotoDynamics sys]
  (h_sw : is_small_world sys.net) 
  (h_fd : ∃ d, has_fractal_dimension sys.net d) 
  (h_cr : exhibits_criticality sys.net) :
  (∀ (energy_landscape : MicroState sys.net → Real), ¬ is_spin_glass sys.net energy_landscape) → 
  sys.coupling_strength > dyn.critical_coupling → 
  Tendsto (dyn.amplitude_time) atTop (nhds 1) := by
  intro _ h_coupled
  have h_mono : Monotone dyn.amplitude_time := kuramoto_monotone sys h_coupled
  have h_bdd : BddAbove (range dyn.amplitude_time) := amplitude_bdd_above
  have h_tendsto := tendsto_atTop_ciSup h_mono h_bdd
  have h_no_fp := kuramoto_no_spurious_fixed_points sys h_coupled
  have h_sup : iSup dyn.amplitude_time = 1 := isup_eq_one_of_bound dyn.amplitude_time h_mono dyn.bounded h_no_fp
  rw [h_sup] at h_tendsto
  exact h_tendsto

-- The topological fixed point (The Self) is achieved when the amplitude converges to 1 as time goes to infinity.
def converges_to_sync (sys : KuramotoSystem) [dyn : KuramotoDynamics sys] : Prop :=
  Tendsto (dyn.amplitude_time) atTop (nhds 1)

-- The Kuramoto Transition Theorem (The Emergence of the Self)
theorem kuramoto_phase_transition (sys : KuramotoSystem) [dyn : KuramotoDynamics sys]
  (h_sw : is_small_world sys.net) 
  (h_fd : ∃ d, has_fractal_dimension sys.net d) 
  (h_cr : exhibits_criticality sys.net) :
  (∀ (energy_landscape : MicroState sys.net → Real), ¬ is_spin_glass sys.net energy_landscape) → 
  sys.coupling_strength > dyn.critical_coupling → converges_to_sync sys := by
  intro h_evades h_coupled
  exact converges_when_coupled sys h_sw h_fd h_cr h_evades h_coupled

end PhysicsOfConsciousness
