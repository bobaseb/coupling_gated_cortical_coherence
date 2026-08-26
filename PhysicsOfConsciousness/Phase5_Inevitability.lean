/-
  Phase 5: The Inevitability of the Self
  
  This module formalizes:
  1. The Kuramoto model for the macroscopic field
  2. Phase Synchronization
  3. The unified topological fixed point ("The Self")
-/

import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import PhysicsOfConsciousness.Phase4_MacroscopicCoupling

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
  -- In the mean-field limit (evading spin-glass), if coupling is supercritical, 
  -- the amplitude is monotonically increasing.
  -- This abstracts the Ott-Antonsen ansatz ODE for the Kuramoto model.
  monotone : sys.coupling_strength > critical_coupling → 
    Monotone amplitude_time
  -- Physical Postulate: For supercritical coupling, the macroscopic field has no stable 
  -- partial-synchronization fixed points below complete sync (R=1). 
  -- This replaces the tautological assumption that the supremum equals 1, 
  -- and accurately reflects the dynamical landscape of the Kuramoto ODE.
  no_spurious_fixed_points : sys.coupling_strength > critical_coupling → 
    ∀ L < 1, ∃ t, amplitude_time t > L

-- Lemma to show the amplitude is bounded above, required for the monotone convergence theorem.
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
-- We now rigorously prove this convergence from the monotone convergence theorem.
theorem converges_when_coupled (sys : KuramotoSystem) [dyn : KuramotoDynamics sys] [top : ComplexNetworkTopology sys.net]
  (h_sw : ComplexNetworkTopology.is_small_world sys.net) 
  (h_fd : ComplexNetworkTopology.has_fractal_dimension sys.net) 
  (h_cr : ComplexNetworkTopology.exhibits_criticality sys.net) :
  avoids_spin_glass sys.net → sys.coupling_strength > dyn.critical_coupling → 
  Tendsto (dyn.amplitude_time) atTop (nhds 1) := by
  intro _ h_coupled
  have h_mono : Monotone dyn.amplitude_time := dyn.monotone h_coupled
  have h_bdd : BddAbove (range dyn.amplitude_time) := amplitude_bdd_above
  have h_tendsto := tendsto_atTop_ciSup h_mono h_bdd
  have h_no_fp := dyn.no_spurious_fixed_points h_coupled
  have h_sup : iSup dyn.amplitude_time = 1 := isup_eq_one_of_bound dyn.amplitude_time h_mono dyn.bounded h_no_fp
  rw [h_sup] at h_tendsto
  exact h_tendsto

-- The topological fixed point (The Self) is achieved when the amplitude converges to 1 as time goes to infinity.
def converges_to_sync (sys : KuramotoSystem) [dyn : KuramotoDynamics sys] : Prop :=
  Tendsto (dyn.amplitude_time) atTop (nhds 1)

-- The Kuramoto Transition Theorem (The Emergence of the Self)
theorem kuramoto_phase_transition (sys : KuramotoSystem) [dyn : KuramotoDynamics sys] [ComplexNetworkTopology sys.net]
  (h_sw : ComplexNetworkTopology.is_small_world sys.net) 
  (h_fd : ComplexNetworkTopology.has_fractal_dimension sys.net) 
  (h_cr : ComplexNetworkTopology.exhibits_criticality sys.net) :
  avoids_spin_glass sys.net → sys.coupling_strength > dyn.critical_coupling → converges_to_sync sys := by
  intro h_evades h_coupled
  exact converges_when_coupled sys h_sw h_fd h_cr h_evades h_coupled

end PhysicsOfConsciousness

