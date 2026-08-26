import PhysicsOfConsciousness.Phase1_Primitives
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace PhysicsOfConsciousness

structure ExternalPerturbation where
  magnitude : Real

def is_erasure {sys : Type} (t : sys → sys) : Prop :=
  ¬ Function.Injective t

noncomputable def boltzmann_entropy {sys : Type} [DecidableEq sys] (states : Finset sys) : Real :=
  Real.log (states.card : Real)

noncomputable def entropy {sys : Type} [Fintype sys] [DecidableEq sys] (t : sys → sys) : Real :=
  boltzmann_entropy (Finset.image t Finset.univ)

class Thermodynamics (sys : Type) where
  heat_dissipation : (sys → sys) → Real
  temperature : Real
  temperature_pos : temperature > 0

class StatisticalMechanics (sys : Type) [Fintype sys] [DecidableEq sys] extends Thermodynamics sys where
  env_entropy_change : (sys → sys) → Real
  second_law : ∀ (t : sys → sys), env_entropy_change t + (entropy t - entropy (id : sys → sys)) ≥ 0
  heat_eq : ∀ (t : sys → sys), Thermodynamics.heat_dissipation t = temperature * env_entropy_change t

theorem landauer_bound {sys : Type} [Fintype sys] [DecidableEq sys] [StatisticalMechanics sys] :
  ∀ (t : sys → sys), Thermodynamics.heat_dissipation (sys := sys) t ≥ Thermodynamics.temperature (sys := sys) * (entropy (id : sys → sys) - entropy t) := by
  intro t
  rw [StatisticalMechanics.heat_eq]
  have h2 : Thermodynamics.temperature (sys := sys) > 0 := Thermodynamics.temperature_pos
  have h_sec := StatisticalMechanics.second_law (sys := sys) t
  nlinarith

def heat_dissipation {sys : Type} [Thermodynamics sys] (t : sys → sys) : Real :=
  Thermodynamics.heat_dissipation t

lemma not_injective_image_card_lt {sys : Type} [Fintype sys] [DecidableEq sys] (t : sys → sys) (h : ¬ Function.Injective t) : 
  (Finset.image t Finset.univ).card < Fintype.card sys := by
  have h1 : (Finset.image t Finset.univ).card ≤ Fintype.card sys := Finset.card_image_le
  by_contra hc
  have heq : (Finset.image t Finset.univ).card = Fintype.card sys := le_antisymm h1 (not_lt.mp hc)
  have hsurj : Function.Surjective t := by
    have himage_eq_univ : Finset.image t Finset.univ = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le
      · intro x _ ; exact Finset.mem_univ x
      · rw [heq] ; rfl
    intro y
    have hy : y ∈ Finset.univ := Finset.mem_univ y
    rw [← himage_eq_univ] at hy
    rcases Finset.mem_image.mp hy with ⟨x, _, hx_eq⟩
    exact ⟨x, hx_eq⟩
  have hinj : Function.Injective t := Finite.injective_iff_surjective.mpr hsurj
  exact h hinj

theorem erasure_decreases_entropy {sys : Type} [Fintype sys] [DecidableEq sys] [Nonempty sys] (t : sys → sys) (h : is_erasure t) :
  entropy (id : sys → sys) > entropy t := by
  unfold entropy boltzmann_entropy
  have h_id_card : (Finset.image id (Finset.univ : Finset sys)).card = Fintype.card sys := by
    have himage : Finset.image id (Finset.univ : Finset sys) = Finset.univ := Finset.image_id
    rw [himage]
    rfl
  rw [h_id_card]
  have h_lt : (Finset.image t Finset.univ).card < Fintype.card sys := not_injective_image_card_lt t h
  have h_pos1 : (0 : Real) < ((Finset.image t Finset.univ).card : Real) := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    have ⟨x⟩ := ‹Nonempty sys›
    exact ⟨t x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  have h_pos2 : (0 : Real) < (Fintype.card sys : Real) := by
    apply Nat.cast_pos.mpr
    apply Fintype.card_pos
  exact Real.strictMonoOn_log h_pos1 h_pos2 (Nat.cast_lt.mpr h_lt)

theorem entropy_decrease_implies_heat {sys : Type} [Fintype sys] [DecidableEq sys] [StatisticalMechanics sys] (t : sys → sys) 
  (h : entropy (id : sys → sys) > entropy t) : heat_dissipation t > 0 := by
  have bound := landauer_bound (sys := sys) t
  have diff_pos : entropy (id : sys → sys) - entropy t > 0 := sub_pos.mpr h
  have rhs_pos : Thermodynamics.temperature (sys := sys) * (entropy (id : sys → sys) - entropy t) > 0 :=
    mul_pos (Thermodynamics.temperature_pos) diff_pos
  exact lt_of_lt_of_le rhs_pos bound

theorem landauers_principle {sys : Type} [Fintype sys] [DecidableEq sys] [Nonempty sys] [StatisticalMechanics sys] (t : sys → sys) :
  is_erasure t → heat_dissipation t > 0 := by
  intro h_erasure
  have h_entropy := erasure_decreases_entropy t h_erasure
  exact entropy_decrease_implies_heat t h_entropy

def is_dissipative_structure {sys : Type} [Thermodynamics sys] (t : sys → sys) : Prop :=
  heat_dissipation t > 0

theorem boundary_is_dissipative {sys : Type} [Fintype sys] [DecidableEq sys] [Nonempty sys] [StatisticalMechanics sys] (t : sys → sys) (h : is_erasure t) :
  is_dissipative_structure t := by
  exact landauers_principle t h

class PhysicalSystem (sys : Type) [DecidableEq sys] extends FinitePhaseSpace sys, StatisticalMechanics sys where
  volume : Real
  surface_tension : Real
  available_energy : Real

axiom strict_confining_potential {sys : Type} [DecidableEq sys] [PhysicalSystem sys] : PhysicalSystem.surface_tension (sys := sys) > 0

def is_integration_erasure {sys input : Type} (update : sys × input → sys) : Prop :=
  ¬ Function.Injective update

theorem pigeonhole_erasure {sys input : Type} [Fintype sys] [Fintype input] 
  (h_input : Fintype.card input > 1) (h_sys_pos : Fintype.card sys > 0)
  (update : sys × input → sys) : is_integration_erasure update := by
  intro h_inj
  have h_le := Fintype.card_le_of_injective update h_inj
  have h_prod : Fintype.card (sys × input) = Fintype.card sys * Fintype.card input := Fintype.card_prod sys input
  rw [h_prod] at h_le
  nlinarith

def expansion_cost {sys : Type} [DecidableEq sys] [PhysicalSystem sys] (delta_volume : Real) : Real :=
  delta_volume * (PhysicalSystem.surface_tension (sys := sys))

end PhysicsOfConsciousness
