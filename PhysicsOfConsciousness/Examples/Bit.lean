/-
  Examples/Bit.lean — one bit, with a bath, and the heat it pays

  §1 of the witnesses. It is on its own for the same reason
  `Examples/Cortex.lean` is: two later files stand on it. The erasure model
  inhabits `Thermodynamics`, `BipartiteEnvironment` and `StatisticalMechanics`
  on `Bool` with a genuine bath, so Landauer's heat equation is discharged by
  an instance rather than assumed; `Examples/Phase1.lean` §19 then measures the
  capacity of that same bit, and `Examples/Phase3.lean` §18 reads the
  predictive bound on it.
-/

import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_LandauerBridge

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 1. A one-bit erasure system satisfying Landauer's heat equation -/

/-- Temperature 1, and every operation dumps exactly `log 2` of heat — which is
    what `heat_eq` will force, given the bath below. -/
noncomputable instance boolThermo : Thermodynamics Bool where
  heat_dissipation := fun _ => Real.log 2
  temperature := 1
  temperature_pos := by norm_num

/-- The bath starts in one known state and ends anywhere in a two-state space:
    exactly one bit of bath entropy per operation.

    `U t` is a genuine bijection of `Bool × Bool`. It routes the system's state
    into the bath (`(s, false) ↦ (t false, s)`), which is what lets a
    non-injective `t` coexist with globally reversible dynamics — the Norton /
    Shenker point the manuscript makes in Derivation 2. -/
instance boolBath : BipartiteEnvironment Bool where
  bath := Bool
  dec_bath := inferInstance
  U := fun t p => (if p.2 = false then t false else !(t false), p.1)
  U_inj := by decide
  initial_bath := fun _ => {false}
  final_bath := fun _ => Finset.univ
  h_evolve := by
    intro t p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_singleton] at hq
    simp only [Finset.mem_product, Finset.mem_univ, and_true, hq.2]
    exact Finset.mem_image.mpr ⟨false, Finset.mem_univ _, rfl⟩
  h_bath_nonempty := fun _ => ⟨false, Finset.mem_singleton_self _⟩

noncomputable instance boolStatMech : StatisticalMechanics Bool where
  heat_eq := by
    intro t
    show Real.log 2 = 1 * (boltzmann_entropy (Finset.univ : Finset Bool)
                            - boltzmann_entropy ({false} : Finset Bool))
    simp [boltzmann_entropy]

/-- Sanity check: the general theory, applied to this instance, reproduces the
    expected physics — erasing a bit dissipates strictly positive heat. -/
example : heat_dissipation (fun _ => false : Bool → Bool) > 0 :=
  landauers_principle _ (by
    intro h
    exact absurd (h (a₁ := true) (a₂ := false) rfl) (by simp))

end Examples
end PhysicsOfConsciousness
