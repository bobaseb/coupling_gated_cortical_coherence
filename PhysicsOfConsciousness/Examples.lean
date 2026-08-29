/-
  Examples.lean — Non-vacuity witnesses

  Every physical postulate in this development is now carried as a *class field*
  rather than a standalone `axiom` (see `Axioms.lean` §5 for why: the standalone
  formulations were inconsistent). That change is only an improvement if the
  classes can actually be inhabited — an uninhabitable class makes every theorem
  about it vacuously true, which is no better than an inconsistent axiom.

  This file discharges that obligation for the finite-state parts of the theory
  by exhibiting concrete instances.

  **Coverage.**
    ✓ `StatisticalMechanics` — a one-bit erasure model with a genuine bath.
    ✓ `StructuralResonance`  — a perfectly-resonant system (KL = 0).
    ✓ `ActionPrinciples`     — a scalar field on a one-point spacetime.
    ✗ `LocalSectionSynchronization` / `ThermodynamicCover` — NOT witnessed.
      These require constructing sections of the sheafified probability presheaf,
      which is substantial work. Until an instance exists, `overlap_agreement`
      and `global_section_from_thermodynamics` are conditional on structures not
      yet shown to exist. This is the largest open gap in the formalization.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_KLBound

open MeasureTheory

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

/-! ## 2. A perfectly resonant system -/

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

/-! ## 3. A scalar field on a one-point spacetime -/

/-- `V v = v²`, minimised at `v = 0`. Spacetime is a single point carrying the
    Dirac probability measure, so `∫ V (phi x) = V (phi ())`. -/
noncomputable instance unitAction :
    ActionPrinciples Unit ℝ (fun _ => 0) (fun phi => ∫ x, (phi x)^2 ∂(Measure.dirac ()))
      (fun phi => ∫ x, (phi x)^2 ∂(Measure.dirac ())) (fun v => v^2) (Measure.dirac ()) where
  total_eq := by intro phi; simp
  kinetic_nonneg := by intro phi; norm_num
  kinetic_const := by intro v; rfl
  potential_integral := by intro phi; rfl
  potential_integrable := by
    intro phi
    exact Integrable.of_finite

/-- The one-point spacetime really does witness the vacuum theorem: the constant
    zero field minimises the energy, and lands in the vacuum manifold. -/
example : (0 : ℝ) ∈ DynamicalVacuum (fun v : ℝ => v^2) := by
  intro v'
  simpa using sq_nonneg v'

end Examples
end PhysicsOfConsciousness
