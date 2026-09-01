/-
  Phase 5 (continued): the lift obstruction measured around cortical phase
  singularities.

  `Phase5_TwistedGluing.lean` studies circle-valued offsets between patches. Any
  offsets obtained by subtracting absolute patch phases are a coboundary. The
  physical observable identified in F3 has a different type: experimental phase
  maps are locally unwrapped to real phases, and neighbouring unwraps can differ
  by an integer number of turns. Around an electrode loop those integer jumps
  sum to the measured winding number.

  This file formalizes the discrete loop calculation only. It neither constructs
  a Čech complex nor identifies winding with cognitive or phenomenal content.
-/
import PhysicsOfConsciousness.Phase5_TwistedGluing
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace PhysicsOfConsciousness

/-! ## Integer transitions on a measured loop -/

/-- The winding measured around a loop of `n + 1` overlapping phase patches.

Each integer records the number of full turns between two neighbouring local
real-valued phase lifts. Summing the transitions is the discrete winding number
used for an electrode loop around a phase singularity. -/
def loopWinding {n : ℕ} (transition : Fin (n + 1) → ℤ) : ℤ :=
  ∑ i, transition i

/-- **The loop transitions come from one globally consistent real lift.**

The first `n` equations relate consecutive vertices and the final equation
closes the loop. This is deliberately a predicate rather than a strengthened
data structure: the existence of a global lift is exactly what winding tests. -/
def HasGlobalLift {n : ℕ} (transition : Fin (n + 1) → ℤ) : Prop :=
  ∃ lift : ℕ → ℤ,
    (∀ i : Fin n, transition i.castSucc = lift i - lift (i + 1)) ∧
      transition (Fin.last n) = lift n - lift 0

/-- **A globally lifted phase has zero loop winding.**

The local integer transitions telescope around the closed loop. Consequently a
non-zero measured winding obstructs a single real-valued phase lift. This proves
only the discrete obstruction. It does not prove that a cortical singularity is
stable, dynamically generated, or a carrier of phenomenal content. -/
theorem loopWinding_eq_zero_of_hasGlobalLift {n : ℕ} {transition : Fin (n + 1) → ℤ}
    (h : HasGlobalLift transition) : loopWinding transition = 0 := by
  obtain ⟨lift, hedge, hclose⟩ := h
  rw [loopWinding, Fin.sum_univ_castSucc]
  simp_rw [hedge]
  rw [show (∑ i : Fin n, (lift i - lift (i + 1))) =
      lift 0 - lift n by
    calc
      _ = ∑ k ∈ Finset.range n, (lift k - lift (k + 1)) :=
        Fin.sum_univ_eq_sum_range (fun k => lift k - lift (k + 1)) n
      _ = lift 0 - lift n := Finset.sum_range_sub' lift n]
  rw [hclose]
  abel

/-- **Non-zero winding forbids a global real phase lift.**

This is the experimentally usable form: compute the integer winding from a
closed electrode loop; if it is non-zero, no choice of patchwise unwrapping can
make one global real phase on that loop. -/
theorem not_hasGlobalLift_of_loopWinding_ne_zero {n : ℕ}
    {transition : Fin (n + 1) → ℤ} (h : loopWinding transition ≠ 0) :
    ¬ HasGlobalLift transition :=
  fun hlift => h (loopWinding_eq_zero_of_hasGlobalLift hlift)

/-! ## A non-trivial three-electrode witness -/

/-- Three overlap transitions with one net turn around the loop. This is the
smallest discrete witness of the phase-singularity measurement: two adjacent
unwraps agree and the closing overlap crosses the branch cut once. -/
def threeElectrodeWinding : Fin 3 → ℤ :=
  ![0, 0, 1]

/-- The three-electrode witness has winding number one. -/
theorem threeElectrodeWinding_loopWinding : loopWinding threeElectrodeWinding = 1 := by
  decide

/-- The non-zero witness cannot arise from a global real-valued lift. -/
theorem threeElectrodeWinding_not_hasGlobalLift : ¬ HasGlobalLift threeElectrodeWinding :=
  not_hasGlobalLift_of_loopWinding_ne_zero (by rw [threeElectrodeWinding_loopWinding]; norm_num)

end PhysicsOfConsciousness
