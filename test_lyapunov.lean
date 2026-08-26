import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import PhysicsOfConsciousness.Phase4_MacroscopicCoupling

open Finset Set Filter Topology

namespace PhysicsOfConsciousness

structure KuramotoSystem where
  net : DissipativeNetwork
  field : MacroField
  coupling_strength : Real
  intrinsic_freqs : Nat → Real

def is_kuramoto_trajectory (sys : KuramotoSystem) (theta : Real → Nat → Real) : Prop :=
  ∀ (i : Nat) (t : Real), 
    i < sys.net.nodes → 
    HasDerivAt (fun t => theta t i) 
      (sys.intrinsic_freqs i + (sys.coupling_strength / sys.net.nodes) * 
        ∑ j ∈ range sys.net.nodes, sys.net.coupling_matrix i j * Real.sin (theta t j - theta t i)) t

noncomputable def kuramoto_potential (sys : KuramotoSystem) (state : MicroState sys.net) : Real :=
  - (sys.coupling_strength / (2 * sys.net.nodes)) * 
    ∑ i ∈ range sys.net.nodes, ∑ j ∈ range sys.net.nodes, 
      sys.net.coupling_matrix i j * Real.cos (state j - state i)

lemma kuramoto_potential_derivative_identity (sys : KuramotoSystem) (theta : Real → Nat → Real) 
  (h_diff : ∀ i, i < sys.net.nodes → ∀ t, DifferentiableAt ℝ (fun t => theta t i) t) :
  ∀ t, HasDerivAt (fun t => kuramoto_potential sys (theta t)) 
       (- (sys.coupling_strength / (2 * sys.net.nodes)) * 
         ∑ i ∈ range sys.net.nodes, ∑ j ∈ range sys.net.nodes, sys.net.coupling_matrix i j * (- Real.sin (theta t j - theta t i)) * (deriv (fun t => theta t j) t - deriv (fun t => theta t i) t)) t := by
  intro t
  have h_sum : HasDerivAt (∑ i ∈ range sys.net.nodes, fun t => ∑ j ∈ range sys.net.nodes, sys.net.coupling_matrix i j * Real.cos (theta t j - theta t i)) 
                          (∑ i ∈ range sys.net.nodes, ∑ j ∈ range sys.net.nodes, sys.net.coupling_matrix i j * (- Real.sin (theta t j - theta t i)) * (deriv (fun t => theta t j) t - deriv (fun t => theta t i) t)) t := by
    apply HasDerivAt.sum
    intro i hi
    have h_sum2 : HasDerivAt (∑ j ∈ range sys.net.nodes, fun t => sys.net.coupling_matrix i j * Real.cos (theta t j - theta t i))
                             (∑ j ∈ range sys.net.nodes, sys.net.coupling_matrix i j * (- Real.sin (theta t j - theta t i)) * (deriv (fun t => theta t j) t - deriv (fun t => theta t i) t)) t := by
      apply HasDerivAt.sum
      intro j hj
      have h1 : HasDerivAt (fun t => theta t j - theta t i) (deriv (fun t => theta t j) t - deriv (fun t => theta t i) t) t := by
        apply HasDerivAt.sub
        · exact (h_diff j (mem_range.mp hj) t).hasDerivAt
        · exact (h_diff i (mem_range.mp hi) t).hasDerivAt
      have h2 := HasDerivAt.comp t (Real.hasDerivAt_cos (theta t j - theta t i)) h1
      have h3 := HasDerivAt.const_mul (sys.net.coupling_matrix i j) h2
      exact h3.congr_deriv (by ring)
    have h_eq : (∑ j ∈ range sys.net.nodes, fun t => sys.net.coupling_matrix i j * Real.cos (theta t j - theta t i)) = (fun t => ∑ j ∈ range sys.net.nodes, sys.net.coupling_matrix i j * Real.cos (theta t j - theta t i)) := by ext x; simp
    rw [h_eq] at h_sum2
    exact h_sum2
  have h_eq2 : (∑ i ∈ range sys.net.nodes, fun t => ∑ j ∈ range sys.net.nodes, sys.net.coupling_matrix i j * Real.cos (theta t j - theta t i)) = (fun t => ∑ i ∈ range sys.net.nodes, ∑ j ∈ range sys.net.nodes, sys.net.coupling_matrix i j * Real.cos (theta t j - theta t i)) := by ext x; simp
  rw [h_eq2] at h_sum
  have h_final := HasDerivAt.const_mul (- (sys.coupling_strength / (2 * sys.net.nodes))) h_sum
  exact h_final.congr_deriv (by ring)

end PhysicsOfConsciousness
