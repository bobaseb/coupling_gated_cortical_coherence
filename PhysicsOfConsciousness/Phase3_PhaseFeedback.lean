import PhysicsOfConsciousness.Phase3_ObservationalLearning

/-!
# A phase state inside the register feedback process

One step reads the installed coupling from the register, evolves the retained
phase state, samples that new phase, then updates the same register. Noise is
part of the supplied phase and sensor channels. Joint laws retain correlations.
The resource account below is an explicit work-store ledger, not a heat theorem:
no local detailed balance, thermal calibration or phase-current cost is supplied.
-/
namespace PhysicsOfConsciousness.PhaseFeedback
open scoped BigOperators
variable {P R A O : Type*} [Fintype P] [Fintype R] [Fintype O] [DecidableEq P]

/-- The phase persists between updates. Sensor and learner cannot directly read
an unknown external parameter; this channel alone asserts no learning benefit. -/
noncomputable def transition (install : R → A) (evolve : A → P → ProbDist P)
    (sensor : P → ProbDist O) (update : O → R → ProbDist R)
    (z : P × R) : ProbDist (P × R) :=
  (evolve (install z.2) z.1).bind fun p =>
    (sensor p).bind fun o => (ProbDist.dirac p).prod (update o z.2)

/-- Expanded joint transition: phase evolution, observation and register update
all occur on the same path. This is finite probability bookkeeping, not LDB. -/
theorem transition_apply (install : R → A) (evolve : A → P → ProbDist P)
    (sensor : P → ProbDist O) (update : O → R → ProbDist R) (z z' : P × R) :
    (transition install evolve sensor update z).p z' =
      (evolve (install z.2) z.1).p z'.1 *
        ∑ o, (sensor z'.1).p o * (update o z.2).p z'.2 := by
  classical
  simp [transition, ProbDist.bind_apply, ProbDist.prod_apply, ProbDist.dirac_apply]

/-- Summing out the updated register leaves exactly the installed phase
channel. Sensing and learning change later phase steps through the register;
they do not retroactively change this step's evolved phase. This is a finite
channel identity, with no claim about a physical sensor implementation. -/
theorem transition_phase_marginal (install : R → A)
    (evolve : A → P → ProbDist P) (sensor : P → ProbDist O)
    (update : O → R → ProbDist R) (z : P × R) (p : P) :
    ∑ r' : R, (transition install evolve sensor update z).p (p, r') =
      (evolve (install z.2) z.1).p p := by
  classical
  simp_rw [transition_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ProbDist.sum_one, mul_one]
  rw [(sensor p).sum_one, mul_one]

/-- Iteration carries the full joint law; it never replaces it by its marginals. -/
noncomputable def law (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R)) : ℕ → ProbDist (P × R)
  | 0 => prior
  | n + 1 => (law prior channel n).bind channel

/-- Store balance after declared net work costs. Replenishment is explicit;
preparation is charged by the caller in the initial available store. -/
def store (initial : ℝ) (cost replenish : ℕ → ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => store initial cost replenish n + replenish n - cost n

/-- Pathwise ledger telescopes for any declared costs, including sensing,
reset and installation. Identifying those costs with a physical process is a
separate obligation; no heat is inferred from this identity. -/
theorem store_balance (initial : ℝ) (cost replenish : ℕ → ℝ) (n : ℕ) :
    store initial cost replenish n = initial +
      ∑ k ∈ Finset.range n, replenish k - ∑ k ∈ Finset.range n, cost k := by
  induction n with
  | zero => simp [store]
  | succ n ih => simp only [store, ih, Finset.sum_range_succ]; ring

/-- A finite unreplenished store cannot fund a prefix whose positive per-step
cost floor already exceeds it. This bounds feasible operation, not stopping
behavior of a controller that has not yet been equipped with a stop rule. -/
theorem finite_store_obstruction (initial ε : ℝ) (cost : ℕ → ℝ) (n : ℕ)
    (hcost : ∀ k < n, ε ≤ cost k) (hexhaust : initial < n * ε) :
    store initial cost (fun _ => 0) n < 0 := by
  rw [store_balance]
  have hsum : (n : ℝ) * ε ≤ ∑ k ∈ Finset.range n, cost k := by
    calc
      (n : ℝ) * ε = ∑ _k ∈ Finset.range n, ε := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk => hcost k (Finset.mem_range.mp hk)
  simp only [Finset.sum_const_zero, add_zero]
  linarith

#print axioms transition_apply
#print axioms transition_phase_marginal
#print axioms store_balance
#print axioms finite_store_obstruction
end PhysicsOfConsciousness.PhaseFeedback
