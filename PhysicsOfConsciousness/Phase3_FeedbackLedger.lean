import PhysicsOfConsciousness.Phase3_PhaseFeedback

/-!
# Path costs on the executed phase/register feedback process

The joint law retains phase/register correlations. Expected sensing and reset
prices and changes of installed-mode energy are charged to that law. The
balance includes preparation and replenishment. Prices are declared work costs,
not derived heat or probability-current cost; local detailed balance, a bath,
path support and a physical stop rule remain separate obligations.
-/

namespace PhysicsOfConsciousness.PhaseFeedback
open scoped BigOperators
variable {P R : Type*} [Fintype P] [Fintype R]

/-- The next joint law uses the installed coupling, evolved phase, sensor and
register update in that order. The phase is retained rather than marginalized. -/
theorem closed_loop_law_succ_apply {A O : Type*} [Fintype O] [DecidableEq P]
    (prior : ProbDist (P × R)) (install : R → A)
    (evolve : A → P → ProbDist P) (sensor : P → ProbDist O)
    (update : O → R → ProbDist R) (n : ℕ) (z' : P × R) :
    (law prior (transition install evolve sensor update) (n + 1)).p z' =
      ∑ z, (law prior (transition install evolve sensor update) n).p z *
        (evolve (install z.2) z.1).p z'.1 *
          ∑ o, (sensor z'.1).p o * (update o z.2).p z'.2 := by
  simp only [law, ProbDist.bind_apply, transition_apply]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The next phase marginal averages the installed evolution channel against
the current joint phase/register law. The current-step sensor and learner
affect later phases through the updated register; this identity alone does not
prove a performance benefit or a physical work cost. -/
theorem closed_loop_phase_marginal {A O : Type*} [Fintype O] [DecidableEq P]
    (prior : ProbDist (P × R)) (install : R → A)
    (evolve : A → P → ProbDist P) (sensor : P → ProbDist O)
    (update : O → R → ProbDist R) (n : ℕ) (p : P) :
    ∑ r' : R, (law prior (transition install evolve sensor update) (n + 1)).p (p, r') =
      ∑ z, (law prior (transition install evolve sensor update) n).p z *
        (evolve (install z.2) z.1).p p := by
  classical
  simp only [law, ProbDist.bind_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, transition_phase_marginal]


/-- Expected path cost under the actual joint law at update `n`. A price may
represent declared sensing, reset or installation work; heat needs a separate
reservoir model. -/
noncomputable def expectedPathCost (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R)) (price : (P × R) → (P × R) → ℝ)
    (n : ℕ) : ℝ :=
  ∑ z, ∑ z', (law prior channel n).p z * (channel z).p z' * price z z'

/-- Expected path cost is linear in declared stage prices. This uses the joint
law and transition at the same step, retaining their correlations. -/
theorem expectedPathCost_add (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R))
    (price₁ price₂ : (P × R) → (P × R) → ℝ) (n : ℕ) :
    expectedPathCost prior channel (fun z z' => price₁ z z' + price₂ z z') n =
      expectedPathCost prior channel price₁ n +
        expectedPathCost prior channel price₂ n := by
  unfold expectedPathCost
  have heq (z z' : P × R) :
      (law prior channel n).p z * (channel z).p z' *
        (price₁ z z' + price₂ z z') =
      (law prior channel n).p z * (channel z).p z' * price₁ z z' +
        (law prior channel n).p z * (channel z).p z' * price₂ z z' := by ring
  simp_rw [heq, Finset.sum_add_distrib]


/-- An installed mode's declared energy is read from the register in the same
joint law that the feedback channel evolves. No heat or mode-switch cost is
inferred from the energy alone. -/
noncomputable def installedEnergy (price : R → ℝ) (P : ProbDist (P × R)) : ℝ :=
  ∑ z, P.p z * price z.2

/-- The expected change of installed energy equals the path average of the
actual joint transition. This ties the installation ledger to the process;
other work channels and any physical heat law remain separate inputs. -/
theorem installation_energy_balance (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R)) (price : R → ℝ) (n : ℕ) :
    expectedPathCost prior channel (fun z z' => price z'.2 - price z.2) n =
      installedEnergy price (law prior channel (n + 1)) -
        installedEnergy price (law prior channel n) := by
  classical
  unfold expectedPathCost installedEnergy
  simp only [law, ProbDist.bind_apply]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hfirst : (∑ z, ∑ z', (law prior channel n).p z *
      (channel z).p z' * price z'.2) =
      ∑ z', (∑ z, (law prior channel n).p z * (channel z).p z') * price z'.2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z' _
    rw [Finset.sum_mul]
  have hsecond : (∑ z, ∑ z', (law prior channel n).p z *
      (channel z).p z' * price z.2) =
      ∑ z, (law prior channel n).p z * price z.2 := by
    apply Finset.sum_congr rfl
    intro z _
    calc
      (∑ z', (law prior channel n).p z * (channel z).p z' * price z.2) =
          ((law prior channel n).p z * price z.2) * (∑ z', (channel z).p z') := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z' _
            ring
      _ = (law prior channel n).p z * price z.2 := by rw [ProbDist.sum_one, mul_one]
  rw [hfirst, hsecond]

/-- Expected energy of a phase/register state. This can include phase energy
under the installed action as well as actuator mode energy; the value is a
declared state function, not a microscopic Hamiltonian derived here. -/
noncomputable def stateEnergy (energy : (P × R) → ℝ) (μ : ProbDist (P × R)) : ℝ :=
  ∑ z, μ.p z * energy z

/-- Changes of any declared state energy telescope on the executed joint law.
This is probability bookkeeping and does not itself identify work or heat. -/
theorem expected_state_energy_balance (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R)) (energy : (P × R) → ℝ) (n : ℕ) :
    expectedPathCost prior channel (fun z z' => energy z' - energy z) n =
      stateEnergy energy (law prior channel (n + 1)) -
        stateEnergy energy (law prior channel n) := by
  classical
  unfold expectedPathCost stateEnergy
  simp only [law, ProbDist.bind_apply]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hfirst : (∑ z, ∑ z', (law prior channel n).p z *
      (channel z).p z' * energy z') =
      ∑ z', (∑ z, (law prior channel n).p z * (channel z).p z') * energy z' := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z' _
    rw [Finset.sum_mul]
  have hsecond : (∑ z, ∑ z', (law prior channel n).p z *
      (channel z).p z' * energy z) =
      ∑ z, (law prior channel n).p z * energy z := by
    apply Finset.sum_congr rfl
    intro z _
    calc
      (∑ z', (law prior channel n).p z * (channel z).p z' * energy z) =
          ((law prior channel n).p z * energy z) * (∑ z', (channel z).p z') := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z' _
            ring
      _ = (law prior channel n).p z * energy z := by rw [ProbDist.sum_one, mul_one]
  rw [hfirst, hsecond]

/-- A supplied pathwise first-law identity yields an expected first-law
balance on the closed-loop process. The work and heat price functions must be
justified for a physical realization; this theorem does not derive local
detailed balance or assert that sensing/reset prices are bath heat. -/
theorem expected_first_law (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R))
    (energy : (P × R) → ℝ)
    (installation heat : (P × R) → (P × R) → ℝ) (n : ℕ)
    (hpath : ∀ z z', energy z' - energy z = installation z z' - heat z z') :
    expectedPathCost prior channel installation n -
      expectedPathCost prior channel heat n =
      stateEnergy energy (law prior channel (n + 1)) -
        stateEnergy energy (law prior channel n) := by
  calc
    expectedPathCost prior channel installation n -
        expectedPathCost prior channel heat n =
        expectedPathCost prior channel (fun z z' => installation z z' - heat z z') n := by
          unfold expectedPathCost
          simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ = expectedPathCost prior channel (fun z z' => energy z' - energy z) n := by
      congr 1
      funext z z'
      exact (hpath z z').symm
    _ = _ := expected_state_energy_balance prior channel energy n


/-- Installed-energy changes telescope on the actual evolving phase/register
law, even when the phase and register are correlated at every step. This is an
energy account, not a heat bound or a guarantee of available work. -/
theorem cumulative_installation_energy_balance (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R)) (price : R → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      expectedPathCost prior channel (fun z z' => price z'.2 - price z.2) n) =
      installedEnergy price (law prior channel N) - installedEnergy price prior := by
  induction N with
  | zero => simp [law]
  | succ N ih =>
    rw [Finset.sum_range_succ, installation_energy_balance, ih]
    change installedEnergy price (law prior channel N) - installedEnergy price prior +
      (installedEnergy price (law prior channel (N + 1)) -
        installedEnergy price (law prior channel N)) = _
    ring

/-- Stage prices for sensing, reset, and installed-mode energy change. These
prices are declared externally; the channel does not imply thermal costs. -/
def totalStagePrice {A : Type*} (install : R → A) (modePrice : A → ℝ)
    (sense reset : (P × R) → (P × R) → ℝ) (z z' : P × R) : ℝ :=
  sense z z' + reset z z' +
    (modePrice (install z'.2) - modePrice (install z.2))

/-- Available work after prior preparation and expected stage costs on the
executed joint law, with explicitly supplied replenishment. -/
noncomputable def fundedStore {A : Type*} (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R)) (install : R → A)
    (modePrice : A → ℝ) (sense reset : (P × R) → (P × R) → ℝ)
    (initial preparation : ℝ) (replenish : ℕ → ℝ) (N : ℕ) : ℝ :=
  store (initial - preparation)
    (expectedPathCost prior channel (totalStagePrice install modePrice sense reset))
    replenish N

/-- The complete declared work ledger on the actual evolving joint law.
Preparation is paid once, sensing and reset are expected path costs, and
installation telescopes to stored mode energy. Replenishment is explicit.
Neither heat nor phase-current cost is identified with these prices. -/
theorem fundedStore_balance {A : Type*} (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R)) (install : R → A)
    (modePrice : A → ℝ) (sense reset : (P × R) → (P × R) → ℝ)
    (initial preparation : ℝ) (replenish : ℕ → ℝ) (N : ℕ) :
    fundedStore prior channel install modePrice sense reset initial preparation
      replenish N = initial - preparation +
      ∑ k ∈ Finset.range N, replenish k -
      ∑ k ∈ Finset.range N, expectedPathCost prior channel sense k -
      ∑ k ∈ Finset.range N, expectedPathCost prior channel reset k -
      (installedEnergy (modePrice ∘ install) (law prior channel N) -
        installedEnergy (modePrice ∘ install) prior) := by
  have hcost (k : ℕ) :
      expectedPathCost prior channel (totalStagePrice install modePrice sense reset) k =
        expectedPathCost prior channel sense k +
          expectedPathCost prior channel reset k +
          expectedPathCost prior channel
            (fun z z' => modePrice (install z'.2) - modePrice (install z.2)) k := by
    change expectedPathCost prior channel
      (fun z z' => (sense z z' + reset z z') +
        (modePrice (install z'.2) - modePrice (install z.2))) k = _
    rw [expectedPathCost_add, expectedPathCost_add]
  rw [fundedStore, store_balance]
  simp_rw [hcost, Finset.sum_add_distrib]
  have hinst :
      (∑ k ∈ Finset.range N,
        expectedPathCost prior channel
          (fun z z' => modePrice (install z'.2) - modePrice (install z.2)) k) =
        installedEnergy (modePrice ∘ install) (law prior channel N) -
          installedEnergy (modePrice ∘ install) prior := by
    simpa only [Function.comp_apply] using
      cumulative_installation_energy_balance prior channel (modePrice ∘ install) N
  rw [hinst]
  ring

/-- With a positive lower bound on expected net stage cost and no replenishment,
any finite initial work store eventually becomes negative. A feasible controller
must stop before that horizon or obtain explicitly modelled replenishment.
The lower bound is a substantive assumption about the supplied process; it is
not inferred from phase order or information gain. -/
theorem finite_funded_operation_exhausts {A : Type*} (prior : ProbDist (P × R))
    (channel : P × R → ProbDist (P × R)) (install : R → A)
    (modePrice : A → ℝ) (sense reset : (P × R) → (P × R) → ℝ)
    (initial preparation ε : ℝ) (hε : 0 < ε)
    (hcost : ∀ n, ε ≤ expectedPathCost prior channel
      (totalStagePrice install modePrice sense reset) n) :
    ∃ N : ℕ, fundedStore prior channel install modePrice sense reset
      initial preparation (fun _ => 0) N < 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((initial - preparation) / ε)
  refine ⟨N, ?_⟩
  have hlimit : initial - preparation < (N : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hN
  exact finite_store_obstruction (initial - preparation) ε
    (expectedPathCost prior channel (totalStagePrice install modePrice sense reset))
    N (fun k _ => hcost k) hlimit

#print axioms finite_funded_operation_exhausts

#print axioms closed_loop_law_succ_apply
#print axioms closed_loop_phase_marginal
#print axioms fundedStore_balance

#print axioms cumulative_installation_energy_balance

#print axioms installation_energy_balance
#print axioms expected_state_energy_balance
#print axioms expected_first_law
end PhysicsOfConsciousness.PhaseFeedback
