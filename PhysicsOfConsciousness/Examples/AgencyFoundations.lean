import PhysicsOfConsciousness.Phase3_MeasureFeedback
import PhysicsOfConsciousness.Phase3_ResourceFoundations
import PhysicsOfConsciousness.Phase3_SupportedThermodynamics
import PhysicsOfConsciousness.Phase5_ContentDynamics
import PhysicsOfConsciousness.Examples.AgencyThermodynamics
import PhysicsOfConsciousness.Examples.ContinuingLimit

/-!
# Regression specifications for the agency foundations

These specifications were run before the named foundations existed. Concrete
resource, support and content witnesses are added below during implementation.
This is a Lean-only handoff; no cortical or optimal-control identification is made.
-/

namespace PhysicsOfConsciousness.Examples.AgencyFoundations

example {S : Type*} (s : ℕ → S) (B : S → ℝ) (d u : ℕ → ℝ) (N : ℕ)
    (h : ∀ n < N, B (s (n + 1)) = B (s n) - d n + u n) :
    B (s N) = B (s 0) - ∑ n ∈ Finset.range N, d n + ∑ n ∈ Finset.range N, u n :=
  ResourceTrajectory.balance_sum s B d u N h

example (n : ℕ) : ResourceTrajectory.transferCharge (n, 0) = (0, n) :=
  ResourceTrajectory.transferCharge_sharp n

example {V : Type*} [Fintype V] (P Q : ProbDist V)
    (h : ProbDist.SupportIncluded P Q) : 0 ≤ KL P Q :=
  KL_nonneg_of_support P Q h

example {V : Type*} [Fintype V] (P Q : ProbDist V) (v : V)
    (hp : 0 < P.p v) (hq : Q.p v = 0) : ProbDist.extendedKL P Q = ⊤ :=
  ProbDist.extendedKL_top_of_missing P Q v hp hq

example {X S : Type*} [Fintype X] [Fintype S] (M : FiniteFeedbackStep X S)
    (h : M.ReversibleSupport) :
    M.entropyProduction = shannon_entropy M.final.p -
      shannon_entropy M.initial.p + M.bathEntropy :=
  M.entropy_balance_of_support h

example {I A : Type*} (U : I → Set A) (s o : I → A → ℝ) (ε δ η : ℝ)
    (hη : 0 ≤ η) (hη' : η ≤ 1)
    (hs : LocalContent.Compatible U s ε) (ho : LocalContent.Compatible U o δ) :
    LocalContent.Compatible U (LocalContent.update η o s) ((1 - η) * ε + η * δ) :=
  LocalContent.update_residual U s o ε δ η hη hη' hs ho

example (m : ℕ) :
    65 / 127 - Continuing.agent.performance (3 * (m + 1)) =
      (65 / 127 - 65 / 128) * (1 / 128 : ℝ) ^ m :=
  Continuing.performance_error m

example : Filter.Tendsto (fun m => Continuing.agent.performance (3 * (m + 1)))
    Filter.atTop (nhds (65 / 127 : ℝ)) := Continuing.performance_tendsto

example (b : ℝ) : ∃ m, b < Continuing.process.totalWork (3 * m) :=
  Continuing.work_unbounded b

/-! ## Concrete witnesses

The specifications above are the general statements. These are instances of
them, so that none of the foundations is vacuous: an unbounded state space
carrying an actual trajectory, a feedback step whose support condition holds
where the earlier positivity premise fails, an erasure whose extended
divergence is infinite, and a cover on which the readout actually glues.
-/

namespace Resource

open PhysicsOfConsciousness.ResourceTrajectory

/-- A declared real-valued trajectory drawing one unit per operation from ten.
`horizon_bound` reads its horizon off the initial reading, with no finite state
space anywhere in the statement. -/
example (N : ℕ) (h : 0 ≤ refuel 10 1 0 N) : (N : ℝ) ≤ 10 := by
  have hb := horizon_bound (refuel 10 1 0) id (fun _ => 1) (fun _ => 0) N 1
    (fun n _ => refuel_ledger 10 1 0 n) (fun n _ => by norm_num) h
  simpa [refuel] using hb

/-- Delivery matching the draw sustains the same trajectory at every operation.
The unbounded cumulative delivery is supplied from outside the boundary. -/
example (n : ℕ) : 0 ≤ refuel 5 2 2 n := refuel_nonneg 5 2 2 (by norm_num) le_rfl n

/-- The sharp transfer on a countably infinite state space: a source carrying
seven units is emptied into the buffer, and nothing is created. -/
example : transferCharge (7, 0) = (0, 7) := transferCharge_sharp 7

example (s : ℕ × ℕ) : (transferCharge s).1 + (transferCharge s).2 = s.1 + s.2 :=
  transferCharge_conserves s

end Resource

namespace Support

open PhysicsOfConsciousness

/-- A controller-state law supported on one atom. -/
noncomputable def sparseInitial : ProbDist (Bool × Bool) where
  p z := if z = (true, true) then 1 else 0
  nonneg z := by split <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- A channel that forgets its input completely. -/
noncomputable def coin (_x _s : Bool) : ProbDist Bool where
  p _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- The step whose initial law has zeros and whose reverse support is still
complete: exactly the regime the earlier positivity premise excludes. -/
noncomputable def sparse : FiniteFeedbackStep Bool Bool := ⟨sparseInitial, coin⟩

theorem sparse_not_positive : ¬ sparse.Positive := by
  intro h
  have hz := h.1 (false, false)
  norm_num [sparse, sparseInitial] at hz

theorem sparse_reversibleSupport : sparse.ReversibleSupport := by
  rintro ⟨x, s, t⟩ hz
  revert hz
  cases x <;> cases s <;> cases t <;>
    norm_num [FiniteFeedbackStep.forward, FiniteFeedbackStep.reverse,
      FiniteFeedbackStep.final, sparse, sparseInitial, coin, Fintype.sum_bool]

/-- The entropy balance holds on this step, which `entropy_balance` does not
reach. Nonnegativity of its production follows from the same condition. -/
example : sparse.entropyProduction =
    shannon_entropy sparse.final.p - shannon_entropy sparse.initial.p +
      sparse.bathEntropy :=
  sparse.entropy_balance_of_support sparse_reversibleSupport

example : 0 ≤ sparse.entropyProduction :=
  sparse.entropyProduction_nonneg_of_support sparse_reversibleSupport

/-- A definite bit, and the opposite definite bit. -/
noncomputable def diracTrue : ProbDist Bool where
  p b := if b then 1 else 0
  nonneg b := by cases b <;> norm_num
  sum_one := by norm_num [Fintype.sum_bool]

noncomputable def diracFalse : ProbDist Bool where
  p b := if b then 0 else 1
  nonneg b := by cases b <;> norm_num
  sum_one := by norm_num [Fintype.sum_bool]

noncomputable def uniformBit : ProbDist Bool where
  p _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- Erasure of a definite bit onto the opposite definite bit has no reverse
support, and the extended divergence records that as infinity rather than as a
finite real cost. -/
example : diracTrue.extendedKL diracFalse = ⊤ :=
  ProbDist.extendedKL_top_of_missing _ _ true (by norm_num [diracTrue])
    (by norm_num [diracFalse])

theorem sharp_supported : diracTrue.SupportIncluded uniformBit := by
  intro v _
  norm_num [uniformBit]

/-- Where support is included the extended divergence is the real one, here
one bit. -/
example : (diracTrue.extendedKL uniformBit).toReal = Real.log 2 := by
  rw [ProbDist.extendedKL_toReal_of_support _ _ sharp_supported]
  norm_num [KL, diracTrue, uniformBit, Fintype.sum_bool]

end Support

namespace Content

open PhysicsOfConsciousness.LocalContent

/-- Two patches on three sites, sharing the middle one. -/
def U : Bool → Set (Fin 3)
  | false => {0, 1}
  | true => {1, 2}

/-- Local contents that agree on the shared site and carry different values
away from it, so the glued field is neither patch. -/
noncomputable def s : Bool → Fin 3 → ℝ
  | false => fun x => if x = 0 then 5 else 1
  | true => fun x => if x = 2 then 7 else 1

/-- The readout reads the left patch at the left site and the right patch
elsewhere. -/
def choose : Fin 3 → Bool := fun x => if x = 0 then false else true

theorem covers (x : Fin 3) : x ∈ U (choose x) := by
  fin_cases x <;> simp [U, choose]

theorem compatible : Compatible U s 0 := by
  intro i j x hi hj
  cases i <;> cases j <;> fin_cases x <;> simp_all [U, s]

/-- The declared readout extends both patches, and is the only field that
does. -/
example (i : Bool) (x : Fin 3) (hx : x ∈ U i) : readout choose s x = s i x :=
  readout_agrees U choose s covers compatible i x hx

example (f : Fin 3 → ℝ) (hf : ∀ i x, x ∈ U i → f x = s i x) :
    f = readout choose s :=
  readout_unique U choose s covers f hf

example (x : Fin 3) :
    readout choose s x = if x = 0 then 5 else if x = 2 then 7 else 1 := by
  fin_cases x <;> norm_num [readout, choose, s]

/-- A family that disagrees by one on the shared site: compatible at `ε = 1`
and demonstrably not at `ε = 0`, so the gluing premise is not automatic. -/
noncomputable def t : Bool → Fin 3 → ℝ
  | false => fun _ => 0
  | true => fun _ => 1

theorem t_compatible_one : Compatible U t 1 := by
  intro i j x _ _
  cases i <;> cases j <;> norm_num [t]

example : ¬ Compatible U t 0 := by
  intro h
  have h1 := h false true 1 (by simp [U]) (by simp [U])
  norm_num [t] at h1

/-- Constant observations agree everywhere. -/
theorem const_compatible : Compatible U (fun (_ : Bool) (_ : Fin 3) => (1 : ℝ)) 0 := by
  intro i j x _ _
  norm_num

/-- Under those observations the disagreement of `t` decays by a half per
observation. The limit is the observed value, not an independently chosen
global content. -/
example (n : ℕ) :
    Compatible U (run (1 / 2) (fun _ _ _ => (1 : ℝ)) t n) ((1 / 2 : ℝ) ^ n) := by
  have h := run_residual U t (fun _ _ _ => (1 : ℝ)) 1 (1 / 2) (by norm_num)
    (by norm_num) t_compatible_one (fun _ => const_compatible) n
  norm_num at h
  exact h


/-! ### Agreement acquired from coherence

The witnesses above all *assume* the observations agree. These do not: the
residual is computed from the phases through `compatible_of_coherence`, and the
negative control shows that at zero coherence the contents genuinely disagree,
so the derivation is not returning zero for free. -/

/-- Content is the in-phase component of the local oscillator. -/
noncomputable def proj : ℝ × ℝ → ℝ := fun p => p.1

theorem proj_lipschitz : LipschitzEncoder proj 1 := by
  intro a b
  rw [one_mul]
  unfold proj circlePoint chord
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Real.sin a - Real.sin b)])

/-- Two antiphase oscillators. -/
noncomputable def antiphase : Fin 2 → ℝ := ![0, Real.pi]

/-- Two oscillators at the same phase. -/
noncomputable def locked : Fin 2 → ℝ := ![0, 0]

/-- Computed through the mean-cosine identity, not assumed. -/
theorem antiphase_incoherent : order_parameter_r_sq antiphase = 0 := by
  have h := order_parameter_r_sq_eq_mean_cos antiphase
  rw [show Fintype.card (Fin 2) = 2 from rfl] at h
  simp [antiphase, Fin.sum_univ_two] at h
  exact h

theorem locked_is_phase_locked : is_phase_locked locked := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [locked]

/-- Which oscillator each patch reads. -/
def patchOf : Bool → Fin 2 := fun b => if b then 1 else 0

/-- **At zero coherence the derived residual is `√2 · √2 = 2`.** The actual
disagreement below is also `2`, so on this pair the bound is attained: the
single factor `N` in `cos_gap_le_of_coherence` cannot be lowered in general. -/
example : Compatible U (fun i (_ : Fin 3) => proj (circlePoint (antiphase (patchOf i))))
    (1 * (Real.sqrt 2 * Real.sqrt (Fintype.card (Fin 2) : ℝ) * Real.sqrt (1 - 0))) := by
  have h := compatible_of_coherence U patchOf antiphase proj 1 zero_le_one proj_lipschitz
  rwa [antiphase_incoherent] at h

/-- **The negative control.** At zero coherence the two patches do not agree, so
`compatible_of_coherence` is not returning a vacuous zero residual: something
has to make the phases agree before the contents do. -/
example : ¬ Compatible U
    (fun i (_ : Fin 3) => proj (circlePoint (antiphase (patchOf i)))) 0 := by
  intro h
  have h1 := h false true 1 (by simp [U]) (by simp [U])
  simp [proj, circlePoint, antiphase, patchOf, Real.cos_pi] at h1

/-- **And at perfect locking the residual is exactly zero**, so the readout of
the preserve half applies to observations nothing assumed to be compatible. -/
example : Compatible U
    (fun i (_ : Fin 3) => proj (circlePoint (locked (patchOf i)))) 0 :=
  compatible_of_phase_locked U patchOf locked proj 1 proj_lipschitz locked_is_phase_locked

/-- The floor does not decay: mixing observations that disagree by one leaves a
residual of one however long the run continues. -/
example (n : ℕ) :
    Compatible U (run (1 / 2) (fun _ => t) t n) ((1 - (1 : ℝ) / 2) ^ n * 1 + 1) :=
  run_residual_floor U t (fun _ => t) 1 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) t_compatible_one (fun _ => t_compatible_one) n

end Content


namespace Ledger

open PhysicsOfConsciousness.ResourceTrajectory
open PhysicsOfConsciousness.Examples.ThermalAgency

/-! ## The drawn unit as one step's own reservoir heat

`draw_eq_thermal_work` is discharged by any real number written `θ * log ratio`.
These four observables carry one actuation of the two-bit thermal agent across
the resource boundary instead, so the heat term in the ledger is that step's
`bathEntropy` and nothing else can be substituted for it.

The control increment is **declared**, not derived. Pricing gate fabrication is
precisely what these results do not do, and the witness is built so that the
unpriced quantity is visible on the page rather than hidden in an aggregate. -/

/-- Usable store: one unit of work is drawn over the operation. -/
noncomputable def store : Bool → ℝ := fun b => if b then -Real.log 2 else 0

/-- The system's own interaction energy, which falls by the step's heat. -/
noncomputable def system : Bool → ℝ := fun b => if b then -(Real.log 3 / 4) else 0

/-- The reservoir coordinate. `bath_tracks_step` is what ties it to the channel. -/
noncomputable def bath : Bool → ℝ := fun b => if b then Real.log 3 / 4 else 0

/-- Installation and control. Declared, never derived. -/
noncomputable def control : Bool → ℝ := fun b => if b then Real.log 2 else 0

theorem ledger_balance : store true = store false - Real.log 2 + 0 := by
  norm_num [store]

theorem ledger_conserved :
    store true + system true + bath true + control true =
      store false + system false + bath false + control false + 0 := by
  norm_num [store, system, bath, control]

/-- The reservoir coordinate gains exactly the mean heat of the channel this
stage runs. This is the hypothesis a microscopic model would have to supply. -/
theorem bath_tracks_step : bath true - bath false = actuation.meanHeat heat := by
  rw [actuation_heat]
  norm_num [bath]

/-- The draw is the declared control increment and nothing else: an autonomous
relaxation step pays for its gate, and its heat is covered by the interaction
energy it consumes. -/
example : (Real.log 2 : ℝ) =
    (system true - system false) + 1 * actuation.bathEntropy +
      (control true - control false) :=
  draw_eq_step_heat store system bath control false true (Real.log 2) 0 1
    actuation heat actuation_local_balance ledger_balance ledger_conserved
    bath_tracks_step

example :
    1 * (shannon_entropy actuation.initial.p - shannon_entropy actuation.final.p)
      ≤ Real.log 2 - (system true - system false) - (control true - control false) :=
  draw_ge_entropy_reduction store system bath control false true (Real.log 2) 0 1
    actuation heat one_pos
    (actuation.reversibleSupport_of_positive actuation_positive)
    actuation_local_balance ledger_balance ledger_conserved bath_tracks_step

theorem entropy_reduction_value :
    shannon_entropy actuation.initial.p - shannon_entropy actuation.final.p =
      3 / 4 * Real.log 3 - Real.log 2 := by
  rw [actuation_final, entropy_correlated]
  change shannon_entropy independent.p - _ = _
  rw [entropy_independent]
  ring

/-- The step genuinely compresses: without this the Landauer bound would be
vacuous on the witness. -/
theorem entropy_reduction_pos :
    0 < shannon_entropy actuation.initial.p - shannon_entropy actuation.final.p := by
  rw [entropy_reduction_value]
  have h : Real.log 16 < Real.log 27 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, show (27 : ℝ) = 3 ^ 3 by norm_num,
    Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- And the bound is not attained. The slack is the step's own entropy
production, so a witness that saturated it would be a reversible one. -/
theorem landauer_slack :
    1 * (shannon_entropy actuation.initial.p - shannon_entropy actuation.final.p)
      < Real.log 2 - (system true - system false) - (control true - control false) := by
  rw [entropy_reduction_value]
  have h : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
  push_cast at h
  norm_num [system, control]
  linarith

end Ledger


namespace Broad

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-! ## Probability laws on unbounded and continuous state

`ResourceTrajectory`'s witnesses are trajectories: real readings indexed by
operation number, with no probability law anywhere. These are the laws. They sit
on `ℕ` and on `ℝ`, they are genuine probability measures, and the production is
computed from them rather than declared. -/

/-- A step on a countably infinite state space that cannot be reversed: it moves
a definite state to a different definite state, and the same-channel reverse
never returns to where it started. -/
noncomputable def jump : MeasureFeedbackStep ℕ where
  initial := Measure.dirac 0
  transition := Kernel.const ℕ (Measure.dirac 1)
  initial_prob := inferInstance
  transition_markov := inferInstance

theorem jump_forward : jump.forward = Measure.dirac (0, 1) := by
  unfold MeasureFeedbackStep.forward jump
  simp [Measure.compProd_const, Measure.dirac_prod_dirac]

theorem jump_final : jump.final = Measure.dirac 1 := by
  unfold MeasureFeedbackStep.final MeasureFeedbackStep.forward jump
  rw [Measure.snd_compProd]
  simp

theorem jump_reverse : jump.reverse jump.transition = Measure.dirac (1, 1) := by
  unfold MeasureFeedbackStep.reverse MeasureFeedbackStep.reversePath
  rw [jump_final]
  show ((Measure.dirac 1 ⊗ₘ Kernel.const ℕ (Measure.dirac 1)).map Prod.swap) = _
  rw [Measure.compProd_const, Measure.dirac_prod_dirac]
  simp

/-- **The laws really move**, so this is not a stationary witness dressed up. -/
theorem jump_changes : jump.final ≠ jump.initial := by
  rw [jump_final]
  intro h
  have := congrArg (fun μ => μ {(1 : ℕ)}) h
  simp [jump] at this

/-- **Absolute irreversibility on a countably infinite space.** No finiteness,
no positivity, and no `ENNReal.toReal`: the production is `⊤` because the
forward law is not absolutely continuous with respect to the reversed one. -/
theorem jump_entropyProduction :
    jump.entropyProduction jump.transition = ⊤ := by
  refine jump.entropyProduction_eq_top jump.transition ?_
  intro hac
  rw [jump_forward, jump_reverse] at hac
  have hz : (Measure.dirac ((1 : ℕ), (1 : ℕ))) {((0 : ℕ), (1 : ℕ))} = 0 := by simp
  have h := hac hz
  simp at h

/-- A stationary step on the same infinite space produces nothing, so the `⊤`
above is a property of that step and not of the state space. -/
noncomputable def rest : MeasureFeedbackStep ℕ where
  initial := Measure.dirac 0
  transition := Kernel.const ℕ (Measure.dirac 0)
  initial_prob := inferInstance
  transition_markov := inferInstance

theorem rest_forward : rest.forward = Measure.dirac (0, 0) := by
  unfold MeasureFeedbackStep.forward rest
  simp [Measure.compProd_const, Measure.dirac_prod_dirac]

theorem rest_final : rest.final = Measure.dirac 0 := by
  unfold MeasureFeedbackStep.final MeasureFeedbackStep.forward rest
  rw [Measure.snd_compProd]
  simp

theorem rest_entropyProduction : rest.entropyProduction rest.transition = 0 := by
  refine rest.entropyProduction_self ?_
  unfold MeasureFeedbackStep.reverse MeasureFeedbackStep.reversePath
  rw [rest_final, rest_forward]
  show ((Measure.dirac 0 ⊗ₘ Kernel.const ℕ (Measure.dirac 0)).map Prod.swap) = _
  rw [Measure.compProd_const, Measure.dirac_prod_dirac]
  simp

/-- **A continuous state space with a nonatomic law.** Nothing in the finite
theory can carry this: the initial measure assigns zero to every singleton, so
there is no atom to put a `ProbDist.p` value on. -/
noncomputable def diffuse : MeasureFeedbackStep ℝ where
  initial := gaussianReal 0 1
  transition := Kernel.const ℝ (gaussianReal 0 1)
  initial_prob := inferInstance
  transition_markov := inferInstance

theorem diffuse_nonatomic (x : ℝ) : diffuse.initial {x} = 0 := by
  have : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  show (gaussianReal 0 1) {x} = 0
  exact measure_singleton x

/-- The stationary continuous step is reversible, computed rather than declared:
the swap of a product of a measure with itself is that product. -/
theorem diffuse_final : diffuse.final = gaussianReal 0 1 := by
  unfold MeasureFeedbackStep.final MeasureFeedbackStep.forward diffuse
  rw [Measure.snd_compProd]
  simp

theorem diffuse_entropyProduction :
    diffuse.entropyProduction diffuse.transition = 0 := by
  refine diffuse.entropyProduction_self ?_
  unfold MeasureFeedbackStep.reverse MeasureFeedbackStep.reversePath
    MeasureFeedbackStep.forward
  rw [diffuse_final]
  show ((gaussianReal 0 1 ⊗ₘ diffuse.transition).map Prod.swap) = _
  show ((gaussianReal 0 1 ⊗ₘ Kernel.const ℝ (gaussianReal 0 1)).map Prod.swap) = _
  rw [Measure.compProd_const, Measure.prod_swap]
  show _ = ((gaussianReal 0 1) ⊗ₘ Kernel.const ℝ (gaussianReal 0 1))
  rw [Measure.compProd_const]

/-! ### Control with no finiteness on the state

The action moves a point on the line; the reward is the position reached and the
cost is quadratic. The state space is `ℝ`. -/

noncomputable def place : MeasureControlProblem ℝ ℝ where
  initial := Measure.dirac 0
  world := fun a => Kernel.const ℝ (Measure.dirac a)
  reward := id
  cost := fun a => a ^ 2
  initial_prob := inferInstance
  world_markov := fun _ => inferInstance

theorem place_final (a : ℝ) : place.final a = Measure.dirac a := by
  unfold MeasureControlProblem.final place
  rw [Measure.snd_compProd]
  simp

theorem place_performance (a : ℝ) : place.performance a = a := by
  unfold MeasureControlProblem.performance
  rw [place_final]
  simp [place]

/-- A maximizer over a finite permitted set, on a state space with no `Fintype`. -/
example : ∃ a ∈ ({0, 1, 2} : Finset ℝ), place.cost a ≤ 4 ∧
    ∀ b ∈ ({0, 1, 2} : Finset ℝ), place.cost b ≤ 4 →
      place.performance b ≤ place.performance a :=
  place.exists_optimal 4 {0, 1, 2} 0 (by norm_num) (by norm_num [place])

/-- A maximizer over a *compact* permitted set: the existence assumption is
continuity, which is discharged here rather than replaced by a `Finset`. -/
example : ∃ a ∈ Set.Icc (0 : ℝ) 1, place.cost a ≤ 1 ∧
    ∀ b ∈ Set.Icc (0 : ℝ) 1, place.cost b ≤ 1 →
      place.performance b ≤ place.performance a := by
  refine place.exists_optimal_compact 1 (Set.Icc 0 1) isCompact_Icc ?_ ?_ 0
    (by norm_num) (by norm_num [place])
  · exact (continuous_pow 2).congr fun a => rfl
  · exact continuous_id.congr fun a => (place_performance a).symm

end Broad


namespace SharpCharge

open PhysicsOfConsciousness

/-! ## Preparing a sharp charge, and preparing an approximate one

`ResourceTrajectory.transferCharge` is a reversible involution: it moves a sharp
charge and creates nothing. These witnesses are the operation it does not
perform. The exact preparation has no finite path cost at all; the approximate
one is an ordinary priced step. -/

/-- A channel that drives every state to `true`, whatever it started from. -/
noncomputable def toTrue (_x _s : Bool) : ProbDist Bool where
  p t := if t then 1 else 0
  nonneg t := by cases t <;> norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- Exact preparation of a sharp charge from a uniform hardware law. -/
noncomputable def sharpPrep : FiniteFeedbackStep Bool Bool :=
  ⟨ThermalAgency.independent, toTrue⟩

theorem sharpPrep_not_reversibleSupport : ¬ sharpPrep.ReversibleSupport :=
  sharpPrep.sharp_preparation_not_reversibleSupport true
    (fun _ _ => by norm_num [sharpPrep, toTrue])
    true false (by norm_num) (by norm_num [sharpPrep, ThermalAgency.independent])

/-- **The exact sharp charge is not fundable.** Its path divergence is infinite,
recorded in `ℝ≥0∞` rather than converted to a real cost. -/
theorem sharpPrep_extendedKL_top :
    sharpPrep.forward.extendedKL sharpPrep.reverse = ⊤ :=
  sharpPrep.sharp_preparation_extendedKL_top true
    (fun _ _ => by norm_num [sharpPrep, toTrue])
    true false (by norm_num) (by norm_num [sharpPrep, ThermalAgency.independent])

/-- The same preparation stopped short of sharp: three quarters, not all. -/
noncomputable def nearlyTrue (_x _s : Bool) : ProbDist Bool where
  p t := if t then 3 / 4 else 1 / 4
  nonneg t := by cases t <;> norm_num
  sum_one := by norm_num [Fintype.sum_bool]

noncomputable def nearlyPrep : FiniteFeedbackStep Bool Bool :=
  ⟨ThermalAgency.independent, nearlyTrue⟩

theorem nearlyPrep_positive : nearlyPrep.Positive := by
  constructor
  · intro z; norm_num [nearlyPrep, ThermalAgency.independent]
  · intro x s t; cases t <;> norm_num [nearlyPrep, nearlyTrue]

/-- **The approximate charge is an ordinary priced step.** Support holds, so the
second law applies to it and its entropy reduction is covered by its bath term —
the bound that the exact preparation above has no access to. -/
example : shannon_entropy nearlyPrep.initial.p - shannon_entropy nearlyPrep.final.p
    ≤ nearlyPrep.bathEntropy :=
  entropy_reduction_le_bathEntropy nearlyPrep
    (nearlyPrep.reversibleSupport_of_positive nearlyPrep_positive)

example : 0 ≤ nearlyPrep.entropyProduction :=
  nearlyPrep.entropyProduction_nonneg_of_support
    (nearlyPrep.reversibleSupport_of_positive nearlyPrep_positive)

end SharpCharge

namespace Supply

open PhysicsOfConsciousness.ResourceTrajectory

/-! ## What refuelling buys

The state is a store reading paired with a source reading, on `ℝ × ℝ` — an
unbounded state space with no finite structure. Delivery is the source's loss by
construction, not a declared input. -/

/-- **A refuelled run at unit cost has a horizon set by store plus source.** -/
example (s : ℕ → ℝ × ℝ) (N : ℕ)
    (hled : ∀ n < N, (s (n + 1)).1 = (s n).1 - 1 + ((s n).2 - (s (n + 1)).2))
    (hB : 0 ≤ (s N).1) (hR : 0 ≤ (s N).2) :
    (N : ℝ) * 1 ≤ (s 0).1 + (s 0).2 :=
  horizon_le_of_sourced_delivery s Prod.fst Prod.snd (fun _ => 1)
    (fun n => (s n).2 - (s (n + 1)).2) N 1 hled (fun _ => rfl)
    (fun _ _ => le_rfl) hB hR

/-- **And no such run continues forever.** Any store-and-source pair whose
delivery is the source's own loss, both readings nonnegative, drawing one unit
per operation, is an impossible object. Sustained operation is a claim about
what lies outside the boundary, not a property this agent can have. -/
example (s : ℕ → ℝ × ℝ)
    (hled : ∀ n, (s (n + 1)).1 = (s n).1 - 1 + ((s n).2 - (s (n + 1)).2))
    (hB : ∀ n, 0 ≤ (s n).1) (hR : ∀ n, 0 ≤ (s n).2) : False :=
  no_finite_source_sustains s Prod.fst Prod.snd (fun _ => 1)
    (fun n => (s n).2 - (s (n + 1)).2) 1 one_pos hled (fun _ => rfl)
    (fun _ => le_rfl) hB hR

end Supply

#print axioms Support.sparse_reversibleSupport
#print axioms Support.sparse_not_positive
#print axioms Content.compatible
#print axioms Content.covers
#print axioms Ledger.bath_tracks_step
#print axioms Ledger.landauer_slack
#print axioms Content.antiphase_incoherent
#print axioms Content.proj_lipschitz
#print axioms Broad.jump_entropyProduction
#print axioms Broad.diffuse_nonatomic
#print axioms SharpCharge.sharpPrep_extendedKL_top
#print axioms SharpCharge.nearlyPrep_positive

end PhysicsOfConsciousness.Examples.AgencyFoundations
