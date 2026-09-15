import PhysicsOfConsciousness.Phase3_SupportedThermodynamics

/-!
# Resource and implementation foundations

Resource bounds on actual trajectories need no finite state assumption. The
ledger and the total-energy conservation premise remain explicit; neither is
inferred from a stochastic channel's name. Installation and control have their
own energy observable, and reservoir identification is a separate hypothesis.

`ContinuingProcess.horizon_le_of_cost` is the expected-work ledger read as one
of these trajectories, so the finite-state store of `Phase3_ContinuingAgent`
specializes the bound below rather than restating it; the pathwise store's own
reachability bounds branch over states and are proved there.
`PathwiseStore.withPreparation`, which puts the preparation stage inside the
same boundary, lives with the preparation channel in `Phase3_Preparation`.

The sharp-charge transfer is a reversible swap from a supplied source. It does
not prepare that source, price fabrication, or assert finite heat for an
irreversible sharp reset. General stochastic integrability and control remain
outside these trajectory results.

`entropy_reduction_le_bathEntropy` is what the drawn work is charged against on
a finite step: the weakened forward/reverse support condition of
`Phase3_SupportedThermodynamics` is already enough for the second-law form, so
the bound below is available where the full positivity premise is not. The bath
term is a log-ratio of the declared channel; identifying it with reservoir
entropy remains local detailed balance's job, not this theorem's.
-/

namespace PhysicsOfConsciousness
namespace ResourceTrajectory

/-- Telescope a ledger on any state space. This includes individual countable
or continuous trajectories; it does not construct their probability law. -/
theorem balance_sum {S : Type*} (s : ℕ → S) (B : S → ℝ) (d u : ℕ → ℝ) (N : ℕ)
    (h : ∀ n < N, B (s (n + 1)) = B (s n) - d n + u n) :
    B (s N) = B (s 0) - ∑ n ∈ Finset.range N, d n + ∑ n ∈ Finset.range N, u n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [h N (Nat.lt_succ_self N), ih (fun n hn => h n (Nat.lt_succ_of_lt hn)),
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- Nonnegative final resources bound cumulative draw by initial resources
and external deliveries. Prefix solvency is stronger than the premise here. -/
theorem draw_le_resources {S : Type*} (s : ℕ → S) (B : S → ℝ) (d u : ℕ → ℝ)
    (N : ℕ) (h : ∀ n < N, B (s (n + 1)) = B (s n) - d n + u n)
    (hB : 0 ≤ B (s N)) :
    ∑ n ∈ Finset.range N, d n ≤ B (s 0) + ∑ n ∈ Finset.range N, u n := by
  have hb := balance_sum s B d u N h
  linarith

/-- A uniform net cost bounds the horizon without a finite state restriction.
The costs and conservation law are about the declared trajectory only. -/
theorem horizon_bound {S : Type*} (s : ℕ → S) (B : S → ℝ) (d u : ℕ → ℝ)
    (N : ℕ) (c : ℝ)
    (h : ∀ n < N, B (s (n + 1)) = B (s n) - d n + u n)
    (hc : ∀ n < N, c ≤ d n - u n) (hB : 0 ≤ B (s N)) :
    (N : ℝ) * c ≤ B (s 0) := by
  have hs : ∑ n ∈ Finset.range N, c ≤ ∑ n ∈ Finset.range N, (d n - u n) :=
    Finset.sum_le_sum fun n hn => hc n (Finset.mem_range.mp hn)
  have hb := draw_le_resources s B d u N h hB
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hs
  linarith

/-- Including stored system energy, bath energy and installation/control energy
in a conserved boundary identifies the draw. Conservation is a physical premise;
this algebra does not establish gate fabrication or a reservoir temperature. -/
theorem draw_eq_energy_heat_control {S : Type*} (B E H C : S → ℝ) (s t : S)
    (d u : ℝ) (hB : B t = B s - d + u)
    (hE : B t + E t + H t + C t = B s + E s + H s + C s + u) :
    d = (E t - E s) + (H t - H s) + (C t - C s) := by
  linarith

/-- The drawn work has the channel's thermal heat only after its actual bath
energy gain has been identified with that log ratio. The premise is not derived
from the resource ledger, and control/installation changes remain charged. -/
theorem draw_eq_thermal_work {S : Type*} (B E H C : S → ℝ) (s t : S)
    (d u θ ratio : ℝ) (hB : B t = B s - d + u)
    (hE : B t + E t + H t + C t = B s + E s + H s + C s + u)
    (hH : H t - H s = θ * Real.log ratio) :
    d = (E t - E s) + θ * Real.log ratio + (C t - C s) := by
  rw [← hH]
  exact draw_eq_energy_heat_control B E H C s t d u hB hE

/-- Reversible charge transfer on a countably infinite state space. The source
is supplied; swapping its charge into the buffer creates no energy. -/
def transferCharge : ℕ × ℕ → ℕ × ℕ := Prod.swap

theorem transferCharge_involutive : Function.Involutive transferCharge := by
  intro s
  rfl

theorem transferCharge_conserves (s : ℕ × ℕ) :
    (transferCharge s).1 + (transferCharge s).2 = s.1 + s.2 := Nat.add_comm _ _

theorem transferCharge_sharp (n : ℕ) : transferCharge (n, 0) = (0, n) := rfl

/-- A continuous-state trajectory with declared constant draw and delivery.
Its supply is an external input, not a finite autonomous source. -/
noncomputable def refuel (b d u : ℝ) (n : ℕ) : ℝ := b + n * (u - d)

theorem refuel_ledger (b d u : ℝ) (n : ℕ) :
    refuel b d u (n + 1) = refuel b d u n - d + u := by
  simp only [refuel, Nat.cast_add, Nat.cast_one]
  ring

/-- Delivery at least equal to draw sustains this declared trajectory. The
unbounded cumulative delivery still has to be provided by an external source. -/
theorem refuel_nonneg (b d u : ℝ) (hb : 0 ≤ b) (hdu : d ≤ u) (n : ℕ) :
    0 ≤ refuel b d u n := by
  exact add_nonneg hb (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hdu))

end ResourceTrajectory

/-- **What the step's own bath term must cover.** Under forward/reverse support
inclusion the entropy the system loses over a step is at most its bath
log-ratio term. Full positivity of the initial law and of every transition is
not needed, so this reaches the sparse laws an actual agent runs on. It prices
no work: the bath term is reservoir entropy only under local detailed balance,
and installation and control energies are charged separately by
`ResourceTrajectory.draw_eq_energy_heat_control`. -/
theorem entropy_reduction_le_bathEntropy {X S : Type*} [Fintype X] [Fintype S]
    (M : FiniteFeedbackStep X S) (h : M.ReversibleSupport) :
    shannon_entropy M.initial.p - shannon_entropy M.final.p ≤ M.bathEntropy := by
  have hb := M.entropy_balance_of_support h
  have hp := M.entropyProduction_nonneg_of_support h
  linarith


#print axioms ResourceTrajectory.horizon_bound
#print axioms entropy_reduction_le_bathEntropy
#print axioms ResourceTrajectory.draw_eq_thermal_work

end PhysicsOfConsciousness
