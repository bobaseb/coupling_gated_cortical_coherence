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


namespace ResourceTrajectory

/-- **The drawn unit is the step's own reservoir heat.** `draw_eq_thermal_work`
leaves `ratio` a free real: nothing there ties it to a channel, so the identity
accepts any number written as a logarithm. Here the bath coordinate's energy
gain is identified with the mean heat of the channel the stage actually runs,
and local detailed balance turns that mean heat into `θ` times *that step's own*
`bathEntropy` — a log-ratio of the declared transition matrix, computable from
the channel rather than supplied alongside it.

What still carries physical content: `hE` is conservation over the boundary,
`hldb` is local detailed balance at the declared thermal scale, and `hH` says
the bath coordinate tracks this stage's heat rather than some other reservoir's.
Removing `hH` needs a microscopic model in which the bath coordinate *is* the
channel's reservoir. Installation and control remain charged to `C` and are not
priced here. -/
theorem draw_eq_step_heat {S X Y : Type*} [Fintype X] [Fintype Y]
    (B E H C : S → ℝ) (s t : S) (d u θ : ℝ)
    (M : FiniteFeedbackStep X Y) (q : X → Y → Y → ℝ)
    (hldb : M.LocalDetailedBalance θ q)
    (hB : B t = B s - d + u)
    (hE : B t + E t + H t + C t = B s + E s + H s + C s + u)
    (hH : H t - H s = M.meanHeat q) :
    d = (E t - E s) + θ * M.bathEntropy + (C t - C s) := by
  rw [← M.heat_eq_thermal_bathEntropy θ q hldb, ← hH]
  exact draw_eq_energy_heat_control B E H C s t d u hB hE

/-- **Landauer's bound, read on the resource ledger.** The work actually drawn
from the store, net of the system's stored energy and of installation/control,
is at least `θ` times the entropy this step removes from the joint state. The
premise is forward/reverse support inclusion, not full positivity, so this
reaches the sparse laws an agent runs on.

This is the sense in which the ledger's draw is no longer a free parameter: it
is bounded below by a quantity computed from the channel's own initial and final
laws. It prices neither gate fabrication nor control — both sit in `C` on the
right-hand side and are *subtracted*, so a large control budget weakens the
bound rather than being constrained by it. -/
theorem draw_ge_entropy_reduction {S X Y : Type*} [Fintype X] [Fintype Y]
    (B E H C : S → ℝ) (s t : S) (d u θ : ℝ)
    (M : FiniteFeedbackStep X Y) (q : X → Y → Y → ℝ)
    (hθ : 0 < θ) (hsupp : M.ReversibleSupport)
    (hldb : M.LocalDetailedBalance θ q)
    (hB : B t = B s - d + u)
    (hE : B t + E t + H t + C t = B s + E s + H s + C s + u)
    (hH : H t - H s = M.meanHeat q) :
    θ * (shannon_entropy M.initial.p - shannon_entropy M.final.p)
      ≤ d - (E t - E s) - (C t - C s) := by
  have hd := draw_eq_step_heat B E H C s t d u θ M q hldb hB hE hH
  have hb := entropy_reduction_le_bathEntropy M hsupp
  have := mul_le_mul_of_nonneg_left hb hθ.le
  linarith

end ResourceTrajectory

#print axioms ResourceTrajectory.draw_eq_step_heat
#print axioms ResourceTrajectory.draw_ge_entropy_reduction

namespace ProbDist

/-- A law that puts all its mass on one atom puts none anywhere else. -/
theorem eq_zero_of_eq_one {V : Type*} [Fintype V] (P : ProbDist V) (v : V)
    (h : P.p v = 1) (w : V) (hw : w ≠ v) : P.p w = 0 := by
  classical
  have hsub : ({v, w} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
  have hpair : ∑ u ∈ ({v, w} : Finset V), P.p u = P.p v + P.p w :=
    Finset.sum_pair (Ne.symm hw)
  have hle : ∑ u ∈ ({v, w} : Finset V), P.p u ≤ ∑ u, P.p u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => P.nonneg u
  rw [hpair, P.sum_one, h] at hle
  exact le_antisymm (by linarith) (P.nonneg w)

end ProbDist

namespace FiniteFeedbackStep

/-- **Exact sharp preparation is absolutely irreversible.** A channel that drives
every state to one target `t₀` has no reverse path from `t₀` back to any other
state, so a forward path that actually started elsewhere has zero reverse mass
and the support condition fails.

This is why `ResourceTrajectory.transferCharge` moves a sharp charge but cannot
make one. The swap is an involution on `ℕ × ℕ` and costs nothing; *preparing*
`(n, 0)` from a law with mass away from it is the operation priced here, and the
price is that no finite path cost exists for it at all. The `⊤` is recorded by
`extendedKL`, not converted to a real by `toReal`. -/
theorem sharp_preparation_not_reversibleSupport {X S : Type*} [Fintype X] [Fintype S]
    (M : FiniteFeedbackStep X S) (t₀ : S)
    (hdet : ∀ x s, (M.transition x s).p t₀ = 1)
    (x : X) (s : S) (hs : s ≠ t₀) (hpos : 0 < M.initial.p (x, s)) :
    ¬ M.ReversibleSupport := by
  intro h
  have hzero : (M.transition x t₀).p s = 0 :=
    (M.transition x t₀).eq_zero_of_eq_one t₀ (hdet x t₀) s hs
  have hfwd : 0 < M.forward.p (x, (s, t₀)) := by
    show 0 < M.initial.p (x, s) * (M.transition x s).p t₀
    rw [hdet x s, mul_one]
    exact hpos
  have hrev := h (x, (s, t₀)) hfwd
  have : M.reverse.p (x, (s, t₀)) = 0 := by
    show M.final.p (x, t₀) * (M.transition x t₀).p s = 0
    rw [hzero, mul_zero]
  rw [this] at hrev
  exact lt_irrefl 0 hrev

/-- The same statement in the form the ledger uses: the extended divergence of
the sharp preparation's own path laws is infinite. -/
theorem sharp_preparation_extendedKL_top {X S : Type*} [Fintype X] [Fintype S]
    (M : FiniteFeedbackStep X S) (t₀ : S)
    (hdet : ∀ x s, (M.transition x s).p t₀ = 1)
    (x : X) (s : S) (hs : s ≠ t₀) (hpos : 0 < M.initial.p (x, s)) :
    M.forward.extendedKL M.reverse = ⊤ := by
  refine ProbDist.extendedKL_top_of_missing _ _ (x, (s, t₀)) ?_ ?_
  · show 0 < M.initial.p (x, s) * (M.transition x s).p t₀
    rw [hdet x s, mul_one]
    exact hpos
  · show M.final.p (x, t₀) * (M.transition x t₀).p s = 0
    rw [(M.transition x t₀).eq_zero_of_eq_one t₀ (hdet x t₀) s hs, mul_zero]

end FiniteFeedbackStep

namespace ResourceTrajectory

/-! ## Delivery from a source, and what refuelling can and cannot buy

`refuel` takes `u` as an input, and `refuel_nonneg` sustains a run forever on the
hypothesis `d ≤ u`. That hypothesis is not free: it says an external supply
delivers without limit. These results say exactly what it costs to drop it. -/

/-- Delivery identified with the loss of a source coordinate, on any state type.
This is the general-state form of `PathwiseStore.SourceLedgered`. -/
def SourceDelivery {S : Type*} (s : ℕ → S) (R : S → ℝ) (u : ℕ → ℝ) : Prop :=
  ∀ n, u n = R (s n) - R (s (n + 1))

theorem totalDelivery_eq_source_loss {S : Type*} (s : ℕ → S) (R : S → ℝ) (u : ℕ → ℝ)
    (h : SourceDelivery s R u) (N : ℕ) :
    ∑ n ∈ Finset.range N, u n = R (s 0) - R (s N) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, h N]; ring

/-- A source that never reads below empty bounds everything it has delivered by
what it started with. -/
theorem delivery_le_source {S : Type*} (s : ℕ → S) (R : S → ℝ) (u : ℕ → ℝ)
    (h : SourceDelivery s R u) (N : ℕ) (hR : 0 ≤ R (s N)) :
    ∑ n ∈ Finset.range N, u n ≤ R (s 0) := by
  rw [totalDelivery_eq_source_loss s R u h N]
  linarith

/-- **A finite source buys a longer horizon, not an unbounded one.** The store
and the source enter the same bound, so refuelling adds its initial content to
the initial store and changes nothing else about the shape of the result. -/
theorem horizon_le_of_sourced_delivery {S : Type*} (s : ℕ → S) (B R : S → ℝ)
    (d u : ℕ → ℝ) (N : ℕ) (c : ℝ)
    (hled : ∀ n < N, B (s (n + 1)) = B (s n) - d n + u n)
    (hsrc : SourceDelivery s R u) (hc : ∀ n < N, c ≤ d n)
    (hB : 0 ≤ B (s N)) (hR : 0 ≤ R (s N)) :
    (N : ℝ) * c ≤ B (s 0) + R (s 0) := by
  have hb := balance_sum s B d u N hled
  have hd : ∑ n ∈ Finset.range N, c ≤ ∑ n ∈ Finset.range N, d n :=
    Finset.sum_le_sum fun n hn => hc n (Finset.mem_range.mp hn)
  have hu := delivery_le_source s R u hsrc N hR
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hd
  linarith

/-- **No finite source sustains a positive cost forever.** Given the ledger, a
delivery that is some nonnegative source's loss, a store that never reads below
empty, and a strictly positive cost at every operation, the hypotheses are
jointly contradictory: there is no such run.

This is the precise sense in which `refuel`'s `d ≤ u` declares an external
supply rather than modelling one. Sustained operation is not a property a finite
agent can have; it is a hypothesis about what is outside the boundary. -/
theorem no_finite_source_sustains {S : Type*} (s : ℕ → S) (B R : S → ℝ)
    (d u : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hled : ∀ n, B (s (n + 1)) = B (s n) - d n + u n)
    (hsrc : SourceDelivery s R u) (hcost : ∀ n, c ≤ d n)
    (hB : ∀ n, 0 ≤ B (s n)) (hR : ∀ n, 0 ≤ R (s n)) : False := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((B (s 0) + R (s 0)) / c)
  have hbound := horizon_le_of_sourced_delivery s B R d u N c
    (fun n _ => hled n) hsrc (fun n _ => hcost n) (hB N) (hR N)
  rw [div_lt_iff₀ hc] at hN
  linarith

end ResourceTrajectory


#print axioms ResourceTrajectory.horizon_bound
#print axioms entropy_reduction_le_bathEntropy
#print axioms ResourceTrajectory.draw_eq_thermal_work
#print axioms FiniteFeedbackStep.sharp_preparation_extendedKL_top
#print axioms ResourceTrajectory.no_finite_source_sustains

end PhysicsOfConsciousness
