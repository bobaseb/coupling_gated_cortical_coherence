/-
  Examples/Phase1.lean — the primitives: a field, a broken symmetry, a capacity

  §3 inhabits `ActionPrinciples` on a one-point spacetime — the degenerate case
  rather than the simplest-looking one. §11 is the double well: the symmetry, its
  breaking, and §11.1's computation that the vacuum manifold `{-1, 1}` is
  disconnected, which is what forces a wall. §19 is the capacity of a finite
  phase space on two bits, together with the `Nat.succ` refutation that fences
  the claim off from infinite spaces.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase1_PhaseSpaceCapacity
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Examples.Bit

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

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

/-! ## 11. A double well: the symmetry, its breaking, and why the conclusion is a.e.

`§3` witnesses `ActionPrinciples` on a one-point spacetime with `V v = v²`. That
suffices to show the class is inhabitable and nothing more: the vacuum is a
single point, so there is no symmetry to break, and on a one-point spacetime
"almost everywhere" and "everywhere" coincide, so the theorem's actual
conclusion is invisible. This section fixes both.

The substrate is `Bool` carrying `Measure.dirac true` — a probability measure
whose support is one of the two points, so a field can deviate off the support
for free. The potential is the double well `V v = (v² - 1)²`, whose vacuum
manifold is `{-1, 1}`: **degenerate**, which is the premise the phrase
"spontaneous symmetry breaking" presupposes and which `§3`'s `v²` does not have.

Three things get proved here that were previously assumed or unstated.

* **`h_min` is discharged, not hypothesised.** `spontaneous_symmetry_breaking`
  takes `h_min : ∀ phi', TotalEnergy phi ≤ TotalEnergy phi'` as an assumption,
  and no compactness or direct-method argument anywhere in the development
  produces one. Here `wellSpike_global_min` proves it outright, so the theorem is
  applied to a system where its hypothesis is a fact.
* **The `∀ᵐ` cannot be strengthened to `∀`.** `wellSpike` sits at the vacuum on
  the support and at `0` off it; `wellSpike_ae_vacuum` holds and
  `wellSpike_not_everywhere_vacuum` proves the pointwise version *fails* for the
  same field. The doc-string on `pointwise_vacuum_of_global_min` says the old
  `∀ x` form "was one of the reasons the axiomatic formulation was unsound"; this
  is that claim as a theorem.
* **The symmetry classes are inhabited, and the symmetry is a real one.**
  `signSymmetry` is the `ℤ₂` action `v ↦ ±v` on the value space;
  `signInvariant` discharges `total_energy_invariant` because `(±v)² = v²`. The
  action is not trivial — `symmetry_swaps_vacua` sends one vacuum to the other —
  so `wellSpike` and its image have equal energy and differ
  (`wellSpike_partner_same_energy`, `wellSpike_partner_ne`): a symmetric
  functional with a non-symmetric minimiser, which is what symmetry breaking is.

**What this does not establish.** There is still no Noether theorem: nothing
constructs a conserved quantity from `signInvariant`, and `ℤ₂` is discrete, so
there is no one-parameter family to differentiate along in the first place. The
`Continuous` in `ContinuousSymmetryGroup` is a name, not a hypothesis — the class
carries no continuity or homomorphism law at all, which is why this instance is
cheap. And the spacetime is two points with a Dirac measure, so nothing here
exercises any geometry. -/

/-- The double well `V v = (v² - 1)²`. Vacuum manifold `{-1, 1}`. -/
noncomputable def wellV (v : ℝ) : ℝ := (v ^ 2 - 1) ^ 2

/-- Total energy on the two-point spacetime: the potential integrated against
`δ_true`, so only the value at `true` counts. -/
noncomputable def wellEnergy (phi : FieldState Bool ℝ) : ℝ :=
  ∫ x, wellV (phi x) ∂(Measure.dirac true)

noncomputable instance wellAction :
    ActionPrinciples Bool ℝ (fun _ => 0) wellEnergy wellEnergy wellV
      (Measure.dirac true) where
  total_eq := by intro phi; simp
  kinetic_nonneg := by intro phi; norm_num
  kinetic_const := by intro v; rfl
  potential_integral := by intro phi; rfl
  potential_integrable := by intro phi; exact Integrable.of_finite

@[simp] theorem wellEnergy_apply (phi : FieldState Bool ℝ) :
    wellEnergy phi = wellV (phi true) := by
  unfold wellEnergy; simp

/-- The vacuum is degenerate: both `1` and `-1` minimise, and they differ. This
is what `§3`'s single-well witness lacks. -/
theorem one_mem_vacuum : (1 : ℝ) ∈ DynamicalVacuum wellV := by
  intro v'; simp [wellV]; positivity

theorem neg_one_mem_vacuum : (-1 : ℝ) ∈ DynamicalVacuum wellV := by
  intro v'; simp [wellV]; positivity

theorem vacuum_degenerate :
    (1 : ℝ) ∈ DynamicalVacuum wellV ∧ (-1 : ℝ) ∈ DynamicalVacuum wellV
      ∧ (1 : ℝ) ≠ -1 :=
  ⟨one_mem_vacuum, neg_one_mem_vacuum, by norm_num⟩

theorem zero_not_mem_vacuum : (0 : ℝ) ∉ DynamicalVacuum wellV := by
  intro h
  have := h 1
  simp [wellV] at this
  linarith

/-- At the vacuum on the support of the measure, off it elsewhere. -/
noncomputable def wellSpike : FieldState Bool ℝ :=
  ⟨fun b => if b then 1 else 0, continuous_of_discreteTopology⟩

/-- **The minimisation hypothesis, discharged.** `h_min` of
`spontaneous_symmetry_breaking` is an assumption everywhere else in the
development; here it is a proof. -/
theorem wellSpike_global_min : ∀ phi', wellEnergy wellSpike ≤ wellEnergy phi' := by
  intro phi'
  rw [wellEnergy_apply, wellEnergy_apply]
  have h : wellV (wellSpike true) = 0 := by simp [wellSpike, wellV]
  rw [h]
  simp [wellV]
  positivity

/-- Derivation 1 applied to a system whose every hypothesis is proved. -/
theorem wellSpike_ae_vacuum :
    ∀ᵐ x ∂(Measure.dirac true), wellSpike x ∈ DynamicalVacuum wellV :=
  spontaneous_symmetry_breaking wellAction wellSpike 1 one_mem_vacuum wellSpike_global_min

/-- **And the almost-everywhere is necessary.** The same energy-minimising field
leaves the vacuum at `false`, which the measure does not see. -/
theorem wellSpike_not_everywhere_vacuum :
    ¬ ∀ b : Bool, wellSpike b ∈ DynamicalVacuum wellV := by
  intro h
  exact zero_not_mem_vacuum (by simpa [wellSpike] using h false)

/-- The `ℤ₂` sign symmetry `v ↦ ±v`, acting trivially on spacetime. The class
carries no law, so the content is entirely in `signInvariant` below. -/
noncomputable instance signSymmetry : ContinuousSymmetryGroup ℤˣ Bool ℝ where
  space_action := fun _ x => x
  value_action := fun g v => ((g : ℤ) : ℝ) * v
  field_action := fun g phi =>
    ⟨fun x => ((g : ℤ) : ℝ) * phi x, continuous_of_discreteTopology⟩

/-- **The energy really is invariant**, because `(±v)² = v²`. This is the first
instance of `SymmetryInvariantAction` in the development; the class previously
had none, and `main.tex` said so. -/
instance signInvariant :
    SymmetryInvariantAction ℤˣ Bool ℝ (fun _ => 0) wellEnergy wellEnergy wellV
      (Measure.dirac true) where
  total_energy_invariant := by
    intro g phi
    rw [wellEnergy_apply, wellEnergy_apply]
    show wellV (((g : ℤ) : ℝ) * phi true) = wellV (phi true)
    rcases Int.units_eq_one_or g with h | h <;> simp [h, wellV]

/-- The symmetry is not trivial on the vacuum: it exchanges the two minima. -/
theorem symmetry_swaps_vacua :
    ContinuousSymmetryGroup.value_action (G := ℤˣ) (Spacetime := Bool) (-1 : ℤˣ) (1 : ℝ)
      = -1 := by
  show ((((-1 : ℤˣ) : ℤ)) : ℝ) * 1 = -1
  norm_num

/-- **Symmetry breaking, exhibited.** The minimiser has a distinct image under a
symmetry of the energy, and the image has the same energy. So the minimiser is
not invariant even though the functional is. -/
theorem wellSpike_partner_same_energy :
    wellEnergy (ContinuousSymmetryGroup.field_action (-1 : ℤˣ) wellSpike)
      = wellEnergy wellSpike :=
  signInvariant.total_energy_invariant (-1 : ℤˣ) wellSpike

theorem wellSpike_partner_ne :
    (ContinuousSymmetryGroup.field_action (-1 : ℤˣ) wellSpike) true ≠ wellSpike true := by
  show ((((-1 : ℤˣ) : ℤ)) : ℝ) * wellSpike true ≠ wellSpike true
  simp [wellSpike]
  norm_num

/-! ### 11.1 The vacuum manifold is disconnected, and that forces a wall

  Everything above concerns the *energy* side of Derivation 1: a degenerate
  minimum, a symmetry that exchanges its two branches, and a minimiser that is
  not invariant. None of it produces a defect. The section's title claims
  inevitability of boundaries, and the theorem that delivers it is the `π₀`
  obstruction in `Phase1_Primitives.lean` §3 — which needs the vacuum manifold
  to be genuinely disconnected, and needs that to be proved rather than drawn.

  `wellVacuum_eq` computes the vacuum manifold of the double well outright:
  `DynamicalVacuum wellV = {-1, 1}`. Before this the file knew only that `1` and
  `-1` are in it and `0` is not, which leaves open that the set is larger and
  possibly connected. `wellVacuum_separated` then proves the disconnection in
  the form the theorem consumes: **no** preconnected subset of the vacuum
  manifold contains both minima, because a preconnected subset of `ℝ` is an
  interval and an interval spanning `-1` and `1` contains `0`, which is at the
  top of the barrier.

  `wellV_domain_wall` is the payoff and it quantifies over *every* field: any
  continuous field on any connected substrate that reaches `-1` somewhere and
  `1` somewhere else leaves the vacuum manifold at some point. No formula for
  the field appears, and none is needed — this is the sense in which the wall is
  inevitable rather than exhibited.

  **Non-vacuity is a separate question and is answered separately.** A theorem
  quantified over all fields is worthless if no field satisfies its hypotheses,
  so `kink` supplies one: the clipped identity on `ℝ`, at `-1` below `-1`, at
  `1` above `1`. `kink_leaves_vacuum` fires the theorem on it, and
  `kink_zero_notMem` locates the wall — at the origin, where the field sits at
  the top of the barrier — so the existence statement is not merely formal.
-/

section DomainWall

/-- **The vacuum manifold, computed.** `{-1, 1}` exactly: a minimiser has
`(v² - 1)² ≤ 0`, so `v² = 1`. -/
theorem wellVacuum_eq : DynamicalVacuum wellV = {-1, 1} := by
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have h1 : wellV v ≤ wellV 1 := h 1
    have h0 : wellV 1 = 0 := by norm_num [wellV]
    have hsq : (v ^ 2 - 1) ^ 2 ≤ 0 := by rw [h0] at h1; exact h1
    have hfac : (v - 1) * (v + 1) = 0 := by nlinarith [sq_nonneg (v ^ 2 - 1)]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (rfl | rfl)
    · exact neg_one_mem_vacuum
    · exact one_mem_vacuum

/-- **The disconnection, in the form the `π₀` theorem consumes.** No preconnected
subset of the vacuum manifold contains both minima.

In `ℝ` a preconnected set is order-convex, so one containing `-1` and `1`
contains the whole interval between them, and in particular `0` — which is the
top of the barrier, not a minimum. -/
theorem wellVacuum_separated (S : Set ℝ) (hS : _root_.IsPreconnected S)
    (hSM : S ⊆ DynamicalVacuum wellV) (h1 : (-1 : ℝ) ∈ S) : (1 : ℝ) ∉ S := by
  intro h2
  have h0 : (0 : ℝ) ∈ S :=
    hS.Icc_subset h1 h2 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  exact zero_not_mem_vacuum (hSM h0)

/-- **Derivation 1's central claim, as a theorem.** Every continuous field on a
connected substrate that sits at one vacuum somewhere and at the other somewhere
else leaves the vacuum manifold at some point.

The substrate `X` is arbitrary — any connected topological space — and the field
is arbitrary. Nothing is exhibited and nothing is solved: this is the
inevitability the section's title claims, and it holds of fields for which no
formula exists. -/
theorem wellV_domain_wall {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (phi : X → ℝ) (h_cont : Continuous phi) (a b : X)
    (ha : phi a = -1) (hb : phi b = 1) :
    ∃ x, phi x ∉ DynamicalVacuum wellV := by
  refine exists_notMem_of_no_common_preconnected _ phi h_cont a b fun S hS hSM haS => ?_
  rw [hb]
  rw [ha] at haS
  exact wellVacuum_separated S hS hSM haS

/-! #### A field that satisfies the hypotheses -/

/-- The clipped identity: `-1` below `-1`, `1` above `1`, and the straight climb
between them. A field connecting the two vacua, so the theorem above is not
quantifying over an empty class. -/
noncomputable def kink : ℝ → ℝ := fun x => max (-1) (min 1 x)

theorem kink_continuous : Continuous kink := by
  unfold kink
  exact continuous_const.max (continuous_const.min continuous_id)

@[simp] theorem kink_neg_one : kink (-1) = -1 := by norm_num [kink]

@[simp] theorem kink_one : kink 1 = 1 := by norm_num [kink]

@[simp] theorem kink_zero : kink 0 = 0 := by norm_num [kink]

/-- The theorem fires on a real substrate: `kink` cannot stay in the vacuum. -/
theorem kink_leaves_vacuum : ∃ x : ℝ, kink x ∉ DynamicalVacuum wellV :=
  wellV_domain_wall kink kink_continuous (-1) 1 kink_neg_one kink_one

/-- **And the wall is where one expects it.** At the origin the field is at the
top of the barrier. Recorded so that `kink_leaves_vacuum` is not merely a formal
existence statement. -/
theorem kink_zero_notMem : kink 0 ∉ DynamicalVacuum wellV := by
  rw [kink_zero]; exact zero_not_mem_vacuum

/-- The field really does connect the two components, rather than satisfying the
hypotheses degenerately: its two endpoint values are distinct minima. -/
theorem kink_connects_distinct_vacua :
    kink (-1) ∈ DynamicalVacuum wellV ∧ kink 1 ∈ DynamicalVacuum wellV
      ∧ kink (-1) ≠ kink 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [kink_neg_one]; exact neg_one_mem_vacuum
  · rw [kink_one]; exact one_mem_vacuum
  · rw [kink_neg_one, kink_one]; norm_num

end DomainWall

/-! ## 19. The capacity of a finite phase space, on two bits

  `Phase1_PhaseSpaceCapacity.lean` is the answer to the standing complaint that
  the first premise "contributes vocabulary rather than content". This section
  runs its three theorems on the smallest system that can carry them, and — as
  everywhere else in this file — fences the hypotheses that are doing the work.

  What is witnessed:

  * the capacity bound is *attained*, so `log |X|` is the exact figure and not a
    slack over-estimate (`bool_uniform_entropy`);
  * it is *strict* off the uniform law, on a concrete biased bit
    (`biased_bit_below_capacity`);
  * a two-letter stream of length two already outruns a one-bit phase space
    (`bit_cannot_record_two_perturbations`), and its entropy strictly exceeds
    anything that phase space can hold (`two_bit_source_exceeds_bit_capacity`);
  * an unreachable state on a finite phase space costs heat, on §1's
    `boolStatMech` (`unreachable_state_costs_heat`);
  * and the finiteness hypothesis is not decoration: on `ℕ` the same step fails,
    because `Nat.succ` is injective and misses `0`
    (`succ_is_not_an_erasure`). That last one is the fence. Without it,
    `is_erasure_of_not_surjective` would read like a triviality about maps
    rather than a fact about *finite* phase spaces.
-/

section PhaseSpaceCapacityWitness

/-- The uniform law on a bit is the fair coin. -/
theorem bool_uniformDist_eq : uniformDist Bool = fun _ => (1 : ℝ) / 2 := by
  funext b
  simp [uniformDist]

/-- **Capacity is attained.** One bit holds exactly `log 2` nats. -/
theorem bool_uniform_entropy : shannon_entropy (uniformDist Bool) = Real.log 2 := by
  rw [shannon_entropy_uniformDist]
  norm_num

/-- A bit that is not fair: `3/4` on `false`, `1/4` on `true`. -/
noncomputable def biasedBit : Bool → ℝ := fun b => if b then 1 / 4 else 3 / 4

theorem is_prob_dist_biasedBit : is_prob_dist biasedBit := by
  refine ⟨fun b => by cases b <;> norm_num [biasedBit], ?_⟩
  simp [biasedBit]
  norm_num

/-- **The bound is strict off the uniform law**, on this instance rather than in
general: a biased bit holds strictly less than `log 2`. -/
theorem biased_bit_below_capacity : shannon_entropy biasedBit < Real.log 2 := by
  have h := shannon_entropy_lt_log_card_of_ne_uniform biasedBit is_prob_dist_biasedBit true
    (by simp [biasedBit])
  simpa using h

/-- **A one-bit phase space cannot record two binary perturbations.** Four
histories, two states. The update below is a genuine one — the perturbation is
`xor`-ed into the state, which is *reversible at each step* — so the collision is
not an artefact of a lossy update but of the phase space being smaller than the
stream. -/
theorem bit_cannot_record_two_perturbations :
    ¬ Function.Injective (fun w : Fin 2 → Bool => absorb (fun s p => xor s p) false w) := by
  apply absorb_not_injective
  simp

/-- The two histories that collide, exhibited. `absorb` on `xor` returns the
parity of the word, so `(true, false)` and `(false, true)` are indistinguishable
to the system while being different perturbation streams. -/
example :
    absorb (fun s p => xor s p) false (![true, false] : Fin 2 → Bool)
      = absorb (fun s p => xor s p) false (![false, true] : Fin 2 → Bool) := by
  decide

/-- **The source outruns the capacity, entropically.** No law on one bit reaches
the entropy of the uniform law on two-letter words of length two. -/
theorem two_bit_source_exceeds_bit_capacity (p : Bool → ℝ) (hp : is_prob_dist p) :
    shannon_entropy p < shannon_entropy (uniformDist (Fin 2 → Bool)) :=
  source_entropy_exceeds_capacity 2 (by simp) p hp

/-- **An unreachable state costs heat**, on §1's one-bit thermodynamic system.
`fun _ => false` never reaches `true`; §1's `boolStatMech` supplies the bath, and
`finite_phase_space_dissipates` supplies the rest. This is the same conclusion §1
reaches by exhibiting non-injectivity directly — the point is that the hypothesis
is now the physically checkable one. -/
theorem unreachable_state_costs_heat :
    heat_dissipation (fun _ => false : Bool → Bool) > 0 := by
  apply finite_phase_space_dissipates
  intro hsurj
  obtain ⟨b, hb⟩ := hsurj true
  exact Bool.noConfusion hb

/-- **The finiteness hypothesis is load-bearing.** `Nat.succ` misses `0` and is
injective, so on an infinite phase space "cannot reach every state" does not
imply erasure and no Landauer charge follows. `is_erasure_of_not_surjective`
therefore says something about finite phase spaces specifically, which is what
makes it a consumer of the first premise rather than a general fact about
maps. -/
theorem succ_is_not_an_erasure :
    ¬ Function.Surjective Nat.succ ∧ ¬ is_erasure Nat.succ := by
  refine ⟨fun h => ?_, fun h => h Nat.succ_injective⟩
  obtain ⟨n, hn⟩ := h 0
  exact Nat.succ_ne_zero n hn

/-- **Refreshing the incoming register is what dissipates**, exhibited on the
joint two-bit space. The record-keeping alternative is injective and appears
immediately below, so the two are visibly different maps rather than two
descriptions of one. -/
theorem absorbStep_bool_is_erasure :
    is_erasure (absorbStep (fun s p => xor s p) false) :=
  absorbStep_is_erasure _ (p₁ := true) (by simp)

/-- The map that keeps the record instead of refreshing it **is** injective, so
nothing forces it to dissipate. This is the Norton / Shenker point in one line:
losing the history is not the same as erasing it, and only the second is
charged. -/
theorem keepRecord_injective :
    Function.Injective (fun sp : Bool × Bool => (xor sp.1 sp.2, sp.2)) := by
  decide

end PhaseSpaceCapacityWitness

end Examples
end PhysicsOfConsciousness
