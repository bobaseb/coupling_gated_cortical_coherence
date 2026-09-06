import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase1_PhaseSpaceCapacity
import PhysicsOfConsciousness.Phase2_SimplicialBridge
import PhysicsOfConsciousness.Phase2_MeshConvergence
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_KLBound
import PhysicsOfConsciousness.Phase3_PredictiveThermodynamics
import PhysicsOfConsciousness.Phase3_MeasureThermodynamics
import PhysicsOfConsciousness.Phase4_KuramotoDynamics
import PhysicsOfConsciousness.Phase4_RotatingFrame
import PhysicsOfConsciousness.Phase4_MacroscopicScaling
import PhysicsOfConsciousness.Phase5_GlobalSection
import PhysicsOfConsciousness.Phase5_EquilibriumBridge
import PhysicsOfConsciousness.Phase6_ReflexiveTopology
import PhysicsOfConsciousness.Phase7_HardwareComparison
import PhysicsOfConsciousness.Phase7_Rigidity
import PhysicsOfConsciousness.Phase8_ContinuousField
import PhysicsOfConsciousness.Phase8_SelfConsistency
import PhysicsOfConsciousness.Phase9_EMIdentification
import PhysicsOfConsciousness.Examples

/-!
# The chain, as one theorem

Every other module in this development proves things about *one* link of the
deductive chain. This module is about the **edges**: it states each node as a
`Prop`, and for each arrow of the chain either proves the passage from one node
to the next or records it as a named hypothesis of `chain`.

## Why the module exists

Compiling ten developments certifies that each of them is consistent. It does
not certify that they run into one another, and until this file nothing in the
development did. The evidence was in the import graph rather than in the prose:

* `Phase8_SelfConsistency` — the whole `K_c = 2D` bifurcation, node n7 — had
  exactly one importer, the root aggregator. Nothing consumed it.
* `Phase2_MeshConvergence` (n5) and `Phase3_PredictiveThermodynamics` (n4) were
  imported only by `Examples.lean`, which consumes their *witnesses* and none of
  their theorems.
* The one apparent cross-link, from n7 to n9, ran through
  `critical_coupling D = 2 * D`, a `def`. `self_of_supercritical` consumes the
  numeral `2 * D`, not the bifurcation theorem, and would prove exactly what it
  proves if `Phase8_SelfConsistency.lean` were deleted.

So the honesty of this development was **per node, not per edge**. This file is
where the edges become checkable objects.

## How to read it

`chain` takes the named hypotheses as explicit arguments and concludes `Self`.
Two consequences, and they are the point:

* A gap recorded in prose can be softened by a later edit. A gap that is an
  argument to `chain` cannot: delete it and the build fails.
* The number of gaps is a number the reader can obtain in one command
  (`#check @chain`) rather than a claim they have to trust.

Each named hypothesis carries a docstring saying what it asserts physically, what
would discharge it, and which of three kinds it is:

* **Formalization gap** — true, provable, nobody has done it in Lean;
* **Modelling assumption** — an idealisation the framework adopts knowingly;
* **Physical commitment** — could simply be false of cortex.

The three are not equally serious and the manuscript used to blur the first two.

## What is deliberately *not* here

* **`n0` is not a chain node.** `Phase1_Primitives`'s spacetime, metric and
  symmetry group are consumed by no theorem anywhere, and the figure's `n0 → n1`
  arrow is therefore an inference that does not exist. There is no `e01`.
* **`n10` is outside the theorem.** "That fixed point is experience" is the
  framework's stipulation. It is named and owned in the manuscript; encoding it
  here would turn a stipulation into a hypothesis of a theorem and make it look
  like the same kind of object as the rest. It is not.
* **No edge is manufactured.** An "edge" whose proof is a definitional unfolding
  is worse than a named hypothesis, because it looks like content. The n7 → n9
  link used to be exactly that failure: `self_of_supercritical` consumes
  `critical_coupling D < K`, and `critical_coupling` unfolds to `2 * D`, so the
  Self was provable with the bifurcation deleted. `supercritical_of_coherent`
  (§2) closes it in the other direction — a coherent order parameter *forces*
  `K > K_c` — so the last step of `chain` now consumes Derivation 7's theorem.

## Composition order

`Chain.lean` sits above every phase module and nothing imports it except the root
aggregator. No existing module's imports were rewired: composition happens at the
top, so no phase file acquires a new dependency and no cycle is possible.
-/

open CategoryTheory TopologicalSpace MeasureTheory Opposite
open Filter Topology
open scoped NNReal ENNReal

namespace PhysicsOfConsciousness

namespace Chain

universe u

/-! ## 1. The nodes, as propositions

Each definition below is the *conclusion* of one link, stated so that an edge can
be an implication between two of them. Where a node's content is "a structure
exists and its theorem applies", the node is an existential over that structure —
otherwise the implication into it would be provable by unfolding, and the edge
would be manufactured rather than proved.
-/

/-- **n1 — a finite phase space has bounded information capacity.**
`H(p) ≤ log |X|` for every distribution on `sys`. Proved outright by
`capacity`; its only hypothesis about the system is finiteness. -/
def Capacity (sys : Type*) [Fintype sys] : Prop :=
  ∀ p : sys → ℝ, is_prob_dist p → shannon_entropy p ≤ Real.log (Fintype.card sys)

/-- **n2 — broken symmetry forces a boundary.** The field `phi` leaves the vacuum
manifold `vac` somewhere. This is the `π₀` case of Kibble's classification, and
`exists_notMem_of_no_common_preconnected` proves it from connectedness of the
substrate and disconnectedness of the vacuum manifold. -/
def LeavesVacuum {Y V : Type*} (vac : Set V) (phi : Y → V) : Prop :=
  ∃ y, phi y ∉ vac

/-- **n3 — the boundary erases, and erasure costs heat.** The register update
`t` dissipates strictly positive heat. -/
def Dissipates {sys : Type*} [Thermodynamics sys] (t : sys → sys) : Prop :=
  heat_dissipation t > 0

/-- **n4 — dissipation is bounded below by the nonpredictive information.**

Stated as an existential over `PredictiveDissipation` rather than as a bare
inequality. The inequality alone is a theorem of the class
(`PredictiveDissipation.nonpredictive_le_dissipation`), so an implication into it
would be provable by ignoring its hypothesis; what n4 actually asserts is that
the boundary *carries* such a structure — a joint law, a signal dynamics, finite
memory, and Still's bound discharged. -/
def PredictiveBound (Xs Sg Sg' : Type*)
    [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg'] : Prop :=
  ∃ R : PredictiveDissipation Xs Sg Sg',
    (R.nonpredictive).toReal ≤ R.dissipatedWork / R.thermalEnergy

/-- **n5 — discrete couplings coarse-grain to a continuous kernel.** The discrete
coupling energies `E n` of a refining sequence of triangulations converge to the
continuum value `L`.

Abstracted to a sequence and its limit rather than carrying the eight hypotheses
of `mesh_refinement_convergence`, which `coarseGrains_of_meshRefinement` below
supplies. About the *energy functional*, not about the dynamics — see `e56`. -/
def CoarseGrains (E : ℕ → ℝ) (L : ℝ) : Prop :=
  Tendsto E atTop (𝓝 L)

/-- **n6 — the field realizing that kernel in cortex is the endogenous EM field.**

Not formalized and not derivable, and this definition does not pretend
otherwise. What it records is the *only thing the formal chain can ask of the
identification*: that the continuum coupling energy `L` produced by n5 is the
mean-field coupling constant `K` of the field whose phase noise is `D > 0`. No
formal object in this development denotes cortex, so nothing stronger is
statable here.

That is itself worth recording. The empirical commitment enters the chain as an
identification of two real numbers and a sign condition; everything else about
it — that the field is electromagnetic, that it is endogenous, that it is the
one measured by EEG — is carried by the manuscript and by no theorem. -/
def FieldRealizes (L K D : ℝ) : Prop :=
  0 < D ∧ 0 ≤ K ∧ L = K

/-- **n7 — above `K_c = 2D` a coherent order parameter exists and is unique.**
The self-consistency equation `r = R(K, r)` has exactly one solution with
`0 < r ≤ 1`. -/
def Coherent (K D : ℝ) : Prop :=
  ∃! r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency K D r

variable {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X]

/-- **n8 — synchronized local states glue to one global section: unity.**

An existential over `ThermodynamicCover` for the same reason n4 is an existential:
`global_section_from_thermodynamics` is a theorem *of* the class, so the content
of n8 is that the substrate carries such a cover, not that gluing works once it
does. -/
def Unity (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X]
    [TriangulatedManifold ↥X] : Prop :=
  ∃ T : ThermodynamicCover X, ∃! s : GlobalSection (X := X),
    ∀ i : T.I, (probabilityPresheaf X).map (homOfLE (le_top : T.cover i ≤ ⊤)).op s
      = T.sync_to_section i

/-- A particular global section is the unity produced by `T`: it restricts to
every local state of that thermodynamic cover. -/
def IsUnifiedBy (T : ThermodynamicCover X) (s : GlobalSection (X := X)) : Prop :=
  ∀ i : T.I, (probabilityPresheaf X).map (homOfLE (le_top : T.cover i ≤ ⊤)).op s
    = T.sync_to_section i

/-- **n9 — the self-prediction map has a unique fixed point: the Self.** -/
def Self (rb : ReflexiveBoundary X) : Prop :=
  ∃! s : GlobalSection (X := X), rb.predict s = s

/-- **n9, with the n8 state preserved.** A cover's glued global section is the
unique fixed point of the boundary's self-prediction map.

This is stronger than `Self rb`: it rules out the former shape in which one
global section witnessed Unity while an unrelated section witnessed the Self. -/
def UnifiedSelf (rb : ReflexiveBoundary X) : Prop :=
  ∃ (T : ThermodynamicCover X) (s : GlobalSection (X := X)),
    IsUnifiedBy T s ∧ rb.predict s = s ∧
      ∀ t : GlobalSection (X := X), rb.predict t = t → t = s

/-- Forgetting which cover produced the fixed point recovers the old `Self`
statement. -/
theorem unifiedSelf_self {rb : ReflexiveBoundary X} (h : UnifiedSelf rb) : Self rb := by
  obtain ⟨_, s, _, hs, huniq⟩ := h
  exact ⟨s, hs, huniq⟩

/-! ## 2. The node theorems

Each of these says that the corresponding node is reached once its own link's
hypotheses are in hand. They are wrappers, and they are here so that `chain`
reads as a composition rather than as a proof.
-/

/-- n1 holds outright. -/
theorem capacity (sys : Type*) [Fintype sys] [Nonempty sys] : Capacity sys :=
  fun p hp => shannon_entropy_le_log_card p hp

/-- n2 from the `π₀` obstruction. -/
theorem leavesVacuum_of_separated {Y V : Type*} [TopologicalSpace Y] [PreconnectedSpace Y]
    [TopologicalSpace V] (vac : Set V) (phi : Y → V) (h_cont : Continuous phi) (y₁ y₂ : Y)
    (h_sep : ∀ S : Set V, IsPreconnected S → S ⊆ vac → phi y₁ ∈ S → phi y₂ ∉ S) :
    LeavesVacuum vac phi :=
  exists_notMem_of_no_common_preconnected vac phi h_cont y₁ y₂ h_sep

/-- n3 from Landauer, with finiteness doing the step from "unreachable state" to
"many-to-one update". -/
theorem dissipates_of_not_surjective {sys : Type*} [Fintype sys] [DecidableEq sys]
    [Nonempty sys] [StatisticalMechanics sys] (t : sys → sys)
    (h : ¬ Function.Surjective t) : Dissipates t :=
  finite_phase_space_dissipates t h

/-- n4 from the existence of a predictive-dissipation structure. -/
theorem predictiveBound_of_nonempty {Xs Sg Sg' : Type*}
    [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']
    (h : Nonempty (PredictiveDissipation Xs Sg Sg')) : PredictiveBound Xs Sg Sg' :=
  h.elim fun R => ⟨R, R.nonpredictive_le_dissipation⟩

/-- n5 from mesh refinement. The bridge between the abstract sequence `CoarseGrains`
quantifies over and the theorem that produces it. -/
theorem coarseGrains_of_meshRefinement {M : Type u} [PseudoMetricSpace M] [MeasurableSpace M]
    (μ : MeasureTheory.Measure M) (f : M → ℝ) {S : Set M}
    (hf : UniformContinuous f) (hμS : μ S ≠ ⊤) (hfS : IntegrableOn f S μ)
    (TM : ℕ → TriangulatedManifold M) [∀ n, Fintype (TM n).V] [∀ n, LinearOrder (TM n).V]
    (hreg : ∀ n, IsRegularTriangulation (TM n) S)
    (m : ℕ → ℝ) (hm : Tendsto m atTop (𝓝 0))
    (hfine : ∀ n u v, ∀ x ∈ (TM n).edge_region u v, ∀ y ∈ (TM n).edge_region u v,
      dist x y ≤ m n) :
    CoarseGrains (fun n => discreteEnergy (TM n) μ f) (∫ x in S, f x ∂μ) :=
  mesh_refinement_convergence μ f hf hμS hfS TM hreg m hm hfine

/-- n7 from supercriticality: the bifurcation theorem. -/
theorem coherent_of_supercritical {K D : ℝ} (hD : 0 < D)
    (hKD : critical_coupling D < K) : Coherent K D :=
  supercritical_fixed_point_existsUnique hD hKD

/-- **n7 → n9: the coherent order parameter forces supercriticality.**

The converse of `coherent_of_supercritical`, and the theorem that makes the Self
consume Derivation 7 rather than the numeral `2 * D`. Contrapositive of the first
component of `critical_coupling_is_threshold_unique`: at or below threshold the
only non-negative solution of `r = R(K, r)` is `r = 0`, so a strictly positive
one puts `K` above threshold.

Both sign conditions are supplied by n6 (`FieldRealizes`), which is where they
belong: `0 < D` is what makes the von Mises density a density at all, and
`0 ≤ K` is the unfrustrated-coupling assumption the development carries
throughout. -/
theorem supercritical_of_coherent {K D : ℝ} (hD : 0 < D) (hK : 0 ≤ K)
    (h : Coherent K D) : critical_coupling D < K := by
  obtain ⟨r, ⟨hr0, _, hfix⟩, _⟩ := h
  by_contra hcon
  exact hr0.ne'
    (fixed_point_eq_zero_of_le_critical hD hK (not_lt.mp hcon) hr0.le hfix)

/-- n8 from a cover at thermodynamic equilibrium: Derivation 5. -/
theorem unity_of_cover (h : Nonempty (ThermodynamicCover X)) : Unity X :=
  h.elim fun T => ⟨T, @global_section_from_thermodynamics X _ _ _ T⟩

/-- Unity produces an inhabitant of the global-section space. Kept for callers
of the standalone Banach theorem; `chain` no longer uses this lossy projection,
because doing so forgets which section the cover glued. -/
theorem nonempty_globalSection_of_unity (h : Unity X) :
    Nonempty (GlobalSection (X := X)) :=
  h.elim fun _ hT => ⟨hT.choose⟩

omit [TriangulatedManifold ↥X] in
/-- n9 from a contraction at the order parameter's relaxation rate. -/
theorem self_of_contraction [Nonempty (GlobalSection (X := X))]
    [MetricSpace (GlobalSection (X := X))] [CompleteSpace (GlobalSection (X := X))]
    {K D τ : ℝ} (hτ : 0 < τ) (hKD : critical_coupling D < K) (rb : ReflexiveBoundary X)
    (h_lip : LipschitzWith (resonanceRate K D τ) rb.predict) : Self rb :=
  self_of_supercritical hτ hKD rb h_lip

omit [TriangulatedManifold ↥X] in
/-- **C2's theorem: the Self, from the coherent order parameter.**

Derivation 6 with its threshold hypothesis replaced by Derivation 7's
conclusion. `self_of_supercritical` stays where it is — it is the correct
statement of its own claim — and this is the *edge*: the hypothesis is that a
coherent order parameter exists, and `supercritical_of_coherent` turns that into
the contraction rate.

The difference is not cosmetic. `self_of_supercritical` would prove exactly what
it proves if `Phase8_SelfConsistency.lean` were deleted, because
`critical_coupling D < K` unfolds to `2 * D < K`. This one would not. -/
theorem self_of_coherent_order_parameter [Nonempty (GlobalSection (X := X))]
    [MetricSpace (GlobalSection (X := X))] [CompleteSpace (GlobalSection (X := X))]
    {K D τ : ℝ} (hD : 0 < D) (hK : 0 ≤ K) (hτ : 0 < τ) (hcoh : Coherent K D)
    (rb : ReflexiveBoundary X)
    (h_lip : LipschitzWith (resonanceRate K D τ) rb.predict) : Self rb :=
  self_of_contraction hτ (supercritical_of_coherent hD hK hcoh) rb h_lip

/-! ## 3. The edges that are not theorems

Eight propositions, one per unproved arrow. Each is an implication between two of
the node predicates above, so that discharging one is a statement about the two
links it joins rather than about an opaque symbol.

The kinds, tallied: **one independent physical premise** (`E12`), **three
formalization gaps** (`E23`, `E34`, `E78`), **two modelling assumptions**
(`E45`, `E89`) and **two physical commitments** (`E56`, `E67`). There were nine
until `supercritical_of_coherent` discharged the n7 → n9 edge.
-/

/-- **n1 and n2 are independent physical premises, not a formalization gap.**

`Capacity sys` is a theorem with no hypotheses, so `E12` is logically equivalent
to its own conclusion: assuming it is assuming n2 outright. That is not a defect
of the encoding; it is what the figure's first arrow amounts to. The capacity
bound says nothing about vacuum manifolds, and the `π₀` obstruction says nothing
about entropy. **n1 and n2 are two independent starting points, not two links of
one chain.**

Where n1 *does* connect is n3: finiteness of the phase space is exactly what
turns "some state is unreachable" into "the update is many-to-one", which is
`is_erasure_of_not_surjective` and then Landauer. See
`dissipation_of_unreachable` below for that edge, which is a theorem, and note
that it skips n2 entirely. -/
def E12 (sys : Type*) [Fintype sys] {Y V : Type*} (vac : Set V) (phi : Y → V) : Prop :=
  Capacity sys → LeavesVacuum vac phi

/-- **n2 → n3. Formalization gap.**

Asserts that the defect forced by n2 is a region whose phase space is the finite
register `sys` and whose update cannot reach every state. Both halves are
unformalized: nothing in this development relates the topological locus
`{y | phi y ∉ vac}` to a state space, and nothing derives non-surjectivity of the
update from the geometry.

**What would discharge it.** A model in which the defect region carries a finite
register — the natural route is `absorbStep`, which is non-surjective as soon as
the perturbation alphabet has two letters (`absorbStep_not_surjective`), so the
missing step is the identification of the defect with a system absorbing a
stream, not the non-surjectivity. -/
def E23 {Y V : Type*} (vac : Set V) (phi : Y → V)
    {sys : Type*} (t : sys → sys) : Prop :=
  LeavesVacuum vac phi → ¬ Function.Surjective t

/-- **n3 → n4. Formalization gap.**

Asserts that a register that dissipates carries a `PredictiveDissipation`
structure *of that register*: a joint law over state and signal, a Markov signal
dynamics, finite memory, and a thermal budget that is the register's own — its
thermal scale is the system's temperature, its dissipated work is the system's
Landauer heat, and the memory it wastes is not zero.

**Why the three conjuncts are there.** Asking only for
`Nonempty (PredictiveDissipation Xs Sg Sg')` — which is what this edge asked
until 2026-09-03 — is asking for a structure that already exists:
`Examples.lean` §18.1's `frozenSystem` proves it for `Xs = Sg = Sg' = Bool` with
no reference to `t` at all, so the edge was dischargeable *by ignoring its
hypothesis*, which is the manufactured-edge shape this module exists to prevent.
`frozenSystem_not_of_eraser` is the regression: its dissipated work is `0` where
the register's Landauer heat is `log 2`, and it wastes no memory, so it fails
two of the three conjuncts.

**What would discharge it.** Landauer's heat and Still's dissipated work are two
accounts of the same physical quantity, and `Phase3_LandauerBridge.lean` now
identifies them: `PredictiveDissipation.ofLandauer` builds exactly this structure
from a bipartite environment, deriving `still_bound` from `landauer_bound`
instead of assuming it a second time. What that constructor still requires, and
what keeps this edge a named hypothesis rather than a theorem, is the physical
identification `(nonpredictiveInfo μ κ).toReal ≤ erasedEntropy t`: that the bits
the register clears are the bits its memory wasted. Nothing relates `μ`, `κ` and
`t` except that inequality, and `nonpredictive_eq_zero_of_injective` shows it is
not free — a reversible register cannot pay for a single wasted bit.

`e34_boolEraser` below discharges the edge on `§1`'s one-bit eraser, where the
inequality is an equality. -/
def E34 {sys : Type*} [Fintype sys] [DecidableEq sys] [Thermodynamics sys] (t : sys → sys)
    (Xs Sg Sg' : Type*) [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg'] :
    Prop :=
  Dissipates t → ∃ R : PredictiveDissipation Xs Sg Sg',
    R.thermalEnergy = Thermodynamics.temperature (sys := sys)
      ∧ R.dissipatedWork = heat_dissipation t
      ∧ 0 < (R.nonpredictive).toReal

/-- **n4 → n5. Modelling assumption.**

Asserts that a substrate held to a dissipation budget has couplings whose
discrete energies converge — that selection against nonpredictive memory is what
puts the coupling matrix in the regime where coarse-graining is legitimate.

This is the framework's central dynamical story and it is an *assumption*, not a
gap in the formalization: there is no theorem here or elsewhere that a
dissipation bound constrains a coupling matrix, because the two objects have no
formal relation. `Phase8_ContinuousField` §7 proves the nearest available thing —
that a gradient flow on the coupling kernel decreases entropy production — which
is the converse direction and at frozen phases. -/
def E45 (Xs Sg Sg' : Type*) [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']
    (E : ℕ → ℝ) (L : ℝ) : Prop :=
  PredictiveBound Xs Sg Sg' → CoarseGrains E L

/-- **n5 → n6. Physical commitment, and the load-bearing joint of the framework.**

Asserts that the continuum limit of the discrete coupling energy is the mean-field
coupling constant of the cortical electromagnetic field, whose phase noise is
positive, and that the field in question satisfies `IsEMFieldCoupling`: its
kernel is jointly continuous, its substrate is normalized, `K` *is* that kernel's
mean-field average, no single site carries more than half of it, and `D` is the
field's own noise.

**This is the one that could simply be false**, and the manuscript says so: the
kernel might be realized by synaptic connectivity, by gap junctions, or by
nothing with a mean-field description at all. It is not a formalization gap —
there is no Lean statement that would settle it — and it is not a modelling
idealisation, because the framework's empirical content lives here.

The two conjuncts do different work. `FieldRealizes` relates three real numbers
and is what the chain's arithmetic consumes. `IsEMFieldCoupling` is what stops
those numbers from being free: it ties `K` and `D` to a named field on a named
substrate, so a model discharging `E56` must exhibit the kernel rather than
assert its strength. Neither conjunct says the field is electromagnetic, or that
the substrate is cortex; no formal object here denotes cortex.

The second conjunct is not inert. `em_field_exhibits_phase_transition` below
consumes it together with `E67` to conclude `exhibits_phase_transition` for the
very field `E56` names — a statement about a substrate, which `FieldRealizes`
alone cannot reach. -/
def E56 {M : Type*} [MeasureSpace M] [TopologicalSpace M] (sys : StochasticNeuralField M)
    (Xs Sg Sg' : Type*) [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']
    (E : ℕ → ℝ) (L K D : ℝ) : Prop :=
  CoarseGrains E L → (FieldRealizes L K D ∧ Nonempty (IsEMFieldCoupling sys K D))

/-- **n6 → n7. Physical commitment.**

Asserts that cortex operates *above* the synchronization threshold,
`K > K_c = 2D`. Separate from `E56` and weaker in kind: `E56` says which field
realizes the kernel, `E67` says which regime that field is in.

**What would discharge it.** Nothing in Lean; this is a measurement. `K` and `D`
are estimable from the same data the sleep-inertia prediction is fitted against,
which makes this the most nearly testable of the three commitments. Note the
negative half is already a theorem: below threshold Derivation 6's argument is
not merely hard but unavailable (`not_contractingWith_resonanceRate`). -/
def E67 (L K D : ℝ) : Prop :=
  FieldRealizes L K D → critical_coupling D < K

/-- **n7 → n8. Formalization gap.**

Asserts that a substrate with a coherent order parameter carries a
`ThermodynamicCover`: a finite cover with positive symmetric couplings sitting at
the minimum of the reduced Kuramoto potential, whose synchronized patches agree
where they overlap.

**Why the cover has to be a reached one, and coupled at `K`.** Until 2026-09-03
this edge asked for `Nonempty (ThermodynamicCover X)`, and `Examples.lean` §4's
`cortexCover` proves that outright — a cover whose phase field is constant by
construction and whose coupling is unit, with no reference to `K`, to `D`, or to
any dynamics. The edge was dischargeable by ignoring its hypothesis. It now asks
for `ThermodynamicCover.IsReachedByRelaxation K`
(`Phase5_EquilibriumBridge.lean`): the cover's patches are coupled at least as
strongly as the mean field the coherent regime names, and its equilibrium
configuration is the limit of a Kuramoto trajectory on that coupling rather than
a configuration the instance was placed at.

Both halves have a fence. `trioCover_not_reachedByRelaxation_three` is a cover
that *is* reached and fails the coupling floor at `K = 3`; `cortexCover` is a
cover that meets no relaxation condition at all. `trioCover3` — three sites,
coupling `3`, initial data that is not phase-locked — is what discharges the
edge in §8, through `ThermodynamicCover.ofConvergentTrajectory`.

**What would still discharge it as a theorem, and does not.** Nothing derives a
cover from a coherent order parameter. `ofConvergentTrajectory` needs initial
data in the basin of §7, and n7 supplies a statement about a continuum mean
field, not initial data for a finite index set — the scale mismatch is exactly
where the edge sits, and the strengthened form makes it visible in the type
rather than in this paragraph. The cover's other physical hypothesis,
`LocalSectionSynchronization.section_agrees_of_phase_eq`, is untouched by any
dynamics here and is the standing open item ranked second in `tasks/todo.md`. -/
def E78 (K D : ℝ) (T : ThermodynamicCover X) : Prop :=
  Coherent K D → T.IsReachedByRelaxation K

/-- **n8 → n9. Modelling assumption, with the state identity explicit.**

Asserts both that the self-prediction map is Lipschitz at the order parameter's
linear relaxation rate and that the particular section glued by the cover is a
fixed point of that map. Banach supplies uniqueness; it cannot supply this
identification, which is the physical content the former edge omitted.

An idealisation rather than a gap: the rate is the linearisation of the
mean-field dynamics about the coherent branch, and taking the *nonlinear*
self-model to contract at the *linearised* rate is a modelling step the framework
makes knowingly. What it buys is that the contraction constant is read off the
substrate rather than stipulated — which is why replacing it by a bare
`ContractingWith c` would be weaker, not simpler. -/
def E89 {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X]
    [MetricSpace (GlobalSection (X := X))] (K D τ : ℝ) (T : ThermodynamicCover X)
    (rb : ReflexiveBoundary X) : Prop :=
  T.IsReachedByRelaxation K →
    ∃ s : GlobalSection (X := X),
      IsUnifiedBy T s ∧ LipschitzWith (resonanceRate K D τ) rb.predict ∧ rb.predict s = s

/- Regression specification for C2: E89 must consume the particular reached cover
supplied by E78, rather than choosing an unrelated cover. -/
example {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X]
    [MetricSpace (GlobalSection (X := X))] {K D τ : ℝ} {rb : ReflexiveBoundary X}
    (T : ThermodynamicCover X) (e89 : E89 K D τ T rb) (hT : T.IsReachedByRelaxation K) :
    ∃ s : GlobalSection (X := X), IsUnifiedBy T s ∧
      LipschitzWith (resonanceRate K D τ) rb.predict ∧ rb.predict s = s :=
  e89 hT

/-! ## 4. The edge that the figure does not draw

n1 → n3 is a theorem, and it is the only edge out of n1 that is one. The figure
routes n1 through n2; the development routes it past n2. See `E12`.
-/

/-- **Finiteness, straight to Landauer.** A finite phase space whose update cannot
reach every state dissipates. This is `finite_phase_space_dissipates` restated as
an edge, and it is the inference n1 actually supports: no vacuum manifold, no
symmetry, no boundary. -/
theorem dissipation_of_unreachable {sys : Type*} [Fintype sys] [DecidableEq sys]
    [Nonempty sys] [StatisticalMechanics sys] (t : sys → sys)
    (h : ¬ Function.Surjective t) : Capacity sys ∧ Dissipates t :=
  ⟨capacity sys, dissipates_of_not_surjective t h⟩

/-! ## 5. The chain -/

/--
**The conditional composition, end to end: n1 ⟹ n9.**

Eight named hypotheses, `e12 … e89`, one per arrow of Figure 1 that is not a
theorem. Everything else in the passage from a finite phase space to the
state-preserving `UnifiedSelf` is carried by results proved elsewhere in the
development, and this theorem is where they are put together.

**How to read the count.** `#check @chain` lists the arguments. Eight of them are
propositions named `E..`; each is an implication between two node predicates, so
none of them can be discharged by a definitional unfolding. One is an independent
physical premise, three are formalization gaps, two are modelling assumptions and
two are physical commitments.

**The last step runs through n7.** `self_of_coherent_order_parameter` takes the
*existence of a coherent order parameter* as its hypothesis, not `K > 2D`, so
deleting `Phase8_SelfConsistency.lean` breaks this theorem. Under the shape this
module had before `supercritical_of_coherent`, it would not have.

**What it does not establish.**

* Not that the toy witness identifies its ingredients as one physical mechanism.
  §8 supplies a simultaneous witness for all eight hypotheses, but its double
  well, register, mesh and cortical cover remain deliberately distinct toy
  systems.
* Not a downstream preservation of every constraint in `E34` or `E56`. `E34`'s
  thermal-scale, heat-budget and nonzero-waste conjuncts constrain the predictive
  structure admitted at n4, but the n4 → n5 passage uses only its existence.
  Likewise, `chain` uses `FieldRealizes` to reach n7; the concrete-kernel part of
  `E56` is consumed separately by `em_field_exhibits_phase_transition`. These
  constraints therefore validate their local links, rather than becoming
  additional conjuncts of `UnifiedSelf`.
* Not n10. The step from the fixed point to experience is the framework's
  stipulation and is deliberately outside this statement.
* Not the identification of Unity with the fixed point. That identification is
  explicit in `e89`; the theorem preserves it and Banach proves uniqueness, but
  no field dynamics derives it.
* Not that nine is the right number. It is the number *this* factorisation of
  the chain produces; a different set of node predicates would produce a
  different one. What is not negotiable is that the gaps are arguments rather
  than sentences.
-/
theorem chain
    {X : TopCat.{u}} [MeasureSpace X] [BorelSpace X] [TriangulatedManifold ↥X]
    [MetricSpace (GlobalSection (X := X))] [CompleteSpace (GlobalSection (X := X))]
    -- the continuum coupling kernel, on the same substrate the cover glues over.
    -- `MeasureSpace X` rather than `MeasurableSpace X`: the field needs a measure
    -- to average its kernel against, and carrying both classes would put two
    -- σ-algebras on `X` that nothing forces to agree.
    (kernel : StochasticNeuralField X)
    -- the boundary's register
    {sys : Type*} [Fintype sys] [DecidableEq sys] [Nonempty sys] [StatisticalMechanics sys]
    (upd : sys → sys)
    -- the order-parameter field and its vacuum manifold
    {Y V : Type*} (vac : Set V) (phi : Y → V)
    -- the predictive structure's carrier types
    (Xs Sg Sg' : Type*) [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']
    -- the coarse-graining sequence and its limit
    (E : ℕ → ℝ) (L : ℝ)
    -- the mean-field parameters and the elapsed time
    {K D τ : ℝ} (hτ : 0 < τ)
    (T : ThermodynamicCover X)
    -- the reflexive boundary
    (rb : ReflexiveBoundary X)
    -- the eight unproved arrows
    (e12 : E12 sys vac phi)
    (e23 : E23 vac phi upd)
    (e34 : E34 upd Xs Sg Sg')
    (e45 : E45 Xs Sg Sg' E L)
    (e56 : E56 kernel Xs Sg Sg' E L K D)
    (e67 : E67 L K D)
    (e78 : E78 K D T)
    (e89 : E89 K D τ T rb) :
    UnifiedSelf rb := by
  have n1 : Capacity sys := capacity sys
  have n2 : LeavesVacuum vac phi := e12 n1
  have n3 : Dissipates upd := dissipates_of_not_surjective upd (e23 n2)
  obtain ⟨R, _, _, _⟩ := e34 n3
  have n4 : PredictiveBound Xs Sg Sg' := predictiveBound_of_nonempty ⟨R⟩
  have n5 : CoarseGrains E L := e45 n4
  have h56 : FieldRealizes L K D ∧ Nonempty (IsEMFieldCoupling kernel K D) := e56 n5
  have n6 : FieldRealizes L K D := h56.1
  have n7 : Coherent K D := coherent_of_supercritical n6.1 (e67 n6)
  have hT : T.IsReachedByRelaxation K := e78 n7
  have n8 : Unity X := unity_of_cover ⟨T⟩
  obtain ⟨s, hs_unified, h_lip, hs_fixed⟩ := e89 hT
  let _ : Nonempty (GlobalSection (X := X)) := ⟨s⟩
  obtain ⟨p, hp, huniq⟩ :=
    self_of_coherent_order_parameter n6.1 n6.2.1 hτ n7 rb h_lip
  have hsp : s = p := huniq s hs_fixed
  exact ⟨T, s, hs_unified, hs_fixed, fun t ht => (huniq t ht).trans hsp.symm⟩

/-! ## 6. Non-vacuity

`chain` would be worth nothing if its hypotheses could not hold: an unsatisfiable
premise proves anything. The arrows below are the ones whose content is
numerical, and each is exhibited satisfied at `D = 1`, `K = 3`. Section 8
discharges all eight simultaneously. Its structural edges use the double-well
domain wall, a one-bit eraser tied to Landauer's heat, a genuinely refining mesh,
and a cover reached by relaxation.

§7 witnesses the n7 → n9 theorem on the three-site cortex. §8 additionally uses
the two-patch cover whose glued section is that same fixed point.
-/

/-- A concrete coherent order parameter: at `D = 1`, `K = 3` the threshold is
`K_c = 2` and the self-consistency equation has exactly one solution in `(0, 1]`. -/
theorem coherent_three_one : Coherent 3 1 := by
  refine coherent_of_supercritical one_pos ?_
  rw [critical_coupling]
  norm_num

/-- The `n6 → n7` commitment is satisfiable, at the same parameters. -/
theorem e67_three_one : E67 3 3 1 := fun _ => by rw [critical_coupling]; norm_num

/-- The `n5 → n6` identification is satisfiable: take the coarse-graining limit
to be the coupling constant. Requires a proof that the continuum coupling kernel
satisfies `IsEMFieldCoupling` — the numerical half is free, the identification is
not. -/
theorem e56_of_eq {M : Type*} [MeasureSpace M] [TopologicalSpace M]
    (kernel : StochasticNeuralField M) (Xs Sg Sg' : Type*)
    [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']
    (E : ℕ → ℝ) (hEM : Nonempty (IsEMFieldCoupling kernel (3 : ℝ) (1 : ℝ))) :
    E56 kernel Xs Sg Sg' E 3 3 1 :=
  fun _ => ⟨⟨one_pos, by norm_num, rfl⟩, hEM⟩

/-- **The identification half of `E56` does work.** Together with `E67` it puts
the named field above the synchronization threshold in the sense of
`Phase8_ContinuousField`'s `exhibits_phase_transition` — a statement about a
substrate and its kernel, which the three real numbers of `FieldRealizes` cannot
express on their own.

This is the consumer that keeps `IsEMFieldCoupling` from being an annotation
beside the chain rather than a hypothesis in it. -/
theorem em_field_exhibits_phase_transition {M : Type*} [MeasureSpace M] [TopologicalSpace M]
    [IsProbabilityMeasure (volume : Measure M)]
    (kernel : StochasticNeuralField M) (Xs Sg Sg' : Type*)
    [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']
    {E : ℕ → ℝ} {L K D : ℝ}
    (e56 : E56 kernel Xs Sg Sg' E L K D) (e67 : E67 L K D)
    (n5 : CoarseGrains E L) :
    exhibits_phase_transition kernel :=
  let h56 := e56 n5
  exhibits_phase_transition_of_isEMFieldCoupling h56.2.some (e67 h56.1)

open Examples in
/-- **The n3 → n4 edge, discharged on the one-bit eraser.**

`Examples.lean` §18.5 builds `landauerSystem` by `PredictiveDissipation.ofLandauer`
from `§1`'s bipartite environment, so its thermal scale and its dissipated work
are the register's own and its `still_bound` comes out of `landauer_bound`. The
register erases one bit and the law wastes one bit, so the budget is met with
equality (`landauerSystem_tight`).

This is a discharge *at one register and one joint law*, not a proof of `E34`:
the identification of the wasted memory with the erased entropy is supplied here
by computation on two bits and is exactly what no theorem supplies in general. -/
theorem e34_boolEraser : E34 (fun _ : Bool => true) Bool Bool Bool :=
  fun _ => ⟨landauerSystem, rfl, rfl, landauerSystem_nonpredictive_pos⟩

/-- `CoarseGrains` is inhabited by a constant sequence, so `E45` is satisfiable
by a constant function. -/
theorem coarseGrains_const (L : ℝ) : CoarseGrains (fun _ => L) L :=
  tendsto_const_nhds

/-! ## 7. The n7 → n9 edge, witnessed

`Examples.lean` §10 builds a three-site cortex, a reflexive boundary whose avatar
reads the field, and a Self obtained from `self_of_supercritical` — that is, from
`K > critical_coupling 1`. The two theorems below rebuild that Self through
`self_of_coherent_order_parameter` instead, so the witness's Self comes out of the
*existence of a coherent order parameter* rather than out of `3 > 2`.

This is the check C2 asked for: the two routes must land on the same fixed point,
and they do — `cortexState`, by uniqueness.
-/

open Examples in
/-- The witness's parameters put it above threshold, so Derivation 7 supplies a
coherent order parameter: `K = 3`, `D = 1`, `K_c = 2`. -/
theorem cortexCoherent : Coherent 3 1 := coherent_three_one

open Examples in
/-- **The witness's Self, from the order parameter.** Same substrate, same map,
same conclusion as `cortexHasSelf` — but the hypothesis is now n7 rather than a
numerical comparison, so this theorem depends on the bifurcation development. -/
theorem cortexHasSelf_of_coherent :
    Self (X := Cortex) cortexReflexive :=
  self_of_coherent_order_parameter one_pos (by norm_num) cortexTau_pos cortexCoherent
    cortexReflexive cortexPredict_lipschitz_rate

open Examples in
/-- **The two routes agree.** The Self produced from the coherent order parameter
is `cortexState`, which is the fixed point `Examples.lean` §10 already names. Had
they disagreed the edge would have been the wrong one. -/
theorem cortexHasSelf_of_coherent_eq :
    ∀ s : GlobalSection (X := Cortex), cortexReflexive.predict s = s → s = cortexState :=
  fun s hs => cortexPredict_fixed_unique s hs

/-! ## 8. Joint satisfiability of the conditional composition

The eight named hypotheses hold **simultaneously**, on one substrate. The n8
section and n9 fixed point are both `cortexState`, and the map it is a fixed
point of is provably non-constant (`cortexReflexive_avatar_separates`).

This matters more than the individual satisfiability checks of §6. A theorem
whose hypotheses are jointly unsatisfiable proves its conclusion for no reason at
all, and eight implications between eight different structures is exactly the
shape in which that can hide. The witness below rules it out.

**What the witness is and is not.** Every physical ingredient already existed:
`Examples.lean` §1 has a `StatisticalMechanics` instance on `Bool`, §18 has a
`PredictiveDissipation` on the two-bit law, §17 has a `ThermodynamicCover` on the
three-site cortex, §11 has a double-well domain wall, §6 has a moving refining
mesh, and §10 has the reflexive boundary. What is new is that they are made to
satisfy the *edges* at once. It is a strengthened mathematical witness, not a
derivation that identifies these toy systems with one cortical mechanism.
-/

open Examples in
/-- The register: a bit whose update cannot reach `false`. -/
theorem witness_not_surjective : ¬ Function.Surjective (fun _ : Bool => true) := by
  intro h
  obtain ⟨x, hx⟩ := h false
  exact Bool.noConfusion hx

open Examples in
/-- A `MeasureSpace` for `Cortex`: counting measure on the three sites, normalized
to total mass one.

The normalization is not cosmetic. `mean_field_coupling` averages the kernel
against `volume` *twice*, so on a substrate of total mass `m` a constant kernel
`c` has strength `c · m²`; comparing that against `K_c = 2D` would make the
threshold a statement about how many sites the substrate has rather than about
how strongly it is coupled. `IsEMFieldCoupling.domain_probability` and
`exhibits_phase_transition` both require exactly this normalization, and for
exactly this reason. -/
noncomputable instance cortexMeasureSpace : MeasureSpace Cortex :=
  { volume := (3 : ENNReal)⁻¹ • Measure.count }

open Examples in
theorem cortexVolume_apply (s : Set Site) :
    (volume : Measure Cortex) s = (3 : ENNReal)⁻¹ * Measure.count s := rfl

open Examples in
instance : IsProbabilityMeasure (volume : Measure Cortex) where
  measure_univ := by
    have hcard : Fintype.card Site = 3 := by decide
    have hcount : Measure.count (Set.univ : Set Site) = (3 : ENNReal) := by
      simp [hcard]
    rw [cortexVolume_apply, hcount, ENNReal.inv_mul_cancel] <;> norm_num

open Examples in
/-- Each of the three sites carries a third of the substrate — at most half, so
the modulatory condition of `IsEMFieldCoupling` holds and no site is the field. -/
theorem cortexVolume_singleton_le (y : Site) :
    ((volume : Measure Cortex) {y}).toReal ≤ 1 / 2 := by
  rw [cortexVolume_apply, Measure.count_singleton, mul_one]
  rw [show ((3 : ENNReal)⁻¹).toReal = (3 : ℝ)⁻¹ by
    rw [ENNReal.toReal_inv]; norm_num]
  norm_num

open Examples in
/-- The joint witness's field: the three-site cortex with a uniform kernel of
strength `3` and phase noise `1`.

Not the zero kernel. `IsEMFieldCoupling` ties `K` to `mean_field_coupling`, so
the witness parameters `K = 3`, `D = 1` used everywhere else in this section now
have to be produced by the field rather than declared beside it. -/
noncomputable def cortexNeuralField : StochasticNeuralField Cortex :=
  constField (M := Cortex) 3 1 one_pos

open Examples in
/-- The cortex neural field satisfies `IsEMFieldCoupling` at the witness
parameters, by the general construction of `Phase9_EMIdentification`. -/
theorem cortexNeuralField_isEMFieldCoupling :
    Nonempty (IsEMFieldCoupling cortexNeuralField (3 : ℝ) (1 : ℝ)) :=
  ⟨isEMFieldCoupling_const (by norm_num) one_pos cortexVolume_singleton_le⟩

open Examples in
/-- The witness substrate is above threshold in the sense of
`Phase8_ContinuousField`, not merely at numbers that satisfy an inequality:
`mean_field_coupling cortexNeuralField = 3 > 2 = critical_coupling 1`. -/
theorem cortexNeuralField_exhibits_phase_transition :
    exhibits_phase_transition cortexNeuralField :=
  exhibits_phase_transition_of_isEMFieldCoupling cortexNeuralField_isEMFieldCoupling.some
    (by rw [critical_coupling]; norm_num)

open Examples in
/-- **The predicate has teeth.** A field with no coupling at all does *not*
satisfy `IsEMFieldCoupling` at the witness parameters, because `K` is the
kernel's mean-field average and not a scalar standing beside it.

Kept as a regression: the identification is discharged by exhibiting a kernel of
the claimed strength, and a substrate that couples nothing cannot discharge it. -/
theorem not_isEMFieldCoupling_of_zero_kernel :
    ¬ IsEMFieldCoupling (constField (M := Cortex) 0 1 one_pos) (3 : ℝ) (1 : ℝ) := by
  intro h
  have h0 : mean_field_coupling (constField (M := Cortex) 0 1 one_pos) = 0 :=
    mean_field_coupling_const _ 0 rfl
  rw [h.coupling_is_mean_field] at h0
  norm_num at h0

/-! ### T5: the three remaining mechanistic edges -/

open Examples in
/-- `E12` on the genuine double well: the kink connects its two distinct vacuum
components and crosses the barrier at the origin. The capacity premise is
present because `E12` requires it; the wall itself is supplied by the proved
double-well geometry rather than by an empty vacuum. -/
theorem t5_e12_doubleWell : E12 Bool (DynamicalVacuum wellV) kink :=
  fun _ => kink_leaves_vacuum

open Examples in
/-- `E23` on a refreshed one-bit input register. After the step the input slot
is always `true`, so `false` is unreachable. Unlike the former empty-vacuum
witness, the premise is the domain wall of `t5_e12_doubleWell`. -/
theorem t5_e23_absorbingRegister :
    E23 (DynamicalVacuum wellV) kink (fun _ : Bool => true) :=
  fun _ => witness_not_surjective

open Examples in
/-- The actual energies of the uniform refining grids, translated so that their
continuum limit is the chain witness's coupling strength `3`. Translation
preserves the genuinely changing approximants while aligning the limit with the
field used by `E56`. -/
noncomputable def t5_refiningEnergy (n : ℕ) : ℝ :=
  discreteEnergy (gridTriangulation (n + 1)) volume (fun x : ℝ => |x - 1 / 2|)
    + (3 - ∫ x in Set.Ico (0 : ℝ) 1, |x - 1 / 2|)

open Examples in
/-- The translated grid energies converge to `3` by the proved mesh-refinement
theorem, rather than because the sequence is constant. -/
theorem t5_refiningEnergy_tendsto : Tendsto t5_refiningEnergy atTop (𝓝 3) := by
  have h := grid_mesh_refinement (fun x : ℝ => |x - 1 / 2|) tent_uniformContinuous
  change Tendsto (fun n =>
      discreteEnergy (gridTriangulation (n + 1)) volume (fun x : ℝ => |x - 1 / 2|)
        + (3 - ∫ x in Set.Ico (0 : ℝ) 1, |x - 1 / 2|)) atTop (𝓝 3)
  have ht := h.add_const (3 - ∫ x in Set.Ico (0 : ℝ) 1, |x - 1 / 2|)
  have heq : (∫ x in Set.Ico (0 : ℝ) 1, |x - 1 / 2|)
      + (3 - ∫ x in Set.Ico (0 : ℝ) 1, |x - 1 / 2|) = 3 := by ring
  rw [heq] at ht
  exact ht

open Examples in
/-- Regression: the refining witness is not the old constant sequence. -/
theorem t5_refiningEnergy_moves : t5_refiningEnergy 0 ≠ t5_refiningEnergy 1 := by
  intro h
  unfold t5_refiningEnergy at h
  rw [tent_energy_one, tent_energy_two] at h
  norm_num at h

open Examples in
/-- `E45` realized by the moving uniform-grid sequence. The predictive premise
selects this coarse-graining regime; it does not manufacture convergence. -/
theorem t5_e45_refiningMesh : E45 Bool Bool Bool t5_refiningEnergy 3 :=
  fun _ => t5_refiningEnergy_tendsto

/-! ### T5 specifications: the three remaining mechanistic edges -/

open Examples in
example : E12 Bool (DynamicalVacuum wellV) kink := t5_e12_doubleWell

open Examples in
example : E23 (DynamicalVacuum wellV) kink (fun _ : Bool => true) :=
  t5_e23_absorbingRegister

open Examples in
example : E45 Bool Bool Bool t5_refiningEnergy 3 := t5_e45_refiningMesh

open Examples in
/-- **All eight arrows, at once, on one substrate.**

`#print axioms chain_hypotheses_jointly_satisfiable` reports only the three, so
the witness is as sound as the conditional theorem whose hypotheses it
discharges. The name remains limited to satisfiability: concrete non-trivial
edge witnesses do not identify the double well, register, mesh and cortical
cover as one physical mechanism. -/
theorem chain_hypotheses_jointly_satisfiable : UnifiedSelf (X := Cortex) cortexReflexive :=
  chain (X := Cortex) (kernel := cortexNeuralField) (sys := Bool) (fun _ => true)
    (vac := DynamicalVacuum wellV) (phi := kink) Bool Bool Bool
    (E := t5_refiningEnergy) (L := 3) (K := 3) (D := 1) (τ := cortexTau)
    cortexTau_pos cortexCover cortexReflexive
    t5_e12_doubleWell
    t5_e23_absorbingRegister
    e34_boolEraser
    t5_e45_refiningMesh
    (fun _ => ⟨⟨one_pos, by norm_num, rfl⟩, cortexNeuralField_isEMFieldCoupling⟩)
    (fun _ => by rw [critical_coupling]; norm_num)
    (fun _ => cortexCover_reachedByRelaxation_three)
    (fun _ => ⟨cortexState, (fun _ => rfl),
      cortexPredict_lipschitz_rate, cortexPredict_fixed⟩)

/-! ## 9. The n5 → n7 edge: why there is not one

The figure routes n5 into n7 through n6, and the natural question is whether the
coarse-graining theorem could produce the structure the field results are stated
over — a `ContinuousNeuralField.ofMeshLimit`. The attempt was made and it fails,
twice over, and neither failure is the recorded blocker (the dynamical mean-field
limit, propagation of chaos).

**First: the structure asks for nothing, so a constructor would prove nothing.**
`ContinuousNeuralField M` is three fields — `omega : M → ℝ`, `K : M → M → ℝ`,
`tau : ℝ` — and no conditions. `ofMeshLimit` would typecheck with *any* kernel
whatever, including one unrelated to the mesh, so it would be an edge whose proof
is a definitional unfolding: precisely the manufactured edge this module exists to
avoid. `continuousNeuralField_free` below records this as a statement rather than
as a remark.

**Second, and this is the real finding: the coarse-graining theorem does not
produce a kernel.** `mesh_refinement_convergence` converges the discrete coupling
*energy* — one real number per triangulation — to `∫_S f dμ`, and
`total_weight_eq_setIntegral` sums the edge weights to the same scalar. Both
integrate the pair structure away. `ContinuousNeuralField.K` is a function of two
continuum points, and nothing in the development produces one from discrete data:
`TriangulatedManifold.edge_region` is a subset of `M`, not of `M × M`, so the
discrete side has no product structure to pass to the limit.

**And the obvious repair is blocked by a theorem.** The natural candidate kernel
places each discrete weight at its pair of embedded vertices. `vertexKernel` is
that kernel, and `vertexKernel_fieldCorrelation_eq_zero` shows it carries
*exactly zero* continuum coupling energy on any substrate whose measure has no
atoms — whatever weights the triangulation carries. A finite set is null, and the
continuum functional cannot see it. This is the same fact as the hardware
comparison's `fieldCorrelation_sited_eq_zero` (Derivation 8) arriving from the
other direction: there it says discrete hardware registers nothing in the field;
here it says a discretization's kernel registers nothing either.

So the gap between n5 and n7 is one level earlier than recorded. It is not that
the dynamics fail to pass to the limit; it is that **no kernel survives the
passage at all**, because the theorem that does the coarse-graining is about a
scalar. `E56` is where this lands in `chain`: the empirical commitment identifies
the coarse-graining limit `L` with the mean-field coupling *constant* `K`, a real
number, and the continuum kernel never enters the chain. That is the honest
shape, and it is smaller than the manuscript's "discrete couplings coarse-grain to
a continuous kernel" suggests.
-/

/-- **`ContinuousNeuralField` constrains nothing.** Any drift, any kernel and any
timescale assemble into one. A constructor from a mesh limit would therefore
carry no information about the mesh, which is why none is built. -/
theorem continuousNeuralField_free {M : Type*} [MeasureSpace M] [TopologicalSpace M]
    (omega : M → ℝ) (K : M → M → ℝ) (tau : ℝ) : Nonempty (ContinuousNeuralField M) :=
  ⟨⟨omega, K, tau⟩⟩

/-- The kernel a triangulation would induce on the continuum: weight `w u v`
placed at the embedded pair `(embedding u, embedding v)`, and zero elsewhere. -/
noncomputable def vertexKernel {M : Type*} [TopologicalSpace M] [DecidableEq M]
    (TM : TriangulatedManifold M) [Fintype TM.V] (w : TM.V → TM.V → ℝ) : M → M → ℝ :=
  fun x y => ∑ u, ∑ v, if x = TM.embedding u ∧ y = TM.embedding v then w u v else 0

/-- The induced kernel is sited on the image of the vertex set — finitely many
points of `M`. -/
theorem vertexKernel_sitedOn {M : Type*} [TopologicalSpace M] [DecidableEq M]
    (TM : TriangulatedManifold M) [Fintype TM.V] (w : TM.V → TM.V → ℝ) :
    SitedOn (Finset.univ.image TM.embedding) (vertexKernel TM w) := by
  intro x hx y
  refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
  have hne : x ≠ TM.embedding u := by
    rintro rfl
    exact hx (Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩)
  simp [hne]

/-- **The induced kernel really does carry the weights.** At an embedded pair it
takes the value the triangulation assigns, so the no-go below is not a statement
about a kernel that was zero to begin with. -/
theorem vertexKernel_apply_embedding {M : Type*} [TopologicalSpace M] [DecidableEq M]
    (TM : TriangulatedManifold M) [Fintype TM.V] [DecidableEq TM.V]
    (hinj : Function.Injective TM.embedding) (w : TM.V → TM.V → ℝ) (u v : TM.V) :
    vertexKernel TM w (TM.embedding u) (TM.embedding v) = w u v := by
  classical
  unfold vertexKernel
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · simp
    · intro b _ hb
      have hne : TM.embedding v ≠ TM.embedding b := fun h => hb (hinj h).symm
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ v) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    have hne : TM.embedding u ≠ TM.embedding b := fun h => hb (hinj h).symm
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ u) h

/-- **The no-go for the n5 → n7 edge.** A triangulation's weights, placed at its
vertices, contribute exactly zero to the continuum coupling energy on any
substrate whose measure has no atoms — whatever the weights are and whatever the
phase field does.

The discrete data lives on a finite set, the finite set is null, and the
functional the field theorems are stated in ignores null sets. Spreading the
weights over cells instead would need a product-structured decomposition of
`M × M`, and `TriangulatedManifold.edge_region` provides only subsets of `M`. -/
theorem vertexKernel_fieldCorrelation_eq_zero {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [DecidableEq M] (TM : TriangulatedManifold M) [Fintype TM.V]
    (w : TM.V → TM.V → ℝ) (μ : Measure M) [NullSingletonClass μ] (theta : M → ℝ) :
    fieldCorrelation μ theta (vertexKernel TM w) = 0 :=
  fieldCorrelation_sited_eq_zero μ _ _ (vertexKernel_sitedOn TM w) theta

end Chain

end PhysicsOfConsciousness
