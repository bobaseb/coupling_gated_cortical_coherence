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

The kinds, tallied: **four formalization gaps** (`E12`, `E23`, `E34`, `E78`),
**two modelling assumptions** (`E45`, `E89`) and **two physical commitments**
(`E56`, `E67`). There were nine until `supercritical_of_coherent` discharged the
n7 → n9 edge.
-/

/-- **n1 → n2. Formalization gap — and the sharpest one, because there is nothing
to formalize.**

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
structure: a joint law over state and signal, a Markov signal dynamics, finite
memory, a thermal scale, and Still's bound.

**What would discharge it.** Landauer's heat and Still's dissipated work are two
different accounts of the same physical quantity, and no theorem here identifies
them: `heat_dissipation` is `T · Δ boltzmann_entropy` of the bath, `dissipatedWork`
is `W − ΔF` over one drive step. Discharging this edge means building a bipartite
environment whose Landauer heat *is* the dissipated work of a predictive
structure, which is a real formalization task and not a research problem. -/
def E34 {sys : Type*} [Thermodynamics sys] (t : sys → sys)
    (Xs Sg Sg' : Type*) [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg'] :
    Prop :=
  Dissipates t → Nonempty (PredictiveDissipation Xs Sg Sg')

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
positive, and that the continuum kernel satisfies the mathematical conditions of
`IsEMFieldCoupling` (joint continuity, positive domain measure, etc.).

**This is the one that could simply be false**, and the manuscript says so: the
kernel might be realized by synaptic connectivity, by gap junctions, or by
nothing with a mean-field description at all. It is not a formalization gap —
there is no Lean statement that would settle it — and it is not a modelling
idealisation, because the framework's empirical content lives here.

The `IsEMFieldCoupling` half is the formal part of the empirical commitment;
it records the *mathematical* conditions a kernel claiming to be the EM field
must satisfy, which are independent of whether cortex satisfies them. -/
def E56 {M : Type*} [MeasureSpace M] [TopologicalSpace M] (sys : ContinuousNeuralField M)
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

**What would discharge it.** Two things, of very different sizes.
`Phase5_EquilibriumBridge`'s `ThermodynamicCover.ofConvergentTrajectory` already
builds the equilibrium field from a convergent trajectory, so the first half is
reachable for initial data within a quarter turn. The second half is
`LocalSectionSynchronization.section_agrees_of_phase_eq` — that synchronized
patches agree on overlaps — which is untouched by any dynamics in this
development and is the standing open item ranked second in `tasks/todo.md`.

Note also the scale mismatch this edge hides: n7 is a statement about a continuum
mean field and `ThermodynamicCover` is a statement about a finite index set. -/
def E78 (K D : ℝ) (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X]
    [TriangulatedManifold ↥X] : Prop :=
  Coherent K D → Nonempty (ThermodynamicCover X)

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
    [MetricSpace (GlobalSection (X := X))] (K D τ : ℝ) (rb : ReflexiveBoundary X) : Prop :=
  Unity X → ∃ (T : ThermodynamicCover X) (s : GlobalSection (X := X)),
    IsUnifiedBy T s ∧ LipschitzWith (resonanceRate K D τ) rb.predict ∧ rb.predict s = s

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
none of them can be discharged by a definitional unfolding. Four are
formalization gaps, two are modelling assumptions and two are physical
commitments.

**The last step runs through n7.** `self_of_coherent_order_parameter` takes the
*existence of a coherent order parameter* as its hypothesis, not `K > 2D`, so
deleting `Phase8_SelfConsistency.lean` breaks this theorem. Under the shape this
module had before `supercritical_of_coherent`, it would not have.

**What it does not establish.**

* Not that the hypotheses are jointly satisfiable. §6 discharges the arrows whose
  content is numerical, at concrete parameters, so those are not vacuous; a
  *simultaneous* witness for all eight — which would need a substrate carrying a
  cover, a reflexive boundary and a predictive structure at once — is not built
  here and is recorded as the next non-vacuity task.
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
    {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X] [MeasureSpace X] [TriangulatedManifold ↥X]
    [MetricSpace (GlobalSection (X := X))] [CompleteSpace (GlobalSection (X := X))]
    -- the continuum coupling kernel
    (kernel : ContinuousNeuralField X)
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
    -- the reflexive boundary
    (rb : ReflexiveBoundary X)
    -- the eight unproved arrows
    (e12 : E12 sys vac phi)
    (e23 : E23 vac phi upd)
    (e34 : E34 upd Xs Sg Sg')
    (e45 : E45 Xs Sg Sg' E L)
    (e56 : E56 kernel Xs Sg Sg' E L K D)
    (e67 : E67 L K D)
    (e78 : E78 K D X)
    (e89 : E89 K D τ rb) :
    UnifiedSelf rb := by
  have n1 : Capacity sys := capacity sys
  have n2 : LeavesVacuum vac phi := e12 n1
  have n3 : Dissipates upd := dissipates_of_not_surjective upd (e23 n2)
  have n4 : PredictiveBound Xs Sg Sg' := predictiveBound_of_nonempty (e34 n3)
  have n5 : CoarseGrains E L := e45 n4
  have h56 : FieldRealizes L K D ∧ Nonempty (IsEMFieldCoupling kernel K D) := e56 n5
  have n6 : FieldRealizes L K D := h56.1
  have n7 : Coherent K D := coherent_of_supercritical n6.1 (e67 n6)
  have n8 : Unity X := unity_of_cover (e78 n7)
  obtain ⟨T, s, hs_unified, h_lip, hs_fixed⟩ := e89 n8
  let _ : Nonempty (GlobalSection (X := X)) := ⟨s⟩
  obtain ⟨p, hp, huniq⟩ :=
    self_of_coherent_order_parameter n6.1 n6.2.1 hτ n7 rb h_lip
  have hsp : s = p := huniq s hs_fixed
  exact ⟨T, s, hs_unified, hs_fixed, fun t ht => (huniq t ht).trans hsp.symm⟩

/-! ## 6. Non-vacuity

`chain` would be worth nothing if its hypotheses could not hold: an unsatisfiable
premise proves anything. The arrows below are the ones whose content is
numerical, and each is exhibited satisfied at `D = 1`, `K = 3`. The remaining five
(`E12`, `E23`, `E34`, `E45`, `E78`) assert relations between structures rather
than between numbers, and a witness for them is a witness for the chain as a
whole; that is not built here.

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
satisfies `IsEMFieldCoupling`. -/
theorem e56_of_eq [MeasureSpace X] (kernel : ContinuousNeuralField X) (Xs Sg Sg' : Type*)
    [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']
    (E : ℕ → ℝ) (hEM : Nonempty (IsEMFieldCoupling kernel (3 : ℝ) (1 : ℝ))) :
    E56 kernel Xs Sg Sg' E 3 3 1 :=
  fun _ => ⟨⟨one_pos, by norm_num, rfl⟩, hEM⟩

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

**What the witness is and is not.** Every piece of it already existed:
`Examples.lean` §1 has a `StatisticalMechanics` instance on `Bool`, §18 has a
`PredictiveDissipation` on the two-bit law, §17 has a `ThermodynamicCover` on the
three-site cortex, and §10 has the reflexive boundary. What is new is that they
are made to satisfy the *edges* at once. It is a mathematical witness: the
register is a bit, the vacuum manifold is empty, and the coarse-graining sequence
is constant. It shows joint satisfiability, not a mechanistic cortical chain.
-/

open Examples in
/-- The register: a bit whose update cannot reach `false`. -/
theorem witness_not_surjective : ¬ Function.Surjective (fun _ : Bool => true) := by
  intro h
  obtain ⟨x, hx⟩ := h false
  exact Bool.noConfusion hx

open Examples in
/-- A `MeasureSpace` for `Cortex` (finite discrete type with counting measure). -/
noncomputable instance : MeasureSpace Cortex :=
  { volume := Measure.count }

open Examples in
/-- A trivial `ContinuousNeuralField` on Cortex for the joint witness. -/
noncomputable def cortexNeuralField : ContinuousNeuralField Cortex :=
  ⟨fun _ => (0 : ℝ), fun _ _ => (0 : ℝ), (0 : ℝ)⟩

open Examples in
/-- The cortex neural field satisfies `IsEMFieldCoupling` at the witness parameters. -/
theorem cortexNeuralField_isEMFieldCoupling :
    Nonempty (IsEMFieldCoupling cortexNeuralField (3 : ℝ) (1 : ℝ)) := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · -- kernel_continuous: zero kernel on a discrete space is continuous
    unfold cortexNeuralField
    have h : (Function.uncurry fun (_ _ : Cortex) => (0 : ℝ)) = fun _ : Cortex × Cortex => (0 : ℝ) := by
      ext ⟨x, y⟩; rfl
    rw [h]
    exact continuous_const
  · -- domain_positive_measure: counting measure of Cortex (3 points) is positive
    have hcard : Fintype.card Site = 3 := by
      decide
    have hvol : (volume : Measure Cortex) (Set.univ : Set Cortex) = (3 : ENNReal) := by
      calc
        (volume : Measure Cortex) (Set.univ : Set Cortex) = Measure.count (Set.univ : Set Site) := rfl
        _ = (Fintype.card Site : ENNReal) := by simp
        _ = (3 : ENNReal) := by simp [hcard]
    rw [hvol]
    norm_num

open Examples in
/-- **All eight arrows, at once, on one substrate.**

`#print axioms chain_hypotheses_jointly_satisfiable` reports only the three, so
the witness is as sound as the conditional theorem whose hypotheses it
discharges. The name is deliberately limited to satisfiability: the empty
vacuum and constant coarse-graining sequence do not constitute a mechanism. -/
theorem chain_hypotheses_jointly_satisfiable : UnifiedSelf (X := Cortex) cortexReflexive :=
  chain (X := Cortex) (kernel := cortexNeuralField) (sys := Bool) (fun _ => true)
    (vac := (∅ : Set Bool)) (phi := id) Bool Bool Bool
    (E := fun _ => 3) (L := 3) (K := 3) (D := 1) (τ := cortexTau)
    cortexTau_pos cortexReflexive
    (fun _ => ⟨true, Set.notMem_empty _⟩)
    (fun _ => witness_not_surjective)
    (fun _ => ⟨frozenSystem⟩)
    (fun _ => tendsto_const_nhds)
    (fun _ => ⟨⟨one_pos, by norm_num, rfl⟩, cortexNeuralField_isEMFieldCoupling⟩)
    (fun _ => by rw [critical_coupling]; norm_num)
    (fun _ => ⟨cortexCover⟩)
    (fun _ => ⟨cortexCover, cortexState, (fun _ => rfl),
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
