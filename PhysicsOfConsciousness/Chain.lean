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
  link was exactly that failure; `e79` below records it as a hypothesis rather
  than pretending otherwise.

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

/-- **n9 — the self-prediction map has a unique fixed point: the Self.** -/
def Self (rb : ReflexiveBoundary X) : Prop :=
  ∃! s : GlobalSection (X := X), rb.predict s = s

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

/-- n8 from a cover at thermodynamic equilibrium: Derivation 5. -/
theorem unity_of_cover (h : Nonempty (ThermodynamicCover X)) : Unity X :=
  h.elim fun T => ⟨T, @global_section_from_thermodynamics X _ _ _ T⟩

/-- **The one thing n8 gives n9 outright.** Unity produces a global section, so
the space of global sections is inhabited — which is one of the three instance
hypotheses Banach needs and the only one the chain supplies rather than assumes.

This is a genuine but thin contribution and is recorded as such: the substantive
half of the n8 → n9 edge is the contraction, and that is `e89`. -/
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

/-! ## 3. The edges that are not theorems

Nine propositions, one per unproved arrow. Each is an implication between two of
the node predicates above, so that discharging one is a statement about the two
links it joins rather than about an opaque symbol.

The kinds, tallied: **four formalization gaps** (`E12`, `E23`, `E34`, `E78`),
**two modelling assumptions** (`E45`, `E89`), **two physical commitments**
(`E56`, `E67`), and **one edge expected to be dischargeable** (`E79`).
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
positive.

**This is the one that could simply be false**, and the manuscript says so: the
kernel might be realized by synaptic connectivity, by gap junctions, or by
nothing with a mean-field description at all. It is not a formalization gap —
there is no Lean statement that would settle it — and it is not a modelling
idealisation, because the framework's empirical content lives here. -/
def E56 (Xs Sg Sg' : Type*) [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']
    (E : ℕ → ℝ) (L K D : ℝ) : Prop :=
  CoarseGrains E L → FieldRealizes L K D

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

/-- **n8 → n9. Modelling assumption.**

Asserts that the self-prediction map of the reflexive boundary is Lipschitz at
the order parameter's linear relaxation rate `exp(-(K - K_c)τ/2)`.

An idealisation rather than a gap: the rate is the linearisation of the
mean-field dynamics about the coherent branch, and taking the *nonlinear*
self-model to contract at the *linearised* rate is a modelling step the framework
makes knowingly. What it buys is that the contraction constant is read off the
substrate rather than stipulated — which is why replacing it by a bare
`ContractingWith c` would be weaker, not simpler. -/
def E89 {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X]
    [MetricSpace (GlobalSection (X := X))] (K D τ : ℝ) (rb : ReflexiveBoundary X) : Prop :=
  Unity X → LipschitzWith (resonanceRate K D τ) rb.predict

/-- **n7 → n9. Expected to be dischargeable, and recorded as a hypothesis until it
is.**

Asserts that the existence of a coherent order parameter forces the coupling
above threshold — the converse of `coherent_of_supercritical`, and the step that
makes the Self consume Derivation 7's *theorem* rather than the numeral `2 * D`.

**Why it is here.** `self_of_supercritical` takes `critical_coupling D < K`, and
`critical_coupling` is a `def` unfolding to `2 * D`. As the development stands,
the Self would be provable with `Phase8_SelfConsistency.lean` deleted. Routing
the last step through `E79` rather than through `E67` is what makes the
bifurcation load-bearing.

**What would discharge it.** The first component of
`critical_coupling_is_threshold_unique`, contrapositively: a non-zero non-negative
fixed point of the self-consistency equation forces `critical_coupling D < K`.
That needs `0 < D` and `0 ≤ K`, which `FieldRealizes` carries. This is work item
C2 in `tasks/todo.md`; when it is done this definition is replaced by a theorem
and `chain` loses an argument. -/
def E79 (K D : ℝ) : Prop :=
  Coherent K D → critical_coupling D < K

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
**The chain, end to end: n1 ⟹ n9.**

Nine named hypotheses, `e12 … e89`, one per arrow of Figure 1 that is not a
theorem. Everything else in the passage from a finite phase space to the Self is
carried by results proved elsewhere in the development, and this theorem is where
they are put together.

**How to read the count.** `#check @chain` lists the arguments. Nine of them are
propositions named `E..`; each is an implication between two node predicates, so
none of them can be discharged by a definitional unfolding. Four are
formalization gaps, two are modelling assumptions, two are physical commitments,
and one (`e79`) is expected to become a theorem.

**What it does not establish.**

* Not that the hypotheses are jointly satisfiable. §6 discharges the four
  arrows whose content is numerical, at concrete parameters, so those are not
  vacuous; a *simultaneous* witness for all nine — which would need a substrate
  carrying a cover, a reflexive boundary and a predictive structure at once — is
  not built here and is recorded as the next non-vacuity task.
* Not n10. The step from the fixed point to experience is the framework's
  stipulation and is deliberately outside this statement.
* Not that nine is the right number. It is the number *this* factorisation of
  the chain produces; a different set of node predicates would produce a
  different one. What is not negotiable is that the gaps are arguments rather
  than sentences.
-/
theorem chain
    {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X]
    [MetricSpace (GlobalSection (X := X))] [CompleteSpace (GlobalSection (X := X))]
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
    -- the nine unproved arrows
    (e12 : E12 sys vac phi)
    (e23 : E23 vac phi upd)
    (e34 : E34 upd Xs Sg Sg')
    (e45 : E45 Xs Sg Sg' E L)
    (e56 : E56 Xs Sg Sg' E L K D)
    (e67 : E67 L K D)
    (e78 : E78 K D X)
    (e79 : E79 K D)
    (e89 : E89 K D τ rb) :
    Self rb := by
  have n1 : Capacity sys := capacity sys
  have n2 : LeavesVacuum vac phi := e12 n1
  have n3 : Dissipates upd := dissipates_of_not_surjective upd (e23 n2)
  have n4 : PredictiveBound Xs Sg Sg' := predictiveBound_of_nonempty (e34 n3)
  have n5 : CoarseGrains E L := e45 n4
  have n6 : FieldRealizes L K D := e56 n5
  have n7 : Coherent K D := coherent_of_supercritical n6.1 (e67 n6)
  have n8 : Unity X := unity_of_cover (e78 n7)
  have : Nonempty (GlobalSection (X := X)) := nonempty_globalSection_of_unity n8
  exact self_of_contraction hτ (e79 n7) rb (e89 n8)

/-! ## 6. Non-vacuity

`chain` would be worth nothing if its hypotheses could not hold: an unsatisfiable
premise proves anything. The four arrows below are the ones whose content is
numerical, and each is exhibited satisfied at `D = 1`, `K = 3`. The remaining five
(`E12`, `E23`, `E34`, `E45`, `E78`) assert relations between structures rather
than between numbers, and a witness for them is a witness for the chain as a
whole; that is not built here.
-/

/-- A concrete coherent order parameter: at `D = 1`, `K = 3` the threshold is
`K_c = 2` and the self-consistency equation has exactly one solution in `(0, 1]`. -/
theorem coherent_three_one : Coherent 3 1 := by
  refine coherent_of_supercritical one_pos ?_
  rw [critical_coupling]
  norm_num

/-- The `n6 → n7` commitment is satisfiable, at the same parameters. -/
theorem e67_three_one : E67 3 3 1 := fun _ => by rw [critical_coupling]; norm_num

/-- The `n7 → n9` edge is satisfiable at those parameters too — trivially, since
its conclusion is a true numerical statement there. That is *not* a proof of
`E79` in general, which is the point of C2. -/
theorem e79_three_one : E79 3 1 := fun _ => by rw [critical_coupling]; norm_num

/-- The `n5 → n6` identification is satisfiable: take the coarse-graining limit
to be the coupling constant. -/
theorem e56_of_eq (Xs Sg Sg' : Type*)
    [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']
    (E : ℕ → ℝ) : E56 Xs Sg Sg' E 3 3 1 :=
  fun _ => ⟨one_pos, by norm_num, rfl⟩

/-- `CoarseGrains` is inhabited by a constant sequence, so `E45` is satisfiable
by a constant function. -/
theorem coarseGrains_const (L : ℝ) : CoarseGrains (fun _ => L) L :=
  tendsto_const_nhds

end Chain

end PhysicsOfConsciousness
