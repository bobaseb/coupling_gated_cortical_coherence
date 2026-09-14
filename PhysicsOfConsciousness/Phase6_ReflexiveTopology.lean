/-
  Phase 6: Reflexive Topology and the Emergence of the Self

  This module formalizes:
  1. The distinction between Unity (a Global Section) and the Self.
  2. The thermodynamic requirement for the unified field to predict its own internal
     state-changes (auto-resonance).
  3. The topological folding that creates a low-dimensional avatar of the boundary.

  **The 2026-08-31 redesign (work item W5).** Until this pass `ReflexiveBoundary`
  carried the predictive map as *free data*, sitting beside the avatar and unrelated
  to it. The consequence was recorded in the theorem `self_of_constResonance`:
  replacing the avatar by a constant left a legal boundary with the same predictive
  model and the same Self, so the fixed-point theorem could not detect whether the
  avatar read the field. Derivation 6 was Banach's theorem with a
  consciousness-flavoured label.

  Two changes fix it, and both are visible in the statements below.

  * **The self-prediction map is built out of the avatar.** `ReflexiveBoundary` no
    longer carries a `PredictiveModel`; it carries the avatar's *write*
    (`auto_resonance`, the encoding of the global state into the avatar region) and
    the avatar's *read-out* (`readout`, the global state that encoding predicts), and
    `predict` is their composite. The field's model of itself is now, by construction,
    what its own localized self-encoding reconstructs. `self_of_constResonance` does
    not typecheck any more — blinding the avatar changes the predictive map, so a
    contraction hypothesis about the original map says nothing about the blinded one —
    and its replacements say the opposite thing:
    `constResonance_predict_const` (the blinded model is a constant map, not a
    dynamics), `constResonance_existsUnique_self` (its Self is the stipulated value
    `readout a₀` whatever the field does) and `not_self_of_constResonance` (**the Self
    moves when the avatar is blinded**). `Examples.lean` §10 witnesses the last one on
    the three-site cortex, where the blinded Self is provably a different section.
    What being a fixed point now *buys* is `self_eq_readout_restrict`: under resonance
    the Self satisfies `s = readout (restrictToAvatar s)`, so it is reconstructed from
    a section over the avatar region alone. That is the low-dimensional fold the
    header has always claimed, as a theorem rather than as a name.
  * **The contraction rate comes from `K` and `D`.** `resonanceRate K D τ` is
    `exp (-(K - K_c) τ / 2)` with `K_c = critical_coupling D = 2D`, where `(K - K_c)/2`
    is the growth rate of the *incoherent* state's instability, over a time `τ`.
    Relaxation about the coherent branch is `(K - K_c)`, twice as fast, so this factor
    is the larger of the two and the Lipschitz hypothesis stated with it is the weaker.
    `resonanceRate_lt_one` and `one_le_resonanceRate` then split the parameter plane at
    Sakaguchi's threshold, and `self_of_supercritical` derives the Self from `K > 2D`
    rather than from a hard-coded `1/2`. Below the threshold
    `not_contractingWith_resonanceRate` records that the rate is not a contraction rate
    *for any map*, so Derivation 6's argument is unavailable there. This is a
    conditional claim, not a new derivation: the rate enters as a Lipschitz hypothesis
    on the substrate's self-model, and what the threshold decides is whether that
    hypothesis can produce a fixed point.

  **Proof strategy for reflexive_topology_implies_self:**
  The predictive map `rb.predict : GlobalSection X → GlobalSection X` is a continuous
  self-map. We prove it has a fixed point via the **Banach Contraction Mapping
  Theorem** (`ContractingWith.fixedPoint_isFixedPt` in Mathlib), which requires:
    - `GlobalSection X` is a nonempty complete metric space.
    - `predict` is a contracting map (physically: successive predictions lose
      entropy, i.e., the prediction process is dissipative).

  Both are hypotheses here, and neither is idle. `Examples.lean` §10 discharges them
  on the three-site cortex: it pierces the sheafification layer (`massEquiv` proves
  the global sections there *are* the finite measures on the substrate, read as
  densities), metrizes them by the uniform distance between those densities,
  proves that metric complete, and supplies an avatar whose read-out contracts by
  exactly one half without being constant. An earlier witness used the 0/1 metric
  instead; `contracting_implies_const` in the same section records why that was
  empty — under the 0/1 metric every contraction is constant.

  A caveat worth keeping: the Lévy–Prokhorov metric is *not* what is constructed
  there, and the substitution is not cosmetic. On a discrete substrate the
  ε-thickening of a set is the set itself for ε < 1, so the natural relaxation map
  `μ ↦ ½μ + ½μ₀` fails to be a Lévy–Prokhorov contraction; Mathlib also has no
  completeness result for that metric to build on. The uniform distance between
  densities is what the substrate supports.

  Note: Brouwer/Schauder fixed-point theorems are not available in this Mathlib
  version; Banach contraction is the constructive alternative.
-/

import PhysicsOfConsciousness.Phase5_GlobalSection
import PhysicsOfConsciousness.Phase8_ContinuousField
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.MetricSpace.Contracting

open CategoryTheory TopologicalSpace MeasureTheory
open Opposite

namespace PhysicsOfConsciousness

universe u

variable {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]

-- We define an internal perturbation as a transition map of the Global Section over time.
-- Auto-resonance implies the field contains a sub-topology (the 'avatar') that
-- continuously maps the state of the Global Section.

/-- A predictive model is a mapping from the current state to a future state.

**No longer free data on a `ReflexiveBoundary`.** The structure below induces one
(`ReflexiveBoundary.predictive_model`) by composing the avatar's write with its
read-out; this wrapper is kept because the manuscript's Derivation 6 names it, and
because a model *not* factoring through an avatar is still a meaningful object — it
is exactly the object whose fixed point cannot see reflexivity. -/
structure PredictiveModel (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X] where
  predict : GlobalSection (X := X) → GlobalSection (X := X)

/-- A Reflexive Boundary (The Self) is a topological feature where the system
encodes its own global state into a localized sub-region (the avatar) and predicts
its next global state from that encoding alone.

The two maps are the two halves of the fold. `auto_resonance` is the **write**: what
the field puts into the avatar region. `readout` is the **read-out**: the global state
that encoding predicts. Their composite is `predict`, and it is not a field — a
reflexive boundary has no self-model other than the one its avatar supplies.

Neither map is constrained here, per rule §3 of `PhysicsOfConsciousness/AGENTS.md`.
A constant `auto_resonance` is still a legal boundary (`constResonance` builds one);
what has changed since 2026-08-31 is that it is no longer the *same* boundary's
dynamics, so nothing about the original Self transfers to it. The condition that makes
the name honest is the predicate `IsRestrictionResonance` below. -/
structure ReflexiveBoundary (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X] where
  avatar_region : Opens X
  /-- The write: the state the field encodes into the avatar region. -/
  auto_resonance : GlobalSection (X := X) → (probabilityPresheaf X).obj (op avatar_region)
  /-- The read-out: the global state a given avatar encoding predicts. This is where the
  fold is low-dimensional — the whole prediction is a function of a section over
  `avatar_region`. -/
  readout : (probabilityPresheaf X).obj (op avatar_region) → GlobalSection (X := X)

namespace ReflexiveBoundary

variable {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]

/-- **The self-prediction map, built out of the avatar.** The field's model of its next
global state is what its own self-encoding reconstructs: `readout ∘ auto_resonance`.

This is the W5 change. Previously `predict` was an independent field and the fixed-point
theorem projected it out, never touching the avatar; now every statement about `predict`
is a statement about the avatar, and replacing the avatar replaces the dynamics. -/
def predict (rb : ReflexiveBoundary X) (s : GlobalSection (X := X)) : GlobalSection (X := X) :=
  rb.readout (rb.auto_resonance s)

/-- The predictive model a reflexive boundary *induces*. Derived, not assumed. -/
def predictive_model (rb : ReflexiveBoundary X) : PredictiveModel X := ⟨rb.predict⟩

@[simp] theorem predictive_model_predict (rb : ReflexiveBoundary X) :
    rb.predictive_model.predict = rb.predict := rfl

/-- The global state, read on the avatar region: the presheaf restriction. -/
noncomputable def restrictToAvatar (rb : ReflexiveBoundary X) (s : GlobalSection (X := X)) :
    (probabilityPresheaf X).obj (op rb.avatar_region) :=
  (probabilityPresheaf X).map (homOfLE (le_top : rb.avatar_region ≤ ⊤)).op s

/-- **Auto-resonance, as a constraint rather than a name.** The avatar's state *is* the
field's own state restricted to the avatar region.

A predicate and not a field of `ReflexiveBoundary`, per rule §3: the structure is data,
and the results below say which of them require this. It is known satisfiable —
`Examples.lean` §10's `cortexReflexive` discharges it by `rfl`. -/
def IsRestrictionResonance (rb : ReflexiveBoundary X) : Prop :=
  ∀ s : GlobalSection (X := X), rb.auto_resonance s = rb.restrictToAvatar s

/-- **Resonance is a condition on the dynamics, not beside it.** A boundary is resonant
exactly when its prediction is the read-out of the field's *own* restriction — that is,
when the self-model runs on the field rather than on something the avatar invented.

Stated as an implication in one direction and an equivalence under injectivity of the
read-out, because a read-out that collapses two encodings to the same prediction cannot
distinguish a resonant avatar from a non-resonant one that happens to agree after the
fold. Injectivity is the modelling condition "distinct self-encodings predict distinct
fields"; it is *not* assumed anywhere else in this file. -/
theorem predict_eq_readout_restrict (rb : ReflexiveBoundary X)
    (hres : rb.IsRestrictionResonance) (s : GlobalSection (X := X)) :
    rb.predict s = rb.readout (rb.restrictToAvatar s) := by
  rw [predict, hres s]

theorem isRestrictionResonance_iff_of_injective (rb : ReflexiveBoundary X)
    (hinj : Function.Injective rb.readout) :
    rb.IsRestrictionResonance ↔
      ∀ s : GlobalSection (X := X), rb.predict s = rb.readout (rb.restrictToAvatar s) :=
  ⟨rb.predict_eq_readout_restrict, fun h s => hinj (h s)⟩

end ReflexiveBoundary

/--
**Reflexive topology implies a self-predictive fixed point.**

Physical content: A continuous self-interacting field must contain a fixed point —
a state where the field's self-prediction matches its own state. This is the
formal definition of the "Self" as distinct from mere Unity (which only requires
a Global Section).

**Proof:** By the Banach Contraction Mapping Theorem, any contraction on a complete
nonempty metric space has a unique fixed point. The hypothesis `h_contracting`
asserts that the predictive map is contracting — physically, this means successive
predictions converge: the field's model of itself is dissipative, not amplifying.
See `self_of_supercritical` for the version in which the rate is
`resonanceRate K D τ` and the contraction is *derived* from `K > K_c`.

**Hypotheses (replacing the former `is_self_predictive : True`):**
- `[Nonempty (GlobalSection X)]`: The system has at least one possible state.
- `[MetricSpace (GlobalSection X)]`: The space of global sections has a metric
  (on a finite discrete substrate, the uniform distance between the densities of the
  measures the sections glue to — constructed in `Examples.lean` §10).
- `[CompleteSpace (GlobalSection X)]`: The metric is complete.
- `h_contracting : ContractingWith c rb.predict`: The prediction map contracts
  distances by a factor `c < 1` — a quantitative form of "predictions converge".

**What this does and does not establish.** Since 2026-08-31 the hypothesis is about
`rb.predict = rb.readout ∘ rb.auto_resonance`, so it *is* a hypothesis about the avatar:
a boundary whose avatar ignores the field has a different predictive map, and this
theorem says nothing about the original Self there (`not_self_of_constResonance`). What
it still does not establish is that the fixed point is a state the avatar reads
*correctly*; that needs `IsRestrictionResonance`, and `self_eq_readout_restrict` is what
resonance then buys. That the Self is *determined* by localized readings is the separate
content of `eq_of_avatar_eq`, which needs a cover.

The fixed point is also unique, which this statement does not record: see `self_unique`.
-/
theorem reflexive_topology_implies_self
  {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]
  [Nonempty (GlobalSection (X := X))]
  [MetricSpace (GlobalSection (X := X))]
  [CompleteSpace (GlobalSection (X := X))]
  {c : NNReal}
  (rb : ReflexiveBoundary X)
  (h_contracting : ContractingWith c rb.predict) :
  ∃ s : GlobalSection (X := X), rb.predict s = s :=
  -- ContractingWith.fixedPoint_isFixedPt : IsFixedPt f (fixedPoint f hf)
  -- IsFixedPt f x is definitionally `f x = x`, which is our goal.
  ⟨ContractingWith.fixedPoint rb.predict h_contracting,
   h_contracting.fixedPoint_isFixedPt⟩

namespace ReflexiveBoundary

variable {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]

/-- The Self is unique, not merely existent: Banach gives both halves, and only the
existence half was recorded before. -/
theorem self_unique {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]
    [Nonempty (GlobalSection (X := X))]
    [MetricSpace (GlobalSection (X := X))]
    [CompleteSpace (GlobalSection (X := X))]
    {c : NNReal}
    (rb : ReflexiveBoundary X)
    (h_contracting : ContractingWith c rb.predict) :
    ∃! s : GlobalSection (X := X), rb.predict s = s :=
  ⟨ContractingWith.fixedPoint rb.predict h_contracting,
   h_contracting.fixedPoint_isFixedPt,
   fun _ hs => h_contracting.fixedPoint_unique hs⟩

/-! ### Approximate reconstruction of a fixed state -/

/-- A reconstruction residual at most `ε` confines the state to the ball of radius
`ε / (1 - q)` about a fixed point of the same map. Mathlib supplies the a-posteriori
estimate. The existing existence theorem supplies the fixed point under completeness;
this estimate needs only a named fixed point. It does not construct the readout, supply
restriction resonance, or relax the independent overlap-compatibility hypothesis. -/
theorem approximate_self_bound
    [MetricSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X) {q : NNReal} (hq : ContractingWith q rb.predict)
    {s sstar : GlobalSection (X := X)} {ε : ℝ}
    (hfixed : rb.predict sstar = sstar) (hε : dist s (rb.predict s) ≤ ε) :
    dist s sstar ≤ ε / (1 - (q : ℝ)) :=
  (hq.dist_le_of_fixedPoint s hfixed).trans
    ((div_le_div_iff_of_pos_right hq.one_sub_K_pos).2 hε)

/-- Displacing a state by at most `δ` raises its reconstruction residual by at most
`(1 + q) δ`. The map and metric are held fixed; this is not a bound on a changing
readout or a mechanism producing approximately compatible local sections. -/
theorem prediction_residual_of_dist_le
    [MetricSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X) {q : NNReal} (hq : LipschitzWith q rb.predict)
    {s t : GlobalSection (X := X)} {ε δ : ℝ}
    (hε : dist s (rb.predict s) ≤ ε) (hδ : dist t s ≤ δ) :
    dist t (rb.predict t) ≤ ε + (1 + (q : ℝ)) * δ := by
  have hst : dist s t ≤ δ := by rwa [dist_comm]
  calc
    dist t (rb.predict t) ≤ dist t s + dist s (rb.predict t) := dist_triangle _ _ _
    _ ≤ dist t s + (dist s (rb.predict s) + dist (rb.predict s) (rb.predict t)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ ≤ δ + (ε + (q : ℝ) * δ) :=
      add_le_add hδ (add_le_add hε
        ((hq.dist_le_mul s t).trans (mul_le_mul_of_nonneg_left hst q.coe_nonneg)))
    _ = ε + (1 + (q : ℝ)) * δ := by ring

/-- Reconstruction and displacement errors add before division by the contraction
gap. This inverse gap can amplify their effect near threshold; the result supplies
neither the displacement bound nor an approximate-gluing theorem. -/
theorem approximate_self_bound_of_dist_le
    [MetricSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X) {q : NNReal} (hq : ContractingWith q rb.predict)
    {s t sstar : GlobalSection (X := X)} {ε δ : ℝ}
    (hfixed : rb.predict sstar = sstar)
    (hε : dist s (rb.predict s) ≤ ε) (hδ : dist t s ≤ δ) :
    dist t sstar ≤ (ε + (1 + (q : ℝ)) * δ) / (1 - (q : ℝ)) :=
  rb.approximate_self_bound hq hfixed
    (rb.prediction_residual_of_dist_le hq.toLipschitzWith hε hδ)

/-! ### What being a fixed point buys

Two theorems that are *false statements about the old structure*, because there
`predict` had nothing to do with `readout`. -/

/-- **The Self is low-dimensional.** Whatever else it is, a fixed point of the
self-prediction map lies in the range of the read-out: it is reconstructed from a single
section over the avatar region. The "topological folding that creates a low-dimensional
avatar" of the module header is this, and it is now a one-line consequence of the
structure rather than a claim in prose. -/
theorem self_mem_range_readout (rb : ReflexiveBoundary X) {s : GlobalSection (X := X)}
    (hs : rb.predict s = s) : s ∈ Set.range rb.readout :=
  ⟨rb.auto_resonance s, hs⟩

/-- **At the Self, the field is what its own avatar reading reconstructs.**

`s = readout (restrictToAvatar s)`: the global state is recovered from its own
restriction to the avatar region. This is the statement Derivation 6 wanted and could
not previously make — under the old structure `predict` was unrelated to
`restrictToAvatar`, and no fixed point said anything about the field's restriction.

**What carries the content.** `hres`. For a blind boundary the fixed-point equation reads
`s = readout a₀` with `a₀` stipulated in advance, which is a statement about the avatar's
contents and not about `s`. -/
theorem self_eq_readout_restrict (rb : ReflexiveBoundary X)
    (hres : rb.IsRestrictionResonance) {s : GlobalSection (X := X)}
    (hs : rb.predict s = s) : s = rb.readout (rb.restrictToAvatar s) :=
  ((rb.predict_eq_readout_restrict hres s).symm.trans hs).symm

/-! ## The avatar has to read the field

`auto_resonance` is *data*: an arbitrary function from the global state to a local
section over the avatar region. Nothing in the structure makes the avatar's state track
the field's, and until 2026-08-30 no theorem in the development mentioned the field at
all. That was open item **O2**; the 2026-08-31 redesign above (W5) is what finished it.

Following rule §3 of `PhysicsOfConsciousness/AGENTS.md`, the constraint is added as a
*predicate*, not as a field: `IsRestrictionResonance` says the avatar's state is the
presheaf restriction of the global state. The class stays bare, and results say which
of them they need.

Three theorems then divide the question.

* `eq_of_avatar_eq` is the positive half, and it is where the sheaf condition earns its
  place in Derivation 6: if a family of resonant avatars *covers* the substrate, the
  global state is determined by the avatar readings alone. Localized self-encodings
  reconstruct unity; no separate access to the global section is needed.
* `self_eq_readout_restrict` is what the fixed-point equation itself says once the
  avatar is resonant: the Self is its own restriction, extended.
* `constResonance_not_isRestrictionResonance` is the negative half, in the same style as
  `contracting_implies_const` in `Examples.lean` §10: from any boundary one can build
  another with the same region and the same read-out whose avatar reads a constant, so it
  satisfies the class and fails the predicate. `not_self_of_constResonance` is the point —
  the Self does **not** survive the blinding. That is the reversal W5 asked for; the old
  `self_of_constResonance`, which asserted that it did, no longer typechecks.

What this does *not* establish: that any physical process realizes the restriction. The
predicate is a modelling condition on an instance, like `section_agrees_of_phase_eq`;
`Examples.lean` §10 discharges it on the three-site cortex and §10 also exhibits the
blind boundary, so both halves are known non-vacuous.
-/

/-- Restrictions of one global section to the members of a family agree on overlaps.
Functoriality, and nothing else; it is what lets the avatar readings be fed to the sheaf
condition. -/
theorem restrictToAvatar_compatible {J : Type u} (U : J → Opens X)
    (s : GlobalSection (X := X)) (i j : J) :
    (probabilityPresheaf X).map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
        ((probabilityPresheaf X).map (homOfLE (le_top : U i ≤ ⊤)).op s) =
      (probabilityPresheaf X).map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op
        ((probabilityPresheaf X).map (homOfLE (le_top : U j ≤ ⊤)).op s) := by
  have H1 : (probabilityPresheaf X).map (homOfLE (le_top : U i ≤ ⊤)).op ≫
      (probabilityPresheaf X).map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op =
      (probabilityPresheaf X).map (homOfLE (le_top : U i ⊓ U j ≤ ⊤)).op := by
    rw [← Functor.map_comp]; rfl
  have H2 : (probabilityPresheaf X).map (homOfLE (le_top : U j ≤ ⊤)).op ≫
      (probabilityPresheaf X).map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op =
      (probabilityPresheaf X).map (homOfLE (le_top : U i ⊓ U j ≤ ⊤)).op := by
    rw [← Functor.map_comp]; rfl
  have L : (probabilityPresheaf X).map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
        ((probabilityPresheaf X).map (homOfLE (le_top : U i ≤ ⊤)).op s) =
      ((probabilityPresheaf X).map (homOfLE (le_top : U i ≤ ⊤)).op ≫
        (probabilityPresheaf X).map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op) s := rfl
  have R : (probabilityPresheaf X).map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op
        ((probabilityPresheaf X).map (homOfLE (le_top : U j ≤ ⊤)).op s) =
      ((probabilityPresheaf X).map (homOfLE (le_top : U j ≤ ⊤)).op ≫
        (probabilityPresheaf X).map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op) s := rfl
  rw [L, R, H1, H2]

/-- Under the resonance condition the avatar reading is exactly as informative as the
field on the avatar region: same reading iff same restriction. Without the condition the
forward direction fails — see `constResonance_not_isRestrictionResonance`. -/
theorem auto_resonance_eq_iff (rb : ReflexiveBoundary X) (hres : rb.IsRestrictionResonance)
    (s t : GlobalSection (X := X)) :
    rb.auto_resonance s = rb.auto_resonance t ↔ rb.restrictToAvatar s = rb.restrictToAvatar t := by
  rw [hres s, hres t]

/-- **A covering family of resonant avatars determines the global state.**

This is the theorem open item O2 asked for: one that mentions the field. The avatars are
local — each `auto_resonance` sees only its own region — and the hypothesis is only that
their readings of `s` and `t` agree. The conclusion is that `s` and `t` are the same
global state. Unity is not assumed alongside the avatars; it is recovered from them, by
the sheaf condition (`probability_glue_unique`).

**What carries the content.** `hres` — that each avatar's state is the field's own
restriction — and `hcover`. Both fail for a boundary whose resonance ignores its input,
and the conclusion fails with them: two distinct sections then have identical readings.

**What it does not establish.** That a physical avatar performs the restriction, and
that any *single* avatar suffices: a proper sub-region determines the field only where it
sits, which is why the hypothesis is a cover. -/
theorem eq_of_avatar_eq {J : Type u} (rbs : J → ReflexiveBoundary X)
    (hres : ∀ j, (rbs j).IsRestrictionResonance)
    (hcover : (⨆ j, (rbs j).avatar_region) = ⊤)
    {s t : GlobalSection (X := X)}
    (h : ∀ j, (rbs j).auto_resonance s = (rbs j).auto_resonance t) :
    s = t := by
  have hst : ∀ j, (rbs j).restrictToAvatar s = (rbs j).restrictToAvatar t := fun j => by
    rw [← hres j, ← hres j]; exact h j
  obtain ⟨g, -, huniq⟩ := probability_glue_unique (fun j => (rbs j).avatar_region) hcover
    (fun j => (rbs j).restrictToAvatar s)
    (fun i j => restrictToAvatar_compatible (fun j => (rbs j).avatar_region) s i j)
  rw [huniq s fun j => rfl, huniq t fun j => (hst j).symm]

/-- **The Self, and its avatar encoding.** Under a covering family of resonant avatars a
contracting predictive model has a fixed point, and that fixed point is the *only* global
state producing its avatar readings.

This is Derivation 6 as the module header states it — the field encodes its own global
state in localized sub-regions — with both halves proved: the Banach fixed point supplies
the Self, and `eq_of_avatar_eq` supplies the encoding. -/
theorem self_eq_of_avatar_eq {J : Type u} (rbs : J → ReflexiveBoundary X)
    (hres : ∀ j, (rbs j).IsRestrictionResonance)
    (hcover : (⨆ j, (rbs j).avatar_region) = ⊤)
    [Nonempty (GlobalSection (X := X))]
    [MetricSpace (GlobalSection (X := X))]
    [CompleteSpace (GlobalSection (X := X))]
    {c : NNReal}
    (rb : ReflexiveBoundary X)
    (h_contracting : ContractingWith c rb.predict) :
    ∃ s : GlobalSection (X := X), rb.predict s = s ∧
      ∀ t : GlobalSection (X := X),
        (∀ j, (rbs j).auto_resonance t = (rbs j).auto_resonance s) → t = s :=
  ⟨ContractingWith.fixedPoint rb.predict h_contracting,
   h_contracting.fixedPoint_isFixedPt,
   fun _ ht => eq_of_avatar_eq rbs hres hcover ht⟩

/-! ### What goes wrong without the predicate

The old `self_of_constResonance` is deleted rather than weakened, and its deletion is the
content of work item W5. It said: the blinded boundary has *the same* Self, by the *same*
proof, from the *same* contraction hypothesis. All three clauses fail now, because
`predict` is no longer free data that survives the substitution. -/

/-- The same avatar region and the same read-out, with an avatar that reads a constant.
Every field of `ReflexiveBoundary` is satisfied; the structure cannot tell this apart
from `rb`. What it *cannot* keep is `rb`'s dynamics — see the next theorem. -/
def constResonance (rb : ReflexiveBoundary X)
    (a₀ : (probabilityPresheaf X).obj (op rb.avatar_region)) : ReflexiveBoundary X where
  avatar_region := rb.avatar_region
  auto_resonance := fun _ => a₀
  readout := rb.readout

/-- **Blinding the avatar destroys the dynamics.** The blinded boundary's self-prediction
is a constant map: it has stopped being a function of the field at all. Under the old
structure this substitution left `predict` untouched, which is precisely why the Self
theorem could not see it. -/
@[simp] theorem constResonance_predict_const (rb : ReflexiveBoundary X)
    (a₀ : (probabilityPresheaf X).obj (op rb.avatar_region)) (s : GlobalSection (X := X)) :
    (rb.constResonance a₀).predict s = rb.readout a₀ := rfl

/-- The blinded boundary's fixed points are exactly the one state its avatar stipulates.
A "Self" fixed in advance of any field: the same value on every substrate with the same
read-out, and no information about the state it is supposed to be a self *of*. -/
theorem constResonance_fixedPt_iff (rb : ReflexiveBoundary X)
    (a₀ : (probabilityPresheaf X).obj (op rb.avatar_region)) (s : GlobalSection (X := X)) :
    (rb.constResonance a₀).predict s = s ↔ rb.readout a₀ = s := Iff.rfl

/-- The blinded boundary does have a unique fixed point — a constant map always does — and
naming it is the point: it is `readout a₀`, with no hypothesis on the metric, no
completeness, and no contraction. Banach is not being used; nothing is. -/
theorem constResonance_existsUnique_self (rb : ReflexiveBoundary X)
    (a₀ : (probabilityPresheaf X).obj (op rb.avatar_region)) :
    ∃! s : GlobalSection (X := X), (rb.constResonance a₀).predict s = s :=
  ⟨rb.readout a₀, rfl, fun _ hs => hs.symm⟩

/-- **Blinding the avatar moves the Self.** This is the theorem that replaces
`self_of_constResonance`, and it says the opposite: a fixed point `s` of the field's own
self-model is *not* a fixed point of the blinded one, as soon as the avatar's stipulated
contents predict something other than `s`.

The old theorem was `reflexive_topology_implies_self (rb.constResonance a₀) h_contracting`
— the same contraction hypothesis, transported. It cannot be stated now: `h_contracting`
constrains `rb.predict`, the blinded boundary's map is `fun _ => rb.readout a₀`, and there
is no longer any route from one to the other.

**Non-vacuity.** The hypothesis `rb.readout a₀ ≠ s` is a genuine condition and it is
checked, not assumed: `Examples.lean` §10's `cortexBlind_self_ne` exhibits it on the
three-site cortex with `a₀` the silent field's reading. -/
theorem not_self_of_constResonance (rb : ReflexiveBoundary X)
    (a₀ : (probabilityPresheaf X).obj (op rb.avatar_region)) {s : GlobalSection (X := X)}
    (hne : rb.readout a₀ ≠ s) : ¬ (rb.constResonance a₀).predict s = s := hne

/-- **A blind avatar is not a resonant one**, as soon as the field has two states the
avatar region can tell apart. The hypothesis is exactly the non-degeneracy that
`Examples.lean` §10 checks for the three-site cortex; on a substrate where it fails the
avatar region sees nothing, and the distinction is empty. -/
theorem constResonance_not_isRestrictionResonance (rb : ReflexiveBoundary X)
    (a₀ : (probabilityPresheaf X).obj (op rb.avatar_region))
    {s t : GlobalSection (X := X)} (h : rb.restrictToAvatar s ≠ rb.restrictToAvatar t) :
    ¬ (rb.constResonance a₀).IsRestrictionResonance := by
  intro hres
  exact h ((hres s).symm.trans (hres t))

end ReflexiveBoundary

/-! ## The contraction rate, from the coupling and the noise

The second half of work item W5. `ContractingWith (1/2)` is not a physical hypothesis:
`1/2` was built into the witness's definition, so "the self-model contracts by a half"
said only that we had defined a map that does. What follows replaces it with a rate that
is a function of the substrate's parameters, and a threshold that decides whether the
rate is a contraction rate at all.

**The rate.** Near the incoherent state the noisy mean-field Kuramoto order parameter
obeys `ṙ = ((K - K_c)/2) r + O(r³)` with `K_c = 2D` (Sakaguchi 1988; `critical_coupling`
in `Phase8_ContinuousField.lean` is that threshold), so `(K - K_c)/2` is the rate at
which the incoherent state loses stability. Over a time `τ` that rate gives the factor
`exp(-(K - K_c) τ / 2)`, and `resonanceRate K D τ` is that factor.

**Which rate this is not.** Linearising `ṙ = ((K - 2D)/2) r - c r³` about the *coherent*
fixed point gives a relaxation rate of `(K - K_c)`, twice the growth rate above, so
perturbations of the coherent branch decay by `exp(-(K - K_c) τ)`, which is smaller.
`resonanceRate` is therefore the larger factor, and requiring the self-model to be
Lipschitz at it is a weaker demand than the coherent branch's own relaxation would
license. Both factors are `< 1` on exactly the same half-plane `K > K_c`, so nothing
downstream distinguishes them.

**What is assumed and what is derived.** That the substrate's self-model is Lipschitz
with *this* constant is an instance obligation — it is the modelling input, and it is the
same kind of commitment `IsRestrictionResonance` is. What is derived is the consequence:
above Sakaguchi's threshold the rate is `< 1` and Banach applies
(`self_of_supercritical`); at or below it the rate is `≥ 1` and `ContractingWith` is
unsatisfiable *for any map at all* (`not_contractingWith_resonanceRate`), so Derivation
6's argument is not merely unproved below threshold but unavailable. No claim is made
that a Self fails to exist there; the claim is that this route to it does.

This is a linearization of an established result, not a new one, and the linear rate is
exact only near threshold. -/

open scoped NNReal

/-- The damping factor of the self-model over a time `τ`: the growth rate of the
incoherent state's instability, `(K - K_c)/2` with `K_c = critical_coupling D = 2D`,
exponentiated over `τ`. The coherent branch relaxes at `(K - K_c)`, so this is the
larger factor and the weaker Lipschitz hypothesis; the threshold `K > K_c` is the same
for both. -/
noncomputable def resonanceRate (K D τ : ℝ) : ℝ≥0 :=
  Real.toNNReal (Real.exp (-(K - critical_coupling D) * τ / 2))

@[simp] theorem coe_resonanceRate (K D τ : ℝ) :
    (resonanceRate K D τ : ℝ) = Real.exp (-(K - critical_coupling D) * τ / 2) :=
  Real.coe_toNNReal _ (Real.exp_pos _).le

/-- **Above Sakaguchi's threshold the self-model contracts.** For `K > K_c = 2D` and any
positive elapsed time the rate is strictly below one, which is the half of
`ContractingWith` that the substrate cannot supply by fiat. -/
theorem resonanceRate_lt_one {K D τ : ℝ} (hτ : 0 < τ) (hKD : critical_coupling D < K) :
    resonanceRate K D τ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_resonanceRate, NNReal.coe_one, Real.exp_lt_one_iff]
  have h : 0 < K - critical_coupling D := sub_pos.mpr hKD
  nlinarith

/-- **At or below the threshold it does not.** The rate is `≥ 1`, so no map is
`ContractingWith` it. -/
theorem one_le_resonanceRate {K D τ : ℝ} (hτ : 0 ≤ τ) (hKD : K ≤ critical_coupling D) :
    1 ≤ resonanceRate K D τ := by
  rw [← NNReal.coe_le_coe, coe_resonanceRate, NNReal.coe_one, Real.one_le_exp_iff]
  have h : 0 ≤ critical_coupling D - K := sub_nonneg.mpr hKD
  nlinarith

/-- **Derivation 6's argument is unavailable below the synchronization threshold.** Not
"the fixed point is hard to find": `ContractingWith (resonanceRate K D τ) f` is false for
*every* self-map of *every* metric space when `K ≤ 2D`, because its first conjunct is
`rate < 1`. This does not say a Self fails to exist below threshold — only that Banach
cannot produce one at this rate. -/
theorem not_contractingWith_resonanceRate {α : Type*} [EMetricSpace α] {K D τ : ℝ}
    (hτ : 0 ≤ τ) (hKD : K ≤ critical_coupling D) (f : α → α) :
    ¬ ContractingWith (resonanceRate K D τ) f := fun h =>
  absurd h.1 (not_lt.mpr (one_le_resonanceRate hτ hKD))

/-- **The Self, above the threshold.** Derivation 6 with the contraction constant read off
the substrate rather than stipulated: given that the self-model relaxes at the order
parameter's rate, a unique fixed point exists exactly because the coupling exceeds
Sakaguchi's `K_c = 2D`.

The Lipschitz hypothesis is the physical commitment and is stated as such; the threshold
is what turns it into a fixed point. Compare `not_contractingWith_resonanceRate`, which is
the same statement's negative half. -/
theorem self_of_supercritical {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]
    [Nonempty (GlobalSection (X := X))]
    [MetricSpace (GlobalSection (X := X))]
    [CompleteSpace (GlobalSection (X := X))]
    {K D τ : ℝ} (hτ : 0 < τ) (hKD : critical_coupling D < K)
    (rb : ReflexiveBoundary X)
    (h_lip : LipschitzWith (resonanceRate K D τ) rb.predict) :
    ∃! s : GlobalSection (X := X), rb.predict s = s :=
  ReflexiveBoundary.self_unique rb ⟨resonanceRate_lt_one hτ hKD, h_lip⟩

/-- The approximate-self estimate at the prescribed supercritical rate. The fixed
point can be the one supplied by `self_of_supercritical` or by E89 on a named cover.
The Lipschitz law remains a separate hypothesis; supercriticality alone does not
construct an encoding/readout or establish representational accuracy. -/
theorem approximate_self_bound_of_supercritical
    [MetricSpace (GlobalSection (X := X))]
    {K D τ : ℝ} (hτ : 0 < τ) (hKD : critical_coupling D < K)
    (rb : ReflexiveBoundary X)
    (h_lip : LipschitzWith (resonanceRate K D τ) rb.predict)
    {s sstar : GlobalSection (X := X)} {ε : ℝ}
    (hfixed : rb.predict sstar = sstar) (hε : dist s (rb.predict s) ≤ ε) :
    dist s sstar ≤ ε / (1 - Real.exp (-(K - critical_coupling D) * τ / 2)) := by
  simpa only [coe_resonanceRate] using
    rb.approximate_self_bound ⟨resonanceRate_lt_one hτ hKD, h_lip⟩ hfixed hε

/-- Exact bounds on the tolerance radius: with `x = (K - 2D) τ / 2 > 0`, it lies
between `ε / x` and `ε / x + ε`. Thus its leading threshold behaviour is `ε / x`,
and it diverges for fixed positive `ε` and `τ` as `K` decreases to `2D`. This is
a statement about the bound, not divergence of an actual state's error; for zero
residual the radius is zero at every supercritical coupling. -/
theorem resonance_error_radius_bounds {K D τ ε : ℝ}
    (hτ : 0 < τ) (hKD : critical_coupling D < K) (hε : 0 ≤ ε) :
    2 * ε / ((K - critical_coupling D) * τ) ≤
      ε / (1 - (resonanceRate K D τ : ℝ)) ∧
    ε / (1 - (resonanceRate K D τ : ℝ)) ≤
      2 * ε / ((K - critical_coupling D) * τ) + ε := by
  let x := (K - critical_coupling D) * τ / 2
  have hx : 0 < x := div_pos (mul_pos (sub_pos.mpr hKD) hτ) (by norm_num)
  have hx1 : 0 < x + 1 := by linarith
  have hgap : 0 < 1 - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
  have hsmall : 1 - Real.exp (-x) ≤ x := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hlarge : x / (x + 1) ≤ 1 - Real.exp (-x) := by
    rw [Real.exp_neg, le_sub_iff_add_le]
    have hinv : (Real.exp x)⁻¹ ≤ (x + 1)⁻¹ :=
      inv_anti₀ hx1 (Real.add_one_le_exp x)
    calc
      x / (x + 1) + (Real.exp x)⁻¹ ≤ x / (x + 1) + (x + 1)⁻¹ :=
        add_le_add le_rfl hinv
      _ = 1 := by field_simp
  have hbase : 2 * ε / ((K - critical_coupling D) * τ) = ε / x := by
    dsimp [x]
    rw [div_div_eq_mul_div]
    ring
  rw [hbase, coe_resonanceRate]
  rw [show -(K - critical_coupling D) * τ / 2 = -x by dsimp [x]; ring]
  change ε / x ≤ ε / (1 - Real.exp (-x)) ∧
    ε / (1 - Real.exp (-x)) ≤ ε / x + ε
  constructor
  · exact div_le_div_of_nonneg_left hε hgap hsmall
  · calc
      ε / (1 - Real.exp (-x)) ≤ ε / (x / (x + 1)) :=
        div_le_div_of_nonneg_left hε (div_pos hx hx1) hlarge
      _ = ε / x + ε := by field_simp; ring

end PhysicsOfConsciousness
