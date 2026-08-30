/-
  Phase 6: Reflexive Topology and the Emergence of the Self

  This module formalizes:
  1. The distinction between Unity (a Global Section) and the Self.
  2. The thermodynamic requirement for the unified field to predict its own internal
     state-changes (auto-resonance).
  3. The topological folding that creates a low-dimensional avatar of the boundary.

  **Proof strategy for reflexive_topology_implies_self:**
  The predictive model `predict : GlobalSection X → GlobalSection X` is a
  continuous self-map. We prove it has a fixed point via the **Banach Contraction
  Mapping Theorem** (`ContractingWith.fixedPoint_isFixedPt` in Mathlib), which
  requires:
    - `GlobalSection X` is a nonempty complete metric space.
    - `predict` is a contracting map (physically: successive predictions lose
      entropy, i.e., the prediction process is dissipative).

  Both are hypotheses here, and neither is idle. `Examples.lean` §10 discharges them
  on the three-site cortex: it pierces the sheafification layer (`massEquiv` proves
  the global sections there *are* the finite measures on the substrate, read as
  densities), metrizes them by the uniform distance between those densities,
  proves that metric complete, and supplies a self-prediction map that contracts by
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

  **The avatar (2026-08-30, open item O2).** `reflexive_topology_implies_self` consumes
  only `predictive_model`; it never mentions `auto_resonance`, and `auto_resonance` is
  unconstrained data, so nothing in the theorem makes the avatar track the field. The
  section "The avatar has to read the field" below supplies the missing constraint as a
  *predicate* — `ReflexiveBoundary.IsRestrictionResonance` — together with the two
  theorems that make it matter: `ReflexiveBoundary.eq_of_avatar_eq`, where a covering
  family of resonant avatars determines the global state, and
  `ReflexiveBoundary.self_of_constResonance`, where blinding the avatar changes nothing
  the Self theorem can see.
-/

import PhysicsOfConsciousness.Phase5_GlobalSection
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

structure PredictiveModel (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X] where
  -- A predictive model is a mapping from the current state to a future state
  -- that minimizes thermodynamic friction.
  predict : GlobalSection (X := X) → GlobalSection (X := X)

-- A Reflexive Boundary (The Self) is a topological feature where the system
-- explicitly encodes its own global state (the Global Section) into a localized
-- sub-region (the avatar), achieving auto-resonance.
structure ReflexiveBoundary (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X] where
  avatar_region : Opens X
  /-- The state of the avatar region, as a function of the global section.

      **Unconstrained data.** Nothing here says the avatar's state has anything to do
      with the field's: a constant function is a legal `auto_resonance`, and
      `constResonance` builds one. The constraint that makes the name honest is the
      predicate `IsRestrictionResonance` below, kept out of the structure per rule §3 of
      `PhysicsOfConsciousness/AGENTS.md`. -/
  auto_resonance : GlobalSection (X := X) → (probabilityPresheaf X).obj (op avatar_region)
  -- The predictive model is self-referential: the avatar's prediction IS a global section.
  -- (Replacing `is_self_predictive : True` with the actual fixed-point content.)
  predictive_model : PredictiveModel X

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

**Hypotheses (replacing the former `is_self_predictive : True`):**
- `[Nonempty (GlobalSection X)]`: The system has at least one possible state.
- `[MetricSpace (GlobalSection X)]`: The space of global sections has a metric
  (on a finite discrete substrate, the uniform distance between the densities of the
  measures the sections glue to — constructed in `Examples.lean` §10).
- `[CompleteSpace (GlobalSection X)]`: The metric is complete.
- `h_contracting : ContractingWith (1/2) predict`: The prediction map contracts
  distances by at least 1/2 — a quantitative form of "predictions converge".

**What this does not establish.** Nothing about the avatar. `rb` enters only through
`rb.predictive_model`, so the statement is unchanged if `rb.auto_resonance` is replaced by
a constant — `self_of_constResonance` proves exactly that. The Self here is a fixed point
of a self-map of the global sections; that it is *encoded in a sub-region* is the separate
content of `eq_of_avatar_eq`, which needs `IsRestrictionResonance` and a cover.

The fixed point is also unique, which this statement does not record: see `self_unique`.
-/
theorem reflexive_topology_implies_self
  {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]
  [Nonempty (GlobalSection (X := X))]
  [MetricSpace (GlobalSection (X := X))]
  [CompleteSpace (GlobalSection (X := X))]
  (rb : ReflexiveBoundary X)
  (h_contracting : ContractingWith (1/2) rb.predictive_model.predict) :
  ∃ s : GlobalSection (X := X), rb.predictive_model.predict s = s :=
  -- ContractingWith.fixedPoint_isFixedPt : IsFixedPt f (fixedPoint f hf)
  -- IsFixedPt f x is definitionally `f x = x`, which is our goal.
  ⟨ContractingWith.fixedPoint rb.predictive_model.predict h_contracting,
   h_contracting.fixedPoint_isFixedPt⟩

/-! ## The avatar has to read the field

`auto_resonance` is *data*: an arbitrary function from the global state to a local
section over the avatar region. Nothing in the structure makes the avatar's state track
the field's, and until 2026-08-30 no theorem in the development mentioned the field at
all — `reflexive_topology_implies_self` consumes only `predictive_model`, so a boundary
whose avatar ignores its input satisfies every hypothesis and reaches the same
conclusion. That was open item **O2**.

Following rule §3 of `PhysicsOfConsciousness/AGENTS.md`, the constraint is added as a
*predicate*, not as a field: `IsRestrictionResonance` says the avatar's state is the
presheaf restriction of the global state. The class stays bare, and results say which
of them they need.

Two theorems then divide the question.

* `eq_of_avatar_eq` is the positive half, and it is where the sheaf condition earns its
  place in Derivation 6: if a family of resonant avatars *covers* the substrate, the
  global state is determined by the avatar readings alone. Localized self-encodings
  reconstruct unity; no separate access to the global section is needed.
* `constResonance_not_isRestrictionResonance` is the negative half, in the same style as
  `contracting_implies_const` in `Examples.lean` §10: from any boundary one can build
  another with the same region and the same predictive model whose avatar reads a
  constant, so it satisfies the class and fails the predicate. `self_of_constResonance`
  is the point — the Self still exists there, unchanged. The fixed-point theorem is
  blind to the avatar, and only the predicate makes the avatar mean anything.

What this does *not* establish: that any physical process realizes the restriction. The
predicate is a modelling condition on an instance, like `section_agrees_of_phase_eq`;
`Examples.lean` §10 discharges it on the three-site cortex and §10 also exhibits the
blind boundary, so both halves are known non-vacuous.
-/

namespace ReflexiveBoundary

variable {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]

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
    (rb : ReflexiveBoundary X)
    (h_contracting : ContractingWith (1/2) rb.predictive_model.predict) :
    ∃ s : GlobalSection (X := X), rb.predictive_model.predict s = s ∧
      ∀ t : GlobalSection (X := X),
        (∀ j, (rbs j).auto_resonance t = (rbs j).auto_resonance s) → t = s :=
  ⟨ContractingWith.fixedPoint rb.predictive_model.predict h_contracting,
   h_contracting.fixedPoint_isFixedPt,
   fun _ ht => eq_of_avatar_eq rbs hres hcover ht⟩

/-- The Self is unique, not merely existent: Banach gives both halves, and only the
existence half was recorded before. -/
theorem self_unique {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]
    [Nonempty (GlobalSection (X := X))]
    [MetricSpace (GlobalSection (X := X))]
    [CompleteSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X)
    (h_contracting : ContractingWith (1/2) rb.predictive_model.predict) :
    ∃! s : GlobalSection (X := X), rb.predictive_model.predict s = s :=
  ⟨ContractingWith.fixedPoint rb.predictive_model.predict h_contracting,
   h_contracting.fixedPoint_isFixedPt,
   fun _ hs => h_contracting.fixedPoint_unique hs⟩

/-! ### What goes wrong without the predicate -/

/-- The same avatar region and the same predictive model, with an avatar that reads a
constant. Every field of `ReflexiveBoundary` is satisfied; the structure cannot tell this
apart from `rb`. -/
def constResonance (rb : ReflexiveBoundary X)
    (a₀ : (probabilityPresheaf X).obj (op rb.avatar_region)) : ReflexiveBoundary X where
  avatar_region := rb.avatar_region
  auto_resonance := fun _ => a₀
  predictive_model := rb.predictive_model

/-- **The fixed-point theorem is blind to the avatar.** `reflexive_topology_implies_self`
applies verbatim to the blinded boundary, with the same proof and the same Self: it
consumes `predictive_model` and never mentions `auto_resonance`. This is why the
predicate, and not the class, has to carry the constraint. -/
theorem self_of_constResonance
    [Nonempty (GlobalSection (X := X))]
    [MetricSpace (GlobalSection (X := X))]
    [CompleteSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X) (a₀ : (probabilityPresheaf X).obj (op rb.avatar_region))
    (h_contracting : ContractingWith (1/2) rb.predictive_model.predict) :
    ∃ s : GlobalSection (X := X), (rb.constResonance a₀).predictive_model.predict s = s :=
  reflexive_topology_implies_self (rb.constResonance a₀) h_contracting

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

end PhysicsOfConsciousness
