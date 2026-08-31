/-
  Phase 5 (continued): gluing that is obstructed rather than unique.

  Derivation 5 glues local probability sections into one global section under the
  hypothesis `LocalSectionSynchronization.section_agrees_of_phase_eq`: patches at
  *equal* phases agree where they overlap. Under geometric frustration the
  minimisers of the coupling potential are twisted and splay states, at which no
  two patches share a phase, so that hypothesis has nothing to fire on.

  This module weakens the hypothesis in the only direction that keeps the sheaf
  machinery: patches agree on overlaps **up to a phase**. The offsets then form a
  Čech-style 1-cochain with coefficients in `Phase = ℝ/2πℤ`,
  the family glues after a per-patch rotation exactly when that cochain is a
  coboundary, and the obstruction is its class in `PhaseObstruction`.
-/
import PhysicsOfConsciousness.Phase5_GlobalSection
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs

open CategoryTheory TopologicalSpace MeasureTheory
open Opposite

namespace PhysicsOfConsciousness

universe u v

noncomputable section

/-- The phase group `ℝ / 2πℤ`. A phase is periodic, so the coefficients of the
obstruction are the circle and not the line: two configurations differing by a
full turn are the same configuration. -/
abbrev Phase : Type := AddCircle (2 * Real.pi)

section TwistedGluing

variable {X : TopCat.{u}}

/-- Restriction of a section along an inclusion of opens. Notation only; every
statement below is easier to read with it than with the `homOfLE _ |>.op` it
abbreviates. -/
abbrev rest (F : (Opens X)ᵒᵖ ⥤ Type u) {U V : Opens X} (h : U ≤ V)
    (x : F.obj (op V)) : F.obj (op U) :=
  F.map (homOfLE h).op x

theorem rest_rest (F : (Opens X)ᵒᵖ ⥤ Type u) {U V W : Opens X} (h₁ : U ≤ V) (h₂ : V ≤ W)
    (x : F.obj (op W)) : rest F h₁ (rest F h₂ x) = rest F (h₁.trans h₂) x := by
  show (F.map (homOfLE h₂).op ≫ F.map (homOfLE h₁).op) x = _
  rw [← F.map_comp]
  congr 1

/-! ## The phase action -/

/-- **A phase action on a presheaf of local states**: the circle acts on the
sections over every open, compatibly with restriction.

This is the structure Derivation 5's presheaf does *not* carry on its own. A
probability section knows nothing about the phase of the patch it sits on, so
the only phase action `probabilityPresheaf` admits without further input is the
trivial one, and the trivial action is not free. Making the offsets carry
    information would require enlarging the local state so that the phase, or
    some independent transition datum, is part of it. This module deliberately
    stops short of choosing such a physical state space. -/
structure PhaseAction (F : (Opens X)ᵒᵖ ⥤ Type u) where
  /-- Rotating a local section by a phase. -/
  act : Phase → ∀ {U : (Opens X)ᵒᵖ}, F.obj U → F.obj U
  act_zero : ∀ {U : (Opens X)ᵒᵖ} (x : F.obj U), act 0 x = x
  act_add : ∀ (s t : Phase) {U : (Opens X)ᵒᵖ} (x : F.obj U), act s (act t x) = act (s + t) x
  /-- The action commutes with restriction: rotating and then restricting is
      restricting and then rotating. Without this the offsets say nothing about
      overlaps. -/
  act_map : ∀ (t : Phase) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (x : F.obj U),
    F.map f (act t x) = act t (F.map f x)

variable {F : (Opens X)ᵒᵖ ⥤ Type u}

theorem PhaseAction.act_neg_act (P : PhaseAction F) (t : Phase) {U : (Opens X)ᵒᵖ}
    (x : F.obj U) : P.act (-t) (P.act t x) = x := by
  rw [P.act_add, neg_add_cancel, P.act_zero]

theorem PhaseAction.act_rest (P : PhaseAction F) (t : Phase) {U V : Opens X} (h : U ≤ V)
    (x : F.obj (op V)) : rest F h (P.act t x) = P.act t (rest F h x) :=
  P.act_map t _ x

/-- **The action is free over `U`**: no non-zero phase fixes a section over `U`.

Freeness is what makes an offset *mean* something: without it two patches can be
declared to differ by any phase at all, and the cochain carries no information.
It fails exactly where one expects it to — over the empty open, and at a section
invariant under the whole circle, which for a phase distribution is the uniform
one. A structureless local state has no phase to disagree about. -/
def IsFreeOn (P : PhaseAction F) (U : Opens X) : Prop :=
  ∀ (x : F.obj (op U)) (t : Phase), P.act t x = x → t = 0

/-! ## Čech-style 1-cochains, with phase coefficients -/

/-- A total phase 1-cochain: one offset per ordered pair of patches.

This is deliberately not yet the cochain group of the nerve: values on pairs
with empty overlap have not been quotiented away. `PhaseObstruction` below is
therefore an obstruction quotient, not a claim to have constructed Čech
cohomology. A proper nerve-indexed complex belongs with the physical transition
model that would make those offsets meaningful. -/
abbrev PhaseCochain (I : Type v) : Type v := I → I → Phase

/-- The coboundary of a 0-cochain: a phase per patch produces the offsets
`h i - h j`. These are the offsets a *globally defined* phase field induces, and
they are precisely the ones that can be rotated away. -/
def coboundaryHom (I : Type*) : (I → Phase) →+ PhaseCochain I where
  toFun h := fun i j => h i - h j
  map_zero' := by funext i j; simp
  map_add' a b := by funext i j; simp; abel

/-- **The offsets come from a phase field.** -/
def IsCoboundary {I : Type*} (θ : PhaseCochain I) : Prop :=
  ∃ h : I → Phase, ∀ i j, θ i j = h i - h j

/-- The 1-coboundaries, as a subgroup of the 1-cochains. -/
def phaseCoboundaries (I : Type*) : AddSubgroup (PhaseCochain I) :=
  (coboundaryHom I).range

theorem mem_phaseCoboundaries_iff {I : Type*} (θ : PhaseCochain I) :
    θ ∈ phaseCoboundaries I ↔ IsCoboundary θ := by
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, fun i j => rfl⟩
  · rintro ⟨h, hh⟩; exact ⟨h, by funext i j; exact (hh i j).symm⟩

/-- The holonomy of a cochain around an ordered triangle of the nerve. -/
def holonomy {I : Type*} (θ : PhaseCochain I) (i j k : I) : Phase :=
  θ i j + θ j k + θ k i

/-- **A coboundary has no holonomy.** The elementary half of the obstruction: if
the offsets come from a phase field then they telescope around every triangle. -/
theorem holonomy_eq_zero_of_isCoboundary {I : Type*} {θ : PhaseCochain I}
    (hb : IsCoboundary θ) (i j k : I) : holonomy θ i j k = 0 := by
  obtain ⟨h, hh⟩ := hb
  simp only [holonomy, hh]
  abel

/-- The contrapositive, and the one that does work: a triangle carrying holonomy
is a family that no per-patch rotation can untwist. -/
theorem not_isCoboundary_of_holonomy_ne_zero {I : Type*} {θ : PhaseCochain I} {i j k : I}
    (h : holonomy θ i j k ≠ 0) : ¬ IsCoboundary θ :=
  fun hb => h (holonomy_eq_zero_of_isCoboundary hb i j k)

/-- The 1-cocycles of the nerve of `cover`: cochains whose holonomy vanishes
around every triangle whose three patches actually meet.

A triangle with empty triple overlap imposes no condition — there is no point at
which the three offsets could be compared — which is exactly why a nerve with a
hole can carry a class. -/
def phaseCocycles {I : Type*} (cover : I → Opens X) : AddSubgroup (PhaseCochain I) where
  carrier := {θ | ∀ i j k, cover i ⊓ cover j ⊓ cover k ≠ ⊥ → holonomy θ i j k = 0}
  zero_mem' := by intro i j k _; simp [holonomy]
  add_mem' := by
    intro a b ha hb i j k h
    have := ha i j k h
    have := hb i j k h
    simp only [holonomy, Pi.add_apply] at *
    rw [show a i j + b i j + (a j k + b j k) + (a k i + b k i)
      = (a i j + a j k + a k i) + (b i j + b j k + b k i) by abel]
    simp [*]
  neg_mem' := by
    intro a ha i j k h
    have := ha i j k h
    simp only [holonomy, Pi.neg_apply] at *
    rw [show -a i j + -a j k + -a k i = -(a i j + a j k + a k i) by abel, this, neg_zero]

theorem phaseCoboundaries_le_phaseCocycles {I : Type*} (cover : I → Opens X) :
    phaseCoboundaries I ≤ phaseCocycles cover := by
  intro θ hθ i j k _
  exact holonomy_eq_zero_of_isCoboundary ((mem_phaseCoboundaries_iff θ).mp hθ) i j k

/-- **The phase-obstruction quotient of a cover.** Cocycles modulo
coboundaries. This detects failure of the total offset cochain to come from
patch phases, but it is not named Čech `H¹`: total cochains still contain values
on empty pairwise overlaps. -/
def PhaseObstruction {I : Type*} (cover : I → Opens X) : Type _ :=
  (phaseCocycles cover) ⧸ (phaseCoboundaries I).addSubgroupOf (phaseCocycles cover)

noncomputable instance {I : Type*} (cover : I → Opens X) : AddCommGroup (PhaseObstruction cover) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- The class of a cocycle. -/
def obstructionClass {I : Type*} {cover : I → Opens X} (θ : PhaseCochain I)
    (hθ : θ ∈ phaseCocycles cover) : PhaseObstruction cover :=
  QuotientAddGroup.mk ⟨θ, hθ⟩

/-- **The class vanishes exactly when the offsets come from a phase field.** -/
theorem obstructionClass_eq_zero_iff {I : Type*} {cover : I → Opens X} (θ : PhaseCochain I)
    (hθ : θ ∈ phaseCocycles cover) :
    obstructionClass θ hθ = (0 : PhaseObstruction cover) ↔ IsCoboundary θ := by
  constructor
  · intro h
    exact (mem_phaseCoboundaries_iff θ).mp
      ((QuotientAddGroup.eq_zero_iff (⟨θ, hθ⟩ : phaseCocycles cover)).mp h)
  · intro h
    exact (QuotientAddGroup.eq_zero_iff (⟨θ, hθ⟩ : phaseCocycles cover)).mpr
      ((mem_phaseCoboundaries_iff θ).mpr h)


/-! ## Families that agree on overlaps only up to a phase -/

/-- **A cover whose local states agree on overlaps up to a phase.**

This is `LocalSectionSynchronization` with its overlap condition weakened in the
one direction that keeps the sheaf machinery. `section_agrees_of_phase_eq`
demands that patches at *equal* phases restrict to the same local state; under
frustration the minimisers of the coupling potential are twisted and splay
states, at which no two patches share a phase, so that condition never fires.
Here the patches restrict to states that differ by a phase, and the differences
are recorded rather than assumed away.

`offset` is data and not a derived quantity, which is the point: a frustrated
configuration has no common phase for its patches to be measured against, so
what the family knows is the *relative* phases. Whether those relative phases
come from absolute ones is precisely the cohomological question below. -/
structure TwistedFamily (F : (Opens X)ᵒᵖ ⥤ Type u) (P : PhaseAction F) where
  /-- The index set of the cover. -/
  I : Type u
  /-- The patches. -/
  cover : I → Opens X
  /-- They cover. -/
  is_cover : iSup cover = ⊤
  /-- The local state carried by each patch. -/
  s : (i : I) → F.obj (op (cover i))
  /-- The phase by which patch `i` leads patch `j` on their overlap. -/
  offset : I → I → Phase
  /-- The weakened overlap condition. -/
  agrees_up_to_phase : ∀ i j,
    rest F (inf_le_left : cover i ⊓ cover j ≤ cover i) (s i)
      = P.act (offset i j) (rest F (inf_le_right : cover i ⊓ cover j ≤ cover j) (s j))

variable {P : PhaseAction F}

/-- The overlap condition, restricted to any open contained in both patches.
Stated once here because every argument below needs it on triple overlaps, and
because it removes the `cover i ⊓ cover j` versus `cover j ⊓ cover i` bookkeeping
that would otherwise obscure the algebra. -/
theorem TwistedFamily.agrees_on (T : TwistedFamily F P) (i j : T.I) {W : Opens X}
    (hi : W ≤ T.cover i) (hj : W ≤ T.cover j) :
    rest F hi (T.s i) = P.act (T.offset i j) (rest F hj (T.s j)) := by
  have h := congrArg (rest F (le_inf hi hj)) (T.agrees_up_to_phase i j)
  rw [rest_rest, P.act_rest, rest_rest] at h
  exact h

/-- **The family glues after a per-patch rotation**: there is one global state
that every patch sees, up to the phase that patch is running at.

This is the conclusion Derivation 5 draws, weakened to the extent the twisted
setting forces and no further. The global object is still unique (see
`gluesUpToPhase_unique`); what it is no longer required to do is agree with each
patch on the nose. -/
def GluesUpToPhase (T : TwistedFamily F P) : Prop :=
  ∃ (g : F.obj (op ⊤)) (h : T.I → Phase),
    ∀ i, T.s i = P.act (h i) (rest F (le_top : T.cover i ≤ ⊤) g)

/-- **A twisted family whose offsets are a coboundary glues.** Rotate patch `i`
backwards by `h i`, and the weakened condition becomes the strict one, at which
point the sheaf property applies unchanged.

This is the positive half of the answer to the frustration objection, and the
half that matters: nothing about the gluing needed the patches to be in phase.
It needed their phase differences to be *differences of phases*. -/
theorem gluesUpToPhase_of_isCoboundary (hF : TopCat.Presheaf.IsSheaf F)
    (T : TwistedFamily F P) (hb : IsCoboundary T.offset) : GluesUpToPhase T := by
  obtain ⟨h, hh⟩ := hb
  have h_compat : ∀ i j,
      rest F (inf_le_left : T.cover i ⊓ T.cover j ≤ T.cover i) (P.act (-h i) (T.s i))
        = rest F (inf_le_right : T.cover i ⊓ T.cover j ≤ T.cover j) (P.act (-h j) (T.s j)) := by
    intro i j
    rw [P.act_rest, P.act_rest, T.agrees_up_to_phase i j, P.act_add, hh i j]
    have : -h i + (h i - h j) = -h j := by abel
    rw [this]
  obtain ⟨g, hg, -⟩ :=
    sheaf_glue_unique hF T.cover T.is_cover (fun i => P.act (-h i) (T.s i)) h_compat
  refine ⟨g, h, fun i => ?_⟩
  have hgi : rest F (le_top : T.cover i ≤ ⊤) g = P.act (-h i) (T.s i) := hg i
  rw [hgi, P.act_add, add_neg_cancel, P.act_zero]

/-- **Conversely, a family that glues has coboundary offsets** — provided the
action is free on the overlaps, so that an offset is determined by the states it
relates rather than being a free label.

Freeness is not a technicality. Where it fails — over an empty overlap, or at a
local state invariant under the whole circle — the offset across that overlap
carries no information at all, and the two halves of this section come apart.
That is exactly how a non-trivial class survives: see `holonomy_eq_zero_of_isFreeOn`. -/
theorem isCoboundary_of_gluesUpToPhase (T : TwistedFamily F P)
    (hfree : ∀ i j, IsFreeOn P (T.cover i ⊓ T.cover j)) (hglue : GluesUpToPhase T) :
    IsCoboundary T.offset := by
  obtain ⟨g, h, hs⟩ := hglue
  refine ⟨h, fun i j => ?_⟩
  set W : Opens X := T.cover i ⊓ T.cover j with hW
  set y : F.obj (op W) := rest F (le_top : W ≤ ⊤) g with hy
  have hxi : rest F (inf_le_left : W ≤ T.cover i) (T.s i) = P.act (h i) y := by
    rw [hs i, P.act_rest, rest_rest]
  have hxj : rest F (inf_le_right : W ≤ T.cover j) (T.s j) = P.act (h j) y := by
    rw [hs j, P.act_rest, rest_rest]
  have key : P.act (h i) y = P.act (T.offset i j + h j) y := by
    rw [← P.act_add, ← hxj, ← hxi]
    exact T.agrees_up_to_phase i j
  have hfix : P.act (h i - h j - T.offset i j) y = y := by
    have := congrArg (P.act (-(T.offset i j + h j))) key
    rw [P.act_add, P.act_add, neg_add_cancel, P.act_zero] at this
    rw [← this]
    congr 1
    abel
  have := hfree i j y _ hfix
  have h2 : h i - h j - T.offset i j + T.offset i j = 0 + T.offset i j := by rw [this]
  simpa using h2.symm

/-- **The holonomy around a triangle of patches that actually meet vanishes.**
On a common point of three patches the three offsets compose, and freeness turns
the composition into an equation on phases.

So a non-zero class needs a triangle of patches with *no* common point — or one
whose common local state is phase-invariant. The obstruction is a property of
the nerve of the cover, not of the dynamics running on it. -/
theorem holonomy_eq_zero_of_isFreeOn (T : TwistedFamily F P) {i j k : T.I}
    (hfree : IsFreeOn P (T.cover i ⊓ T.cover j ⊓ T.cover k)) :
    holonomy T.offset i j k = 0 := by
  set W : Opens X := T.cover i ⊓ T.cover j ⊓ T.cover k with hW
  have hi : W ≤ T.cover i := inf_le_left.trans inf_le_left
  have hj : W ≤ T.cover j := inf_le_left.trans inf_le_right
  have hk : W ≤ T.cover k := inf_le_right
  have e₁ := T.agrees_on i j hi hj
  have e₂ := T.agrees_on j k hj hk
  have e₃ := T.agrees_on k i hk hi
  have hfix : P.act (holonomy T.offset i j k) (rest F hi (T.s i)) = rest F hi (T.s i) := by
    conv_rhs => rw [e₁, e₂, e₃]
    rw [P.act_add, P.act_add]
    congr 1
  exact hfree _ _ hfix

/-- **Offsets that come from a phase field are a coboundary.** The one-line
observation that decides the frustration question: a configuration in which
every patch has a phase — locked, twisted or splay — presents offsets
`φ i - φ j`, and those telescope. -/
theorem isCoboundary_of_phaseField {I : Type v} (φ : I → Phase) :
    IsCoboundary (fun i j => φ i - φ j) :=
  ⟨φ, fun _ _ => rfl⟩

/-- **A frustrated phase configuration alone creates no gluing obstruction.**

Locked, twisted and splay configurations all assign an absolute phase `φ i` to
each patch. If the overlap offsets are their differences, the offsets are a
coboundary and the family glues after patchwise rotation. Thus frustration by
itself cannot supply a non-zero class in `PhaseObstruction`; a genuine obstruction would
need transition data not determined by the oscillator phase field. -/
theorem gluesUpToPhase_of_phaseField (hF : TopCat.Presheaf.IsSheaf F)
    (T : TwistedFamily F P) (φ : T.I → Phase)
    (hoffset : ∀ i j, T.offset i j = φ i - φ j) : GluesUpToPhase T :=
  gluesUpToPhase_of_isCoboundary hF T ⟨φ, hoffset⟩

/-- **A cochain with vanishing holonomy on every triangle is a coboundary**, once
it is antisymmetric and there is a patch to use as a reference. Pure algebra: no
sheaf, no cover, no action. -/
theorem isCoboundary_of_holonomy {I : Type v} [Nonempty I] {θ : PhaseCochain I}
    (hanti : ∀ i j, θ j i = -θ i j) (hhol : ∀ i j k, holonomy θ i j k = 0) :
    IsCoboundary θ := by
  obtain ⟨o⟩ := ‹Nonempty I›
  refine ⟨fun i => θ i o, fun i j => ?_⟩
  have h := hhol i j o
  rw [holonomy, hanti i o] at h
  rw [eq_sub_iff_add_eq]
  have : θ i j + θ j o + -θ i o + θ i o = 0 + θ i o := by rw [h]
  simpa using this

/-! ## Where a non-trivial class can live -/

/-- **Antisymmetry of the offsets**, from freeness on the overlap. -/
theorem TwistedFamily.offset_antisymm (T : TwistedFamily F P) {i j : T.I}
    (hfree : IsFreeOn P (T.cover i ⊓ T.cover j)) :
    T.offset j i = -T.offset i j := by
  set W : Opens X := T.cover i ⊓ T.cover j with hW
  have hi : W ≤ T.cover i := inf_le_left
  have hj : W ≤ T.cover j := inf_le_right
  have e₁ := T.agrees_on i j hi hj
  have e₂ := T.agrees_on j i hj hi
  have hfix : P.act (T.offset i j + T.offset j i) (rest F hi (T.s i)) = rest F hi (T.s i) := by
    conv_rhs => rw [e₁, e₂]
    rw [P.act_add]
  have h0 := hfree _ _ hfix
  have : T.offset i j + T.offset j i + -T.offset i j = 0 + -T.offset i j := by rw [h0]
  simpa using this

/-- **If every triangle of patches meets, and the action is free there, the class
vanishes and the family glues.**

The exact scope of the frustration repair: weakening the overlap condition costs
nothing whenever the cover has no hole in it. A hole is what it takes for the
weakened condition to be strictly weaker. -/
theorem gluesUpToPhase_of_isFreeOn (hF : TopCat.Presheaf.IsSheaf F) (T : TwistedFamily F P)
    [Nonempty T.I] (hpair : ∀ i j, IsFreeOn P (T.cover i ⊓ T.cover j))
    (htriple : ∀ i j k, IsFreeOn P (T.cover i ⊓ T.cover j ⊓ T.cover k)) :
    GluesUpToPhase T :=
  gluesUpToPhase_of_isCoboundary hF T
    (isCoboundary_of_holonomy (fun i j => T.offset_antisymm (hpair i j))
      (fun i j k => holonomy_eq_zero_of_isFreeOn T (htriple i j k)))

end TwistedGluing

end

end PhysicsOfConsciousness
