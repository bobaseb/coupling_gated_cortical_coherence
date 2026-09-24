import PhysicsOfConsciousness.Phase5_GlobalSection
import Mathlib.Topology.Sheaves.SheafOfFunctions

/-!
# Gluing over content variables: the decodability cover

The sheaf of `Phase5_GlobalSection` is built over a spatial substrate, so its
patches overlap where they share sites. The unity question the manuscript asks
is about regions that describe the same thing from different places: visual and
motor territories agree on where a cup is, and they overlap in *what they
describe*, not in where they lie. This module restates the gluing results over
that second kind of overlap.

The base is a set `V` of content variables. Each region is a partial decoder:
its domain is the set of variables it decodes, within a declared tolerance
`θ`, on every state of a declared relevant family (`DecodingSetup.domain`).
Two regions overlap exactly on the variables both decode, and restriction
forgets variables. This is the decodability cover the manuscript proposes; it
is fixed by what each region carries before any comparison of regions is made.

* **Exact gluing transfers verbatim.** Partial decodes are sections of the
  presheaf of real functions on `V` with the discrete topology, which Mathlib
  proves is a sheaf, and the spatial `sheaf_glue_unique` applies without
  change (`decode_glue_unique`). At tolerance zero the glued section is the
  true content (`decode_glue_value`).
* **Compatibility is a consequence of the cover.** Two regions that both decode
  a variable within `θ` agree on it within `2θ` at every relevant state
  (`decode_compatible`). On the spatial cover agreement was a hypothesis; here
  it is a theorem, and the bound is attained (`Examples/ContentCover.lean`
  §37). This is the accuracy confound of the manuscript's disconfirming test,
  in formal form: on a decodability cover, agreement up to `2θ` is what
  fidelity alone delivers, so only *excess* agreement is evidence of anything.
* **Approximate selection transfers, and sharpens.** Weights subordinate to the
  cover select, variable by variable, a convex combination of the regions'
  decodes. For any compatible family of signed or vector contents the selection
  is within `ε` of each patch and two selections differ by at most `ε`, at
  every cover multiplicity (`select_close`, `select_dist`), which is
  `ApproximateGluing.select_close` and `select_dist_le` without the
  nonnegativity and finiteness of the substrate. On the decodability cover the
  selection is within `θ` of the true content (`select_decode_near_value`).
* **The decoder class must be bounded.** A region whose readout is injective on
  the relevant family decodes every variable exactly with some decoder
  (`exists_exact_decoder_of_injOn`), so an unrestricted decoder class makes
  every such region overlap every other on everything. Conversely a region
  that reads two relevant states identically decodes no variable on which they
  differ by more than `2θ`, with any decoder (`not_decodes_of_read_eq`).

## What does not transfer

The probability presheaf and its measure representation are about measures on
a spatial substrate, and have no counterpart here: a section over a set of
variables is a list of values, not a distribution. The `√N`
coherence-to-content bounds (`chord_le_of_coherence` and the patch, nerve-walk
and spectral forms) bound the disagreement between spatial patches of
oscillators, and on this cover the overlap agreement is instead bounded by
decoding error. Bridging the two needs the manuscript's bridge assumption E78:
nothing here relates a region's phase order to what it decodes. Nor does
anything here select the candidate variables, the tolerance or the decoder
class; those are the declared inputs the manuscript gives rules for.

## Scope

The decoding here is deterministic: a variable is in a region's domain when the
decoder is within `θ` on *every* relevant state. The manuscript's criterion is
statistical (cross-validated decoding above a permutation null), and a
worst-case tolerance is its idealization, not its formalization. The relevant
family, the true values, the region readouts and the decoders are all
declared.
-/

open CategoryTheory TopologicalSpace Opposite
open scoped NNReal

namespace PhysicsOfConsciousness.ContentCover

/-! ## Selection for signed and vector contents

`ApproximateGluing` selects nonnegative mass profiles on a finite substrate.
The content cover needs signed values on any index of variables, so the
selection is restated for contents in a real normed space. The weights are the
same `ApproximateGluing.IsPartition`. -/

section Selection

variable {ι A E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise weighted selection of vector contents. -/
noncomputable def select (w : ι → A → ℝ≥0) (s : ι → A → E) : A → E :=
  fun x => ∑ i, (w i x : ℝ) • s i x

/-- **Convexity.** If every patch covering `x` reports within `δ` of `c`, so does
the selection. -/
theorem norm_select_sub_le {U : ι → Set A} {w : ι → A → ℝ≥0} {s : ι → A → E}
    (hw : ApproximateGluing.IsPartition U w) (x : A) (c : E) {δ : ℝ}
    (h : ∀ j, x ∈ U j → ‖s j x - c‖ ≤ δ) :
    ‖select w s x - c‖ ≤ δ := by
  have hw' : ∑ j, (w j x : ℝ) = 1 := by exact_mod_cast hw.2 x
  have hc : c = ∑ j, (w j x : ℝ) • c := by rw [← Finset.sum_smul, hw', one_smul]
  have heq : select w s x - c = ∑ j, (w j x : ℝ) • (s j x - c) := by
    conv_lhs => rw [hc]
    simp only [select, smul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ j, ‖(w j x : ℝ) • (s j x - c)‖ := norm_sum_le _ _
    _ ≤ ∑ j, (w j x : ℝ) * δ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w j x).coe_nonneg]
      by_cases hj : w j x = 0
      · simp [hj]
      · have hxj : x ∈ U j := by
          by_contra hx
          exact hj (hw.1 j x hx)
        exact mul_le_mul_of_nonneg_left (h j hxj) (w j x).coe_nonneg
    _ = δ := by rw [← Finset.sum_mul, hw', one_mul]

/-- **The selection is within `ε` of each patch on that patch.** The vector
form of `ApproximateGluing.select_close`. -/
theorem select_close {U : ι → Set A} {w : ι → A → ℝ≥0} {s : ι → A → E} {ε : ℝ}
    (hw : ApproximateGluing.IsPartition U w) (hs : LocalContent.Compatible U s ε)
    {i : ι} {x : A} (hx : x ∈ U i) :
    ‖select w s x - s i x‖ ≤ ε :=
  norm_select_sub_le hw x (s i x) fun j hj => hs j i x hj hx

/-- **Two selections differ by at most `ε`**, at every cover multiplicity. The
vector form of `ApproximateGluing.select_dist_le`. -/
theorem select_dist {U : ι → Set A} {w v : ι → A → ℝ≥0} {s : ι → A → E} {ε : ℝ}
    (hw : ApproximateGluing.IsPartition U w) (hv : ApproximateGluing.IsPartition U v)
    (hs : LocalContent.Compatible U s ε) (x : A) :
    ‖select w s x - select v s x‖ ≤ ε := by
  rw [norm_sub_rev]
  exact norm_select_sub_le hv x (select w s x) fun j hj => by
    rw [norm_sub_rev]
    exact select_close hw hs hj

end Selection

/-! ## Regions as partial decoders -/

/-- Regions `ι` read a state through their own readouts, and decode each content
variable from what they read. Data only; how well they decode is `domain`. -/
structure DecodingSetup (S : Type*) {ι : Type*} (R : ι → Type*) (V : Type*) where
  /-- The states the criterion is about. -/
  relevant : Set S
  /-- The true value of each content variable at each state. Declared. -/
  value : V → S → ℝ
  /-- What region `i` carries about a state. -/
  read : (i : ι) → S → R i
  /-- Region `i`'s decoder for variable `v`, acting on what the region carries. -/
  dec : (i : ι) → V → R i → ℝ

namespace DecodingSetup

variable {S ι V : Type*} {R : ι → Type*} (D : DecodingSetup S R V)

/-- Region `i`'s decode of variable `v` at state `s`. -/
def decode (i : ι) (v : V) (s : S) : ℝ := D.dec i v (D.read i s)

/-- Region `i` decodes `v` within `θ` on every relevant state. -/
def Decodes (θ : ℝ) (i : ι) (v : V) : Prop :=
  ∀ s ∈ D.relevant, |D.decode i v s - D.value v s| ≤ θ

/-- **The decodability cover.** Region `i`'s domain is the set of variables it
decodes within `θ`. Nothing about any other region enters it. -/
def domain (θ : ℝ) (i : ι) : Set V := {v | D.Decodes θ i v}

variable {D}

/-- **Compatibility is a consequence of decodability.** Two regions that both
decode a variable within `θ` agree on it within `2θ` at every relevant state.
On a spatial cover this was the hypothesis; on the decodability cover it is the
triangle inequality, and it is what the fidelity of each region delivers by
itself. The bound is attained (`Examples/ContentCover.lean` §37). -/
theorem decode_compatible {θ : ℝ} {s : S} (hs : s ∈ D.relevant) :
    LocalContent.Compatible (D.domain θ) (fun i v => D.decode i v s) (2 * θ) := by
  intro i j v hi hj
  have h1 := hi s hs
  have h2 := hj s hs
  rw [Real.norm_eq_abs]
  calc |D.decode i v s - D.decode j v s|
      = |(D.decode i v s - D.value v s) - (D.decode j v s - D.value v s)| := by ring_nf
    _ ≤ |D.decode i v s - D.value v s| + |D.decode j v s - D.value v s| := abs_sub _ _
    _ ≤ 2 * θ := by linarith

/-- **Selection recovers the content within `θ`.** Weights subordinate to the
decodability cover select, at each relevant state, a value within `θ` of every
variable's true value: sharper than the `2θ` compatibility gives. -/
theorem select_decode_near_value [Fintype ι] {θ : ℝ} {w : ι → V → ℝ≥0}
    (hw : ApproximateGluing.IsPartition (D.domain θ) w) {s : S} (hs : s ∈ D.relevant)
    (v : V) :
    |select w (fun i v => D.decode i v s) v - D.value v s| ≤ θ := by
  rw [← Real.norm_eq_abs]
  exact norm_select_sub_le hw v (D.value v s) fun j hj => by
    rw [Real.norm_eq_abs]; exact hj s hs

/-! ## The decoder class -/

/-- **An unrestricted decoder decodes everything a region carries.** If a
region's readout is injective on the relevant family, some decoder recovers
every variable exactly there. An unbounded decoder class therefore puts every
variable in the domain of every such region, and the cover becomes trivial. -/
theorem exists_exact_decoder_of_injOn (D : DecodingSetup S R V) {i : ι}
    (hinj : Set.InjOn (D.read i) D.relevant) (v : V) :
    ∃ d : R i → ℝ, ∀ s ∈ D.relevant, d (D.read i s) = D.value v s := by
  classical
  by_cases hne : D.relevant.Nonempty
  · have : Nonempty S := hne.to_subtype.map Subtype.val
    refine ⟨fun r => D.value v (Function.invFunOn (D.read i) D.relevant r), ?_⟩
    intro s hs
    simp only
    rw [hinj.leftInvOn_invFunOn hs]
  · exact ⟨fun _ => 0, fun s hs => absurd ⟨s, hs⟩ hne⟩

/-- **A region cannot decode what it cannot see.** If region `i` reads two
relevant states identically and variable `v` differs between them by more than
`2θ`, then `v` is outside `i`'s domain, whichever decoder is used. -/
theorem not_decodes_of_read_eq {θ : ℝ} {i : ι} {v : V} {s t : S}
    (hs : s ∈ D.relevant) (ht : t ∈ D.relevant) (hread : D.read i s = D.read i t)
    (hsep : 2 * θ < |D.value v s - D.value v t|) :
    v ∉ D.domain θ i := by
  intro hv
  have h1 := hv s hs
  have h2 := hv t ht
  have heq : D.decode i v s = D.decode i v t := by simp only [decode, hread]
  rw [heq] at h1
  have := abs_sub (D.decode i v t - D.value v s) (D.decode i v t - D.value v t)
  have hre : D.value v s - D.value v t =
      -((D.decode i v t - D.value v s) - (D.decode i v t - D.value v t)) := by ring
  rw [hre, abs_neg] at hsep
  linarith

end DecodingSetup

/-! ## Exact gluing on the content base

Give `V` the discrete topology. Every set of variables is then open, a region's
domain is an open set, and a section over it is a real function on it. That is
Mathlib's `presheafToTypes`, a sheaf by `TopCat.Presheaf.toTypes_isSheaf`, so
`sheaf_glue_unique` applies as it does to the spatial cover. -/

section Sheaf

variable {S : Type} {ι : Type} {R : ι → Type} {V : Type} [TopologicalSpace V] [DiscreteTopology V]

/-- The content base: the variables, with every set of them open. -/
abbrev contentBase (V : Type) [TopologicalSpace V] : TopCat := TopCat.of V

/-- The presheaf of real values on sets of content variables; restriction
forgets variables. -/
noncomputable abbrev contentPresheaf (V : Type) [TopologicalSpace V] :=
  TopCat.presheafToTypes (contentBase V) (fun _ => ℝ)

/-- A region's domain, as an open set of the content base. -/
def domainOpen (D : DecodingSetup S R V) (θ : ℝ) (i : ι) : Opens (contentBase V) :=
  ⟨D.domain θ i, isOpen_discrete _⟩

/-- Region `i`'s decodes at state `s`, as a section over its domain. -/
def regionSection (D : DecodingSetup S R V) (θ : ℝ) (s : S) (i : ι) :
    (contentPresheaf V).obj (op (domainOpen D θ i)) :=
  fun v => D.decode i v.1 s

/-- **Gluing uniqueness on the decodability cover.** If every variable is decoded
by some region and the regions' decodes agree exactly where their domains
overlap, there is exactly one assignment of values to all variables restricting
to every region's decodes. It is `sheaf_glue_unique`, the theorem the spatial
cover uses, applied to the content base. -/
theorem decode_glue_unique (D : DecodingSetup S R V) {θ : ℝ} {s : S}
    (hcov : iSup (domainOpen D θ) = ⊤)
    (hexact : ∀ i j v, v ∈ D.domain θ i → v ∈ D.domain θ j →
      D.decode i v s = D.decode j v s) :
    ∃! g : (contentPresheaf V).obj (op ⊤),
      ∀ i, (contentPresheaf V).map (homOfLE (le_top : domainOpen D θ i ≤ ⊤)).op g =
        regionSection D θ s i :=
  sheaf_glue_unique (TopCat.Presheaf.toTypes_isSheaf _ _) (domainOpen D θ) hcov
    (regionSection D θ s) fun i j => by
      funext x
      exact hexact i j x.1 x.2.1 x.2.2

/-- **At tolerance zero the glued section is the content.** Exact decoders agree
on every overlap automatically, and any section restricting to every region's
decodes is the true value of every variable. -/
theorem decode_glue_value (D : DecodingSetup S R V) {s : S} (hs : s ∈ D.relevant)
    (hcov : iSup (domainOpen D 0) = ⊤) (g : (contentPresheaf V).obj (op ⊤))
    (hg : ∀ i, (contentPresheaf V).map (homOfLE (le_top : domainOpen D 0 i ≤ ⊤)).op g =
      regionSection D 0 s i) :
    g = fun v => D.value v.1 s := by
  have hval : ∀ i v, v ∈ D.domain 0 i → D.decode i v s = D.value v s := fun i v hv => by
    have h := hv s hs
    rwa [abs_nonpos_iff, sub_eq_zero] at h
  obtain ⟨g0, -, huniq⟩ := decode_glue_unique D hcov fun i j v hi hj => by
    rw [hval i v hi, hval j v hj]
  rw [huniq g hg, huniq (fun v => D.value v.1 s) fun i => by
    funext x
    exact (hval i x.1 x.2).symm]

end Sheaf

end PhysicsOfConsciousness.ContentCover
