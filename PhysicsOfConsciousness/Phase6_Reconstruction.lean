import PhysicsOfConsciousness.Phase6_ReflexiveTopology

/-!
# Bounded-error self-reconstruction and the codes it needs

The manuscript's functional-sensitivity requirement says that a Self must be
*sensitive* to the states it is a self of: a candidate implementation that
encodes two relevant states the same way cannot reconstruct both. This module
makes that quantitative and elementary.

The data is an `Encoding`: a declared family of relevant macrostates, an encoder
`E` into an alphabet of codes, and a readout `R` back into the state space. The
property is `Reconstructs ε`: every relevant state is recovered to within `ε` in
the declared metric. Two theorems follow, and both are triangle inequalities.

* **Indistinguishable states split the error.** If `E s = E t` then
  `d s t ≤ error s + error t`, so at least one of the two reconstructions is off
  by `d s t / 2` (`half_dist_le_max_error`). Applied to `ReflexiveBoundary` —
  `E = auto_resonance`, `R = readout`, so `R (E s)` is literally `predict s` —
  this constrains the self-prediction map the development already has
  (`ReflexiveBoundary.dist_le_prediction_residuals`).
* **Distinguishable states need distinct codes.** A finite family of `M`
  relevant states that are pairwise more than `2ε` apart is encoded injectively,
  so `M ≤` the number of codes, and an alphabet of at most `2 ^ b` values forces
  `M ≤ 2 ^ b` (`card_le_two_pow`).

## When the code is supposed to be a restriction

The reflexive boundary asks a second question of the same data: whether the code
the avatar writes *is* the field's own restriction to the avatar region
(`IsRestrictionResonance`). `Resonates` names that shape on bare maps, and the
two questions turn out to constrain each other. Accuracy forces the encoder to
separate states that are far apart, so under resonance it forces the *region* to
separate them — `restrictToAvatar` must be injective on any family of relevant
states pairwise more than `2 ε` apart. Where the region identifies two such
states, resonance and accuracy cannot both hold
(`not_isRestrictionResonance_of_reconstructs`).

This is a demand on the substrate rather than on the mechanism: which states a
region reads the same way is fixed before any encoding is chosen, so no read-out
repairs it. It runs one way — a region that does resolve the family is not
thereby resonant, and nothing here constructs an avatar.
`Phase6_Locality.lean` supplies the same failure with a deadline in place of a
tolerance.

## Scope

`b` counts *distinguishable codes*. Reading it as bits of physical memory, as a
channel capacity, or as information delivered before a deadline requires a
hardware model, and none is supplied here: the alphabet is a bare type. The
family of relevant macrostates, the metric on them, the tolerance and the
encoding region are all declared, and the bound says nothing about states
outside the declared family — in particular nothing about recovering every
microscopic configuration of the substrate.

This is an *additional operational criterion* on a candidate Self, not a
consequence of `Self` or `UnifiedSelf`. Nothing here asserts that a contraction
has several exact fixed points, and nothing here is in tension with a Self
existing: a constant readout has a unique fixed point and still fails the
criterion on any two separated relevant states (`not_reconstructs_of_const`),
which is the precise sense in which a fixed point is not a reconstruction.
-/

namespace PhysicsOfConsciousness.Reconstruction

/-! ## Resonance, as agreement with a declared reference

`ReflexiveBoundary.IsRestrictionResonance` says the avatar's code *is* the
field's own restriction to the avatar region. Written out it is agreement
between two maps out of the state space, and nothing in the argument below needs
either of them to be a presheaf restriction, so the shape is named here and the
instances supply the reference: `restrictToAvatar` at the end of this file, and a
reading region's state at a declared round in `Phase6_Locality`.

The point of the general form is what it makes checkable. `Resonates E ρ`
forces the two maps to *confuse the same pairs of states*, so a mismatch in
either direction refutes it, and a mismatch is a statement about which states
each map separates rather than about the values either one takes. That is how
resonance is refuted without ever evaluating the encoder. -/

/-- The encoder writes what the reference reports. -/
def Resonates {S C : Type*} (E ρ : S → C) : Prop := ∀ s, E s = ρ s

/-- Under resonance the encoder and the reference confuse the same pairs. Both
failure criteria below are this equivalence read backwards. -/
theorem eq_iff_of_resonates {S C : Type*} {E ρ : S → C} (h : Resonates E ρ) (s t : S) :
    E s = E t ↔ ρ s = ρ t := by rw [h s, h t]

/-- **A code blind where the reference is not.** Two states the encoder gives the
same code and the reference separates refute resonance. No metric, no accuracy
requirement and no property of the readout: the hypothesis is that the encoding
region distinguishes a pair the code does not. -/
theorem not_resonates_of_confuses {S C : Type*} {E ρ : S → C} {s t : S}
    (hE : E s = E t) (hrho : ρ s ≠ ρ t) : ¬ Resonates E ρ :=
  fun h => hrho (((h s).symm.trans hE).trans (h t))

/-- **A code that splits what the reference cannot.** The mirror image, and the
half that carries the reconstruction argument: accuracy forces the encoder to
separate states the reference may be too coarse to tell apart. -/
theorem not_resonates_of_splits {S C : Type*} {E ρ : S → C} {s t : S}
    (hE : E s ≠ E t) (hrho : ρ s = ρ t) : ¬ Resonates E ρ :=
  fun h => hE (((h s).trans hrho).trans (h t).symm)

variable {S C : Type*} [PseudoMetricSpace S]

/-! ## The bound, on bare maps

The encoder and readout are the only data these two theorems use, so they are
stated on functions rather than on the structure below. -/

/-- **Two states with one code share their reconstruction error.** The readout
sees a single code, so the one state it lands near is the one the other state is
far from. -/
theorem dist_le_add_error (E : S → C) (R : C → S) {s t : S} (h : E s = E t) :
    dist s t ≤ dist s (R (E s)) + dist t (R (E t)) := by
  calc dist s t ≤ dist s (R (E s)) + dist (R (E s)) t := dist_triangle _ _ _
    _ = dist s (R (E s)) + dist t (R (E t)) := by rw [h, dist_comm (R (E t)) t]

/-- **At least one reconstruction is off by half the separation.** The
quantitative form of functional sensitivity: an implementation that cannot tell
`s` from `t` pays `d s t / 2` on one of them, whatever its readout does. -/
theorem half_dist_le_max_error (E : S → C) (R : C → S) {s t : S} (h : E s = E t) :
    dist s t / 2 ≤ max (dist s (R (E s))) (dist t (R (E t))) := by
  have h1 := dist_le_add_error E R h
  have h2 := le_max_left (dist s (R (E s))) (dist t (R (E t)))
  have h3 := le_max_right (dist s (R (E s))) (dist t (R (E t)))
  linarith

/-- Separated states that are both reconstructed accurately must carry different
codes. This is the contrapositive of the previous theorem and the step the
counting argument uses. -/
theorem encode_ne_of_separated (E : S → C) (R : C → S) {s t : S} {ε : ℝ}
    (hs : dist s (R (E s)) ≤ ε) (ht : dist t (R (E t)) ≤ ε) (hsep : 2 * ε < dist s t) :
    E s ≠ E t := by
  intro h
  have := dist_le_add_error E R h
  linarith

/-! ## The declared data and its property

Per `PhysicsOfConsciousness/AGENTS.md` §3 the structure is bare data — which
states are relevant, how they are encoded, how they are read back — and accuracy
is the separate predicate `Reconstructs`. -/

/-- A candidate reconstruction mechanism: a declared family of relevant
macrostates, an encoder into an alphabet of codes, and a readout. Nothing here
asserts that the readout is any good; that is `Reconstructs`. -/
structure Encoding (S C : Type*) [PseudoMetricSpace S] where
  /-- The macrostates the criterion is about. States outside it are unconstrained. -/
  relevant : Set S
  /-- The encoder. Its codomain is the alphabet whose size the capacity bound counts. -/
  encode : S → C
  /-- The readout, reconstructing a state from a code alone. -/
  readout : C → S

namespace Encoding

variable (Enc : Encoding S C)

/-- The reconstruction error at a state: how far the state is from what its own
code reconstructs. -/
def error (s : S) : ℝ := dist s (Enc.readout (Enc.encode s))

/-- Bounded-error reconstruction at tolerance `ε`, on the declared family only. -/
def Reconstructs (ε : ℝ) : Prop := ∀ s ∈ Enc.relevant, Enc.error s ≤ ε

variable {Enc}

/-- The bound, in the structure's language. -/
theorem dist_le_add_error_of_encode_eq {s t : S} (h : Enc.encode s = Enc.encode t) :
    dist s t ≤ Enc.error s + Enc.error t :=
  dist_le_add_error Enc.encode Enc.readout h

/-- **Separated relevant states are distinguished.** Accuracy better than half
the separation forces the encoder to separate them too. -/
theorem encode_injOn_of_separated {ε : ℝ} (hrec : Enc.Reconstructs ε)
    {F : Set S} (hF : F ⊆ Enc.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    Set.InjOn Enc.encode F := by
  intro s hs t ht hcode
  by_contra hne
  exact encode_ne_of_separated Enc.encode Enc.readout (hrec s (hF hs)) (hrec t (hF ht))
    (hsep s hs t ht hne) hcode

/-- **The capacity bound.** A finite family of relevant macrostates, pairwise
more than `2ε` apart and all reconstructed to within `ε`, is no larger than the
alphabet of codes.

The count is of *distinguishable codes*: `C` is a bare type and no physical
memory, channel or deadline is modelled. -/
theorem card_le_card_codes [Fintype C] [DecidableEq S] {ε : ℝ}
    (hrec : Enc.Reconstructs ε) {F : Finset S} (hF : ↑F ⊆ Enc.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    F.card ≤ Fintype.card C :=
  Finset.card_le_card_of_injOn Enc.encode (fun _ _ => Finset.mem_univ _)
    (encode_injOn_of_separated hrec hF (fun s hs t ht => hsep s hs t ht))

/-- **`M ≤ 2 ^ b`.** With an alphabet of at most `2 ^ b` codes, at most `2 ^ b`
pairwise-separated macrostates are reconstructed to within `ε`. Reading `b` as a
number of physical bits is a separate hardware identification and is not made
here. -/
theorem card_le_two_pow [Fintype C] [DecidableEq S] {ε : ℝ} {b : ℕ}
    (hb : Fintype.card C ≤ 2 ^ b) (hrec : Enc.Reconstructs ε) {F : Finset S}
    (hF : ↑F ⊆ Enc.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    F.card ≤ 2 ^ b :=
  (card_le_card_codes hrec hF hsep).trans hb

/-! ### Accuracy against a coarse reference

The two questions this file asks of the same data — does the mechanism *recover*
the declared macrostates, and is its code the state's own restriction — are not
independent. Accuracy forces the encoder to separate states that are far apart,
so it forces the reference to separate them too. A reference that cannot is a
region too coarse for the family, and the two demands are then incompatible
whatever the readout does. -/

/-- **A reference too coarse for the family the mechanism must resolve.**
Reconstructing two relevant states more than `2 * ε` apart makes their codes
differ, so a reference map that identifies them is not the code the encoder
writes.

Which of the two hypotheses is the substrate's is the content: `hrho` is a
property of the reference alone — on a reflexive boundary, of the avatar region —
and it is refutable by exhibiting two macrostates the region reads the same way. -/
theorem not_resonates_of_reconstructs {ρ : S → C} {ε : ℝ} {s t : S}
    (hrec : Enc.Reconstructs ε) (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant)
    (hsep : 2 * ε < dist s t) (hrho : ρ s = ρ t) :
    ¬ Resonates Enc.encode ρ :=
  not_resonates_of_splits
    (encode_ne_of_separated Enc.encode Enc.readout (hrec s hs) (hrec t ht) hsep) hrho

/-- **What resonance costs the reference.** Read forwards rather than as a
refutation: a resonant mechanism that reconstructs a pairwise-separated family
has a reference map that is injective on it. The resolution demanded is the
*reference's*, not the readout's — for a reflexive boundary, a property of the
avatar region and the substrate, fixed before any encoding is chosen. -/
theorem injOn_of_resonates {ρ : S → C} {ε : ℝ}
    (hres : Resonates Enc.encode ρ) (hrec : Enc.Reconstructs ε)
    {F : Set S} (hF : F ⊆ Enc.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    Set.InjOn ρ F := by
  intro s hs t ht hst
  refine encode_injOn_of_separated hrec hF hsep hs ht ?_
  rw [hres s, hres t]
  exact hst

/-- **A mechanism whose answer does not move reconstructs at most one of two
separated states.** The hypothesis is on the composite: whatever the readout
returns is the same state for every relevant input, so the criterion fails as
soon as the family contains two states more than `2ε` apart.

Both degenerate mechanisms are instances. A constant *encoder* is blind because
it discards the state before the readout sees it (`not_reconstructs_of_const`);
a constant *readout* is blind because it discards the code. -/
theorem not_reconstructs_of_blind {r : S} (hblind : ∀ s, Enc.readout (Enc.encode s) = r)
    {ε : ℝ} {s t : S} (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant)
    (hsep : 2 * ε < dist s t) : ¬ Enc.Reconstructs ε := by
  intro hrec
  have h1 : Enc.error s ≤ ε := hrec s hs
  have h2 : Enc.error t ≤ ε := hrec t ht
  rw [error, hblind s] at h1
  rw [error, hblind t] at h2
  have := dist_triangle s r t
  rw [dist_comm r t] at this
  linarith

/-- **A blind encoder reconstructs at most one of two separated states.** The
encoder is constant, so every relevant state is read back as the same state and
the criterion fails as soon as the family contains two states more than `2ε`
apart.

This is the fixed-point/reconstruction distinction in one statement: the
constant map `fun _ => Enc.readout c` has a unique fixed point, and that fact is
consistent with this failure, because a fixed point is a claim about one state
and reconstruction is a claim about the declared family. -/
theorem not_reconstructs_of_const {c : C} (hconst : ∀ s, Enc.encode s = c) {ε : ℝ}
    {s t : S} (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant)
    (hsep : 2 * ε < dist s t) : ¬ Enc.Reconstructs ε :=
  not_reconstructs_of_blind (r := Enc.readout c) (fun s => by rw [hconst s]) hs ht hsep

/-- A readout that ignores its code is blind in the same sense. This is the
shape a "report" that does not track what it reports has. -/
theorem not_reconstructs_of_const_readout {r : S} (hconst : ∀ c, Enc.readout c = r)
    {ε : ℝ} {s t : S} (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant)
    (hsep : 2 * ε < dist s t) : ¬ Enc.Reconstructs ε :=
  not_reconstructs_of_blind (fun s => hconst (Enc.encode s)) hs ht hsep

end Encoding

end PhysicsOfConsciousness.Reconstruction

open CategoryTheory TopologicalSpace MeasureTheory
open Opposite

namespace PhysicsOfConsciousness
namespace ReflexiveBoundary

open PhysicsOfConsciousness.Reconstruction

universe u

variable {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X]

/-- The reflexive boundary read as a reconstruction mechanism: the avatar's write
is the encoder, the avatar's read-out is the readout, and the alphabet of codes
is the sections over the avatar region. The declared family of relevant
macrostates is an input — the criterion is about the states the implementation
is supposed to be sensitive to, and the structure names none. -/
def encoding [MetricSpace (GlobalSection (X := X))] (rb : ReflexiveBoundary X)
    (relevant : Set (GlobalSection (X := X))) :
    Encoding (GlobalSection (X := X)) ((probabilityPresheaf X).obj (op rb.avatar_region)) where
  relevant := relevant
  encode := rb.auto_resonance
  readout := rb.readout

/-- The reconstruction error of that encoding *is* the self-prediction residual,
because `predict` is the composite of the two maps. -/
@[simp]
theorem encoding_error [MetricSpace (GlobalSection (X := X))] (rb : ReflexiveBoundary X)
    (relevant : Set (GlobalSection (X := X))) (s : GlobalSection (X := X)) :
    (rb.encoding relevant).error s = dist s (rb.predict s) := rfl

/-- **The bound, on the development's own self-prediction map.** Two global
states whose avatars carry the same encoding are no further apart than the sum
of their self-prediction residuals. A boundary whose avatar cannot separate two
states therefore mispredicts at least one of them by half their distance.

The hypothesis is about `auto_resonance` alone; no restriction resonance,
contraction or completeness is used, and no fixed point is claimed or needed. -/
theorem dist_le_prediction_residuals [MetricSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X) {s t : GlobalSection (X := X)}
    (h : rb.auto_resonance s = rb.auto_resonance t) :
    dist s t ≤ dist s (rb.predict s) + dist t (rb.predict t) :=
  dist_le_add_error rb.auto_resonance rb.readout h

/-- At least one of the two residuals is half the separation. -/
theorem half_dist_le_max_prediction_residual [MetricSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X) {s t : GlobalSection (X := X)}
    (h : rb.auto_resonance s = rb.auto_resonance t) :
    dist s t / 2 ≤ max (dist s (rb.predict s)) (dist t (rb.predict t)) :=
  half_dist_le_max_error rb.auto_resonance rb.readout h

/-- **A blinded avatar fails the criterion on any two separated states**, however
its read-out is chosen and whatever the field does. `constResonance_existsUnique_self`
gives that same boundary a unique Self; the two statements are about different
things, and this is the one the manuscript's sensitivity requirement asks for. -/
theorem blinded_not_reconstructs [MetricSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X)
    (a₀ : (probabilityPresheaf X).obj (op rb.avatar_region))
    (relevant : Set (GlobalSection (X := X))) {ε : ℝ}
    {s t : GlobalSection (X := X)} (hs : s ∈ relevant) (ht : t ∈ relevant)
    (hsep : 2 * ε < dist s t) :
    ¬ ((rb.constResonance a₀).encoding relevant).Reconstructs ε :=
  Encoding.not_reconstructs_of_const (c := a₀) (fun _ => rfl) hs ht hsep

/-! ### When restriction resonance fails

`IsRestrictionResonance` is `Resonates` for the two maps the boundary already
carries, so the criteria above apply to it verbatim. What they add to
`constResonance_not_isRestrictionResonance` is generality in two directions.
That theorem refutes resonance for a boundary *built* by blinding another one;
these refute it for any boundary at all, from a property of the avatar region
that a substrate either has or does not.

The second direction is the one E89 feels. E89 asks for a contraction with a
declared fixed point, and Banach supplies uniqueness; neither says the avatar
region resolves the states the self-model is supposed to be about. Under
resonance, accuracy on a separated family forces `restrictToAvatar` itself to be
injective there (`restrictToAvatar_injOn_of_isRestrictionResonance`), which is a
demand on the region and the substrate rather than on the readout, and is fixed
before any avatar is chosen. Where the region fails it, resonance and accuracy
cannot both hold (`not_isRestrictionResonance_of_reconstructs`): a boundary on
that region either misses states it must distinguish or reports something other
than what the region holds. The bound runs one way — nothing here says a region
that does resolve the family carries a resonant avatar, or that one exists. -/

/-- Restriction resonance is resonance of the avatar's write against the
region's own restriction. Definitional; it is stated so that the criteria proved
for bare maps are visibly criteria about this predicate. -/
theorem isRestrictionResonance_iff_resonates (rb : ReflexiveBoundary X) :
    rb.IsRestrictionResonance ↔ Resonates rb.auto_resonance rb.restrictToAvatar := Iff.rfl

/-- **An avatar blind where its region is not.** Two field states the avatar
encodes identically and the avatar region separates refute resonance. No metric
and no fixed point are involved. -/
theorem not_isRestrictionResonance_of_avatar_confuses (rb : ReflexiveBoundary X)
    {s t : GlobalSection (X := X)}
    (hauto : rb.auto_resonance s = rb.auto_resonance t)
    (hrestrict : rb.restrictToAvatar s ≠ rb.restrictToAvatar t) :
    ¬ rb.IsRestrictionResonance :=
  not_resonates_of_confuses hauto hrestrict

/-- **An avatar that separates what its region cannot.** The mirror image: an
avatar reporting a difference the field does not carry on the avatar region is
reporting something other than the field. -/
theorem not_isRestrictionResonance_of_region_blind (rb : ReflexiveBoundary X)
    {s t : GlobalSection (X := X)}
    (hauto : rb.auto_resonance s ≠ rb.auto_resonance t)
    (hrestrict : rb.restrictToAvatar s = rb.restrictToAvatar t) :
    ¬ rb.IsRestrictionResonance :=
  not_resonates_of_splits hauto hrestrict

/-- **A constant avatar on any boundary.** `constResonance_not_isRestrictionResonance`
is this for the boundary `constResonance` builds; the hypothesis here is that the
write happens to be constant, however the boundary was arrived at. -/
theorem not_isRestrictionResonance_of_const_avatar (rb : ReflexiveBoundary X)
    {a₀ : (probabilityPresheaf X).obj (op rb.avatar_region)}
    (hconst : ∀ s, rb.auto_resonance s = a₀)
    {s t : GlobalSection (X := X)}
    (hrestrict : rb.restrictToAvatar s ≠ rb.restrictToAvatar t) :
    ¬ rb.IsRestrictionResonance :=
  not_isRestrictionResonance_of_avatar_confuses rb ((hconst s).trans (hconst t).symm) hrestrict

/-- **A region too coarse for the states the boundary must resolve.** If the
boundary reconstructs two relevant field states more than `2 * ε` apart, and the
avatar region reads them the same way, it is not resonant.

This is the criterion a substrate decides. `hrestrict` mentions neither the
avatar's write nor its read-out: it says the region holds the same section in
two states the mechanism is required to tell apart, which is a fact about where
the region sits. Accuracy is then incompatible with the avatar reporting what
the region holds. -/
theorem not_isRestrictionResonance_of_reconstructs [MetricSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X) (relevant : Set (GlobalSection (X := X))) {ε : ℝ}
    {s t : GlobalSection (X := X)}
    (hrec : (rb.encoding relevant).Reconstructs ε)
    (hs : s ∈ relevant) (ht : t ∈ relevant) (hsep : 2 * ε < dist s t)
    (hrestrict : rb.restrictToAvatar s = rb.restrictToAvatar t) :
    ¬ rb.IsRestrictionResonance :=
  Encoding.not_resonates_of_reconstructs (Enc := rb.encoding relevant) hrec hs ht hsep hrestrict

/-- **What a resonant boundary demands of its region.** The same statement read
forwards: under resonance, reconstructing a pairwise-separated family at
tolerance `ε` forces the region's restriction map to be injective on that family.

E89 supplies a Lipschitz law and a fixed point, and this is what it does not
supply: the resolution is the avatar region's, and a region that identifies two
relevant macrostates cannot be made to work by any choice of encoding or
read-out. The converse fails — a region resolving the family need carry no
resonant avatar. -/
theorem restrictToAvatar_injOn_of_isRestrictionResonance
    [MetricSpace (GlobalSection (X := X))] (rb : ReflexiveBoundary X)
    (relevant : Set (GlobalSection (X := X))) {ε : ℝ}
    (hres : rb.IsRestrictionResonance)
    (hrec : (rb.encoding relevant).Reconstructs ε)
    {F : Set (GlobalSection (X := X))} (hF : F ⊆ relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    Set.InjOn rb.restrictToAvatar F :=
  Encoding.injOn_of_resonates (Enc := rb.encoding relevant) hres hrec hF hsep

#print axioms Reconstruction.dist_le_add_error
#print axioms Reconstruction.half_dist_le_max_error
#print axioms Reconstruction.Encoding.encode_injOn_of_separated
#print axioms Reconstruction.Encoding.card_le_card_codes
#print axioms Reconstruction.Encoding.card_le_two_pow
#print axioms Reconstruction.Encoding.not_reconstructs_of_blind
#print axioms Reconstruction.Encoding.not_reconstructs_of_const
#print axioms Reconstruction.Encoding.not_reconstructs_of_const_readout
#print axioms dist_le_prediction_residuals
#print axioms half_dist_le_max_prediction_residual
#print axioms blinded_not_reconstructs
#print axioms Reconstruction.not_resonates_of_confuses
#print axioms Reconstruction.not_resonates_of_splits
#print axioms Reconstruction.Encoding.not_resonates_of_reconstructs
#print axioms Reconstruction.Encoding.injOn_of_resonates
#print axioms not_isRestrictionResonance_of_avatar_confuses
#print axioms not_isRestrictionResonance_of_region_blind
#print axioms not_isRestrictionResonance_of_const_avatar
#print axioms not_isRestrictionResonance_of_reconstructs
#print axioms restrictToAvatar_injOn_of_isRestrictionResonance

end ReflexiveBoundary
end PhysicsOfConsciousness
