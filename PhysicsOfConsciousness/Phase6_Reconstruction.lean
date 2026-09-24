import PhysicsOfConsciousness.Phase6_ReflexiveTopology
import PhysicsOfConsciousness.Phase6_AttentionRank
import PhysicsOfConsciousness.Phase3_FiniteInformation
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

## The floor on the code space

The bound above is a ceiling. `measure_le_mul_packingNumber` is the matching
floor: give the code space a measure, and a region of measure `μ A` whose
`δ`-balls each measure at most `v` packs at least `μ A / v` separated codes. On
a finite-dimensional real space with a Haar measure that reads as volume over
`δ^d` (`measure_le_pow_mul_packingNumber`), which is what makes "a continuum
code space is large" a quantity rather than a gesture. Both bounds are about the
code space alone, and the gain `L` in the ceiling is still declared.

## When the alphabet is a vocabulary

`C` is a bare type, and one deployed architecture makes it concrete. Everything a
model carries about its own internal condition from one autoregressive step to
the next passes through the tokens it emits: the next step recomputes its
activations from the token sequence, so whatever a forward pass held about itself
reaches the following step only as what was sampled. `tokenChannel` is that
channel and `card_le_card_tokens` is the count it has —
`|vocab| ^ k` codes over `k` steps, which is the honest bound and a large one. It
bites on a *single-step* self-report claim (`card_le_card_tokens_one`) and not on
an extended one, and it is a fact about the architecture as deployed rather than
about digital computation.

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

open scoped ENNReal NNReal

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

/-- A single contracting reconstruction map can be accurate only on a small
family. This is a restriction on a fixed map; it does not apply when the readout
is conditioned on an external input. -/
theorem dist_le_of_contracting_reconstructs {q : ℝ≥0} (hq : q < 1) {ε : ℝ}
    (hmap : LipschitzWith q (fun s => Enc.readout (Enc.encode s)))
    (hrec : Enc.Reconstructs ε) {s t : S}
    (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant) :
    dist s t ≤ 2 * ε / (1 - (q : ℝ)) := by
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast hq
  have hsplit : dist s t ≤ Enc.error s +
      dist (Enc.readout (Enc.encode s)) (Enc.readout (Enc.encode t)) + Enc.error t := by
    calc
      dist s t ≤ dist s (Enc.readout (Enc.encode s)) +
          dist (Enc.readout (Enc.encode s)) t := dist_triangle _ _ _
      _ ≤ dist s (Enc.readout (Enc.encode s)) +
          (dist (Enc.readout (Enc.encode s)) (Enc.readout (Enc.encode t)) +
            dist (Enc.readout (Enc.encode t)) t) := by
            gcongr
            exact dist_triangle _ _ _
      _ = _ := by simp only [Encoding.error, dist_comm t]; ring
  apply (le_div_iff₀ (sub_pos.mpr hq1)).2
  have hsε := hrec s hs
  have htε := hrec t ht
  have hlip := hmap.dist_le_mul s t
  dsimp [Encoding.error] at hsε htε
  dsimp [Encoding.error] at hsplit
  nlinarith


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

/-! ### The report channel: when the alphabet is a vocabulary

The bound above counts codes in an alphabet nothing has named. Name it the
vocabulary a model samples from, and the counting argument becomes a statement
about a self-report: the code is the token sequence emitted, because that is
what the next autoregressive step reads.

The bound is `|vocab| ^ k` over `k` steps and it is deliberately not dressed up.
It is large, so it constrains a single-step claim and says nothing restrictive
about an extended report. It counts codes and not bits: `Fintype.card T` is a
cardinality, and nothing here prices a token or a channel.
`Examples/Reconstruction.lean` §24 exhibits the counting half biting, with three
separated states and one bit (`no_bit_reconstruction`).

What it does not reach. It is not about digital computation, or about what a
model can compute — it counts the codes of one declared channel. It says nothing
about what a single forward pass can read, which is the causal-mask statement of
`Examples/Locality.lean` §31. And a claim resting on activations rather than on
text has declared a *different* encoding: the bound then applies to that one,
with that one's alphabet, which may be the machine's whole state. Which channel
a self-report claim is about is the claim's to declare, and this module does not
declare it. -/

/-- A self-report channel: the code is the token sequence the candidate emits
over `k` steps, and the readout is whatever reconstruction the claim attributes
to it. Data only, as `Encoding` is — that the readout is any good is
`Reconstructs`, and which channel carries the claim is declared, not derived. -/
def tokenChannel {T : Type*} (k : ℕ) (relevant : Set S) (emit : S → Fin k → T)
    (decode : (Fin k → T) → S) : Encoding S (Fin k → T) where
  relevant := relevant
  encode := emit
  readout := decode

/-- **A report of `k` tokens carries `|vocab| ^ k` codes.** `card_le_card_codes`
with the alphabet spelled as a sequence of vocabulary members: a family of
relevant states pairwise more than `2ε` apart, all reconstructed to within `ε`
from the emitted sequence alone, is no larger than `|vocab| ^ k`.

The hypotheses carry the content and all of it is declared: which states the
claim is about, the metric separating them, the tolerance, and that the emitted
sequence is the code. Nothing here says a model has only this channel; it says
what *this* channel counts. -/
theorem card_le_card_tokens {T : Type*} [Fintype T] {k : ℕ} [DecidableEq S]
    {Ch : Encoding S (Fin k → T)} {ε : ℝ} (hrec : Ch.Reconstructs ε) {F : Finset S}
    (hF : ↑F ⊆ Ch.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    F.card ≤ Fintype.card T ^ k := by
  have h := card_le_card_codes hrec hF hsep
  rwa [Fintype.card_fun, Fintype.card_fin] at h

/-- The same bound on the channel as named, which is the form a claim about a
model's own reports instantiates. -/
theorem card_le_card_tokens_channel {T : Type*} [Fintype T] {k : ℕ} [DecidableEq S]
    {relevant : Set S} {emit : S → Fin k → T} {decode : (Fin k → T) → S} {ε : ℝ}
    (hrec : (tokenChannel k relevant emit decode).Reconstructs ε) {F : Finset S}
    (hF : ↑F ⊆ relevant) (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    F.card ≤ Fintype.card T ^ k :=
  card_le_card_tokens hrec hF hsep

/-- **One step is one token.** Where the bound bites: a single-step self-report
distinguishes at most `|vocab|` states of the thing reporting, however large that
thing is. Over `k` steps the alphabet is `|vocab| ^ k` and this is no constraint
worth stating, which is why the single-step case is the one named. -/
theorem card_le_card_tokens_one {T : Type*} [Fintype T] [DecidableEq S]
    {Ch : Encoding S (Fin 1 → T)} {ε : ℝ} (hrec : Ch.Reconstructs ε) {F : Finset S}
    (hF : ↑F ⊆ Ch.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    F.card ≤ Fintype.card T := by
  have h := card_le_card_tokens hrec hF hsep
  rwa [pow_one] at h

/-- **A family too large for the channel is not reconstructed by it.** The
contrapositive, and the usable form: counting the declared family against
`|vocab| ^ k` refutes the accuracy claim without evaluating any readout. -/
theorem not_reconstructs_of_card_tokens_lt {T : Type*} [Fintype T] {k : ℕ}
    [DecidableEq S] {Ch : Encoding S (Fin k → T)} {ε : ℝ} {F : Finset S}
    (hF : ↑F ⊆ Ch.relevant) (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t)
    (hcard : Fintype.card T ^ k < F.card) : ¬ Ch.Reconstructs ε :=
  fun hrec => absurd (card_le_card_tokens hrec hF hsep) (not_le_of_gt hcard)

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

/-! ### From an alphabet to a metric: the packing form

`card_le_two_pow` counts an alphabet, and a continuous family of macrostates has
no alphabet to count. The generalization keeps the argument and replaces the
counting: put a metric on the codes, ask the readout to have bounded gain, and
the triangle inequality that forced *distinct* codes forces *separated* ones.

The gain is where the physics enters. A readout with Lipschitz constant `L`
moves its outputs at most `L` times as far as its inputs, so two states more
than `r` apart, each reconstructed to within `ε`, have codes more than
`(r - 2 ε) / L` apart — the hypothesis is written `δ * L ≤ r - 2 ε` to keep the
division out of the statement. The declared family therefore realizes a packing
of the code space at that scale, and `Metric.packingNumber` of the codes the
encoder actually writes bounds the family above.

The finite case is the special case: an alphabet of `2 ^ b` values has packing
number at most `2 ^ b` at every scale, and the bound reads `M ≤ 2 ^ b` again.
What is new is that the code space may be continuous, which is what a region of
a cortical sheet carrying a field value is.

`L` is declared, like everything else here. Nothing in this module derives a
gain for a physical readout, and a mechanism free to amplify without bound —
`L` arbitrarily large — is subject to no constraint from this theorem, which is
the honest reading of an uncalibrated decoder. -/

section Packing

variable [PseudoMetricSpace C]

/-- **Reconstruction error is what separation must overcome.** The distance
between two relevant states, less the two reconstruction errors, is carried by
the readout, which moves its outputs at most `L` times as far as its inputs. -/
theorem sub_two_mul_le_lipschitz_mul {L : ℝ≥0} {ε : ℝ} (hL : LipschitzWith L Enc.readout)
    (hrec : Enc.Reconstructs ε) {s t : S} (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant) :
    dist s t - 2 * ε ≤ L * dist (Enc.encode s) (Enc.encode t) := by
  have h1 : Enc.error s ≤ ε := hrec s hs
  have h2 : Enc.error t ≤ ε := hrec t ht
  rw [error] at h1 h2
  have htri : dist s t ≤ dist s (Enc.readout (Enc.encode s))
      + dist (Enc.readout (Enc.encode s)) (Enc.readout (Enc.encode t))
      + dist (Enc.readout (Enc.encode t)) t := dist_triangle4 s _ _ t
  have hlip : dist (Enc.readout (Enc.encode s)) (Enc.readout (Enc.encode t))
      ≤ L * dist (Enc.encode s) (Enc.encode t) := hL.dist_le_mul _ _
  rw [dist_comm (Enc.readout (Enc.encode t)) t] at htri
  linarith

/-- **The codes of a separated family are separated.** The metric form of
"distinguishable states need distinct codes": at gain `L` the codes of a family
pairwise more than `r` apart are pairwise more than `δ` apart, for any `δ` with
`δ * L ≤ r - 2 ε`.

A positive gain is required, and it is not a technicality: at `L = 0` the readout
is constant and `not_reconstructs_of_const_readout` says the family is not
reconstructed at all. -/
theorem isSeparated_image_encode {L δ : ℝ≥0} {ε r : ℝ} (hL : LipschitzWith L Enc.readout)
    (hL0 : 0 < L) (hrec : Enc.Reconstructs ε) {F : Set S} (hF : F ⊆ Enc.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → r < dist s t)
    (hδ : (δ : ℝ) * L ≤ r - 2 * ε) :
    Metric.IsSeparated (δ : ℝ≥0∞) (Enc.encode '' F) := by
  have hL' : (0 : ℝ) < L := hL0
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hne
  have hst : s ≠ t := fun h => hne (by rw [h])
  have hkey := sub_two_mul_le_lipschitz_mul hL hrec (hF hs) (hF ht)
  have hdist : (δ : ℝ) < dist (Enc.encode s) (Enc.encode t) := by
    have h1 : (L : ℝ) * (δ : ℝ) < (L : ℝ) * dist (Enc.encode s) (Enc.encode t) := by
      have := hsep s hs t ht hst
      nlinarith
    exact lt_of_mul_lt_mul_left h1 hL'.le
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg δ.coe_nonneg).mpr hdist

/-- **The packing bound.** The declared family is no larger than the packing
number, at scale `δ`, of the codes the encoder writes.

This is `card_le_card_codes` with the alphabet's size replaced by a packing
number, and it degenerates to it: a finite code space has packing number at most
its cardinality at every scale. The quantity on the right is a property of the
code space and the gain — for a reflexive boundary, of the avatar region and its
readout — so it is fixed before the family is declared. -/
theorem encard_le_packingNumber_range {L δ : ℝ≥0} {ε r : ℝ} (hL : LipschitzWith L Enc.readout)
    (hL0 : 0 < L) (hrec : Enc.Reconstructs ε) {F : Set S} (hF : F ⊆ Enc.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → r < dist s t)
    (hδ : (δ : ℝ) * L ≤ r - 2 * ε) :
    F.encard ≤ Metric.packingNumber δ (Set.range Enc.encode) := by
  have hL' : (0 : ℝ) < L := hL0
  have h2ε : 2 * ε ≤ r := by nlinarith [δ.coe_nonneg]
  have hinj : Set.InjOn Enc.encode F :=
    encode_injOn_of_separated hrec hF fun s hs t ht hne =>
      lt_of_le_of_lt h2ε (hsep s hs t ht hne)
  rw [← hinj.encard_image]
  exact Metric.IsSeparated.encard_le_packingNumber (Set.image_subset_range _ _)
    (isSeparated_image_encode hL hL0 hrec hF hsep hδ)

/-- The packing bound on a finite family, in the counting form the alphabet
version states. -/
theorem card_le_packingNumber_range {L δ : ℝ≥0} {ε r : ℝ} (hL : LipschitzWith L Enc.readout)
    (hL0 : 0 < L) (hrec : Enc.Reconstructs ε) {F : Finset S} (hF : ↑F ⊆ Enc.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → r < dist s t)
    (hδ : (δ : ℝ) * L ≤ r - 2 * ε) :
    (F.card : ℕ∞) ≤ Metric.packingNumber δ (Set.range Enc.encode) := by
  have h := encard_le_packingNumber_range hL hL0 hrec hF
    (fun s hs t ht hne => hsep s hs t ht hne) hδ
  rwa [Set.encard_coe_eq_coe_finsetCard] at h

end Packing

end Encoding

/-! ## The floor, to match the ceiling

`encard_le_packingNumber_range` bounds the declared family *above* by the
packing number of the codes the encoder writes. On its own that is a ceiling and
never a floor: it says what a code space cannot exceed and never that the code
space supplies anything. A continuous code space is therefore still a hand-wave
after it, because nothing has said how many `δ`-separated codes a continuum
actually holds.

This section supplies the other direction. Give the code space a measure. A
maximal `δ`-separated family is a `δ`-cover — that is what maximality means —
so the region it packs is covered by that many balls of radius `δ`, and its
measure is at most the number of them times the largest ball measure. Read
backwards, that is a floor: a region of measure `μ A` whose `δ`-balls each
measure at most `v` has packing number at least `μ A / v`, written
`μ A ≤ v * packingNumber δ A` to keep the division out of the statement.

`measure_le_pow_mul_packingNumber` is the quantity the manuscript's reading
wants. On a finite-dimensional real vector space with a Haar measure the ball
measure is `δ^d` times the unit ball's, so the floor grows as volume over
`δ^d` — resolution `δ` and dimension `d`, and nothing else. Against
`card_le_two_pow`, whose `b` is a declared alphabet size, this makes the
corresponding count a physical quantity: `δ` is the noise floor of the readout
and the volume is the region the code lives in.

**Scope, and it is not small.** The floor is about the *code space*, not about
any mechanism reaching it. It says a region of positive measure holds that many
mutually resolvable codes; it does not say an encoder writes them, that a
readout separates them, or that the states they would encode exist. Read with
`encard_le_packingNumber_range`, whose gain `L` is declared and uncalibrated: a
mechanism free to amplify without bound evacuates the ceiling, and no floor on
the code space repairs that. The two bounds meet only when `δ` is fixed by a
measured noise floor and `L` by a measured gain, and this module measures
neither.

Neither theorem needs the encoder, so both are stated on a bare metric measure
space; `Encoding.measure_le_mul_packingNumber_range` carries the first to the
codes an encoder writes, which is the only form the reconstruction argument
uses.

## The comparison the two bounds make possible

With a ceiling and a floor on one quantity, the continuum and the alphabet can
be counted in one currency — mutually resolvable codes — and compared at matched
resource. `two_pow_lt_packingNumber_of_lt_measure` is that comparison: a
continuum code space out-resolves a `b`-bit alphabet exactly when its measure
exceeds `2 ^ b` resolution cells, which on a finite-dimensional real space
(`two_pow_lt_packingNumber_of_lt_measure_haar`) reads as volume against
`2 ^ b · δ^d`. `Encoding.encard_le_two_pow_of_packingNumber_le` runs it the
other way: where the packing number is at most `2 ^ b`, the declared family is
capped at `2 ^ b` exactly as `card_le_two_pow` caps it for a declared alphabet.

**What the comparison returns is a criterion, not a verdict.** Which side wins
is decided by the measure, the resolution and the dimension — measured
quantities, every one — and continuity decides nothing on its own. A continuum
code space read at a *finite* resolution is a finite alphabet, and its capacity
is a bit count; the resolution is a noise floor, which every physical medium
has. `Examples/Phase6.lean` §33 exhibits both signs on the unit interval, at a
fine resolution and at a coarse one, because a witness showing only the
favourable sign would misrepresent what is proved.

Two things the comparison still does not supply. A mechanism: the floor is a
property of the code space, so nothing says an encoder writes those codes or a
readout separates them. And a calibration: `δ` and `L` are declared here, and
the comparison is informative only where both are measured. -/

section Floor

open MeasureTheory

section PackingFloor

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- Packing more room holds at least as much: a separated family inside `A` is a
separated family inside any `B` containing it. -/
theorem packingNumber_mono_set (δ : ℝ≥0) {A B : Set X} (h : A ⊆ B) :
    Metric.packingNumber δ A ≤ Metric.packingNumber δ B := by
  simp only [Metric.packingNumber, iSup_le_iff]
  exact fun D hDA hDsep => Metric.IsSeparated.encard_le_packingNumber (hDA.trans h) hDsep

/-- **The packing floor.** If every ball of radius `δ` has measure at most `v`,
a set of measure `μ A` needs at least `μ A / v` of them to be covered, and a
maximal `δ`-separated family inside `A` is such a cover. So the packing number
is at least `μ A / v`, in the division-free form `μ A ≤ v * packingNumber δ A`.

`v ≠ 0` is needed only where the packing number is infinite, and there it is
needed: the argument runs through a *maximal* separated family, which exists
only when the packing number is finite, so nothing bounds `μ A` while the
right-hand side stays `0`. A positive bound on the ball measure is what the
physical reading supplies anyway — a resolution cell has a volume.

This bounds the *code space*, and says nothing about any mechanism that writes
into it. -/
theorem measure_le_mul_packingNumber (μ : Measure X) {δ : ℝ≥0} {A : Set X} {v : ℝ≥0∞}
    (hv0 : v ≠ 0) (hv : ∀ x, μ (Metric.closedBall x (δ : ℝ)) ≤ v) :
    μ A ≤ v * Metric.packingNumber δ A := by
  rcases eq_or_ne (Metric.packingNumber δ A) ⊤ with h | h
  · rw [h, ENat.toENNReal_top, ENNReal.mul_top hv0]
    exact le_top
  · have hcard : (Metric.maximalSeparatedSet δ A).encard = Metric.packingNumber δ A :=
      Metric.encard_maximalSeparatedSet h
    have hfin : (Metric.maximalSeparatedSet δ A).Finite :=
      Set.encard_ne_top_iff.mp (by rw [hcard]; exact h)
    have hcov := Metric.isCover_maximalSeparatedSet h
    have hsub : A ⊆ ⋃ c ∈ hfin.toFinset, Metric.closedBall c (δ : ℝ) := by
      intro x hx
      obtain ⟨c, hc, hdist⟩ := hcov hx
      refine Set.mem_biUnion (hfin.mem_toFinset.2 hc) ?_
      have hnn : nndist x c ≤ δ := edist_le_coe.mp hdist
      exact Metric.mem_closedBall.2 (by exact_mod_cast hnn)
    have hpack : ((hfin.toFinset.card : ℕ∞) : ℝ≥0∞) = ((Metric.packingNumber δ A : ℕ∞) : ℝ≥0∞) := by
      rw [← hcard, hfin.encard_eq_coe_toFinset_card]
    calc μ A ≤ μ (⋃ c ∈ hfin.toFinset, Metric.closedBall c (δ : ℝ)) := measure_mono hsub
      _ ≤ ∑ c ∈ hfin.toFinset, μ (Metric.closedBall c (δ : ℝ)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _c ∈ hfin.toFinset, v := Finset.sum_le_sum fun c _ => hv c
      _ = v * (hfin.toFinset.card : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = v * Metric.packingNumber δ A := by rw [← hpack, ENat.toENNReal_coe]

/-- The floor in counting form: a region too large to be covered by `n` cells of
resolution `δ` packs more than `n` separated codes. -/
theorem lt_packingNumber_of_mul_lt_measure (μ : Measure X) {δ : ℝ≥0} {A : Set X} {v : ℝ≥0∞}
    {n : ℕ} (hv0 : v ≠ 0) (hv : ∀ x, μ (Metric.closedBall x (δ : ℝ)) ≤ v)
    (hn : (n : ℝ≥0∞) * v < μ A) : (n : ℕ∞) < Metric.packingNumber δ A := by
  by_contra hle
  have hle' : Metric.packingNumber δ A ≤ (n : ℕ∞) := not_lt.mp hle
  have hchain : μ A ≤ v * (n : ℝ≥0∞) := by
    refine (measure_le_mul_packingNumber μ hv0 hv).trans ?_
    calc v * (Metric.packingNumber δ A : ℝ≥0∞) ≤ v * ((n : ℕ∞) : ℝ≥0∞) := by gcongr
      _ = v * (n : ℝ≥0∞) := by rw [ENat.toENNReal_coe]
  rw [mul_comm] at hchain
  exact absurd (lt_of_lt_of_le hn hchain) (lt_irrefl _)

/-- **The resource-matched comparison.** A continuum code space holds strictly
more mutually resolvable codes than a `b`-bit alphabet exactly when its measure
exceeds `2 ^ b` resolution cells, where a cell is the largest a `δ`-ball can
measure.

Both sides are counted in one currency: `card_le_two_pow` caps a declared family
by an alphabet of `2 ^ b` codes, and the packing number is what
`encard_le_packingNumber_range` caps it by when the code space is continuous. So
this is a comparison and not a boast in one direction —
`Encoding.encard_le_two_pow_of_packingNumber_le` is the same statement with the
inequality reversed, and below the threshold it is the alphabet that is larger.

What decides it is `v` and `μ A`: a noise floor and a volume, both measured
quantities. Continuity contributes nothing by itself, and a continuum code space
read at a finite resolution is a finite alphabet whose capacity is a bit
count. -/
theorem two_pow_lt_packingNumber_of_lt_measure (μ : Measure X) {δ : ℝ≥0} {A : Set X}
    {v : ℝ≥0∞} {b : ℕ} (hv0 : v ≠ 0) (hv : ∀ x, μ (Metric.closedBall x (δ : ℝ)) ≤ v)
    (hb : (2 : ℝ≥0∞) ^ b * v < μ A) :
    ((2 ^ b : ℕ) : ℕ∞) < Metric.packingNumber δ A := by
  refine lt_packingNumber_of_mul_lt_measure μ hv0 hv ?_
  simpa using hb

end PackingFloor

section EuclideanFloor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

/-- **Volume over `δ^d`.** On a finite-dimensional real vector space with a Haar
measure, every ball of radius `δ` has the same measure, `δ^d` times the unit
ball's, so the floor is the region's volume divided by a resolution cell's. This
is the sense in which a continuum code space is large: not that it is infinite —
at `δ = 0` the packing number is the cardinality and says nothing physical — but
that at a *fixed* resolution it holds a number of codes growing as the volume
and shrinking as `δ^d`.

`δ ≠ 0` is required, and it is the whole physical content: the bound is a
statement about a code space read at a finite resolution, and the resolution is
supplied by a noise floor this module does not derive. -/
theorem measure_le_pow_mul_packingNumber (μ : Measure E) [μ.IsAddHaarMeasure]
    {δ : ℝ≥0} (hδ : δ ≠ 0) (A : Set E) :
    μ A ≤ ENNReal.ofReal ((δ : ℝ) ^ Module.finrank ℝ E) * μ (Metric.ball 0 1)
        * Metric.packingNumber δ A := by
  refine measure_le_mul_packingNumber μ ?_ fun x => ?_
  · have h1 : ENNReal.ofReal ((δ : ℝ) ^ Module.finrank ℝ E) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : (0 : ℝ) < (δ : ℝ) := lt_of_le_of_ne δ.coe_nonneg (by simpa [eq_comm] using hδ)
      positivity
    exact mul_ne_zero h1 (Metric.measure_ball_pos μ 0 one_pos).ne'
  · exact le_of_eq (Measure.addHaar_closedBall μ x δ.coe_nonneg)

/-- **The comparison in the form a reader can evaluate.** On a
finite-dimensional real space with a Haar measure the resolution cell is `δ^d`
times the unit ball's measure, so a continuum code space out-resolves a `b`-bit
alphabet exactly when its volume exceeds `2 ^ b` cells. The exchange rate is
`b` against `log₂(volume) − d·log₂ δ` up to the unit ball's constant: volume
buys capacity linearly in bits, and resolution buys it `d` times over.

Every quantity on the left is measured or declared — the dimension, the noise
floor and the word length — and none of them is continuity. That is the content:
the advantage an analog medium has here is exactly the number of resolution
cells in its volume, and no more. -/
theorem two_pow_lt_packingNumber_of_lt_measure_haar (μ : Measure E) [μ.IsAddHaarMeasure]
    {δ : ℝ≥0} (hδ : δ ≠ 0) {A : Set E} {b : ℕ}
    (hb : (2 : ℝ≥0∞) ^ b
        * (ENNReal.ofReal ((δ : ℝ) ^ Module.finrank ℝ E) * μ (Metric.ball 0 1)) < μ A) :
    ((2 ^ b : ℕ) : ℕ∞) < Metric.packingNumber δ A := by
  refine two_pow_lt_packingNumber_of_lt_measure μ ?_ (fun x => ?_) hb
  · have h1 : ENNReal.ofReal ((δ : ℝ) ^ Module.finrank ℝ E) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : (0 : ℝ) < (δ : ℝ) := lt_of_le_of_ne δ.coe_nonneg (by simpa [eq_comm] using hδ)
      positivity
    exact mul_ne_zero h1 (Metric.measure_ball_pos μ 0 one_pos).ne'
  · exact le_of_eq (Measure.addHaar_closedBall μ x δ.coe_nonneg)

end EuclideanFloor

namespace Encoding

variable [PseudoMetricSpace C] [MeasurableSpace C]

/-- **The floor, on the codes the encoder writes.** A region of the code space
inside the encoder's range, of measure `μ A`, forces the packing number that
`encard_le_packingNumber_range` bounds the declared family by to be at least
`μ A / v`. The ceiling and the floor then hold of the same quantity, which is
what makes the resource-matched comparison a comparison rather than a bound in
one direction.

That quantity is still a property of the code space and the resolution alone.
Nothing here says the encoder is injective on any family, that the readout
resolves what the code space separates, or that the family the mechanism must
distinguish is that large. -/
theorem measure_le_mul_packingNumber_range (Enc : Encoding S C) (μ : Measure C) {δ : ℝ≥0}
    {A : Set C} {v : ℝ≥0∞} (hA : A ⊆ Set.range Enc.encode) (hv0 : v ≠ 0)
    (hv : ∀ x, μ (Metric.closedBall x (δ : ℝ)) ≤ v) :
    μ A ≤ v * Metric.packingNumber δ (Set.range Enc.encode) := by
  refine (measure_le_mul_packingNumber μ hv0 hv).trans ?_
  gcongr
  exact packingNumber_mono_set δ hA

omit [MeasurableSpace C] in
/-- **The comparison, running the other way.** Where the code space holds at
most `2 ^ b` mutually resolvable codes, the declared family is capped at
`2 ^ b` — which is `card_le_two_pow`'s conclusion, reached without an alphabet
to count.

This is why `two_pow_lt_packingNumber_of_lt_measure` is a comparison and not a
claim about continuity: at a coarse enough resolution a region of any volume
holds few codes, and the `b`-bit alphabet is the larger of the two. Which holds
is a question about `δ` and the volume, and this module measures neither. -/
theorem encard_le_two_pow_of_packingNumber_le (Enc : Encoding S C) {L δ : ℝ≥0} {ε r : ℝ}
    {b : ℕ} (hL : LipschitzWith L Enc.readout) (hL0 : 0 < L) (hrec : Enc.Reconstructs ε)
    {F : Set S} (hF : F ⊆ Enc.relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → r < dist s t)
    (hδ : (δ : ℝ) * L ≤ r - 2 * ε)
    (hpack : Metric.packingNumber δ (Set.range Enc.encode) ≤ ((2 ^ b : ℕ) : ℕ∞)) :
    F.encard ≤ ((2 ^ b : ℕ) : ℕ∞) :=
  (encard_le_packingNumber_range hL hL0 hrec hF hsep hδ).trans hpack

end Encoding

end Floor

#print axioms measure_le_mul_packingNumber
#print axioms measure_le_pow_mul_packingNumber
#print axioms Encoding.measure_le_mul_packingNumber_range
#print axioms two_pow_lt_packingNumber_of_lt_measure
#print axioms two_pow_lt_packingNumber_of_lt_measure_haar
#print axioms Encoding.encard_le_two_pow_of_packingNumber_le

/-- A linear encoder/readout factoring a target spatial operator through a
finite-dimensional code space incurs its omitted squared spectral tail. The
code-space dimension derives the rank constraint. This is an average squared
error on the supplied eigenbasis, not a uniform reconstruction guarantee, a
finite-bit capacity bound, or a rank bound for nonlinear softmax attention. -/
lemma linear_bottleneck_error {ι E F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (b : OrthonormalBasis ι ℝ E) (K : E →ₗ[ℝ] E)
    (encode : E →ₗ[ℝ] F) (decode : F →ₗ[ℝ] E)
    (lam : ι → ℝ) (S : Finset ι) (τ : ℝ)
    (heigen : ∀ i, K (b i) = lam i • b i)
    (hbudget : Module.finrank ℝ F ≤ S.card)
    (hτ : 0 ≤ τ) (hin : ∀ i ∈ S, τ ≤ lam i ^ 2)
    (hout : ∀ i ∉ S, lam i ^ 2 ≤ τ) :
    ∑ i ∈ Sᶜ, lam i ^ 2 ≤ ∑ i, ‖K (b i) - decode (encode (b i))‖ ^ 2 := by
  apply AttentionRank.spectral_tail_le_error b K (decode.comp encode) lam S τ heigen
  · exact (Submodule.finrank_mono (LinearMap.range_comp_le_range encode decode)).trans
      (decode.finrank_range_le.trans hbudget)
  · exact hτ
  · exact hin
  · exact hout

#print axioms linear_bottleneck_error

open MeasureTheory
/-- A fixed-length sequence of k vocabulary symbols carries at most k log₂|V|
bits about a finite input state. The entire joint law is arbitrary, so token
independence is unnecessary. Cache state and timing are separate outputs unless
explicitly included in this alphabet; variable-length termination is not free. -/
lemma token_information_bits_le {X V : Type*} [Fintype X] [Fintype V] [Nonempty V]
    [MeasurableSpace X] [MeasurableSpace V] [MeasurableSingletonClass X]
    [MeasurableSingletonClass V] (k : ℕ) (μ : Measure (X × (Fin k → V)))
    [IsProbabilityMeasure μ] :
    (mutualInfo μ).toReal / Real.log 2 ≤ k * (Real.log (Fintype.card V) / Real.log 2) := by
  calc
    _ ≤ Real.log (Fintype.card (Fin k → V)) / Real.log 2 := mutualInfo_bits_le_log_card μ
    _ = _ := by rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]; ring
/-- With no emitted symbols the output is a singleton and conveys exactly
zero information, including for a nontrivial hidden state. -/
lemma no_tokens_no_information {X V : Type*} [Fintype X] [Fintype V] [Nonempty V]
    [MeasurableSpace X] [MeasurableSpace V] [MeasurableSingletonClass X]
    [MeasurableSingletonClass V] (μ : Measure (X × (Fin 0 → V)))
    [IsProbabilityMeasure μ] : mutualInfo μ = 0 := by
  have h := mutualInfo_le_log_card μ
  simp only [Fintype.card_fun, Fintype.card_fin, pow_zero, Nat.cast_one, Real.log_one] at h
  exact ((ENNReal.toReal_eq_zero_iff _).mp (le_antisymm h ENNReal.toReal_nonneg)).resolve_right
    (mutualInfo_finite μ)

#print axioms token_information_bits_le
#print axioms no_tokens_no_information

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

/-! ### The capacity bound, on the region

The packing bound of `Reconstruction.Encoding` applies to a reflexive boundary
with its own two maps in place, and under resonance its right-hand side is a
property of the *region*: the codes the avatar writes are the sections the
substrate holds there, so the number of states the region can keep apart at a
given scale is fixed before any avatar is built. That is the quantitative form
of the properness condition — a region resolves the declared family only if the
family packs into the region's sections — and it is the form that says something
at a proper region and nothing at `⊤`, where the sections over the region are
the global sections themselves.

The gain `L` is a declared property of the read-out and nothing here supplies
one for a physical decoder. -/

/-- **The declared family packs into the codes the avatar writes.** -/
theorem encard_le_packingNumber_auto_resonance [MetricSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X)
    [PseudoMetricSpace ((probabilityPresheaf X).obj (op rb.avatar_region))]
    (relevant : Set (GlobalSection (X := X))) {L δ : ℝ≥0} {ε r : ℝ}
    (hL : LipschitzWith L rb.readout) (hL0 : 0 < L)
    (hrec : (rb.encoding relevant).Reconstructs ε)
    {F : Set (GlobalSection (X := X))} (hF : F ⊆ relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → r < dist s t)
    (hδ : (δ : ℝ) * L ≤ r - 2 * ε) :
    F.encard ≤ Metric.packingNumber δ (Set.range rb.auto_resonance) :=
  Encoding.encard_le_packingNumber_range (Enc := rb.encoding relevant) hL hL0 hrec hF hsep hδ

/-- **…and under resonance those codes are the region's own sections.** The
bound is then a statement about the avatar region and the substrate, with the
encoding eliminated: a region whose sections do not pack the declared family at
the scale the read-out's gain leaves cannot carry a resonant mechanism that
reconstructs it. -/
theorem encard_le_packingNumber_restrictToAvatar [MetricSpace (GlobalSection (X := X))]
    (rb : ReflexiveBoundary X)
    [PseudoMetricSpace ((probabilityPresheaf X).obj (op rb.avatar_region))]
    (relevant : Set (GlobalSection (X := X))) {L δ : ℝ≥0} {ε r : ℝ}
    (hres : rb.IsRestrictionResonance)
    (hL : LipschitzWith L rb.readout) (hL0 : 0 < L)
    (hrec : (rb.encoding relevant).Reconstructs ε)
    {F : Set (GlobalSection (X := X))} (hF : F ⊆ relevant)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → r < dist s t)
    (hδ : (δ : ℝ) * L ≤ r - 2 * ε) :
    F.encard ≤ Metric.packingNumber δ (Set.range rb.restrictToAvatar) := by
  have hrange : Set.range rb.auto_resonance = Set.range rb.restrictToAvatar :=
    congrArg Set.range (funext hres)
  exact hrange ▸ encard_le_packingNumber_auto_resonance rb relevant hL hL0 hrec hF hsep hδ

/-! ### The region is a choice, and the whole substrate is a legal one

`avatar_region` is unconstrained data, and `⊤` is a value it may take. This
block computes what the criteria above say about the boundary that takes it, and
the answer is nothing: at `⊤` the restriction is the identity map
(`restrictToAvatar_mk_top`), so the whole-substrate boundary is resonant,
reconstructs every declared family exactly, and resolves every family whatsoever
(`topAvatar_satisfies_obligations`). The two demands that restriction resonance
places on a region — that the avatar report what the region holds, and that the
region separate the states the mechanism must tell apart — are therefore jointly
satisfiable with nothing folded into anything.

That is the argument for a properness condition, and it is why the condition is
a hypothesis rather than a field, per rule §3: a `ReflexiveBoundary` is data, and
which results need the region to be a proper part of the substrate is what the
statements say. `IsProperAvatar` is the cheap shape of it. The quantitative
shape is the packing bound of §"From an alphabet to a metric": the family the
region must resolve is no larger than the packing number of the codes the region
carries, which is a constraint exactly when that code space is smaller than the
state space. At `⊤` it is not smaller — the encoder is the identity and its
range is everything (`topAvatar_encode_range`), so the bound is the family's own
packing number and says nothing.

Neither condition is derived here. A substrate is not obliged to fold its state
into a proper region; what this block establishes is that a development which
does not ask it to has not asked for a fold at all. -/

/-- **The restriction to the whole substrate is the identity.** The morphism
`⊤ ⟶ ⊤` is the identity of the poset, and a functor preserves it. -/
theorem restrictToAvatar_mk_top
    (w : GlobalSection (X := X) → (probabilityPresheaf X).obj (op (⊤ : Opens X)))
    (r : (probabilityPresheaf X).obj (op (⊤ : Opens X)) → GlobalSection (X := X))
    (s : GlobalSection (X := X)) :
    (ReflexiveBoundary.mk (X := X) ⊤ w r).restrictToAvatar s = s := by
  show (probabilityPresheaf X).map (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op s = s
  rw [show (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _, op_id]
  exact Functor.map_id_apply (probabilityPresheaf X) (op ⊤) s

/-- A region equal to the whole substrate resolves every family, for free. This
is `restrictToAvatar_injOn_of_isRestrictionResonance`'s conclusion with no
hypothesis in front of it, which is the sense in which that theorem constrains a
region only when the region is proper. -/
theorem restrictToAvatar_injective_of_top (rb : ReflexiveBoundary X)
    (h : rb.avatar_region = ⊤) : Function.Injective rb.restrictToAvatar := by
  obtain ⟨U, w, r⟩ := rb
  subst h
  intro s t hst
  rw [restrictToAvatar_mk_top, restrictToAvatar_mk_top] at hst
  exact hst

/-- **The whole substrate as its own avatar**: the field, written unchanged into
a region that is everything, and read back unchanged. `Examples/Phase6.lean`'s
`cortexIdentity` is this boundary on the three-site substrate. -/
def topAvatar (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X] : ReflexiveBoundary X where
  avatar_region := ⊤
  auto_resonance := id
  readout := id

@[simp] theorem topAvatar_restrictToAvatar (s : GlobalSection (X := X)) :
    (topAvatar X).restrictToAvatar s = s := restrictToAvatar_mk_top _ _ s

@[simp] theorem topAvatar_predict (s : GlobalSection (X := X)) :
    (topAvatar X).predict s = s := rfl

/-- The write is the region's own restriction, so the boundary is resonant. -/
theorem topAvatar_isRestrictionResonance : (topAvatar X).IsRestrictionResonance :=
  fun s => (topAvatar_restrictToAvatar s).symm

theorem topAvatar_restrictToAvatar_injective :
    Function.Injective (topAvatar X).restrictToAvatar :=
  restrictToAvatar_injective_of_top _ rfl

/-- Every state is its own reconstruction, whatever family is declared. -/
theorem topAvatar_reconstructs [MetricSpace (GlobalSection (X := X))]
    (relevant : Set (GlobalSection (X := X))) :
    ((topAvatar X).encoding relevant).Reconstructs 0 := by
  intro s _
  show dist s ((topAvatar X).predict s) ≤ 0
  rw [topAvatar_predict, dist_self]

/-- **The codes are the states.** The encoder is the identity, so the packing
bound of §"From an alphabet to a metric" reads the family's cardinality against
the packing number of the whole state space. A capacity argument over this
region is an argument about nothing. -/
theorem topAvatar_encode_range [MetricSpace (GlobalSection (X := X))]
    (relevant : Set (GlobalSection (X := X))) :
    Set.range ((topAvatar X).encoding relevant).encode = Set.univ := Set.range_id

/-- **The region is a proper part of the substrate.** The cheap properness
condition: a hypothesis on the theorems that need it, not a field on the
structure. It is weak — a region one point short of `⊤` satisfies it — and the
quantitative condition is the packing bound, whose right-hand side is a property
of the region's code space. -/
def IsProperAvatar (rb : ReflexiveBoundary X) : Prop := rb.avatar_region ≠ ⊤

theorem topAvatar_not_isProperAvatar : ¬ (topAvatar X).IsProperAvatar := fun h => h rfl

/-- **Both obligations, met with nothing encoded anywhere.** Restriction
resonance and resolution of the declared family are what a reflexive boundary is
asked for, and the whole-substrate avatar supplies both — reconstructing exactly,
at tolerance zero, for every family that can be declared — while failing
properness. Whatever a fold into a local region buys, it is not this pair. -/
theorem topAvatar_satisfies_obligations [MetricSpace (GlobalSection (X := X))]
    (relevant : Set (GlobalSection (X := X))) :
    (topAvatar X).IsRestrictionResonance ∧
      ((topAvatar X).encoding relevant).Reconstructs 0 ∧
      Function.Injective (topAvatar X).restrictToAvatar ∧
      ¬ (topAvatar X).IsProperAvatar :=
  ⟨topAvatar_isRestrictionResonance, topAvatar_reconstructs relevant,
    topAvatar_restrictToAvatar_injective, topAvatar_not_isProperAvatar⟩

#print axioms Reconstruction.dist_le_add_error
#print axioms Reconstruction.half_dist_le_max_error
#print axioms Reconstruction.Encoding.encode_injOn_of_separated
#print axioms Reconstruction.Encoding.card_le_card_codes
#print axioms Reconstruction.Encoding.card_le_card_tokens
#print axioms Reconstruction.Encoding.card_le_card_tokens_one
#print axioms Reconstruction.Encoding.not_reconstructs_of_card_tokens_lt
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
#print axioms Reconstruction.Encoding.sub_two_mul_le_lipschitz_mul
#print axioms Reconstruction.Encoding.isSeparated_image_encode
#print axioms Reconstruction.Encoding.encard_le_packingNumber_range
#print axioms Reconstruction.Encoding.card_le_packingNumber_range
#print axioms encard_le_packingNumber_auto_resonance
#print axioms encard_le_packingNumber_restrictToAvatar
#print axioms restrictToAvatar_mk_top
#print axioms restrictToAvatar_injective_of_top
#print axioms topAvatar_isRestrictionResonance
#print axioms topAvatar_restrictToAvatar_injective
#print axioms topAvatar_reconstructs
#print axioms topAvatar_encode_range
#print axioms topAvatar_satisfies_obligations

end ReflexiveBoundary
end PhysicsOfConsciousness
