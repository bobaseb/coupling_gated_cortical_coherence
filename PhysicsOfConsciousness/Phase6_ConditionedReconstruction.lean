import PhysicsOfConsciousness.Phase6_Reconstruction

/-!
# Reconstruction conditioned on an input

`Encoding.dist_le_of_contracting_reconstructs` limits a *fixed* `Λ`-contraction
that reconstructs every member of a family within `ε` to a family of diameter
`2ε/(1-Λ)`: at zero error, one state. A self that follows a changing scene is
not that. Its readout is conditioned on the scene, so the map it applies is one
of a family `F u`, each with its own fixed point. This module states what
replaces the fixed-map limit for such a family, and what stops the family from
reconstructing everything by storing it.

The data is a `ConditionedEncoding`: a declared relevant family, a declared
`input` assigning each state the scene it is a state for, an encoder into an
alphabet of codes, and a readout that sees the input and the code. The map is
`F u s = readout u (encode s)`.

* **The diameter limit becomes a Lipschitz condition in the input.** If each
  `F u` is a `Λ`-contraction on the family, `F` moves by at most `L · d(u, v)`
  when the input changes, and every member is reconstructed within `ε`, then
  `d(s, t) ≤ (2ε + L · d(u_s, u_t)) / (1 - Λ)`
  (`dist_le_of_conditioned_contracting`). The family can be as broad as its
  inputs are; states given the *same* input still obey the fixed-map limit
  (`dist_le_of_same_input`).
* **The self-states follow the scene.** On a complete space each `F u` has a
  unique fixed point `selfState u`, these move by at most
  `L · d(u, v) / (1 - Λ)` (`dist_selfState_le`), and each reconstructed member
  lies within `ε / (1 - Λ)` of its input's fixed point
  (`dist_selfState_input_le`).
* **The code must still carry what the input does not.** A readout that returns
  a state stored for each input (`storedReadout`) is a contraction with `Λ = 0`,
  reconstructs every family in which the state is a function of the input, and
  encodes nothing. The code criterion therefore binds *within an input fibre*:
  members of one fibre pairwise more than `2ε` apart need distinct codes
  (`card_le_card_codes_fibre`), and a constant encoder reconstructs only
  families whose fibres have diameter at most `2ε`
  (`dist_le_of_encode_const`). A claim that a system reconstructs its own state,
  rather than its scene, is a claim about a family with non-trivial fibres, and
  that family is the claim's to declare.

## Scope

The input, its metric, the gain `L` and the contraction constant are declared.
Nothing here constructs a physical readout, identifies a scene variable in
cortex, or derives `Λ`; the manuscript's `Λ` for the fixed map is stipulated and
this module inherits that status. `input` is a function of the state, so a
family in which two states share a state but not a scene is not expressible;
the scene is whatever the claim says each state is a state for.
-/

open scoped NNReal

namespace PhysicsOfConsciousness.Reconstruction

/-- A reconstruction mechanism whose readout is conditioned on an input: a
declared relevant family, the input each state is a state for, an encoder, and a
readout that sees both the input and the code. Data only; that the readout is
any good is `Reconstructs`. -/
structure ConditionedEncoding (S U C : Type*) [PseudoMetricSpace S] where
  /-- The states the criterion is about. States outside it are unconstrained. -/
  relevant : Set S
  /-- The scene each state is a state for. Declared, not derived. -/
  input : S → U
  /-- The encoder. Its codomain is the alphabet the fibre bound counts. -/
  encode : S → C
  /-- The readout, reconstructing a state from an input and a code. -/
  readout : U → C → S

namespace ConditionedEncoding

variable {S U C : Type*} [PseudoMetricSpace S] (Enc : ConditionedEncoding S U C)

/-- The map applied under input `u`: encode, then read out conditioned on `u`. -/
def conditionedMap (u : U) (s : S) : S := Enc.readout u (Enc.encode s)

/-- The reconstruction error at a state, under that state's own input. -/
def error (s : S) : ℝ := dist s (Enc.conditionedMap (Enc.input s) s)

/-- Bounded-error reconstruction at tolerance `ε`, on the declared family only. -/
def Reconstructs (ε : ℝ) : Prop := ∀ s ∈ Enc.relevant, Enc.error s ≤ ε

/-- The relevant states given input `u`. -/
def fibre (u : U) : Set S := {s | s ∈ Enc.relevant ∧ Enc.input s = u}

variable {Enc}

/-! ## The diameter limit, conditioned -/

/-- **A conditioned contraction reconstructs a family as broad as its inputs.**
Each `F u` is a `Λ`-contraction on the family, `F` moves by at most `L · d(u, v)`
when the input changes, and every member is reconstructed within `ε`. Then two
members are at most `(2ε + L · d(u_s, u_t)) / (1 - Λ)` apart.

This replaces `Encoding.dist_le_of_contracting_reconstructs`, which is the case
of equal inputs. The hypotheses carry the content and all are declared: the
input and its metric, `L`, `Λ`, `ε`. No physical readout is shown to meet them. -/
theorem dist_le_of_conditioned_contracting [PseudoMetricSpace U] {q L : ℝ≥0} (hq : q < 1)
    {ε : ℝ} (hmap : ∀ u, LipschitzOnWith q (Enc.conditionedMap u) Enc.relevant)
    (hin : ∀ u v, ∀ s ∈ Enc.relevant, dist (Enc.conditionedMap u s) (Enc.conditionedMap v s) ≤ L * dist u v)
    (hrec : Enc.Reconstructs ε) {s t : S} (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant) :
    dist s t ≤ (2 * ε + L * dist (Enc.input s) (Enc.input t)) / (1 - q) := by
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast hq
  set u := Enc.input s
  set v := Enc.input t
  have hsplit := dist_triangle4 s (Enc.conditionedMap u s) (Enc.conditionedMap u t) t
  have hmid : dist (Enc.conditionedMap u t) t ≤ dist (Enc.conditionedMap u t) (Enc.conditionedMap v t) + Enc.error t := by
    have := dist_triangle (Enc.conditionedMap u t) (Enc.conditionedMap v t) t
    rwa [dist_comm (Enc.conditionedMap v t) t] at this
  have hlip := (hmap u).dist_le_mul s hs t ht
  have hshift := hin u v t ht
  have hes : Enc.error s ≤ ε := hrec s hs
  have het : Enc.error t ≤ ε := hrec t ht
  have herr : dist s (Enc.conditionedMap u s) = Enc.error s := rfl
  apply (le_div_iff₀ (sub_pos.mpr hq1)).2
  nlinarith

/-- **Within one input the fixed-map limit still holds.** Members given the same
input are at most `2ε / (1 - Λ)` apart; at zero error, a fibre is one state. -/
theorem dist_le_of_same_input [PseudoMetricSpace U] {q L : ℝ≥0} (hq : q < 1) {ε : ℝ}
    (hmap : ∀ u, LipschitzOnWith q (Enc.conditionedMap u) Enc.relevant)
    (hin : ∀ u v, ∀ s ∈ Enc.relevant, dist (Enc.conditionedMap u s) (Enc.conditionedMap v s) ≤ L * dist u v)
    (hrec : Enc.Reconstructs ε) {s t : S} (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant)
    (hu : Enc.input s = Enc.input t) :
    dist s t ≤ 2 * ε / (1 - q) := by
  simpa [hu] using dist_le_of_conditioned_contracting hq hmap hin hrec hs ht

/-! ## What the code must carry -/

/-- Within one fibre the readout sees one input, so the fixed-alphabet argument
applies unchanged: separated, accurately reconstructed members of a fibre carry
distinct codes. -/
theorem encode_injOn_fibre {ε : ℝ} (hrec : Enc.Reconstructs ε) {u : U} {F : Set S}
    (hF : F ⊆ Enc.fibre u) (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    Set.InjOn Enc.encode F := by
  intro s hs t ht hcode
  by_contra hne
  have hes := hrec s (hF hs).1
  have het := hrec t (hF ht).1
  simp only [error, conditionedMap, (hF hs).2, (hF ht).2] at hes het
  exact encode_ne_of_separated Enc.encode (Enc.readout u) hes het (hsep s hs t ht hne) hcode

/-- **The fibre bound.** A finite set of members sharing one input, pairwise more
than `2ε` apart and all reconstructed within `ε`, is no larger than the alphabet.
This is where the code criterion binds a conditioned readout, and the only
place: across fibres the input carries the distinction. -/
theorem card_le_card_codes_fibre [Fintype C] [DecidableEq S] {ε : ℝ}
    (hrec : Enc.Reconstructs ε) {u : U} {F : Finset S} (hF : ↑F ⊆ Enc.fibre u)
    (hsep : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → 2 * ε < dist s t) :
    F.card ≤ Fintype.card C :=
  Finset.card_le_card_of_injOn Enc.encode (fun _ _ => Finset.mem_univ _)
    (encode_injOn_fibre hrec hF (fun s hs t ht => hsep s hs t ht))

/-- **A constant encoder reconstructs only thin fibres.** If every state gets
the same code, two members sharing an input are at most `2ε` apart. -/
theorem dist_le_of_encode_const (hE : ∀ s t, Enc.encode s = Enc.encode t) {ε : ℝ}
    (hrec : Enc.Reconstructs ε) {s t : S} (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant)
    (hu : Enc.input s = Enc.input t) :
    dist s t ≤ 2 * ε := by
  have h := dist_le_add_error Enc.encode (Enc.readout (Enc.input s)) (hE s t)
  have hes := hrec s hs
  have het := hrec t ht
  simp only [error, conditionedMap, ← hu] at hes het
  linarith

/-- The contrapositive, in the form a witness uses: one fibre holding two
members more than `2ε` apart rules out every constant encoder. -/
theorem not_reconstructs_of_encode_const (hE : ∀ s t, Enc.encode s = Enc.encode t) {ε : ℝ}
    {s t : S} (hs : s ∈ Enc.relevant) (ht : t ∈ Enc.relevant)
    (hu : Enc.input s = Enc.input t) (hsep : 2 * ε < dist s t) :
    ¬ Enc.Reconstructs ε :=
  fun hrec => absurd (dist_le_of_encode_const hE hrec hs ht hu) (not_le.mpr hsep)

/-! ## The degenerate witness, named

`storedReadout` returns a state kept for each input and ignores the code. Its map is
constant in the state, so it is a contraction with `Λ = 0` and every fibre bound
above is satisfied by it. It is here so that the guard is a theorem about it
rather than a remark. -/

/-- The stored-state readout: one code, and the state kept for the input. -/
def storedReadout (relevant : Set S) (input : S → U) (store : U → S) : ConditionedEncoding S U Unit where
  relevant := relevant
  input := input
  encode := fun _ => ()
  readout := fun u _ => store u

/-- The stored readout reconstructs exactly the families lying within `ε` of the
stored state for their input: every family in which the state is a function of
the input, at `ε = 0`. -/
theorem stored_reconstructs_iff {relevant : Set S} {input : S → U} {store : U → S} {ε : ℝ} :
    (storedReadout relevant input store).Reconstructs ε ↔
      ∀ s ∈ relevant, dist s (store (input s)) ≤ ε :=
  Iff.rfl

/-- Its map ignores the state, so it is a contraction with constant zero. -/
theorem stored_contracting {relevant : Set S} {input : S → U} {store : U → S} (u : U) :
    LipschitzWith 0 ((storedReadout relevant input store).conditionedMap u) :=
  LipschitzWith.const (store u)

/-! ## The self-states the family tracks

`ContractingWith` needs a metric rather than a pseudometric, so this section
asks for one. -/

section Fixed

variable {S U C : Type*} [MetricSpace S] [CompleteSpace S] [Nonempty S]
  (Enc : ConditionedEncoding S U C) {q L : ℝ≥0}

/-- The self-state for input `u`: the unique fixed point of the contraction `F u`. -/
noncomputable def selfState (hc : ∀ u, ContractingWith q (Enc.conditionedMap u)) (u : U) : S :=
  ContractingWith.fixedPoint (Enc.conditionedMap u) (hc u)

variable {Enc}

/-- **The self-states move with the scene, at rate `L / (1 - Λ)`.** Here the
input-Lipschitz condition is needed at every state, not only on the family,
because the fixed points need not be members. -/
theorem dist_selfState_le [PseudoMetricSpace U] (hc : ∀ u, ContractingWith q (Enc.conditionedMap u))
    (hin : ∀ u v s, dist (Enc.conditionedMap u s) (Enc.conditionedMap v s) ≤ L * dist u v) (u v : U) :
    dist (Enc.selfState hc u) (Enc.selfState hc v) ≤ L * dist u v / (1 - q) :=
  (hc u).dist_fixedPoint_fixedPoint_of_dist_le' (Enc.conditionedMap v) (hc u).fixedPoint_isFixedPt
    (hc v).fixedPoint_isFixedPt (hin u v)

/-- **Each reconstructed member lies near its own scene's self-state.** A member
reconstructed within `ε` is within `ε / (1 - Λ)` of the fixed point of the map
its input selects. -/
theorem dist_selfState_input_le (hc : ∀ u, ContractingWith q (Enc.conditionedMap u)) {ε : ℝ}
    (hrec : Enc.Reconstructs ε) {s : S} (hs : s ∈ Enc.relevant) :
    dist s (Enc.selfState hc (Enc.input s)) ≤ ε / (1 - q) :=
  ((hc (Enc.input s)).dist_fixedPoint_le s).trans
    (div_le_div_of_nonneg_right (hrec s hs) (hc (Enc.input s)).one_sub_K_pos.le)

end Fixed

end ConditionedEncoding

end PhysicsOfConsciousness.Reconstruction
