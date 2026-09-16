/-
  Examples/Reconstruction.lean — what a Self has to be able to tell apart

  §24, on the three-site cortex of `Examples/Cortex.lean` and the reflexive
  boundary of `Examples/Phase6.lean` §10. The criterion of
  `Phase6_Reconstruction.lean` is applied to the boundary that already exists:
  its own avatar reconstructs the two extreme states of the field to within one,
  and the blinded avatar of `cortexBlind` — which has a unique fixed point —
  reconstructs neither to within a half. A three-level family then exercises the
  counting half: three states two apart need three codes, and one bit does not
  suffice.
-/

import PhysicsOfConsciousness.Phase6_Reconstruction
import PhysicsOfConsciousness.Examples.Phase6

open MeasureTheory CategoryTheory TopologicalSpace Opposite
open scoped NNReal

namespace PhysicsOfConsciousness
namespace Examples

open PhysicsOfConsciousness.Reconstruction

/-! ## 24. Bounded-error self-reconstruction, and the codes the cortex needs

The declared family of relevant macrostates is `{cortexState, cortexSilent}`:
the baseline the field relaxes to and the silent field, two apart in the metric
built from the measures. -/

section ReflexiveSelf

/-- The declared family of relevant macrostates. The criterion says nothing
about states outside it; that choice is data, and it is made here. -/
noncomputable def selfFamily : Set (GlobalSection (X := Cortex)) :=
  {cortexState, cortexSilent}

theorem cortexState_mem : cortexState ∈ selfFamily := Or.inl rfl

theorem cortexSilent_mem : cortexSilent ∈ selfFamily := Or.inr rfl

/-- The baseline is its own reconstruction: it is the fixed point. -/
theorem error_cortexState : dist cortexState (cortexReflexive.predict cortexState) = 0 := by
  rw [cortexPredict_fixed, dist_self]

/-- The silent field is reconstructed to within one: the read-out sends its
reading `0` halfway to the baseline `2`, and the residual is the remaining
unit. -/
theorem error_cortexSilent :
    dist cortexSilent (cortexReflexive.predict cortexSilent) = 1 := by
  refine le_antisymm ?_ ?_
  · rw [gs_dist_eq, dist_pi_le_iff zero_le_one]
    intro x
    rw [Phi_cortexSilent, Phi_cortexPredict, Phi_cortexSilent, NNReal.dist_eq]
    split_ifs <;> push_cast <;> norm_num
  · have h := dist_le_pi_dist (density cortexSilent)
      (density (cortexReflexive.predict cortexSilent)) Site.mid
    rw [← gs_dist_eq, Phi_cortexSilent, Phi_cortexPredict_mid, Phi_cortexSilent] at h
    simpa [NNReal.dist_eq] using h

/-- The cortex's own boundary, read as a reconstruction mechanism. -/
noncomputable def selfEncoding := cortexReflexive.encoding selfFamily

/-- **The positive control.** Both relevant states are reconstructed to within
one, so the criterion is met at that tolerance and is not vacuous. -/
theorem selfEncoding_reconstructs : selfEncoding.Reconstructs 1 := by
  intro s hs
  rcases hs with rfl | rfl
  · show dist cortexState (cortexReflexive.predict cortexState) ≤ 1
    rw [error_cortexState]; norm_num
  · show dist cortexSilent (cortexReflexive.predict cortexSilent) ≤ 1
    rw [error_cortexSilent]

/-- …and it is informative rather than degenerate: the encoder actually
separates the two relevant states. -/
theorem selfEncoding_nonconstant :
    selfEncoding.encode cortexSilent ≠ selfEncoding.encode cortexState := by
  intro h
  exact cortexPredict_not_const (congrArg cortexReflexive.readout h)

/-- The same mechanism is a contraction, so the bounded-error control is
consistent with the fixed-point theorem rather than in competition with it. -/
theorem selfEncoding_contracting : ContractingWith (1/2) cortexReflexive.predict :=
  ⟨by norm_num, cortexPredict_lipschitz⟩

/-- **The blind-encoder rejection.** `cortexBlind` reports the silent field's
reading whatever the field does, so both relevant states carry one code; they
are two apart, and no readout recovers both to within a half. -/
theorem cortexBlind_not_reconstructs :
    ¬ (cortexBlind.encoding selfFamily).Reconstructs (1/2) := by
  refine ReflexiveBoundary.blinded_not_reconstructs cortexReflexive _ selfFamily
    cortexState_mem cortexSilent_mem ?_
  rw [dist_comm, dist_cortexSilent_cortexState]
  norm_num

/-- **A unique fixed point is not a reconstruction.** The blinded boundary has
exactly one Self — a state stipulated in advance of the field — and fails the
reconstruction criterion on the declared family. The two facts sit side by side
because they are about different things: one state predicting itself, and a
family of states being told apart. -/
theorem cortexBlind_self_without_reconstruction :
    (∃! s : GlobalSection (X := Cortex), cortexBlind.predict s = s) ∧
      ¬ (cortexBlind.encoding selfFamily).Reconstructs (1/2) :=
  ⟨cortexBlind_existsUnique_self, cortexBlind_not_reconstructs⟩

/-! ### The counting half: three levels and one bit

A family of uniform mass profiles, whose distances are the differences of their
levels. Nothing about them is special: they are the cheapest states on this
substrate whose pairwise separation can be read off. -/

/-- The uniform section at mass level `c`. -/
noncomputable def lvl (c : ℝ≥0) : GlobalSection (X := Cortex) := sectionOfMass fun _ => c

theorem lvl_dist (c c' : ℝ≥0) : dist (lvl c) (lvl c') = |(c : ℝ) - (c' : ℝ)| := by
  rw [lvl, lvl, gs_dist_sectionOfMass, dist_pi_const, NNReal.dist_eq]

theorem lvl_ne {c c' : ℝ≥0} (h : c ≠ c') : lvl c ≠ lvl c' := by
  intro heq
  apply h
  have hd := congrArg density heq
  rw [lvl, lvl, Phi_sectionOfMass, Phi_sectionOfMass] at hd
  exact congrFun hd Site.mid

open scoped Classical in
/-- Three relevant macrostates, pairwise at least two apart. -/
noncomputable def triple : Finset (GlobalSection (X := Cortex)) := {lvl 0, lvl 2, lvl 4}

open scoped Classical in
theorem triple_card : triple.card = 3 := by
  rw [triple, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    exact lvl_ne (by norm_num)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.2 ⟨lvl_ne (by norm_num), lvl_ne (by norm_num)⟩

open scoped Classical in
theorem triple_separated :
    ∀ s ∈ triple, ∀ t ∈ triple, s ≠ t → 2 * (1/2 : ℝ) < dist s t := by
  intro s hs t ht hne
  simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hs ht
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | (rw [lvl_dist]; push_cast; norm_num)

open scoped Classical in
/-- **One bit does not reconstruct three separated states.** For *any* encoder
into `Bool` and any readout, the criterion fails at tolerance `1/2`, because the
capacity bound would make `3 ≤ 2 ^ 1`. The alphabet is counted, not measured:
nothing here says a bit costs `k T log 2`. -/
theorem no_bit_reconstruction (E : GlobalSection (X := Cortex) → Bool)
    (R : Bool → GlobalSection (X := Cortex)) :
    ¬ (Encoding.mk (↑triple) E R).Reconstructs (1/2) := by
  intro hrec
  have h := Encoding.card_le_two_pow (C := Bool) (b := 1) (by simp) hrec
    (F := triple) (le_refl _) triple_separated
  rw [triple_card] at h
  norm_num at h

open scoped Classical in
/-- The code that does work: three values, read back exactly. -/
noncomputable def tripleCode : GlobalSection (X := Cortex) → Fin 3 :=
  fun s => if s = lvl 0 then 0 else if s = lvl 2 then 1 else 2

noncomputable def tripleDecode : Fin 3 → GlobalSection (X := Cortex) :=
  ![lvl 0, lvl 2, lvl 4]

open scoped Classical in
noncomputable def tripleEncoding : Encoding (GlobalSection (X := Cortex)) (Fin 3) :=
  ⟨↑triple, tripleCode, tripleDecode⟩

open scoped Classical in
/-- **The positive control for the counting half.** Three codes reconstruct the
three states exactly, so the bound `M ≤ Fintype.card C` is attained and the
rejection above is about the alphabet's size and not about the states. -/
theorem tripleEncoding_reconstructs : tripleEncoding.Reconstructs 0 := by
  have h20 : lvl 2 ≠ lvl 0 := lvl_ne (by norm_num)
  have h40 : lvl 4 ≠ lvl 0 := lvl_ne (by norm_num)
  have h42 : lvl 4 ≠ lvl 2 := lvl_ne (by norm_num)
  intro s hs
  simp only [tripleEncoding, Finset.coe_insert, Set.mem_insert_iff,
    Finset.coe_singleton, Set.mem_singleton_iff, triple] at hs
  rcases hs with rfl | rfl | rfl <;>
    simp [Encoding.error, tripleEncoding, tripleCode, tripleDecode, h20, h40, h42]

open scoped Classical in
/-- The encoder is not constant, so the positive control is informative. -/
theorem tripleCode_nonconstant : tripleCode (lvl 0) ≠ tripleCode (lvl 4) := by
  have h40 : lvl 4 ≠ lvl 0 := lvl_ne (by norm_num)
  have h42 : lvl 4 ≠ lvl 2 := lvl_ne (by norm_num)
  simp [tripleCode, h40, h42]

#print axioms error_cortexState
#print axioms error_cortexSilent
#print axioms selfEncoding_reconstructs
#print axioms selfEncoding_nonconstant
#print axioms selfEncoding_contracting
#print axioms cortexBlind_not_reconstructs
#print axioms cortexBlind_self_without_reconstruction
#print axioms triple_card
#print axioms triple_separated
#print axioms no_bit_reconstruction
#print axioms tripleEncoding_reconstructs
#print axioms tripleCode_nonconstant

end ReflexiveSelf

end Examples
end PhysicsOfConsciousness
