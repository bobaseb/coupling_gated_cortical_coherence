import Mathlib
open BigOperators

noncomputable def boltzmann_entropy {sys : Type*} [DecidableEq sys] (states : Finset sys) : ℝ :=
  Real.log (states.card : ℝ)

noncomputable def entropy {sys : Type*} [Fintype sys] [DecidableEq sys] (t : sys → sys) : ℝ :=
  boltzmann_entropy (Finset.image t Finset.univ)

lemma entropy_decrease {sys : Type*} [Fintype sys] [DecidableEq sys] (t : sys → sys)
  (h_nonempty : Nonempty sys) (h_not_inj : ¬ Function.Injective t) :
  entropy t < boltzmann_entropy (Finset.univ : Finset sys) := by
  dsimp [entropy, boltzmann_entropy]
  apply Real.log_lt_log
  · exact Nat.cast_pos.mpr (by
      obtain ⟨x⟩ := h_nonempty
      exact Finset.card_pos.mpr ⟨t x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩)
  · apply Nat.cast_lt.mpr
    have le : (Finset.image t Finset.univ).card ≤ (Finset.univ : Finset sys).card := Finset.card_image_le
    apply lt_of_le_of_ne le
    intro h_eq
    have h_inj : Set.InjOn t ↑(Finset.univ : Finset sys) := by
      rwa [Finset.card_image_iff] at h_eq
    apply h_not_inj
    intro x y hxy
    exact h_inj (Finset.mem_univ x) (Finset.mem_univ y) hxy
