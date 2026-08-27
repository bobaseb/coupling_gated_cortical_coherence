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
  apply Real.strictMonoOn_log.monotoneOn
  sorry
