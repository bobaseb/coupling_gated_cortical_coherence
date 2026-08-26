import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

noncomputable def boltzmann_entropy {sys : Type} [DecidableEq sys] (states : Finset sys) : Real :=
  Real.log (states.card : Real)

theorem landauer_from_reversibility
  {S B : Type} [DecidableEq S] [DecidableEq B]
  (X : Finset S) (Y : Finset B) (U : S × B → S × B)
  (h_inj : Function.Injective U)
  (X_final : Finset S) (B_final : Finset B)
  (h_evolve : Finset.image U (X ×ˢ Y) ⊆ X_final ×ˢ B_final) :
  boltzmann_entropy B_final - boltzmann_entropy Y ≥ boltzmann_entropy X - boltzmann_entropy X_final := by
  sorry

