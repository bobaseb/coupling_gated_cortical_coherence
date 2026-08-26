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
  (h_evolve : Finset.image U (X ×ˢ Y) ⊆ X_final ×ˢ B_final)
  (hX : X.Nonempty) (hY : Y.Nonempty) :
  boltzmann_entropy B_final - boltzmann_entropy Y ≥ boltzmann_entropy X - boltzmann_entropy X_final := by
  have card_prod : (X ×ˢ Y).card = X.card * Y.card := Finset.card_product X Y
  have card_prod_final : (X_final ×ˢ B_final).card = X_final.card * B_final.card := Finset.card_product X_final B_final
  have card_image : (Finset.image U (X ×ˢ Y)).card = (X ×ˢ Y).card := Finset.card_image_of_injective (X ×ˢ Y) h_inj
  have card_le : (Finset.image U (X ×ˢ Y)).card ≤ (X_final ×ˢ B_final).card := Finset.card_le_card h_evolve
  rw [card_image, card_prod, card_prod_final] at card_le
  have hX_pos : X.card > 0 := Finset.card_pos.mpr hX
  have hY_pos : Y.card > 0 := Finset.card_pos.mpr hY
  have h_prod_pos : X.card * Y.card > 0 := mul_pos hX_pos hY_pos
  have h_final_pos : X_final.card * B_final.card > 0 := lt_of_lt_of_le h_prod_pos card_le
  have hXf_pos : X_final.card > 0 := Nat.pos_of_mul_pos_right h_final_pos
  have hBf_pos : B_final.card > 0 := Nat.pos_of_mul_pos_left h_final_pos
  
  have real_le : (X.card : Real) * (Y.card : Real) ≤ (X_final.card : Real) * (B_final.card : Real) := by
    exact_mod_cast card_le
    
  have h_log_le : Real.log ((X.card : Real) * (Y.card : Real)) ≤ Real.log ((X_final.card : Real) * (B_final.card : Real)) := by
    apply Real.log_le_log
    · exact mul_pos (Nat.cast_pos.mpr hX_pos) (Nat.cast_pos.mpr hY_pos)
    · exact real_le
    
  rw [Real.log_mul (ne_of_gt (Nat.cast_pos.mpr hX_pos)) (ne_of_gt (Nat.cast_pos.mpr hY_pos))] at h_log_le
  rw [Real.log_mul (ne_of_gt (Nat.cast_pos.mpr hXf_pos)) (ne_of_gt (Nat.cast_pos.mpr hBf_pos))] at h_log_le
  
  unfold boltzmann_entropy
  linarith
