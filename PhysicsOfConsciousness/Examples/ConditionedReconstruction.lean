/-
  Examples/ConditionedReconstruction.lean — a self that follows a scene

  §36, for `Phase6_ConditionedReconstruction.lean`. Four real states in two
  scenes, `{0, 3}` under input `0` and `{10, 13}` under input `10`. A one-bit
  code with a scene-conditioned readout reconstructs all four within `3/4` by
  maps that halve distances on the family. No single `1/2`-contraction can: the
  family's diameter is `13` and the fixed-map limit at that tolerance is `3`,
  which each scene attains exactly. Each scene needs both codes, so no constant
  encoder reconstructs the family. A second, affine readout contracts the whole
  line, so its self-states exist; they sit at `u + 3/2` and move with the scene
  at the rate the library bound gives.
-/

import PhysicsOfConsciousness.Phase6_ConditionedReconstruction

open scoped NNReal

namespace PhysicsOfConsciousness
namespace Examples

open PhysicsOfConsciousness.Reconstruction

/-! ## 36. A readout conditioned on the scene

The four states and their scenes. -/

/-- The declared family: two states in each of two scenes. -/
def sceneFamily : Set ℝ := {0, 3, 10, 13}

/-- The scene each state is a state for. -/
noncomputable def sceneOf (s : ℝ) : ℝ := if s < 5 then 0 else 10

/-- The value a one-bit code reads out to, above the scene. -/
noncomputable def bitLevel (c : Bool) : ℝ := if c then 9 / 4 else 3 / 4

/-- One bit per state: whether it is the upper state of its scene. -/
noncomputable def sceneBits : ConditionedEncoding ℝ ℝ Bool where
  relevant := sceneFamily
  input := sceneOf
  encode := fun s => decide (1 < s - sceneOf s)
  readout := fun u c => u + bitLevel c

private theorem sceneFamily_cases {s : ℝ} (hs : s ∈ sceneFamily) :
    s = 0 ∨ s = 3 ∨ s = 10 ∨ s = 13 := by
  simpa [sceneFamily] using hs

/-- Every member is reconstructed within `3/4`. -/
theorem sceneBits_reconstructs : sceneBits.Reconstructs (3 / 4) := by
  intro s hs
  rcases sceneFamily_cases hs with rfl | rfl | rfl | rfl <;>
    norm_num [ConditionedEncoding.error, ConditionedEncoding.conditionedMap, sceneBits, sceneOf,
      bitLevel, Real.dist_eq, abs_le]

/-- Under either scene the map halves distances on the family. -/
theorem sceneBits_contracting (u : ℝ) :
    LipschitzOnWith (1 / 2) (sceneBits.conditionedMap u) sceneFamily := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rcases sceneFamily_cases hs with rfl | rfl | rfl | rfl <;>
    rcases sceneFamily_cases ht with rfl | rfl | rfl | rfl <;>
    norm_num [ConditionedEncoding.conditionedMap, sceneBits, sceneOf, bitLevel, Real.dist_eq, abs_le]

/-- Changing the scene moves the map by exactly the change. -/
theorem sceneBits_input_lipschitz (u v : ℝ) :
    ∀ s ∈ sceneBits.relevant, dist (sceneBits.conditionedMap u s) (sceneBits.conditionedMap v s) ≤ (1 : ℝ≥0) * dist u v := by
  intro s _
  simp [ConditionedEncoding.conditionedMap, sceneBits, Real.dist_eq]

/-- **The conditioned bound, applied.** The two extreme members are `13` apart,
within the `(2 · 3/4 + 1 · 10) / (1 - 1/2) = 23` the library allows. -/
theorem sceneBits_extremes :
    dist (0 : ℝ) 13 ≤ (2 * (3 / 4) + (1 : ℝ≥0) * dist (sceneOf 0) (sceneOf 13)) /
      (1 - ((1 / 2 : ℝ≥0) : ℝ)) :=
  ConditionedEncoding.dist_le_of_conditioned_contracting (Enc := sceneBits) (by norm_num)
    sceneBits_contracting sceneBits_input_lipschitz sceneBits_reconstructs
    (by simp [sceneBits, sceneFamily]) (by simp [sceneBits, sceneFamily])

/-- **Each scene attains the fixed-map limit.** Its two states are `3` apart, and
`2 · (3/4) / (1 - 1/2) = 3`. -/
theorem sceneBits_fibre_attains :
    dist (0 : ℝ) 3 = 2 * (3 / 4) / (1 - (1 / 2 : ℝ)) := by
  norm_num [Real.dist_eq]

/-- **No fixed map does this.** Any single encoding whose composite halves every
distance reconstructs no family containing `0` and `13` within `3/4`: the
fixed-map limit is `3`. -/
theorem no_fixed_map_reconstructs_scenes {C : Type*} (E : Encoding ℝ C)
    (h0 : (0 : ℝ) ∈ E.relevant) (h13 : (13 : ℝ) ∈ E.relevant)
    (hmap : LipschitzWith (1 / 2) (fun s => E.readout (E.encode s))) :
    ¬ E.Reconstructs (3 / 4) := by
  intro hrec
  have h := Encoding.dist_le_of_contracting_reconstructs (by norm_num) hmap hrec h0 h13
  norm_num [Real.dist_eq] at h

/-- **Each scene needs both codes.** The fibre of scene `0` holds two states
more than `2 · 3/4` apart, so the fibre bound asks for two codes and a bit has
exactly two. -/
theorem sceneBits_fibre_card :
    ({0, 3} : Finset ℝ).card ≤ Fintype.card Bool :=
  ConditionedEncoding.card_le_card_codes_fibre sceneBits_reconstructs (u := 0)
    (by
      intro s hs
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl <;>
        norm_num [ConditionedEncoding.fibre, sceneBits, sceneFamily, sceneOf])
    (by
      intro s hs t ht hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
        first | exact absurd rfl hne | norm_num [Real.dist_eq])

/-- **The stored-state shortcut fails here.** No encoder that writes one code for
every state, with any readout conditioned on the same scenes, reconstructs the
family within `3/4`. -/
theorem no_constant_code_reconstructs_scenes {C : Type*} (Enc : ConditionedEncoding ℝ ℝ C)
    (hrel : Enc.relevant = sceneFamily) (hin : Enc.input = sceneOf)
    (hE : ∀ s t, Enc.encode s = Enc.encode t) :
    ¬ Enc.Reconstructs (3 / 4) :=
  ConditionedEncoding.not_reconstructs_of_encode_const hE (s := 0) (t := 3)
    (by simp [hrel, sceneFamily]) (by simp [hrel, sceneFamily])
    (by norm_num [hin, sceneOf]) (by norm_num [Real.dist_eq])

/-- **The stored readout, where it works.** Keeping each scene's lower state
reconstructs the family of lower states exactly, with one code and a map that
ignores the state: every fibre is a single state. -/
theorem stored_lower_reconstructs :
    (ConditionedEncoding.storedReadout ({0, 10} : Set ℝ) sceneOf id).Reconstructs 0 := by
  rw [ConditionedEncoding.stored_reconstructs_iff]
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl <;> norm_num [sceneOf]

/-- **And where it does not.** On the four-state family the same readout has a
constant encoder, so it fails at `3/4`. -/
theorem stored_scenes_fails :
    ¬ (ConditionedEncoding.storedReadout sceneFamily sceneOf id).Reconstructs (3 / 4) :=
  no_constant_code_reconstructs_scenes _ rfl rfl (fun _ _ => rfl)

/-! ### Self-states that follow the scene

`sceneBits` contracts only on its family, so Banach's theorem does not apply to
it. The affine readout below reads the whole state as its code and halves every
distance on the line; it reconstructs the same four states within `3/4`. -/

/-- The affine readout: the code is the state, and the scene pulls it halfway. -/
noncomputable def sceneAffine : ConditionedEncoding ℝ ℝ ℝ where
  relevant := sceneFamily
  input := sceneOf
  encode := id
  readout := fun u c => (c + u) / 2 + 3 / 4

/-- The affine map halves every distance on the line. -/
theorem sceneAffine_contracting (u : ℝ) : ContractingWith (1 / 2) (sceneAffine.conditionedMap u) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun s t => ?_⟩
  simp only [ConditionedEncoding.conditionedMap, sceneAffine, id, Real.dist_eq]
  rw [show (s + u) / 2 + 3 / 4 - ((t + u) / 2 + 3 / 4) = (s - t) / 2 by ring, abs_div]
  norm_num
  linarith

/-- It reconstructs the same family within `3/4`. -/
theorem sceneAffine_reconstructs : sceneAffine.Reconstructs (3 / 4) := by
  intro s hs
  rcases sceneFamily_cases hs with rfl | rfl | rfl | rfl <;>
    norm_num [ConditionedEncoding.error, ConditionedEncoding.conditionedMap, sceneAffine, sceneOf,
      Real.dist_eq, abs_le]

/-- The self-state for scene `u` is `u + 3/2`. -/
theorem sceneAffine_selfState (u : ℝ) :
    sceneAffine.selfState sceneAffine_contracting u = u + 3 / 2 := by
  symm
  apply (sceneAffine_contracting u).fixedPoint_unique
  show sceneAffine.conditionedMap u (u + 3 / 2) = u + 3 / 2
  simp only [ConditionedEncoding.conditionedMap, sceneAffine, id]
  ring

/-- **The self-states move with the scene.** Scene `10`'s self-state is `10`
from scene `0`'s, and the library bound, with the scene gain `1/2`, allows
`(1/2) · 10 / (1 - 1/2) = 10`: attained. -/
theorem sceneAffine_selfState_dist :
    dist (sceneAffine.selfState sceneAffine_contracting 0)
        (sceneAffine.selfState sceneAffine_contracting 10) =
      ((1 / 2 : ℝ≥0) : ℝ) * dist (0 : ℝ) 10 / (1 - ((1 / 2 : ℝ≥0) : ℝ)) := by
  rw [sceneAffine_selfState, sceneAffine_selfState]
  norm_num [Real.dist_eq]

/-- The same bound, from the library theorem rather than computed. -/
theorem sceneAffine_selfState_le (u v : ℝ) :
    dist (sceneAffine.selfState sceneAffine_contracting u)
        (sceneAffine.selfState sceneAffine_contracting v) ≤
      ((1 / 2 : ℝ≥0) : ℝ) * dist u v / (1 - ((1 / 2 : ℝ≥0) : ℝ)) := by
  apply ConditionedEncoding.dist_selfState_le
  intro u v s
  simp only [ConditionedEncoding.conditionedMap, sceneAffine, id, Real.dist_eq]
  rw [show (s + u) / 2 + 3 / 4 - ((s + v) / 2 + 3 / 4) = (u - v) / 2 by ring, abs_div]
  norm_num
  linarith

/-- Each member lies within `(3/4) / (1 - 1/2) = 3/2` of its scene's self-state;
the lower member of each scene is exactly that far. -/
theorem sceneAffine_member_near_selfState {s : ℝ} (hs : s ∈ sceneFamily) :
    dist s (sceneAffine.selfState sceneAffine_contracting (sceneOf s)) ≤
      3 / 4 / (1 - ((1 / 2 : ℝ≥0) : ℝ)) :=
  ConditionedEncoding.dist_selfState_input_le (Enc := sceneAffine) sceneAffine_contracting
    sceneAffine_reconstructs hs

end Examples
end PhysicsOfConsciousness
