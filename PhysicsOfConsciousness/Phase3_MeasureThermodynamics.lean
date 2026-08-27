import Mathlib

namespace PhysicsOfConsciousness
open MeasureTheory

variable {M : Type*} [MeasurableSpace M]
variable (vol : Measure M)

def is_volume_preserving (phi : M → M) : Prop :=
  MeasurePreserving phi vol vol

def is_dissipative (phi : M → M) (S : Set M) (hS : MeasurableSet S) : Prop :=
  vol (phi '' S) < vol S

noncomputable def continuous_entropy (S : Set M) : ℝ :=
  Real.log (vol S).toReal

noncomputable def landauer_heat_bound (T : ℝ) (S_init S_final : Set M) : ℝ :=
  T * (continuous_entropy vol S_init - continuous_entropy vol S_final)

theorem dissipative_implies_heat (phi : M → M) (S : Set M) (hS : MeasurableSet S)
  (h_diss : is_dissipative vol phi S hS)
  (h_vol_pos : 0 < (vol S).toReal) (h_vol_fin : (vol S) ≠ ⊤)
  (h_vol_img_pos : 0 < (vol (phi '' S)).toReal)
  (T : ℝ) (hT : T > 0) :
  landauer_heat_bound vol T S (phi '' S) > 0 := by
  unfold landauer_heat_bound continuous_entropy
  have h1 : (vol (phi '' S)).toReal < (vol S).toReal := by
    exact (ENNReal.toReal_lt_toReal (lt_trans h_diss (lt_top_iff_ne_top.mpr h_vol_fin)).ne h_vol_fin).mpr h_diss
  have h2 : Real.log (vol (phi '' S)).toReal < Real.log (vol S).toReal := by
    exact Real.strictMonoOn_log h_vol_img_pos h_vol_pos h1
  have h3 : 0 < Real.log (vol S).toReal - Real.log (vol (phi '' S)).toReal := sub_pos.mpr h2
  exact mul_pos hT h3

end PhysicsOfConsciousness
