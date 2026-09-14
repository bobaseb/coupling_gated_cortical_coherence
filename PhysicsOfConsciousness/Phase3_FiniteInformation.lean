import PhysicsOfConsciousness.Phase3_PredictiveThermodynamics

/-!
# Finite probability laws and the measure-theoretic information API

The conversion below lets finite thermodynamic path laws use exactly the
KL-based mutual information of `Phase3_PredictiveThermodynamics`. The divergence
bridge is proved for a strictly positive reference distribution: the real-valued
finite `KL` convention does not represent infinite divergence at a zero reference
mass. No thermodynamic identification is part of this bridge.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace PhysicsOfConsciousness.ProbDist

@[ext] theorem ext {V : Type*} [Fintype V] {P Q : ProbDist V} (h : P.p = Q.p) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

section Swap

variable {X S : Type*} [Fintype X] [Fintype S]

/-- Exchange the coordinates of the same joint law, without resampling. -/
def swap (P : ProbDist (X × S)) : ProbDist (S × X) where
  p z := P.p z.swap
  nonneg z := P.nonneg z.swap
  sum_one := by
    simp only [Fintype.sum_prod_type, Prod.swap_prod_mk]
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using P.sum_one

@[simp] theorem swap_swap (P : ProbDist (X × S)) : P.swap.swap = P := by
  apply ext
  rfl

/-- Relabelling preserves expectations when the observable is relabelled too. -/
theorem expect_swap (P : ProbDist (X × S)) (f : S × X → ℝ) :
    ∑ z, P.swap.p z * f z = ∑ z, P.p z * f z.swap := by
  simp only [swap, Fintype.sum_prod_type, Prod.swap_prod_mk]
  rw [Finset.sum_comm]

@[simp] theorem entropy_swap (P : ProbDist (X × S)) :
    shannon_entropy P.swap.p = shannon_entropy P.p := by
  unfold shannon_entropy
  rw [expect_swap]
  rfl

end Swap

section Bind

variable {U V : Type*} [Fintype U] [Fintype V]

/-- Sample from `P`, then from the channel `f` at the sampled point. The
intermediate value is marginalized out; a model that must retain it composes
the two laws explicitly instead. -/
noncomputable def bind (P : ProbDist U) (f : U → ProbDist V) : ProbDist V where
  p v := ∑ u, P.p u * (f u).p v
  nonneg v := Finset.sum_nonneg fun u _ => mul_nonneg (P.nonneg u) ((f u).nonneg v)
  sum_one := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ProbDist.sum_one, mul_one, P.sum_one]

@[simp] theorem bind_apply (P : ProbDist U) (f : U → ProbDist V) (v : V) :
    (P.bind f).p v = ∑ u, P.p u * (f u).p v := rfl

/-- A channel whose every output law is positive keeps `bind` positive, for any
input law on a nonempty domain. -/
theorem bind_pos [Nonempty U] (P : ProbDist U) (f : U → ProbDist V)
    (hP : ∀ u, 0 < P.p u) (hf : ∀ u v, 0 < (f u).p v) (v : V) : 0 < (P.bind f).p v :=
  Finset.sum_pos (fun u _ => mul_pos (hP u) (hf u v)) Finset.univ_nonempty

/-- The point mass at `v`. It is the update rule of a register that does not
change, so it is the frozen baseline rather than a physical relaxation. -/
def dirac [DecidableEq V] (v : V) : ProbDist V where
  p u := if u = v then 1 else 0
  nonneg u := by split <;> norm_num
  sum_one := by simp

@[simp] theorem dirac_apply [DecidableEq V] (v u : V) :
    (dirac v).p u = if u = v then 1 else 0 := rfl

/-- Two coordinates updated by unrelated channels in the same operation. A
product is the absence of a correlation written by that operation, not the
absence of correlation in the joint law it acts on. -/
noncomputable def prod (P : ProbDist U) (Q : ProbDist V) : ProbDist (U × V) where
  p z := P.p z.1 * Q.p z.2
  nonneg z := mul_nonneg (P.nonneg z.1) (Q.nonneg z.2)
  sum_one := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ProbDist.sum_one, mul_one, P.sum_one]

@[simp] theorem prod_apply (P : ProbDist U) (Q : ProbDist V) (z : U × V) :
    (P.prod Q).p z = P.p z.1 * Q.p z.2 := rfl

theorem prod_pos (P : ProbDist U) (Q : ProbDist V) (hP : ∀ u, 0 < P.p u)
    (hQ : ∀ v, 0 < Q.p v) (z : U × V) : 0 < (P.prod Q).p z :=
  mul_pos (hP z.1) (hQ z.2)

/-- A channel that ignores its input discards the input law. This is the
identity a frozen register's composite transition reduces to. -/
@[simp] theorem bind_const (P : ProbDist U) (Q : ProbDist V) :
    (P.bind fun _ => Q) = Q := by
  apply ext
  funext v
  simp only [bind_apply, ← Finset.sum_mul, P.sum_one, one_mul]

end Bind

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The probability measure with the specified finite real masses. -/
noncomputable def toMeasure (P : ProbDist V) : Measure V :=
  (PMF.ofFintype (fun v => ENNReal.ofReal (P.p v)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => P.nonneg v), P.sum_one]
    simp)).toMeasure

instance (P : ProbDist V) : IsProbabilityMeasure P.toMeasure := by
  unfold toMeasure
  infer_instance

@[simp] theorem toMeasure_singleton (P : ProbDist V) (v : V) :
    P.toMeasure {v} = ENNReal.ofReal (P.p v) := by
  exact PMF.toMeasure_apply_singleton _ v (measurableSet_singleton v)

@[simp] theorem toMeasure_real_singleton (P : ProbDist V) (v : V) :
    P.toMeasure.real {v} = P.p v := by
  simp [Measure.real, P.nonneg]

open scoped Classical in
theorem toMeasure_apply (P : ProbDist V) (s : Set V) :
    P.toMeasure s = ∑ v, if v ∈ s then ENNReal.ofReal (P.p v) else 0 := by
  classical
  unfold toMeasure
  rw [PMF.toMeasure_ofFintype_apply _ s (Set.to_countable s).measurableSet, tsum_fintype]
  rfl

open scoped Classical in
theorem map_singleton {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W]
    (P : ProbDist V) (f : V → W) (w : W) :
    P.toMeasure.map f {w} = ∑ v, if f v = w then ENNReal.ofReal (P.p v) else 0 := by
  classical
  rw [Measure.map_apply (measurable_of_countable f) (measurableSet_singleton w),
    toMeasure_apply]
  rfl

/-- Finite transition probabilities compose by the usual matrix product. -/
theorem comp_singleton {U W : Type*} [MeasurableSpace U] [MeasurableSpace W]
    [MeasurableSingletonClass W] (κ : Kernel U V) (η : Kernel V W) (u : U) (w : W) :
    (η ∘ₖ κ) u {w} = ∑ v, η v {w} * κ u {v} := by
  rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton w), lintegral_fintype]

theorem comp_measure_singleton {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W]
    (μ : Measure V) (κ : Kernel V W) (w : W) :
    (κ ∘ₘ μ) {w} = ∑ v, κ v {w} * μ {v} := by
  rw [Measure.bind_apply (measurableSet_singleton w) κ.measurable.aemeasurable,
    lintegral_fintype]

omit [Fintype V] [MeasurableSingletonClass V] in
theorem prod_singleton {U W : Type*} [MeasurableSpace U] [MeasurableSpace W]
    (κ : Kernel U V) (η : Kernel U W) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (u : U) (v : V) (w : W) :
    (κ ×ₖ η) u {(v, w)} = κ u {v} * η u {w} := by
  rw [Kernel.prod_apply, ← Set.singleton_prod_singleton, Measure.prod_prod]

/-- A finite family of distributions defines a normalized stochastic kernel. -/
noncomputable def kernel {U : Type*} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (P : U → ProbDist V) : Kernel U V where
  toFun u := (P u).toMeasure
  measurable' := measurable_of_countable _

instance {U : Type*} [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (P : U → ProbDist V) : IsMarkovKernel (kernel P) where
  isProbabilityMeasure u := by change IsProbabilityMeasure (P u).toMeasure; infer_instance

@[simp] theorem kernel_singleton {U : Type*} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (P : U → ProbDist V) (u : U) (v : V) :
    kernel P u {v} = ENNReal.ofReal ((P u).p v) := toMeasure_singleton _ _

theorem toMeasure_ac (P Q : ProbDist V) (hQ : ∀ v, 0 < Q.p v) :
    P.toMeasure ≪ Q.toMeasure := by
  intro s hs
  have hempty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hle := measure_mono (Set.singleton_subset_iff.mpr hv) (μ := Q.toMeasure)
    rw [toMeasure_singleton, hs] at hle
    exact (ENNReal.ofReal_pos.mpr (hQ v)).not_ge hle
  simp [hempty]

theorem rnDeriv_toMeasure (P Q : ProbDist V) (hQ : ∀ v, 0 < Q.p v) (v : V) :
    (P.toMeasure.rnDeriv Q.toMeasure v).toReal = P.p v / Q.p v := by
  have h := Measure.setLIntegral_rnDeriv (P.toMeasure_ac Q hQ) {v}
  rw [lintegral_singleton] at h
  have hr := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, toMeasure_singleton,
    ENNReal.toReal_ofReal (P.nonneg v), ENNReal.toReal_ofReal (Q.nonneg v)] at hr
  exact (eq_div_iff (hQ v).ne').mpr hr

/-- The finite KL calculation is the existing Mathlib KL calculation.
Strict reference positivity makes all likelihood ratios and conversions finite. -/
theorem KL_eq_klDiv (P Q : ProbDist V) (hQ : ∀ v, 0 < Q.p v) :
    KL P Q = (klDiv P.toMeasure Q.toMeasure).toReal := by
  have hint : Integrable (llr P.toMeasure Q.toMeasure) P.toMeasure := Integrable.of_finite
  have hi : (∫ v, llr P.toMeasure Q.toMeasure v ∂P.toMeasure) = KL P Q := by
    rw [integral_fintype hint]
    simp only [toMeasure_real_singleton, smul_eq_mul, llr, P.rnDeriv_toMeasure Q hQ]
    rfl
  rw [klDiv_of_ac_of_integrable (P.toMeasure_ac Q hQ) hint, hi]
  simp only [probReal_univ, add_sub_cancel_right]
  exact (ENNReal.toReal_ofReal (KL_nonneg P Q hQ)).symm

end PhysicsOfConsciousness.ProbDist

namespace PhysicsOfConsciousness

/-- On finite discrete spaces every joint probability law has finite mutual
information, even with zero atoms. The product of marginals dominates its support.
This discharges the finiteness conditions in the feedback identity's examples. -/
theorem mutualInfo_finite {X S : Type*} [Fintype X] [Fintype S]
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSingletonClass X]
    [MeasurableSingletonClass S] (μ : Measure (X × S)) [IsProbabilityMeasure μ] :
    mutualInfo μ ≠ ∞ := by
  apply klDiv_ne_top _ Integrable.of_finite
  intro s hs
  have hatom : ∀ z ∈ s, μ {z} = 0 := by
    intro z hz
    have hprod : (μ.fst.prod μ.snd) {z} = 0 :=
      measure_mono_null (Set.singleton_subset_iff.mpr hz) hs
    have heq : ({z} : Set (X × S)) = {z.1} ×ˢ {z.2} := by ext w; simp [Prod.ext_iff]
    rw [heq, Measure.prod_prod, mul_eq_zero] at hprod
    rcases hprod with hf | hg
    · apply measure_mono_null (μ := μ) (t := Prod.fst ⁻¹' {z.1})
      · intro w hw
        simpa only [Set.mem_singleton_iff, Set.mem_preimage] using
          congrArg Prod.fst (Set.mem_singleton_iff.mp hw)
      · simpa only [Measure.fst_apply (measurableSet_singleton z.1)] using hf
    · apply measure_mono_null (μ := μ) (t := Prod.snd ⁻¹' {z.2})
      · intro w hw
        simpa only [Set.mem_singleton_iff, Set.mem_preimage] using
          congrArg Prod.snd (Set.mem_singleton_iff.mp hw)
      · simpa only [Measure.snd_apply (measurableSet_singleton z.2)] using hg
  have hcover : s = ⋃ z : s, ({z.val} : Set (X × S)) := by ext z; simp
  rw [hcover]
  exact measure_iUnion_null fun z => hatom z.val z.property

end PhysicsOfConsciousness
