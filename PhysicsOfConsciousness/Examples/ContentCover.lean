/-
  Examples/ContentCover.lean — two regions that describe one variable

  §37, for `Phase5_ContentCover.lean`. Three content variables, two regions.
  Region `0` reads variables `0` and `1`, region `1` reads `1` and `2`, and
  each decodes variable `1` with an offset of `b`, in opposite directions.
  At tolerance `b < 1/2` the decodability cover is `{0, 1}` and `{1, 2}`: it
  covers, its nerve is connected, and neither region can decode the variable it
  does not read, with any decoder. With no offset the regions glue exactly, and
  the glued section is the true content. At `b = 1/10` the two decodes of the
  shared variable differ by exactly `2/10`, so the compatibility the cover
  delivers is attained, and for that reason no exact global section exists.
  Equal weights on the shared variable cancel the two offsets, so the selection
  is the true content. At tolerance zero that cover no longer covers.
-/

import PhysicsOfConsciousness.Phase5_ContentCover

open CategoryTheory TopologicalSpace Opposite
open scoped NNReal

namespace PhysicsOfConsciousness
namespace Examples

open PhysicsOfConsciousness.ContentCover

/-! ## 37. The decodability cover of two regions -/

/-- What each region reads: two of the three variables. -/
abbrev TwoReads : Fin 2 → Type := fun _ => ℝ × ℝ

/-- Region `0` reads variables `0, 1`; region `1` reads `1, 2`. Region `0`
reports variable `1` high by `b` and region `1` reports it low by `b`. -/
noncomputable def twoRegions (b : ℝ) : DecodingSetup (Fin 3 → ℝ) TwoReads (Fin 3) where
  relevant := Set.univ
  value := fun v s => s v
  read := fun i s => if i = 0 then (s 0, s 1) else (s 1, s 2)
  dec := fun i v r =>
    if i = 0 then (if v = 0 then r.1 else if v = 1 then r.2 + b else 0)
    else (if v = 1 then r.1 - b else if v = 2 then r.2 else 0)

private theorem twoRegions_decode_zero (b : ℝ) (s : Fin 3 → ℝ) :
    (twoRegions b).decode 0 0 s = s 0 ∧ (twoRegions b).decode 0 1 s = s 1 + b := by
  simp [DecodingSetup.decode, twoRegions]

private theorem twoRegions_decode_one (b : ℝ) (s : Fin 3 → ℝ) :
    (twoRegions b).decode 1 1 s = s 1 - b ∧ (twoRegions b).decode 1 2 s = s 2 := by
  simp [DecodingSetup.decode, twoRegions]

/-- A state that differs from zero only at one variable. -/
private noncomputable def bump (v : Fin 3) : Fin 3 → ℝ := Pi.single v 1

section Offset

variable {b : ℝ} (hb : 0 ≤ b) (hb' : b < 1 / 2)
include hb

private theorem zero_mem_domain_zero : (0 : Fin 3) ∈ (twoRegions b).domain b 0 := by
  intro s _
  rw [(twoRegions_decode_zero b s).1]
  simp [twoRegions, hb]

private theorem one_mem_domain_zero : (1 : Fin 3) ∈ (twoRegions b).domain b 0 := by
  intro s _
  rw [(twoRegions_decode_zero b s).2]
  simp [twoRegions, abs_of_nonneg hb]

private theorem one_mem_domain_one : (1 : Fin 3) ∈ (twoRegions b).domain b 1 := by
  intro s _
  rw [(twoRegions_decode_one b s).1]
  simp [twoRegions, abs_of_nonneg hb]

private theorem two_mem_domain_one : (2 : Fin 3) ∈ (twoRegions b).domain b 1 := by
  intro s _
  rw [(twoRegions_decode_one b s).2]
  simp [twoRegions, hb]

omit hb in
include hb' in
/-- **Region `0` cannot decode variable `2`, with any decoder.** It reads the
zero state and `bump 2` identically, and they differ by `1` there. -/
theorem two_not_mem_domain_zero : (2 : Fin 3) ∉ (twoRegions b).domain b 0 :=
  DecodingSetup.not_decodes_of_read_eq (s := 0) (t := bump 2) (Set.mem_univ _)
    (Set.mem_univ _) (by simp [twoRegions, bump]) (by norm_num [twoRegions, bump]; linarith)

omit hb in
include hb' in
/-- **Region `1` cannot decode variable `0`, with any decoder.** -/
theorem zero_not_mem_domain_one : (0 : Fin 3) ∉ (twoRegions b).domain b 1 :=
  DecodingSetup.not_decodes_of_read_eq (s := 0) (t := bump 0) (Set.mem_univ _)
    (Set.mem_univ _) (by simp [twoRegions, bump]) (by norm_num [twoRegions, bump]; linarith)

include hb' in
/-- **Region `0` decodes exactly `{0, 1}`.** -/
theorem twoRegions_domain_zero : (twoRegions b).domain b 0 = {0, 1} := by
  ext v
  fin_cases v <;>
    simp [zero_mem_domain_zero hb, one_mem_domain_zero hb, two_not_mem_domain_zero hb']

include hb' in
/-- **Region `1` decodes exactly `{1, 2}`.** -/
theorem twoRegions_domain_one : (twoRegions b).domain b 1 = {1, 2} := by
  ext v
  fin_cases v <;>
    simp [zero_not_mem_domain_one hb', one_mem_domain_one hb, two_mem_domain_one hb]

/-- **The cover covers.** Every variable is decoded by some region, so the
content base is the union of the domains. -/
theorem twoRegions_covers : iSup (domainOpen (twoRegions b) b) = ⊤ := by
  refine eq_top_iff.2 fun v _ => Opens.mem_iSup.2 ?_
  fin_cases v
  · exact ⟨0, zero_mem_domain_zero hb⟩
  · exact ⟨0, one_mem_domain_zero hb⟩
  · exact ⟨1, two_mem_domain_one hb⟩

include hb' in
/-- **The regions overlap on the shared variable**, so the nerve of the cover is
connected. -/
theorem twoRegions_overlap : (twoRegions b).domain b 0 ∩ (twoRegions b).domain b 1 = {1} := by
  rw [twoRegions_domain_zero hb hb', twoRegions_domain_one hb hb']
  ext v
  fin_cases v <;> simp

end Offset

/-- **Exact gluing, where the decoders are exact.** With no offset the cover at
tolerance zero is the same cover, and the section the regions glue to is the
true content: `decode_glue_value` on this setup. -/
theorem twoRegions_exact_glue (s : Fin 3 → ℝ) (g : (contentPresheaf (Fin 3)).obj (op ⊤))
    (hg : ∀ i, (contentPresheaf (Fin 3)).map
      (homOfLE (le_top : domainOpen (twoRegions 0) 0 i ≤ ⊤)).op g =
        regionSection (twoRegions 0) 0 s i) :
    g = fun v => s v.1 :=
  decode_glue_value (twoRegions 0) (Set.mem_univ s)
    (twoRegions_covers le_rfl) g hg

/-- The offset used below. -/
noncomputable def θ₃₇ : ℝ := 1 / 10

private theorem θ₃₇_nonneg : 0 ≤ θ₃₇ := by norm_num [θ₃₇]
private theorem θ₃₇_lt : θ₃₇ < 1 / 2 := by norm_num [θ₃₇]

/-- **Compatibility at `2θ` is attained.** At every state the two decodes of
the shared variable differ by exactly `2/10`, which is `decode_compatible`'s
bound with equality. -/
theorem twoRegions_disagreement (s : Fin 3 → ℝ) :
    |(twoRegions θ₃₇).decode 0 1 s - (twoRegions θ₃₇).decode 1 1 s| = 2 * θ₃₇ := by
  rw [(twoRegions_decode_zero θ₃₇ s).2, (twoRegions_decode_one θ₃₇ s).1]
  norm_num [θ₃₇, abs_of_pos]

/-- **So there is no exact global section.** No assignment of values to the
three variables restricts to both regions' decodes. -/
theorem twoRegions_no_exact_glue (s : Fin 3 → ℝ) :
    ¬ ∃ g : Fin 3 → ℝ, ∀ i, ∀ v ∈ (twoRegions θ₃₇).domain θ₃₇ i, g v = (twoRegions θ₃₇).decode i v s := by
  rintro ⟨g, hg⟩
  have h0 := hg 0 1 (by simp [twoRegions_domain_zero θ₃₇_nonneg θ₃₇_lt])
  have h1 := hg 1 1 (by simp [twoRegions_domain_one θ₃₇_nonneg θ₃₇_lt])
  have h := twoRegions_disagreement s
  rw [← h0, ← h1, sub_self, abs_zero] at h
  norm_num [θ₃₇] at h

/-- Weights subordinate to the cover: each region alone where it alone decodes,
and half each on the shared variable. -/
noncomputable def twoWeights : Fin 2 → Fin 3 → ℝ≥0 := fun i v =>
  if v = 1 then 1 / 2 else if i = 0 then (if v = 0 then 1 else 0) else (if v = 2 then 1 else 0)

/-- They are a partition subordinate to the cover. -/
theorem twoWeights_partition :
    ApproximateGluing.IsPartition ((twoRegions θ₃₇).domain θ₃₇) twoWeights := by
  refine ⟨fun i v hv => ?_, fun v => ?_⟩
  · fin_cases i <;> fin_cases v <;>
      simp_all [twoWeights, twoRegions_domain_zero θ₃₇_nonneg θ₃₇_lt,
        twoRegions_domain_one θ₃₇_nonneg θ₃₇_lt]
  · fin_cases v <;> simp [twoWeights, Fin.sum_univ_two]

/-- **The selection is within `θ` of the content**, by the library theorem. -/
theorem twoRegions_select_near (s : Fin 3 → ℝ) (v : Fin 3) :
    |select twoWeights (fun i v => (twoRegions θ₃₇).decode i v s) v - s v| ≤ θ₃₇ :=
  DecodingSetup.select_decode_near_value twoWeights_partition trivial v

/-- **Here it is exactly the content.** The two offsets on the shared variable
cancel under equal weights. The library bound is `θ`; this cover does better
because its errors are opposite, which is a fact about these decoders. -/
theorem twoRegions_select_exact (s : Fin 3 → ℝ) :
    select twoWeights (fun i v => (twoRegions θ₃₇).decode i v s) = s := by
  funext v
  fin_cases v
  all_goals simp [select, twoWeights, Fin.sum_univ_two, DecodingSetup.decode, twoRegions]
  ring

/-- **At tolerance zero the cover does not cover.** Neither region decodes the
shared variable exactly, so exact gluing (`decode_glue_value`) has nothing to
apply to on this setup. -/
theorem twoRegions_zero_uncovered : (1 : Fin 3) ∉ (twoRegions θ₃₇).domain 0 0 ∪ (twoRegions θ₃₇).domain 0 1 := by
  rintro (h | h)
  · have := h 0 trivial
    rw [(twoRegions_decode_zero θ₃₇ 0).2] at this
    norm_num [twoRegions, θ₃₇] at this
  · have := h 0 trivial
    rw [(twoRegions_decode_one θ₃₇ 0).1] at this
    norm_num [twoRegions, θ₃₇] at this

end Examples
end PhysicsOfConsciousness
