import PhysicsOfConsciousness.Phase10_PhysicalUnity

/-!
# Examples/PhysicalUnity.lean — both sides of the margin theorem are inhabited

§38. Two regions, one real micro quantity each.

* **A bit.** Region 0's quantity against the threshold 0. The readout takes
  both values, so the margin is not the margin of a constant map, and at a
  state off the threshold `not_physicallyEnforced_of_bits` applies under the
  identity dynamics.
* **A diffusive pair.** Each region moves a quarter of the way toward the
  other. Region 1's content, its own quantity, depends on region 0's micro
  state at every scale, and the discrepancy `|y 0 − y 1|` halves in one step,
  so agreement between them is physically enforced at every state. The
  definition is therefore not empty, and what excludes the bit is its margin,
  not the definition.
* **A category of an enforced carrier.** The sign of region 1's quantity under
  the diffusive pair has a margin, so it does not depend gradedly on region 0
  off its boundary, although the quantity it is read from is physically
  enforced there. Categorical contents fail graded dependence in any substrate;
  the carrier is what the premise asks about.
* **On the threshold.** At `![0, 0]` the bit does depend gradedly on region 0,
  so `exists_threshold_of_gradedDependence` has instances.
* **The leakage scale is sharp.** At `![1, 0]`, a unit away from the threshold
  with unit Lipschitz constants, `bits_eq_of_lipschitz` leaves the bit fixed
  under every change of region 0 smaller than `1`, and the change of exactly `1`
  to `![0, 0]` flips it.
* **The noisy response bound is attained.** Noise `ω : Bool` pulls region 0
  down by one on `true`, under any noise law `μ`. At `![1, 0]` with `δ = 1`
  the error set is `{true}`, and changing region 0 to `3/2`, half the margin
  width away, raises the probability that the bit reads `true` by exactly
  `μ {true}`, so `bits_law_le_of_lipschitz` cannot be sharpened.
* **One system at the noise floor.** Without noise, a change of either region
  of the diffusive pair moves both next quantities, so every change at a
  positive scale has response `1`, and the pair is one system in the sense of
  `SameSystem` for every noise scale and every yardstick up to `1`.
* **P over carriers is inhabited and strictly weaker.** The diffusive pair, one
  carrier per region, satisfies `EnforcedByCarriers`. A third carrier that
  keeps its own quantity joins region 1: the carrier form still holds, since
  carriers 0 and 1 reach each other, while the universal form fails, since the
  spare carrier's content ignores carrier 0 at every scale.
* **A record joins nothing.** Under `tally`, region 1 carries the mean of regions
  0 and 2, so its carrier moves with every change of either, and its content is
  the bit "that mean is positive". At `![2, 0, 2]` the bit has a margin of radius
  `1` with error rate `0`, every region admits a change above the noise `1/4`
  inside it, and `sameSystem_iff_eq_of_record` makes the record one system only
  with itself, at the yardstick `1/2`, although it reads both graded regions.
* **Write-back adds no link.** Under `writeBack` the rule writes the record's
  symbol into region 2. Region 2's next content reaches region 0 only through the
  record, so `not_coupledAtNoiseFloor_of_factors` leaves regions 0 and 2
  uncoupled; a change of region 0 that carries the record across its threshold
  does move region 2, so the route exists and only symbols travel along it.
* **A graded reader joins.** Under `noisyLin readerW` with uniform noise on
  `[0, 1]`, region 1 reads regions 0 and 2 and they read it back, with no weight
  between 0 and 2. A change of one noise amplitude `1/2` moves a read quantity by
  `1/2` in total variation, so regions 0 and 2 are each coupled to the reader at
  the yardstick `1/2`, are not coupled to each other, and are one system through
  it.
-/

open Filter Topology

namespace PhysicsOfConsciousness.PhysicalUnity.Examples

/-- Two regions with one real micro quantity each. -/
abbrev Pair := Fin 2 → ℝ

/-- The bit "region 0's quantity is positive". -/
noncomputable def bit (y : Pair) : Bool := decide ((0 : ℝ) < y 0)

theorem bit_nonconstant : bit ![1, 0] ≠ bit ![-1, 0] := by
  simp [bit]

/-- The bit is not physically enforced at `![1, 0]`, under the identity dynamics
and for any discrepancy. -/
theorem bit_not_physicallyEnforced (i : Fin 2) (disc : Pair → ℝ) :
    ¬ PhysicallyEnforced (S := fun _ : Fin 2 => ℝ) id (fun y (_ : Unit) => bit y) i disc
      ![1, 0] :=
  not_physicallyEnforced_of_bits (κ := Unit) continuous_id (fun _ => continuous_apply 0)
    (fun _ => 0) (by simp) i disc

/-- Each region moves a quarter of the way toward the other. -/
noncomputable def diffuse (y : Pair) : Pair := ![y 0 + (y 1 - y 0) / 4, y 1 + (y 0 - y 1) / 4]

theorem diffuse_gradedDependence (x : Pair) :
    GradedDependence (S := fun _ : Fin 2 => ℝ) diffuse (fun y => y 1) 0 x := by
  intro h
  have h' : ∀ᶠ s in 𝓝[≠] (x 0), _ := nhdsWithin_le_nhds h
  obtain ⟨s, hs, hne⟩ := (h'.and self_mem_nhdsWithin).exists
  simp [diffuse] at hs
  exact hne hs

theorem diffuse_contracts (x : Pair) :
    Contracts (S := fun _ : Fin 2 => ℝ) diffuse (fun y => |y 0 - y 1|) x := by
  refine ⟨1 / 2, by norm_num, Eventually.of_forall fun y => le_of_eq ?_⟩
  have : diffuse y 0 - diffuse y 1 = (y 0 - y 1) / 2 := by
    simp [diffuse]; ring
  show |diffuse y 0 - diffuse y 1| = 1 / 2 * |y 0 - y 1|
  rw [this, abs_div, abs_two]; ring

theorem diffuse_physicallyEnforced (x : Pair) :
    PhysicallyEnforced (S := fun _ : Fin 2 => ℝ) diffuse (fun y => y 1) 0
      (fun y => |y 0 - y 1|) x :=
  ⟨diffuse_gradedDependence x, diffuse_contracts x⟩

/-- **A category read from an enforced carrier.** Region 1's quantity is
physically enforced under `diffuse` at every state, yet the category "region 1's
quantity is positive" read from it does not depend gradedly on region 0 at
`![0, 1]`, whose successor puts that quantity at `3/4`. -/
theorem category_of_enforced_carrier :
    ¬ GradedDependence (S := fun _ : Fin 2 => ℝ) diffuse^[1]
        (fun y => (fun w : Unit → Bool => w ()) fun _ => decide ((0 : ℝ) < y 1)) 0
        ![0, 1] := by
  have hd : Continuous diffuse := by
    refine continuous_pi fun j : Fin 2 => ?_
    fin_cases j <;> simp [diffuse] <;> fun_prop
  exact not_gradedDependence_iterate_of_bits (κ := Unit) hd
    (fun _ => continuous_apply (1 : Fin 2)) (fun _ => 0) (fun w => w ()) (x := ![0, 1]) 1
    (fun _ => by norm_num [diffuse]) 0

/-- Under `diffuse`, changing either region moves either region's next quantity:
a change of region `i` by `s − x i` moves region `j` by `3/4` or `1/4` of it. -/
theorem diffuse_update_ne (x : Pair) (i j : Fin 2) {s : ℝ} (hs : s ≠ x i) :
    diffuse (Function.update x i s) j ≠ diffuse x j := by
  fin_cases i <;> fin_cases j <;> simp [diffuse, Function.update] at hs ⊢ <;> intro h <;>
    exact hs (by linarith)

open MeasureTheory in
/-- Without noise, a dynamics under which every change of carrier `i` moves carrier
`j`'s next quantity makes `j` depend gradedly above noise on `i`, with response
`1`, for every positive noise. -/
theorem gradedAboveNoise_dirac {ι : Type*} [DecidableEq ι] {g : (ι → ℝ) → ι → ℝ}
    {x : ι → ℝ} {i j : ι} {σ Θ : ℝ} (hσ : 0 < σ)
    (hg : ∀ s, s ≠ x i → g (Function.update x i s) j ≠ g x j) :
    GradedAboveNoise (S := fun _ : ι => ℝ) (Measure.dirac ()) (fun _ : Unit => g)
      (fun y => y j) x i σ Θ 1 := by
  intro s hs _
  have hne : s ≠ x i := fun h => by
    have := hσ.trans_le hs; simp [h] at this
  refine le_iSup_of_le {g (Function.update x i s) j} ?_
  have h1 : {ω : Unit | g (Function.update x i s) j ∈
      ({g (Function.update x i s) j} : Set ℝ)} = Set.univ := by ext; simp
  have h0 : {ω : Unit | g x j ∈ ({g (Function.update x i s) j} : Set ℝ)} = ∅ := by
    ext; simpa using (hg s hne).symm
  rw [h1, h0]; simp

open MeasureTheory in
/-- **The diffusive pair is one system at the noise floor.** Without noise, every
change of either region at any positive scale moves the other's quantity with
certainty, so the response is `1`, the pair is coupled for every noise `σ > 0`
and yardstick `θ ≤ 1`, and its two regions are one system. -/
theorem diffuse_sameSystem (x : Pair) {σ Θ : Fin 2 → ℝ} (hσ : ∀ i, 0 < σ i) :
    SameSystem (S := fun _ : Fin 2 => ℝ) (Measure.dirac ()) (fun _ : Unit => diffuse)
      (fun j y => y j) x σ Θ 1 0 1 :=
  .rel _ _ ⟨gradedAboveNoise_dirac (hσ 0) fun _ hs => diffuse_update_ne x 0 1 hs,
    gradedAboveNoise_dirac (hσ 1) fun _ hs => diffuse_update_ne x 1 0 hs⟩

open MeasureTheory in
/-- **P over carriers is inhabited.** With one carrier per region, the diffusive
pair satisfies it for every positive noise. -/
theorem diffuse_enforcedByCarriers (x : Pair) {σ Θ : Fin 2 → ℝ} (hσ : ∀ i, 0 < σ i) :
    EnforcedByCarriers (S := fun _ : Fin 2 => ℝ) id (· ≠ ·) (Measure.dirac ())
      (fun _ : Unit => diffuse) (fun j y => y j) x σ Θ 1 :=
  fun a b _ => ⟨a, b, rfl, rfl, gradedAboveNoise_dirac (hσ a) fun _ hs => diffuse_update_ne x a b hs⟩

/-- Three carriers: the diffusive pair, and a spare carrier that keeps its value. -/
abbrev Triple := Fin 3 → ℝ

/-- Carriers 0 and 1 diffuse toward each other; carrier 2 is left alone. -/
noncomputable def spare (y : Triple) : Triple :=
  ![y 0 + (y 1 - y 0) / 4, y 1 + (y 0 - y 1) / 4, y 2]

/-- Carrier 0 is region 0; carriers 1 and 2 are region 1. -/
def spareRegion : Fin 3 → Fin 2 := ![0, 1, 1]

theorem spare_update_ne (x : Triple) {i j : Fin 3} (hi : i ≠ 2) (hj : j ≠ 2) {s : ℝ}
    (hs : s ≠ x i) : spare (Function.update x i s) j ≠ spare x j := by
  fin_cases i <;> fin_cases j <;> simp [spare, Function.update] at hi hj hs ⊢ <;> intro h <;>
    exact hs (by linarith)

open MeasureTheory in
/-- The spare carrier's content does not depend above noise on carrier 0: a unit
change of carrier 0 leaves it exactly where it was. -/
theorem spare_not_gradedAboveNoise (x : Triple) :
    ¬ GradedAboveNoise (S := fun _ : Fin 3 => ℝ) (Measure.dirac ()) (fun _ : Unit => spare)
      (fun y => y 2) x 0 1 2 1 := by
  intro h
  have hr := h (x 0 + 1) (by simp) (by norm_num [Real.dist_eq])
  have hfix : spare (Function.update x 0 (x 0 + 1)) 2 = spare x 2 := by simp [spare]
  simp [shiftResponse, hfix] at hr

open MeasureTheory in
/-- **P over carriers holds** for the spare triple: carriers 0 and 1 join the two
regions in both directions. -/
theorem spare_enforcedByCarriers (x : Triple) :
    EnforcedByCarriers (S := fun _ : Fin 3 => ℝ) spareRegion (· ≠ ·) (Measure.dirac ())
      (fun _ : Unit => spare) (fun j y => y j) x (fun _ => 1) (fun _ => 2) 1 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab
  · exact ⟨0, 1, rfl, rfl, gradedAboveNoise_dirac one_pos fun _ hs =>
      spare_update_ne x (by decide) (by decide) hs⟩
  · exact ⟨1, 0, rfl, rfl, gradedAboveNoise_dirac one_pos fun _ hs =>
      spare_update_ne x (by decide) (by decide) hs⟩

open MeasureTheory in
/-- **The universal form fails** for the same triple: the spare carrier belongs to a
region that overlaps carrier 0's, and ignores carrier 0. So P over carriers is
strictly weaker than P over every carrier. -/
theorem spare_not_enforcedAtNoiseFloor (x : Triple) :
    ¬ EnforcedAtNoiseFloor (S := fun _ : Fin 3 => ℝ)
      (fun i j => spareRegion i ≠ spareRegion j) (Measure.dirac ()) (fun _ : Unit => spare)
      (fun j y => y j) x (fun _ => 1) (fun _ => 2) 1 :=
  fun h => spare_not_gradedAboveNoise x (h 0 2 (by simp [spareRegion]))

/-- On its threshold the bit depends gradedly on region 0. -/
theorem bit_gradedDependence_at_threshold :
    GradedDependence (S := fun _ : Fin 2 => ℝ) id (fun y (_ : Unit) => bit y) 0 ![0, 0] := by
  intro h
  have h' : ∀ᶠ s in 𝓝[>] (0 : ℝ), _ := nhdsWithin_le_nhds h
  obtain ⟨s, hs, hpos⟩ := (h'.and self_mem_nhdsWithin).exists
  have := congrFun hs ()
  simp [bit] at this
  exact absurd hpos (not_lt.mpr this)

/-- Below the unit margin width the bit does not move. -/
theorem bit_eq_of_small (s : ℝ) (hs : dist s 1 < 1) :
    bit (Function.update ![1, 0] 0 s) = bit ![1, 0] := by
  have h := bits_eq_of_lipschitz (κ := Unit) (S := fun _ : Fin 2 => ℝ) (f := id) (L := 1)
    LipschitzWith.id (v := fun _ y => y 0) (Lv := 1) (fun _ => LipschitzWith.eval 0)
    (by norm_num) (fun _ => 0) (δ := 1) (x := ![1, 0]) (fun _ => by simp) 0 s
    (by simpa using hs)
  exact congrFun h ()

/-- A change of exactly the margin width flips the bit. -/
theorem bit_flips_at_width : bit (Function.update ![1, 0] 0 0) ≠ bit ![1, 0] := by
  simp [bit]

/-- Noise that pulls region 0 down by one on `true`. -/
noncomputable def kick (ω : Bool) (y : Pair) : Pair := y - if ω then ![1, 0] else 0

theorem kick_lipschitz (ω : Bool) : LipschitzWith 1 (kick ω) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  simp [kick]

open MeasureTheory in
/-- At `![1, 0]` the error set for `δ = 1` is `{true}`. -/
theorem kick_error_set :
    {ω | ∃ _ : Unit, |kick ω ![1, 0] 0 - 0| < 1} = {true} := by
  ext ω; cases ω <;> simp [kick]

open MeasureTheory in
/-- The hypotheses of `bits_law_le_of_lipschitz` hold with error rate `μ {true}`. -/
theorem kick_bound (μ : Measure Bool) :
    μ {ω | bit (kick ω (Function.update ![1, 0] 0 (3 / 2))) = true} ≤
      μ {ω | bit (kick ω ![1, 0]) = true} + μ {true} :=
  (bits_law_le_of_lipschitz (κ := Unit) (S := fun _ : Fin 2 => ℝ) (f := kick) (L := 1)
    kick_lipschitz (v := fun _ y => y 0) (Lv := 1) (fun _ => LipschitzWith.eval 0)
    (by norm_num) (fun _ => 0) (fun w => w ()) (δ := 1) (x := ![1, 0])
    (by rw [kick_error_set]) 0 (3 / 2)
    (by norm_num [Real.dist_eq, abs_of_pos]) {true}).1

open MeasureTheory in
/-- **The error rate is attained.** Changing region 0 from `1` to `3/2`, within
the margin width `1`, raises the probability that the bit reads `true` by
exactly the error rate `μ {true}`, under every noise law. -/
theorem kick_attains (μ : Measure Bool) :
    μ {ω | bit (kick ω (Function.update ![1, 0] 0 (3 / 2))) = true} =
      μ {ω | bit (kick ω ![1, 0]) = true} + μ {true} := by
  have h1 : {ω | bit (kick ω (Function.update ![1, 0] 0 (3 / 2))) = true} = Set.univ := by
    ext ω; cases ω <;> norm_num [bit, kick]
  have h2 : {ω | bit (kick ω ![1, 0]) = true} = {false} := by
    ext ω; cases ω <;> simp [bit, kick]
  rw [h1, h2, ← measure_union (by simp) (measurableSet_singleton _)]
  congr 1; ext ω; cases ω <;> simp

open MeasureTheory

/-- Regions 0 and 2 keep their quantities; region 1 carries their mean. -/
noncomputable def tally (y : Triple) : Triple := ![y 0, (y 0 + y 2) / 2, y 2]

/-- Region 1's content is the bit "its quantity is positive", as `0` or `1`;
regions 0 and 2 read their own quantities. -/
noncomputable def tallyContent (j : Fin 3) (y : Triple) : ℝ :=
  if j = 1 then (if 0 < y 1 then 1 else 0) else y j

/-- `tally` moves no region further than the largest change it is given. -/
theorem tally_lipschitz : LipschitzWith 1 tally := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [NNReal.coe_one, one_mul]
  have h0 := dist_le_pi_dist y z 0
  have h2 := dist_le_pi_dist y z 2
  rw [Real.dist_eq] at h0 h2
  refine (dist_pi_le_iff dist_nonneg).mpr fun k => ?_
  rw [Real.dist_eq]
  fin_cases k
  · simpa [tally] using h0
  · simp only [tally]
    rw [abs_le] at h0 h2 ⊢
    constructor <;> simp <;> linarith [h0.1, h0.2, h2.1, h2.2]
  · simpa [tally] using h2

/-- The record's carrier reads region 0 gradedly: every change of region 0 moves it. -/
theorem tally_update_ne (x : Triple) {s : ℝ} (hs : s ≠ x 0) :
    tally (Function.update x 0 s) 1 ≠ tally x 1 := by
  simp [tally, Function.update]
  intro h; exact hs (by linarith)

/-- The record at `![2, 0, 2]` has a margin of radius `1` with error rate `0`. -/
theorem tally_marginRate :
    HasMarginRate (X := Triple) (Measure.dirac ()) (fun _ : Unit => tally ![2, 0, 2])
      (tallyContent 1) 1 0 := by
  have hset : {ω : Unit | ∃ y, dist y (tally ![2, 0, 2]) < 1 ∧
      tallyContent 1 y ≠ tallyContent 1 (tally ![2, 0, 2])} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun ω ⟨y, hy, hne⟩ => hne ?_
    have h1 := (dist_le_pi_dist y (tally ![2, 0, 2]) 1).trans_lt hy
    rw [Real.dist_eq, abs_lt] at h1
    have hpos : 0 < y 1 := by simp [tally] at h1; linarith [h1.1]
    simp [tallyContent, tally, hpos]
  unfold HasMarginRate
  rw [hset, measure_empty]

/-- **A record that reads two graded regions joins neither.** -/
theorem tally_sameSystem_iff (j : Fin 3) :
    SameSystem (S := fun _ : Fin 3 => ℝ) (Measure.dirac ()) (fun _ : Unit => tally)
      tallyContent ![2, 0, 2] (fun _ => 1 / 4) (fun _ => 1) (1 / 2) 1 j ↔ 1 = j := by
  refine sameSystem_iff_eq_of_record (fun _ => tally_lipschitz) tally_marginRate
    (ENNReal.half_pos one_ne_zero) (fun k _ => ⟨![2, 0, 2] k + 1 / 2, ?_⟩)
  norm_num [Real.dist_eq]

/-- **Write-back.** The rule writes the record's symbol into region 2, overwriting
its quantity: region 2's next content reaches region 0 only through the record. -/
noncomputable def writeBack (y : Triple) : Triple :=
  ![y 0, (y 0 + y 2) / 2, tallyContent 1 (tally y)]

/-- **Write-back through the record adds no link** between regions 0 and 2. -/
theorem writeBack_not_coupled :
    ¬ CoupledAtNoiseFloor (S := fun _ : Fin 3 => ℝ) (Measure.dirac ()) (fun _ : Unit => writeBack)
      tallyContent ![2, 0, 2] (fun _ => 1 / 4) (fun _ => 1) (1 / 2) 0 2 :=
  not_coupledAtNoiseFloor_of_factors (g := fun _ : Unit => tally) (fun _ => tally_lipschitz)
    tally_marginRate (ENNReal.half_pos one_ne_zero) (s := 5 / 2)
    (by norm_num [Real.dist_eq, abs_of_pos]) (by norm_num [Real.dist_eq, abs_of_pos])
    (by norm_num [Real.dist_eq, abs_of_pos])
    (fun _ h => by simpa [writeBack, tallyContent] using h)

/-- The route is real: a change of region 0 that carries the record across its
threshold changes region 2's next content. -/
theorem writeBack_moves_at_crossing :
    writeBack (Function.update ![2, 0, 2] 0 (-4)) 2 ≠ writeBack ![2, 0, 2] 2 := by
  have h2 : Function.update ![(2 : ℝ), 0, 2] 0 (-4) = ![-4, 0, 2] := by
    ext k; fin_cases k <;> rfl
  rw [h2]
  have ha : writeBack ![-4, 0, 2] 2 = 0 := by
    simp [writeBack, tallyContent, tally, Matrix.cons_val_two]; norm_num
  have hb : writeBack ![2, 0, 2] 2 = 1 := by
    simp [writeBack, tallyContent, tally, Matrix.cons_val_two]
  rw [ha, hb]; norm_num

/-- Uniform noise on `[0, 1]`. -/
noncomputable def unifDensity : ℝ → ENNReal := (Set.Icc (0 : ℝ) 1).indicator 1

/-- Uniform noise is Lebesgue measure on `[0, 1]`. -/
theorem withDensity_unifDensity :
    volume.withDensity unifDensity = volume.restrict (Set.Icc (0 : ℝ) 1) :=
  withDensity_indicator_one measurableSet_Icc

/-- Uniform noise is a probability law. -/
instance : IsProbabilityMeasure (volume.withDensity unifDensity) :=
  ⟨by rw [withDensity_unifDensity]; simp⟩

/-- The uniform density rises to its peak at `0`. -/
theorem unifDensity_up : MonotoneOn unifDensity (Set.Iic 0) := by
  intro a ha b hb hab
  rcases lt_or_eq_of_le (show a ≤ 0 from ha) with h | h
  · simp [unifDensity, Set.indicator_of_notMem (show a ∉ Set.Icc (0 : ℝ) 1 from fun h' => by
      linarith [h'.1])]
  · have : b = 0 := le_antisymm hb (h ▸ hab)
    subst this; subst h; rfl

/-- The uniform density falls after `0`. -/
theorem unifDensity_down : AntitoneOn unifDensity (Set.Ici 0) := by
  intro a ha b hb hab
  by_cases hb1 : b ≤ 1
  · have hbm : b ∈ Set.Icc (0 : ℝ) 1 := ⟨hb, hb1⟩
    have ham : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb1⟩
    simp [unifDensity, Set.indicator_of_mem hbm, Set.indicator_of_mem ham]
  · simp [unifDensity, Set.indicator_of_notMem (show b ∉ Set.Icc (0 : ℝ) 1 from fun h' =>
      hb1 h'.2)]

/-- A shift by `a ∈ [0, 1]` of uniform noise on `[0, 1]` raises the probability of
lying above the old top by `a`. -/
theorem unif_rise {m c : ℝ} (h1 : c - m ≤ 1) :
    ENNReal.ofReal (c - m) ≤ lawRise ((volume.withDensity unifDensity).map (m + ·))
      ((volume.withDensity unifDensity).map (c + ·)) := by
  refine le_iSup_of_le (Set.Ioi (m + 1)) ?_
  have hc : (c + ·) ⁻¹' Set.Ioi (m + 1) ∩ Set.Icc 0 1 = Set.Ioc (m + 1 - c) 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h, _, h'⟩; exact ⟨by linarith, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨by linarith, by linarith, h'⟩
  have hm : (m + ·) ⁻¹' Set.Ioi (m + 1) ∩ Set.Icc 0 1 = ∅ := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_Icc,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨h, _, h'⟩; linarith
  rw [map_add_apply, map_add_apply, withDensity_unifDensity,
    Measure.restrict_apply (measurableSet_Ioi.preimage (measurable_const_add c)),
    Measure.restrict_apply (measurableSet_Ioi.preimage (measurable_const_add m)), hc, hm,
    Real.volume_Ioc, measure_empty, tsub_zero]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

/-- Region 1 reads regions 0 and 2 and each of them reads region 1; regions 0 and 2
have no direct coupling. -/
def readerW : Fin 3 → Fin 3 → ℝ := ![![0, 1, 0], ![1, 0, 1], ![0, 1, 0]]

/-- Under `noisyLin readerW` with uniform noise, a change of one noise amplitude
`1/2` of region `i` moves region `j`'s next quantity by `1/2` when `readerW j i = 1`. -/
theorem reader_response_pos (x : Triple) {i j : Fin 3} (hW : readerW j i = 1) :
    (1 / 2 : ENNReal) ≤ shiftResponse (S := fun _ : Fin 3 => ℝ)
      (Measure.pi fun _ : Fin 3 => volume.withDensity unifDensity) (noisyLin readerW)
      (fun y => y j) x i (x i + 1 / 2) := by
  rw [shiftResponse_noisyLin]
  refine le_trans (le_of_eq ?_) (unif_rise (by rw [hW]; norm_num))
  rw [hW]; norm_num
  rw [← one_div, ENNReal.ofReal_div_of_pos two_pos]; simp

/-- With no weight from region `i` to region `j`, no change of `i` moves `j`. -/
theorem reader_response_zero (x : Triple) {i j : Fin 3} (hW : readerW j i = 0) (s : ℝ) :
    shiftResponse (S := fun _ : Fin 3 => ℝ)
      (Measure.pi fun _ : Fin 3 => volume.withDensity unifDensity) (noisyLin readerW)
      (fun y => y j) x i s = 0 := by
  rw [shiftResponse_noisyLin, hW]
  simp [lawRise]

/-- **A graded reader joins what a record cannot.** Under linear dynamics with
uniform noise, regions 0 and 2 are not coupled at the noise floor, each is coupled
to the reader, region 1, and so all three are one system. -/
theorem reader_sameSystem (x : Triple) :
    ¬ CoupledAtNoiseFloor (S := fun _ : Fin 3 => ℝ)
        (Measure.pi fun _ : Fin 3 => volume.withDensity unifDensity) (noisyLin readerW)
        (fun j y => y j) x (fun _ => 1 / 2) (fun _ => 1) (1 / 2) 0 2 ∧
      SameSystem (S := fun _ : Fin 3 => ℝ)
        (Measure.pi fun _ : Fin 3 => volume.withDensity unifDensity) (noisyLin readerW)
        (fun j y => y j) x (fun _ => 1 / 2) (fun _ => 1) (1 / 2) 0 2 := by
  have hc : ∀ i j : Fin 3, readerW j i = 1 → readerW i j = 1 →
      CoupledAtNoiseFloor (S := fun _ : Fin 3 => ℝ)
        (Measure.pi fun _ : Fin 3 => volume.withDensity unifDensity) (noisyLin readerW)
        (fun j y => y j) x (fun _ => 1 / 2) (fun _ => 1) (1 / 2) i j := fun i j hji hij =>
    (noisyLin_coupledAtNoiseFloor_iff readerW (fun _ => unifDensity_up)
      (fun _ => unifDensity_down) x (fun _ => by norm_num) (fun _ => by norm_num) i j).mpr
      ⟨reader_response_pos x hji, reader_response_pos x hij⟩
  refine ⟨fun h => ?_, .trans _ 1 _ (.rel _ _ (hc 0 1 rfl rfl)) (.rel _ _ (hc 1 2 rfl rfl))⟩
  have := h.1 (x 0 + 1 / 2) (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
  rw [reader_response_zero x rfl] at this
  exact absurd this (by norm_num)

end PhysicsOfConsciousness.PhysicalUnity.Examples
