import Mathlib

/-!
# Phase 10 — the noise margin excludes graded cross-region dependence

The physical-unity premise asks more of a system than that its content-level
dynamics bring overlapping regions into agreement. A content-level dynamics that
contracts disagreement is computable, so a digital machine running a consensus
algorithm or a simulation of a coupled field has one. What the premise asks for
sits one level down: the content read out of one region must depend *gradedly*
on the micro state of another, so that sub-threshold changes there move it.

This module states that requirement and proves the fact that separates the two
kinds of substrate.

* **Micro state.** `X = ∀ i, S i`, one topological space of micro states per
  region; `f : X → X` is the micro dynamics, continuous as physical dynamics
  are; a content readout is any `π : X → C`.
* **`HasMargin π M`.** Every micro state in the operating set `M` has a
  neighbourhood on which `π` is constant. This is the noise margin digital
  engineering designs in, and it is stated *on* `M` deliberately: a readout
  that is locally constant everywhere on a connected micro-state space is
  constant, so the margin can only hold away from the switching thresholds, and
  a correctly operating machine keeps its states there.
* **`GradedDependence f π i x`.** No neighbourhood of `x i` leaves the content
  `π (f x)` unchanged when region `i` alone is moved within it.
* **`PhysicallyEnforced f π i disc x`.** Graded dependence together with
  contraction of the overlap discrepancy `disc` under every sufficiently small
  perturbation of the micro state, sub-threshold ones included.

The results:

* **`not_gradedDependence_of_margin`.** A continuous micro dynamics whose next
  state lies in a margin's operating set has no graded dependence there, of any
  region, whatever its content-level dynamics does.
* **`hasMargin_threshold`** and **`HasMargin.pi`.** A thresholded continuous
  quantity has a margin off its threshold, and a finite word of readouts with
  margins has a margin; together they discharge `HasMargin` for any readout
  built from bits, instead of assuming it.
* **`not_physicallyEnforced_of_bits`.** The composition: a content read as a
  finite word of thresholded continuous micro quantities is not physically
  enforced at any state whose successor keeps every bit off its threshold.

* **`exists_threshold_of_gradedDependence`.** Conversely, where such a
  content does depend gradedly on a region, some bit sits exactly on its
  threshold: leakage is confined to the switching set.
* **`GradedDependence.of_comp`** and **`not_gradedDependence_iterate_of_bits`**.
  A category read from a carrier depends gradedly only through the carrier, and
  no function of a bit word, at any number of steps, depends gradedly on any
  region. Categorical human contents have margins too; the premise is stated on
  their graded carriers, and a digital machine has none.
* **`content_eq_of_lipschitz`** and **`bits_eq_of_lipschitz`.** The metric
  form. A margin of radius `r` (`HasMarginRadius`) under an `L`-Lipschitz micro
  dynamics makes every change to one region smaller than `r / L` invisible in
  the next content; for bits read from `Lv`-Lipschitz quantities at least `δ`
  from their thresholds, the invisible scale is `δ / (L Lv)`. This is the size
  a physical influence must reach before it carries any of the content.

The theorems say nothing about which readouts cortex uses; that is the
empirical content of the premise. Non-vacuity of both sides — a thresholded
readout that is not constant, and a diffusively coupled pair whose content is
physically enforced — is `Examples/PhysicalUnity.lean`, with a bit on its
threshold that does depend gradedly and a perturbation of exactly the margin's
width that flips a bit, so the leakage scale cannot be enlarged.
-/

open Filter Topology

namespace PhysicsOfConsciousness.PhysicalUnity

variable {ι : Type*} [DecidableEq ι] {S : ι → Type*} [∀ i, TopologicalSpace (S i)]
  {C : Type*}

/-- A content readout has a noise margin on the operating set `M` when every
operating micro state has a neighbourhood on which the readout is constant. -/
def HasMargin {X : Type*} [TopologicalSpace X] (π : X → C) (M : Set X) : Prop :=
  ∀ x ∈ M, ∀ᶠ y in 𝓝 x, π y = π x

/-- The content read after one step depends gradedly on region `i` at `x`: no
neighbourhood of `x i` leaves it unchanged when region `i` alone is moved. -/
def GradedDependence (f : (∀ i, S i) → ∀ i, S i) (π : (∀ i, S i) → C) (i : ι)
    (x : ∀ i, S i) : Prop :=
  ¬ ∀ᶠ s in 𝓝 (x i), π (f (Function.update x i s)) = π (f x)

/-- The overlap discrepancy `disc` contracts under one step of `f`, uniformly
over a neighbourhood of `x`: every small perturbation, sub-threshold ones
included, is pulled back toward agreement. -/
def Contracts (f : (∀ i, S i) → ∀ i, S i) (disc : (∀ i, S i) → ℝ) (x : ∀ i, S i) :
    Prop :=
  ∃ κ < 1, ∀ᶠ y in 𝓝 x, disc (f y) ≤ κ * disc y

/-- Agreement is physically enforced at `x` when the content depends gradedly on
region `i` and the overlap discrepancy contracts near `x`. -/
def PhysicallyEnforced (f : (∀ i, S i) → ∀ i, S i) (π : (∀ i, S i) → C) (i : ι)
    (disc : (∀ i, S i) → ℝ) (x : ∀ i, S i) : Prop :=
  GradedDependence f π i x ∧ Contracts f disc x

/-- **The margin excludes graded dependence.** If the micro dynamics is
continuous and carries `x` into the operating set of a readout with a margin,
then moving any one region within some neighbourhood of its micro state leaves
the next content unchanged. The content-level dynamics plays no part. -/
theorem not_gradedDependence_of_margin {f : (∀ i, S i) → ∀ i, S i}
    {π : (∀ i, S i) → C} {M : Set (∀ i, S i)} (hf : Continuous f) (hπ : HasMargin π M)
    {x : ∀ i, S i} (hx : f x ∈ M) (i : ι) : ¬ GradedDependence f π i x := by
  have hline : Continuous fun s : S i => f (Function.update x i s) :=
    hf.comp (continuous_const.update i continuous_id)
  have htend : Tendsto (fun s : S i => f (Function.update x i s)) (𝓝 (x i)) (𝓝 (f x)) := by
    simpa [Function.update_eq_self] using hline.tendsto (x i)
  exact not_not.mpr (htend.eventually (hπ _ hx))

/-- The same obstruction for the stronger property. -/
theorem not_physicallyEnforced_of_margin {f : (∀ i, S i) → ∀ i, S i}
    {π : (∀ i, S i) → C} {M : Set (∀ i, S i)} (hf : Continuous f) (hπ : HasMargin π M)
    {x : ∀ i, S i} (hx : f x ∈ M) (i : ι) (disc : (∀ i, S i) → ℝ) :
    ¬ PhysicallyEnforced f π i disc x :=
  fun h => not_gradedDependence_of_margin hf hπ hx i h.1

/-- A bit read as "the continuous quantity `v` exceeds the threshold `c`" has a
margin on every micro state where `v` is off its threshold. -/
theorem hasMargin_threshold {X : Type*} [TopologicalSpace X] {v : X → ℝ}
    (hv : Continuous v) (c : ℝ) :
    HasMargin (fun x => decide (c < v x)) {x | v x ≠ c} := by
  intro x hx
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · filter_upwards [(isOpen_lt hv continuous_const).mem_nhds hlt] with y hy
    simp [not_lt.mpr hy.le, not_lt.mpr hlt.le]
  · filter_upwards [(isOpen_lt continuous_const hv).mem_nhds hgt] with y hy
    simp [hy, hgt]

/-- A finite word of readouts, each with a margin on `M`, has a margin on `M`. -/
theorem HasMargin.pi {X : Type*} [TopologicalSpace X] {κ : Type*} [Finite κ]
    {B : κ → Type*} {π : ∀ k, X → B k} {M : Set X} (h : ∀ k, HasMargin (π k) M) :
    HasMargin (fun x k => π k x) M := by
  intro x hx
  filter_upwards [eventually_all.mpr fun k => h k x hx] with y hy
  exact funext hy

/-- **Content read from bits is not physically enforced.** Let a content be the
word of finitely many bits, bit `k` being the continuous micro quantity `v k`
against its threshold `c k`. At any state whose successor under a continuous
micro dynamics keeps every bit off its threshold, no region's micro state
enters that content gradedly, so agreement in it is not physically enforced,
whatever discrepancy is measured and however the bits evolve logically. -/
theorem not_physicallyEnforced_of_bits {κ : Type*} [Finite κ]
    {f : (∀ i, S i) → ∀ i, S i} (hf : Continuous f) {v : κ → (∀ i, S i) → ℝ}
    (hv : ∀ k, Continuous (v k)) (c : κ → ℝ) {x : ∀ i, S i}
    (hx : ∀ k, v k (f x) ≠ c k) (i : ι) (disc : (∀ i, S i) → ℝ) :
    ¬ PhysicallyEnforced f (fun y k => decide (c k < v k y)) i disc x := by
  have hπ : HasMargin (fun y k => decide (c k < v k y)) {y | ∀ k, v k y ≠ c k} :=
    HasMargin.pi fun k y hy =>
      hasMargin_threshold (hv k) (c k) y (show v k y ≠ c k from hy k)
  exact not_physicallyEnforced_of_margin hf hπ hx i disc

/-- **Graded dependence of a bit word happens only on a threshold.** If the
content read as a finite word of thresholded continuous quantities depends
gradedly on some region at `x`, then some bit of the successor state sits
exactly on its threshold. Leakage into such a content is confined to the
switching set, which correct operation keeps its states off. -/
theorem exists_threshold_of_gradedDependence {κ : Type*} [Finite κ]
    {f : (∀ i, S i) → ∀ i, S i} (hf : Continuous f) {v : κ → (∀ i, S i) → ℝ}
    (hv : ∀ k, Continuous (v k)) (c : κ → ℝ) {x : ∀ i, S i} {i : ι}
    (h : GradedDependence f (fun y k => decide (c k < v k y)) i x) :
    ∃ k, v k (f x) = c k := by
  by_contra hx
  push Not at hx
  have hπ : HasMargin (fun y k => decide (c k < v k y)) {y | ∀ k, v k y ≠ c k} :=
    HasMargin.pi fun k y hy =>
      hasMargin_threshold (hv k) (c k) y (show v k y ≠ c k from hy k)
  exact not_gradedDependence_of_margin hf hπ hx i h

/-! ### Categories and their carriers

A categorical content, such as the dominant percept in binocular rivalry or an
argmax over decoded classes, is locally constant off its boundaries, in cortex as
in silicon, so the margin theorem denies it graded dependence wherever it
applies. The premise is therefore stated on the graded content variables from
which categories are read. The two results below make that restatement
non-vacuous on one side and closed on the other: a category depends gradedly
only through its carrier, and a digital machine has no graded carrier to offer,
because every variable it computes is a function of its bit word. -/

/-- A readout computed from a readout with a margin has the same margin. -/
theorem HasMargin.comp {X : Type*} [TopologicalSpace X] {D : Type*} {π : X → C}
    {M : Set X} (h : HasMargin π M) (q : C → D) : HasMargin (q ∘ π) M :=
  fun x hx => (h x hx).mono fun y hy => by simp [hy]

/-- **A category depends gradedly only through its carrier.** A content `q ∘ ρ`
read from a carrier `ρ` depends gradedly on a region only where the carrier
does. The converse fails wherever `q` has a margin: a category read from an
enforced graded carrier is locally constant off its boundaries. -/
theorem GradedDependence.of_comp {f : (∀ i, S i) → ∀ i, S i} {ρ : (∀ i, S i) → C}
    {D : Type*} {q : C → D} {i : ι} {x : ∀ i, S i}
    (h : GradedDependence f (q ∘ ρ) i x) : GradedDependence f ρ i x :=
  fun hρ => h (hρ.mono fun s hs => by simp [hs])

/-- **A bit word offers no graded carrier, at any delay.** Every variable a
digital machine computes, whether a number, a vector of numbers or a category,
is some function `q` of its bit word. At any state whose `n`-th successor keeps
every bit off its threshold, that variable after `n` steps depends gradedly on
no region. The graded quantities beneath the bits reach none of the machine's
contents, now or later. -/
theorem not_gradedDependence_iterate_of_bits {κ : Type*} [Finite κ]
    {f : (∀ i, S i) → ∀ i, S i} (hf : Continuous f) {v : κ → (∀ i, S i) → ℝ}
    (hv : ∀ k, Continuous (v k)) (c : κ → ℝ) {D : Type*} (q : (κ → Bool) → D)
    {x : ∀ i, S i} (n : ℕ) (hx : ∀ k, v k (f^[n] x) ≠ c k) (i : ι) :
    ¬ GradedDependence f^[n] (fun y => q fun k => decide (c k < v k y)) i x := by
  have hπ : HasMargin (fun y k => decide (c k < v k y)) {y | ∀ k, v k y ≠ c k} :=
    HasMargin.pi fun k y hy =>
      hasMargin_threshold (hv k) (c k) y (show v k y ≠ c k from hy k)
  exact not_gradedDependence_of_margin (hf.iterate n) (hπ.comp q) hx i

end PhysicsOfConsciousness.PhysicalUnity

/-! ## The margin's width

`HasMargin` says only that some neighbourhood is flat. Its metric form says how
wide the flat neighbourhood is, and with a Lipschitz micro dynamics that gives
the perturbation size below which one region's micro state provably moves no
content anywhere: the scale a leakage argument has to exceed. -/

namespace PhysicsOfConsciousness.PhysicalUnity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
  [∀ i, PseudoMetricSpace (S i)] {C : Type*}

/-- A readout has a margin of radius `r` on `M`: it is constant on the open ball
of radius `r` about every operating micro state. -/
def HasMarginRadius {X : Type*} [PseudoMetricSpace X] (π : X → C) (M : Set X) (r : ℝ) :
    Prop :=
  ∀ x ∈ M, ∀ y, dist y x < r → π y = π x

/-- A margin of positive radius is a margin. -/
theorem HasMarginRadius.hasMargin {X : Type*} [PseudoMetricSpace X] {π : X → C}
    {M : Set X} {r : ℝ} (h : HasMarginRadius π M r) (hr : 0 < r) : HasMargin π M :=
  fun x hx => Filter.mem_of_superset (Metric.ball_mem_nhds x hr) fun y hy => h x hx y hy

/-- A bit read from an `Lv`-Lipschitz quantity has a margin of radius `δ / Lv` on
the states at least `δ` from its threshold. -/
theorem hasMarginRadius_threshold {X : Type*} [PseudoMetricSpace X] {v : X → ℝ}
    {Lv : NNReal} (hv : LipschitzWith Lv v) (hLv : 0 < (Lv : ℝ)) (c δ : ℝ) :
    HasMarginRadius (fun x => decide (c < v x)) {x | δ ≤ |v x - c|} (δ / Lv) := by
  intro x hx y hy
  have hvy : |v y - v x| < δ := by
    have := hv.dist_le_mul y x
    rw [Real.dist_eq] at this
    calc |v y - v x| ≤ Lv * dist y x := this
      _ < Lv * (δ / Lv) := mul_lt_mul_of_pos_left hy hLv
      _ = δ := by field_simp
  simp only [Set.mem_ofPred_eq] at hx
  rw [abs_lt] at hvy
  rcases le_abs'.mp hx with h | h
  · simp only [decide_eq_decide]
    constructor <;> intro <;> linarith
  · simp only [decide_eq_decide]
    constructor <;> intro <;> linarith

/-- A finite word of readouts with margins of radius `r` has a margin of radius
`r`. -/
theorem HasMarginRadius.pi {X : Type*} [PseudoMetricSpace X] {κ : Type*} {B : κ → Type*}
    {π : ∀ k, X → B k} {M : Set X} {r : ℝ} (h : ∀ k, HasMarginRadius (π k) M r) :
    HasMarginRadius (fun x k => π k x) M r :=
  fun x hx y hy => funext fun k => h k x hx y hy

lemma dist_update_le (x : ∀ i, S i) (i : ι) (s : S i) :
    dist (Function.update x i s) x ≤ dist s (x i) := by
  refine (dist_pi_le_iff dist_nonneg).mpr fun j => ?_
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

/-- **Below the margin's width, one region moves no content.** If the micro
dynamics is `L`-Lipschitz and carries `x` into the operating set of a readout
with a margin of radius `r`, then changing region `i` alone by less than `r / L`
leaves the next content exactly as it was. -/
theorem content_eq_of_lipschitz {f : (∀ i, S i) → ∀ i, S i} {L : NNReal}
    (hf : LipschitzWith L f) {π : (∀ i, S i) → C} {M : Set (∀ i, S i)} {r : ℝ}
    (hπ : HasMarginRadius π M r) {x : ∀ i, S i} (hx : f x ∈ M) (i : ι) (s : S i)
    (hs : L * dist s (x i) < r) : π (f (Function.update x i s)) = π (f x) :=
  hπ _ hx _ ((hf.dist_le_mul _ _).trans_lt
    ((mul_le_mul_of_nonneg_left (dist_update_le x i s) L.coe_nonneg).trans_lt hs))

/-- **The leakage scale of a bit word.** Let the content be a finite word of
bits, bit `k` the `Lv`-Lipschitz micro quantity `v k` against the threshold
`c k`, and let every bit of the successor state be at least `δ` from its
threshold. Under an `L`-Lipschitz micro dynamics, a change to one region smaller
than `δ / (L Lv)` changes no bit. A physical influence on such a content that
does not reach that size carries none of it. -/
theorem bits_eq_of_lipschitz {κ : Type*} {f : (∀ i, S i) → ∀ i, S i} {L : NNReal}
    (hf : LipschitzWith L f) {v : κ → (∀ i, S i) → ℝ} {Lv : NNReal}
    (hv : ∀ k, LipschitzWith Lv (v k)) (hLv : 0 < (Lv : ℝ)) (c : κ → ℝ) {δ : ℝ}
    {x : ∀ i, S i} (hx : ∀ k, δ ≤ |v k (f x) - c k|) (i : ι) (s : S i)
    (hs : L * dist s (x i) < δ / Lv) :
    (fun k => decide (c k < v k (f (Function.update x i s)))) =
      fun k => decide (c k < v k (f x)) := by
  have hπ : HasMarginRadius (fun y k => decide (c k < v k y))
      {y | ∀ k, δ ≤ |v k y - c k|} (δ / Lv) :=
    HasMarginRadius.pi fun k y hy z hz =>
      hasMarginRadius_threshold (hv k) hLv (c k) δ y (show δ ≤ |v k y - c k| from hy k) z hz
  exact content_eq_of_lipschitz hf hπ hx i s hs

end PhysicsOfConsciousness.PhysicalUnity

/-! ## The margin under noise

A physical gate is noisy. Thermal fluctuation makes its flip probability a
smooth, nowhere-zero function of its input, so the *law* of a digital machine's
next content does depend on every region's micro state, however weakly. The
results below bound that dependence by the machine's error rate.

Micro noise enters as a random map: a noise realisation `ω`, drawn from `μ`,
fixes the step `f ω`. Every Markov kernel on a standard Borel space has such a
representation, additive noise being the familiar case, and an `n`-step
trajectory of `L`-Lipschitz random maps is again a random map, with constant
`L ^ n`. Probabilities are taken of arbitrary sets, as outer measure, so no
measurability of the readout is assumed.

* **`HasMarginRate μ F π r ε`.** Outside a set of noise realisations of
  probability at most `ε`, the readout is constant on the ball of radius `r`
  about the noisy state `F ω`. With `μ` a point mass and `ε = 0` this is
  `HasMarginRadius` at one state.
* **`content_ne_le_of_marginRate`.** Under `L`-Lipschitz random steps, a change
  to one region smaller than `r / L` changes the next content with probability
  at most `ε`, both states driven by the same noise.
* **`law_le_of_marginRate`.** Hence the probability of every event of contents
  moves by at most `ε`: the total-variation response of the next content to the
  change is bounded by the error rate.
* **`bits_law_le_of_lipschitz`.** For any variable computed from a bit word,
  `ε` is the probability that some bit of the successor lands within `δ` of its
  threshold, and the scale is `δ / (L Lv)`.

The bound is attained: `Examples/PhysicalUnity.lean` exhibits a noisy bit whose
response to a sub-margin change equals its error rate exactly. -/

namespace PhysicsOfConsciousness.PhysicalUnity

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
  [∀ i, PseudoMetricSpace (S i)] {C : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- A readout has a margin of radius `r` with error rate `ε` along the noisy state
`F`: outside a set of noise of probability at most `ε`, it is constant on the
ball of radius `r` about `F ω`. -/
def HasMarginRate {X : Type*} [PseudoMetricSpace X] (μ : Measure Ω) (F : Ω → X)
    (π : X → C) (r : ℝ) (ε : ENNReal) : Prop :=
  μ {ω | ∃ y, dist y (F ω) < r ∧ π y ≠ π (F ω)} ≤ ε

/-- A margin of radius `r` on `M` is a margin with error rate the probability of
leaving `M`. -/
theorem HasMarginRadius.hasMarginRate {X : Type*} [PseudoMetricSpace X] {π : X → C}
    {M : Set X} {r : ℝ} (h : HasMarginRadius π M r) (μ : Measure Ω) (F : Ω → X) :
    HasMarginRate μ F π r (μ {ω | F ω ∉ M}) :=
  measure_mono fun _ hω => by
    obtain ⟨y, hy, hne⟩ := hω
    exact fun hM => hne (h _ hM y hy)

/-- **Below the margin's width, one region changes the content only on the error
set.** Driven by the same noise, a state and its copy with region `i` changed by
less than `r / L` read the same next content outside a set of probability at
most `ε`. -/
theorem content_ne_le_of_marginRate {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i}
    {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω)) {π : (∀ i, S i) → C} {r : ℝ}
    {ε : ENNReal} {x : ∀ i, S i} (hπ : HasMarginRate μ (fun ω => f ω x) π r ε) (i : ι)
    (s : S i) (hs : L * dist s (x i) < r) :
    μ {ω | π (f ω (Function.update x i s)) ≠ π (f ω x)} ≤ ε :=
  (measure_mono fun ω (hω : π (f ω (Function.update x i s)) ≠ π (f ω x)) =>
    show ∃ y, dist y (f ω x) < r ∧ π y ≠ π (f ω x) from ⟨_, ((hf ω).dist_le_mul _ _).trans_lt
      ((mul_le_mul_of_nonneg_left (dist_update_le x i s) L.coe_nonneg).trans_lt hs), hω⟩).trans hπ

/-- **The response of a noisy content is bounded by its error rate.** Under
`L`-Lipschitz random steps and a margin of radius `r` with error rate `ε`, a
change to region `i` smaller than `r / L` moves the probability of every event
of next contents by at most `ε`, in either direction. -/
theorem law_le_of_marginRate {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i}
    {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω)) {π : (∀ i, S i) → C} {r : ℝ}
    {ε : ENNReal} {x : ∀ i, S i} (hπ : HasMarginRate μ (fun ω => f ω x) π r ε) (i : ι)
    (s : S i) (hs : L * dist s (x i) < r) (A : Set C) :
    μ {ω | π (f ω (Function.update x i s)) ∈ A} ≤ μ {ω | π (f ω x) ∈ A} + ε ∧
      μ {ω | π (f ω x) ∈ A} ≤ μ {ω | π (f ω (Function.update x i s)) ∈ A} + ε := by
  have hne := content_ne_le_of_marginRate hf hπ i s hs
  constructor
  · calc μ {ω | π (f ω (Function.update x i s)) ∈ A}
        ≤ μ ({ω | π (f ω x) ∈ A} ∪ {ω | π (f ω (Function.update x i s)) ≠ π (f ω x)}) :=
          measure_mono fun ω hω => by
            by_cases h : π (f ω (Function.update x i s)) = π (f ω x)
            · exact Or.inl (show π (f ω x) ∈ A from h ▸ hω)
            · exact Or.inr h
      _ ≤ _ := (measure_union_le _ _).trans (by gcongr)
  · calc μ {ω | π (f ω x) ∈ A}
        ≤ μ ({ω | π (f ω (Function.update x i s)) ∈ A} ∪
            {ω | π (f ω (Function.update x i s)) ≠ π (f ω x)}) :=
          measure_mono fun ω hω => by
            by_cases h : π (f ω (Function.update x i s)) = π (f ω x)
            · exact Or.inl (show π (f ω (Function.update x i s)) ∈ A from h ▸ hω)
            · exact Or.inr h
      _ ≤ _ := (measure_union_le _ _).trans (by gcongr)

/-- **The response of anything computed from noisy bits.** Let bit `k` be the
`Lv`-Lipschitz micro quantity `v k` against the threshold `c k`, let `q` be any
function of the bit word, and let `ε` bound the probability that some bit of the
noisy successor lands within `δ` of its threshold. Under `L`-Lipschitz random
steps, a change to one region smaller than `δ / (L Lv)` moves the probability of
every event of `q` by at most `ε`. -/
theorem bits_law_le_of_lipschitz {κ : Type*} {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {v : κ → (∀ i, S i) → ℝ} {Lv : NNReal} (hv : ∀ k, LipschitzWith Lv (v k))
    (hLv : 0 < (Lv : ℝ)) (c : κ → ℝ) {D : Type*} (q : (κ → Bool) → D) {δ : ℝ}
    {x : ∀ i, S i} {ε : ENNReal} (hε : μ {ω | ∃ k, |v k (f ω x) - c k| < δ} ≤ ε)
    (i : ι) (s : S i) (hs : L * dist s (x i) < δ / Lv) (A : Set D) :
    μ {ω | q (fun k => decide (c k < v k (f ω (Function.update x i s)))) ∈ A} ≤
        μ {ω | q (fun k => decide (c k < v k (f ω x))) ∈ A} + ε ∧
      μ {ω | q (fun k => decide (c k < v k (f ω x))) ∈ A} ≤
        μ {ω | q (fun k => decide (c k < v k (f ω (Function.update x i s)))) ∈ A} + ε := by
  have hπ : HasMarginRadius (fun y k => decide (c k < v k y))
      {y | ∀ k, δ ≤ |v k y - c k|} (δ / Lv) :=
    HasMarginRadius.pi fun k y hy z hz =>
      hasMarginRadius_threshold (hv k) hLv (c k) δ y (show δ ≤ |v k y - c k| from hy k) z hz
  have hq : HasMarginRadius (fun y => q fun k => decide (c k < v k y))
      {y | ∀ k, δ ≤ |v k y - c k|} (δ / Lv) :=
    fun y hy z hz => congrArg q (hπ y hy z hz)
  refine law_le_of_marginRate hf (((hq.hasMarginRate μ _)).trans
    ((measure_mono fun ω hω => ?_).trans hε)) i s hs A
  simpa [not_le] using hω

end PhysicsOfConsciousness.PhysicalUnity

/-! ## Counting systems at the noise floor

Physics counts parts as one system when their states interact, and at the noise
floor the scale of that interaction is set by the parts themselves: a change of
a region smaller than its own noise `σ i` is erased by the region's own
fluctuations, and a change it does hold moves another region's content only if
it moves the content's law by at least the fluctuation yardstick `θ`. This
section states that criterion and proves it is the noise-floor reading of graded
dependence, one pair of overlapping regions at a time.

* **`shiftResponse`** and **`response`.** The response of a content to one
  change of region `i`, the largest rise it makes in the probability of an event
  of next contents, and its supremum over changes of size at most `η`.
  `response_mono`: the response grows with the scale.
* **`GradedAboveNoise μ f π x i σ Θ θ`.** Every change of region `i` larger than
  `σ` and smaller than `Θ` moves `π` by at least `θ`.
  `GradedAboveNoise.le_response`: the response then reaches `θ` at every scale
  that admits such a change.
  `gradedAboveNoise_iff_of_mono`: where the response grows with the change, the
  criterion is decided by one change of the size of the noise; the Gaussian
  carrier below is such a case.
* **`CoupledAtNoiseFloor`** and **`SameSystem`.** Two regions are coupled when
  each one's changes above its noise move the other's content by at least `θ`;
  one system is the equivalence closure of coupling.
* **`enforcedAtNoiseFloor_iff`.** For a symmetric overlap relation, P's
  noise-floor reading — graded dependence above noise of each region's content
  on every region it overlaps — holds exactly when every overlapping pair is
  coupled; so overlapping regions whose agreement P admits are one system
  (`EnforcedAtNoiseFloor.sameSystem`).
* **`shiftResponse_le_of_marginRate`**, **`response_le_of_marginRate`** and
  **`sameSystem_iff_eq_of_bits`.** Under the noisy margin, the response below the
  margin's width is at most the error rate. A machine whose contents are read
  from bits with error rate below `θ`, and whose regions admit a change above
  their noise within the margin, couples no pair, so each region is a system of
  its own; P then fails at any overlap of two distinct regions
  (`not_enforcedAtNoiseFloor_of_bits`).
-/

namespace PhysicsOfConsciousness.PhysicalUnity

open MeasureTheory

variable {ι : Type*} [DecidableEq ι] {S : ι → Type*}
  [∀ i, PseudoMetricSpace (S i)] {C : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- The response of the content `π` to replacing region `i`'s micro state by `s`:
the largest rise, over events of next contents, in their probability. Probability
is outer measure, as in `HasMarginRate`. Under a probability law, for a next
content that is measurable in the noise and takes countably many values, it is
the total-variation distance between the two laws of the next content. -/
noncomputable def shiftResponse (μ : Measure Ω) (f : Ω → (∀ i, S i) → ∀ i, S i)
    (π : (∀ i, S i) → C) (x : ∀ i, S i) (i : ι) (s : S i) : ENNReal :=
  ⨆ A : Set C, μ {ω | π (f ω (Function.update x i s)) ∈ A} - μ {ω | π (f ω x) ∈ A}

/-- The response of `π` to region `i` at scale `η`: the largest response to a
change of region `i` of size at most `η`. -/
noncomputable def response (μ : Measure Ω) (f : Ω → (∀ i, S i) → ∀ i, S i)
    (π : (∀ i, S i) → C) (x : ∀ i, S i) (i : ι) (η : ℝ) : ENNReal :=
  ⨆ (s : S i) (_ : dist s (x i) ≤ η), shiftResponse μ f π x i s

/-- The response grows with the scale. -/
theorem response_mono (μ : Measure Ω) (f : Ω → (∀ i, S i) → ∀ i, S i)
    (π : (∀ i, S i) → C) (x : ∀ i, S i) (i : ι) : Monotone (response μ f π x i) :=
  fun _ _ h => iSup₂_mono' fun s hs => ⟨s, hs.trans h, le_rfl⟩

/-- **Graded dependence above the noise floor.** Every change of region `i` larger
than its noise `σ` and smaller than `Θ`, the change that crosses a threshold,
moves the content `π` by at least the fluctuation yardstick `θ`. -/
def GradedAboveNoise (μ : Measure Ω) (f : Ω → (∀ i, S i) → ∀ i, S i)
    (π : (∀ i, S i) → C) (x : ∀ i, S i) (i : ι) (σ Θ : ℝ) (θ : ENNReal) : Prop :=
  ∀ s : S i, σ ≤ dist s (x i) → dist s (x i) < Θ → θ ≤ shiftResponse μ f π x i s

/-- Graded dependence above noise makes the response reach `θ` at every scale
reached by a change above noise and below `Θ`, and so, by `response_mono`, at
every larger scale. -/
theorem GradedAboveNoise.le_response {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i}
    {π : (∀ i, S i) → C} {x : ∀ i, S i} {i : ι} {σ Θ : ℝ} {θ : ENNReal}
    (h : GradedAboveNoise μ f π x i σ Θ θ) {s : S i} (hσ : σ ≤ dist s (x i))
    (hΘ : dist s (x i) < Θ) {η : ℝ} (hη : dist s (x i) ≤ η) : θ ≤ response μ f π x i η :=
  (h s hσ hΘ).trans (le_iSup₂_of_le (f := fun s (_ : dist s (x i) ≤ η) =>
    shiftResponse μ f π x i s) s hη le_rfl)

/-- **Where the response grows with the change, P is decided at the noise.** If a
larger change of region `i` never moves the content less than a smaller one, and
some change has size exactly the noise `σ`, then graded dependence above the
noise floor holds exactly when that change moves the content by at least `θ`. -/
theorem gradedAboveNoise_iff_of_mono {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i}
    {π : (∀ i, S i) → C} {x : ∀ i, S i} {i : ι} {σ Θ : ℝ} {θ : ENNReal}
    (hmono : ∀ s t : S i, dist s (x i) ≤ dist t (x i) →
      shiftResponse μ f π x i s ≤ shiftResponse μ f π x i t)
    {s₀ : S i} (hs₀ : dist s₀ (x i) = σ) (hσΘ : σ < Θ) :
    GradedAboveNoise μ f π x i σ Θ θ ↔ θ ≤ shiftResponse μ f π x i s₀ :=
  ⟨fun h => h s₀ hs₀.ge (hs₀ ▸ hσΘ), fun h s hs _ => h.trans (hmono s₀ s (hs₀ ▸ hs))⟩

/-- **Coupling at the noise floor.** Regions `i` and `j`, with contents `π i` and
`π j`, noises `σ` and threshold-crossing changes `Θ`, are coupled when every
change of either one above its noise moves the other's content by at least `θ`. -/
def CoupledAtNoiseFloor (μ : Measure Ω) (f : Ω → (∀ i, S i) → ∀ i, S i)
    (π : ι → (∀ i, S i) → C) (x : ∀ i, S i) (σ Θ : ι → ℝ) (θ : ENNReal) (i j : ι) : Prop :=
  GradedAboveNoise μ f (π j) x i (σ i) (Θ i) θ ∧ GradedAboveNoise μ f (π i) x j (σ j) (Θ j) θ

/-- Regions are one system when a chain of couplings at the noise floor joins them. -/
def SameSystem (μ : Measure Ω) (f : Ω → (∀ i, S i) → ∀ i, S i) (π : ι → (∀ i, S i) → C)
    (x : ∀ i, S i) (σ Θ : ι → ℝ) (θ : ENNReal) : ι → ι → Prop :=
  Relation.EqvGen (CoupledAtNoiseFloor μ f π x σ Θ θ)

/-- **P at the noise floor.** For every pair `O i j` of overlapping regions, the
content of `j` depends gradedly above noise on region `i`. -/
def EnforcedAtNoiseFloor (O : ι → ι → Prop) (μ : Measure Ω)
    (f : Ω → (∀ i, S i) → ∀ i, S i) (π : ι → (∀ i, S i) → C) (x : ∀ i, S i)
    (σ Θ : ι → ℝ) (θ : ENNReal) : Prop :=
  ∀ i j, O i j → GradedAboveNoise μ f (π j) x i (σ i) (Θ i) θ

/-- **P's noise-floor reading is the one-system criterion.** For a symmetric
overlap relation, graded dependence above noise of each region's content on
every region it overlaps holds exactly when every overlapping pair is coupled
at the noise floor. -/
theorem enforcedAtNoiseFloor_iff {O : ι → ι → Prop} (hO : ∀ i j, O i j → O j i) {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {π : ι → (∀ i, S i) → C} {x : ∀ i, S i}
    {σ Θ : ι → ℝ} {θ : ENNReal} :
    EnforcedAtNoiseFloor O μ f π x σ Θ θ ↔
      ∀ i j, O i j → CoupledAtNoiseFloor μ f π x σ Θ θ i j :=
  ⟨fun h i j hij => ⟨h i j hij, h j i (hO i j hij)⟩, fun h i j hij => (h i j hij).1⟩

/-- Regions whose overlap P admits at the noise floor are one system. -/
theorem EnforcedAtNoiseFloor.sameSystem {O : ι → ι → Prop} (hO : ∀ i j, O i j → O j i)
    {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i} {π : ι → (∀ i, S i) → C}
    {x : ∀ i, S i} {σ Θ : ι → ℝ} {θ : ENNReal} (h : EnforcedAtNoiseFloor O μ f π x σ Θ θ)
    {i j : ι} (hij : O i j) : SameSystem μ f π x σ Θ θ i j :=
  .rel _ _ ((enforcedAtNoiseFloor_iff hO).mp h i j hij)

/-- With no coupled pair, each region is a system of its own. -/
theorem sameSystem_iff_eq_of_forall_not_coupled {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {π : ι → (∀ i, S i) → C} {x : ∀ i, S i}
    {σ Θ : ι → ℝ} {θ : ENNReal} (h : ∀ i j, ¬ CoupledAtNoiseFloor μ f π x σ Θ θ i j)
    {i j : ι} : SameSystem μ f π x σ Θ θ i j ↔ i = j := by
  refine ⟨fun hs => ?_, fun hij => hij ▸ .refl _⟩
  induction hs with
  | rel a b hab => exact absurd hab (h a b)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Below the margin's width the response is at most the error rate.** -/
theorem shiftResponse_le_of_marginRate [Fintype ι] {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i}
    {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω)) {π : (∀ i, S i) → C} {r : ℝ}
    {ε : ENNReal} {x : ∀ i, S i} (hπ : HasMarginRate μ (fun ω => f ω x) π r ε) (i : ι)
    (s : S i) (hs : L * dist s (x i) < r) : shiftResponse μ f π x i s ≤ ε :=
  iSup_le fun A => tsub_le_iff_left.mpr (law_le_of_marginRate hf hπ i s hs A).1

/-- The response at any scale `η` with `L η < r` is at most the error rate. -/
theorem response_le_of_marginRate [Fintype ι] {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i}
    {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω)) {π : (∀ i, S i) → C} {r : ℝ}
    {ε : ENNReal} {x : ∀ i, S i} (hπ : HasMarginRate μ (fun ω => f ω x) π r ε) (i : ι)
    {η : ℝ} (hη : L * η < r) : response μ f π x i η ≤ ε :=
  iSup₂_le fun s hs => shiftResponse_le_of_marginRate hf hπ i s
    ((mul_le_mul_of_nonneg_left hs L.coe_nonneg).trans_lt hη)

/-- The finite-difference nudge signal at a positive scale `η` is the response
divided by that scale. This defines a local signal, not a learning update or an
objective gradient. -/
noncomputable def nudgeSignal (μ : Measure Ω) (f : Ω → (∀ i, S i) → ∀ i, S i)
    (π : (∀ i, S i) → C) (x : ∀ i, S i) (i : ι) (η : ℝ) : ENNReal :=
  response μ f π x i η / ENNReal.ofReal η

/-- Below a noisy readout's margin, its finite-difference nudge signal is at
most the error rate divided by the nudge size. At zero error rate the signal
vanishes. This does not establish a nonzero signal for a graded substrate or
the gradient identity of equilibrium propagation. -/
theorem nudgeSignal_le_of_marginRate [Fintype ι] {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal}
    (hf : ∀ ω, LipschitzWith L (f ω)) {π : (∀ i, S i) → C} {r : ℝ}
    {ε : ENNReal} {x : ∀ i, S i} (hπ : HasMarginRate μ (fun ω => f ω x) π r ε)
    (i : ι) {η : ℝ} (_hpos : 0 < η) (hη : L * η < r) :
    nudgeSignal μ f π x i η ≤ ε / ENNReal.ofReal η := by
  unfold nudgeSignal
  gcongr
  exact response_le_of_marginRate hf hπ i hη

/-- **A bit word is as many systems as it has regions.** Let every region's
content be a function `q j` of one word of bits, bit `k` the `Lv`-Lipschitz micro
quantity `v k` against the threshold `c k`, and let the error rate `ε`, the
probability that some bit of the noisy successor lands within `δ` of its
threshold, be below the yardstick `θ`. If every region admits a change above its
noise and below its threshold-crossing change that stays within the margin's
width `δ / (L Lv)`, then no two regions are coupled at the noise floor, and
regions are one system only with themselves. -/
theorem sameSystem_iff_eq_of_bits [Fintype ι] {κ : Type*} {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {v : κ → (∀ i, S i) → ℝ} {Lv : NNReal} (hv : ∀ k, LipschitzWith Lv (v k))
    (hLv : 0 < (Lv : ℝ)) (c : κ → ℝ) (q : ι → (κ → Bool) → C) {δ : ℝ}
    {x : ∀ i, S i} {ε θ : ENNReal} (hε : μ {ω | ∃ k, |v k (f ω x) - c k| < δ} ≤ ε)
    (hεθ : ε < θ) {σ Θ : ι → ℝ}
    (hs : ∀ i, ∃ s : S i, σ i ≤ dist s (x i) ∧ dist s (x i) < Θ i ∧
      L * dist s (x i) < δ / Lv) {i j : ι} :
    SameSystem μ f (fun j y => q j fun k => decide (c k < v k y)) x σ Θ θ i j ↔ i = j := by
  refine sameSystem_iff_eq_of_forall_not_coupled fun i j hij => ?_
  obtain ⟨s, hσ, hΘ, hr⟩ := hs i
  refine (hεθ.trans_le (hij.1 s hσ hΘ)).not_ge (iSup_le fun A => tsub_le_iff_left.mpr ?_)
  exact (bits_law_le_of_lipschitz hf hv hLv c (q j) hε i s hr A).1

/-- **A bit word fails P at any overlap of two regions.** Under the hypotheses of
`sameSystem_iff_eq_of_bits`, P at the noise floor fails for every symmetric
overlap relation that joins two distinct regions. -/
theorem not_enforcedAtNoiseFloor_of_bits [Fintype ι] {κ : Type*} {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {v : κ → (∀ i, S i) → ℝ} {Lv : NNReal} (hv : ∀ k, LipschitzWith Lv (v k))
    (hLv : 0 < (Lv : ℝ)) (c : κ → ℝ) (q : ι → (κ → Bool) → C) {δ : ℝ}
    {x : ∀ i, S i} {ε θ : ENNReal} (hε : μ {ω | ∃ k, |v k (f ω x) - c k| < δ} ≤ ε)
    (hεθ : ε < θ) {σ Θ : ι → ℝ}
    (hs : ∀ i, ∃ s : S i, σ i ≤ dist s (x i) ∧ dist s (x i) < Θ i ∧
      L * dist s (x i) < δ / Lv) {O : ι → ι → Prop} (hO : ∀ i j, O i j → O j i) {i j : ι}
    (hij : O i j) (hne : i ≠ j) :
    ¬ EnforcedAtNoiseFloor O μ f (fun j y => q j fun k => decide (c k < v k y)) x σ Θ θ :=
  fun h => hne ((sameSystem_iff_eq_of_bits hf hv hLv c q hε hεθ hs).mp (h.sameSystem hO hij))

end PhysicsOfConsciousness.PhysicalUnity

/-! ## Records and readers

A rule that compares records and corrects them produces one more record, and the
question is whether that record can join the regions it reads into one system.
A *record* here is a region whose content has a noisy margin: under the random
steps its content is constant on a ball of radius `ρ` about the noisy successor,
outside an error set of probability `ε`. Coupling at the noise floor asks each
region to move the other's content by the yardstick `θ`, so a record whose error
rate is below `θ` answers no change inside its margin, whatever the regions
around it carry.

* **`not_coupledAtNoiseFloor_of_record`.** A record with error rate below `θ` is
  coupled to no region that admits a change above its noise inside the margin's
  width. The other regions may be graded; nothing is assumed of their contents.
* **`eqvGen_of_isolated`** and **`eqvGen_iff_of_isolated`.** For any relation
  and any set of points related to nothing but themselves, a chain between two
  points either is trivial or runs entirely outside the set, and the closure is
  the closure of the relation restricted to the complement.
* **`sameSystem_iff_eq_of_record`** and **`sameSystem_iff_of_records`.** A record
  is one system only with itself, and for any set of records, rules on rules
  included, two regions are one system exactly when a chain of couplings that
  avoids every record joins them. Records drop out of every chain.
* **`shiftResponse_le_of_factors`** and **`not_coupledAtNoiseFloor_of_factors`.**
  Write-back. If region `j`'s next content depends on a change of region `i`
  only through a record's symbol, read from the carrier `g ω` the noise carries
  the state to, the response of `j` to that change is at most the record's error
  rate, so a rule that writes corrections back through the record couples `i`
  to `j` at no noise floor above that rate.

A graded reader, by contrast, is a region whose content does move with each of
two regions above their noise; it is coupled to both and joins them
(`Examples/PhysicalUnity.lean`, under linear dynamics with uniform noise), so the
regress stops at a reader on the chain and not at a record beside it.

Scope. The factoring hypothesis of write-back is the physics of the rule: it
says the record is the only route from `i` to `j`, and a leak around the record
(crosstalk, a shared supply) is a separate path that this section does not
bound; `law_le_of_marginRate` bounds it when it too runs through a margin.
Which regions are records is the modeller's choice of margins, as elsewhere in
this module. -/

namespace PhysicsOfConsciousness.PhysicalUnity

open MeasureTheory

variable {ι : Type*} [DecidableEq ι] {S : ι → Type*}
  [∀ i, PseudoMetricSpace (S i)] {C : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- **Isolated points drop out of every chain.** If every point of `D` is related to
nothing but itself, in either direction, then two points joined by a chain of `r`
are equal or lie outside `D` and are joined by a chain of `r` that never enters
`D`. -/
theorem eqvGen_of_isolated {α : Type*} {r : α → α → Prop} {D : Set α}
    (hD : ∀ d ∈ D, ∀ a, a ≠ d → ¬ r a d ∧ ¬ r d a) {a b : α} (h : Relation.EqvGen r a b) :
    a = b ∨ a ∉ D ∧ b ∉ D ∧ Relation.EqvGen (fun a b => a ∉ D ∧ b ∉ D ∧ r a b) a b := by
  induction h with
  | rel a b hab =>
    by_cases he : a = b
    · exact Or.inl he
    have ha : a ∉ D := fun hd => (hD a hd b (Ne.symm he)).2 hab
    have hb : b ∉ D := fun hd => (hD b hd a he).1 hab
    exact Or.inr ⟨ha, hb, .rel _ _ ⟨ha, hb, hab⟩⟩
  | refl => exact Or.inl rfl
  | symm _ _ _ ih =>
    rcases ih with h | ⟨ha, hb, h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hb, ha, h.symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | ⟨ha, hb, h₁⟩
    · exact ih₂
    rcases ih₂ with rfl | ⟨_, hc, h₂⟩
    · exact Or.inr ⟨ha, hb, h₁⟩
    · exact Or.inr ⟨ha, hc, h₁.trans _ _ _ h₂⟩

/-- The closure of a relation whose points in `D` are isolated is the closure of its
restriction to the complement of `D`. -/
theorem eqvGen_iff_of_isolated {α : Type*} {r : α → α → Prop} {D : Set α}
    (hD : ∀ d ∈ D, ∀ a, a ≠ d → ¬ r a d ∧ ¬ r d a) {a b : α} :
    Relation.EqvGen r a b ↔ Relation.EqvGen (fun a b => a ∉ D ∧ b ∉ D ∧ r a b) a b := by
  refine ⟨fun h => ?_, fun h => Relation.EqvGen.mono (fun _ _ h => h.2.2) _ _ h⟩
  rcases eqvGen_of_isolated hD h with rfl | ⟨_, _, h⟩
  · exact .refl _
  · exact h

omit [∀ i, PseudoMetricSpace (S i)] in
/-- The response to a change is at most the probability that the change moves the
content at all, both states driven by the same noise. -/
theorem shiftResponse_le_of_ne_le {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i}
    {π : (∀ i, S i) → C} {x : ∀ i, S i} {i : ι} {s : S i} {ε : ENNReal}
    (h : μ {ω | π (f ω (Function.update x i s)) ≠ π (f ω x)} ≤ ε) :
    shiftResponse μ f π x i s ≤ ε := by
  refine iSup_le fun A => tsub_le_iff_left.mpr ((measure_mono fun ω hω => ?_).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl h)))
  by_cases he : π (f ω (Function.update x i s)) = π (f ω x)
  · exact Or.inl (show π (f ω x) ∈ A from he ▸ hω)
  · exact Or.inr he

/-- **A record joins nothing.** Let region `r`'s content have a margin of radius `ρ`
with error rate `ε` below the yardstick `θ`, under `L`-Lipschitz random steps. If
region `j` admits a change above its noise and below its threshold-crossing change
that stays within the margin's width `ρ / L`, then `r` and `j` are not coupled at the
noise floor. Nothing is assumed of `j`'s content, which may be graded. -/
theorem not_coupledAtNoiseFloor_of_record [Fintype ι] {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {π : ι → (∀ i, S i) → C} {x : ∀ i, S i} {r : ι} {ρ : ℝ} {ε θ : ENNReal}
    (hπ : HasMarginRate μ (fun ω => f ω x) (π r) ρ ε) (hεθ : ε < θ) {σ Θ : ι → ℝ} {j : ι}
    (hs : ∃ s : S j, σ j ≤ dist s (x j) ∧ dist s (x j) < Θ j ∧ L * dist s (x j) < ρ) :
    ¬ CoupledAtNoiseFloor μ f π x σ Θ θ r j := by
  obtain ⟨s, hσ, hΘ, hr⟩ := hs
  exact fun h => (hεθ.trans_le (h.2 s hσ hΘ)).not_ge
    (shiftResponse_le_of_marginRate hf hπ j s hr)

/-- **A record is one system only with itself.** Under the hypotheses of
`not_coupledAtNoiseFloor_of_record`, for every other region, the record and a region
are one system exactly when they are the same region. -/
theorem sameSystem_iff_eq_of_record [Fintype ι] {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {π : ι → (∀ i, S i) → C} {x : ∀ i, S i} {r : ι} {ρ : ℝ} {ε θ : ENNReal}
    (hπ : HasMarginRate μ (fun ω => f ω x) (π r) ρ ε) (hεθ : ε < θ) {σ Θ : ι → ℝ}
    (hs : ∀ j, j ≠ r → ∃ s : S j, σ j ≤ dist s (x j) ∧ dist s (x j) < Θ j ∧ L * dist s (x j) < ρ)
    {j : ι} : SameSystem μ f π x σ Θ θ r j ↔ r = j := by
  refine ⟨fun h => ?_, fun h => h ▸ .refl _⟩
  refine (eqvGen_of_isolated (D := {r}) (fun d hd a had => ?_) h).resolve_right
    fun h' => h'.1 rfl
  rw [Set.mem_singleton_iff] at hd
  subst hd
  have h := not_coupledAtNoiseFloor_of_record hf hπ hεθ (θ := θ) (hs a had)
  exact ⟨fun h' => h ⟨h'.2, h'.1⟩, h⟩

/-- **No chain passes through a record.** Let every region of the set `D` be a
record, with a margin of radius `ρ d` and error rate `ε d` below `θ`, and let every
other region admit a change above its noise within each record's margin width. Then
two regions are one system exactly when a chain of couplings that never enters `D`
joins them. The set is arbitrary, so records that read records, and rules on rules,
drop out together. -/
theorem sameSystem_iff_of_records [Fintype ι] {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {π : ι → (∀ i, S i) → C} {x : ∀ i, S i} {D : Set ι} {ρ : ι → ℝ} {ε : ι → ENNReal}
    {θ : ENNReal} (hπ : ∀ d ∈ D, HasMarginRate μ (fun ω => f ω x) (π d) (ρ d) (ε d))
    (hεθ : ∀ d ∈ D, ε d < θ) {σ Θ : ι → ℝ}
    (hs : ∀ d ∈ D, ∀ j, j ≠ d →
      ∃ s : S j, σ j ≤ dist s (x j) ∧ dist s (x j) < Θ j ∧ L * dist s (x j) < ρ d)
    {i j : ι} :
    SameSystem μ f π x σ Θ θ i j ↔
      Relation.EqvGen (fun a b => a ∉ D ∧ b ∉ D ∧ CoupledAtNoiseFloor μ f π x σ Θ θ a b) i j := by
  refine eqvGen_iff_of_isolated (fun d hd a had => ?_)
  have h := not_coupledAtNoiseFloor_of_record hf (hπ d hd) (hεθ d hd) (θ := θ) (hs d hd a had)
  exact ⟨fun h' => h ⟨h'.2, h'.1⟩, h⟩

/-- **Write-back through a record moves nothing past its error rate.** Let `g ω` be
the random step that carries the state to the record's carrier, `L`-Lipschitz, and
`ψ` the record's readout, with a margin of radius `ρ` and error rate `ε` along
`g · x`. If, for every noise realisation, the change of region `i` to `s` moves the
content `π` read after `f ω` only when it moves the record's symbol, then its
response to that change is at most `ε`. The noise `ω` drives both steps, so `f ω`
may be the rule's write-back composed after `g ω`, each with noise of its own.

The factoring hypothesis carries the physics: it says the record is the only route
from `i` to the content. -/
theorem shiftResponse_le_of_factors [Fintype ι] {μ : Measure Ω}
    {f g : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hg : ∀ ω, LipschitzWith L (g ω))
    {π : (∀ i, S i) → C} {D : Type*} {ψ : (∀ i, S i) → D} {x : ∀ i, S i} {ρ : ℝ}
    {ε : ENNReal} (hψ : HasMarginRate μ (fun ω => g ω x) ψ ρ ε) {i : ι} {s : S i}
    (hfac : ∀ ω, ψ (g ω (Function.update x i s)) = ψ (g ω x) →
      π (f ω (Function.update x i s)) = π (f ω x))
    (hs : L * dist s (x i) < ρ) : shiftResponse μ f π x i s ≤ ε := by
  refine shiftResponse_le_of_ne_le ((measure_mono fun ω hω => ?_).trans
    (content_ne_le_of_marginRate hg hψ i s hs))
  exact fun he => hω (hfac ω he)

/-- **Write-back through a record adds no link.** Under the hypotheses of
`shiftResponse_le_of_factors`, with error rate below `θ` and the change of region
`i` above its noise and below its threshold-crossing change, region `j`'s content
does not depend on `i` above the noise floor, so the two are not coupled. A rule
that reads `i` into a record and writes corrections from the record into `j` joins
them no more than the record itself does. -/
theorem not_coupledAtNoiseFloor_of_factors [Fintype ι] {μ : Measure Ω}
    {f g : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hg : ∀ ω, LipschitzWith L (g ω))
    {π : ι → (∀ i, S i) → C} {D : Type*} {ψ : (∀ i, S i) → D} {x : ∀ i, S i} {ρ : ℝ}
    {ε θ : ENNReal} (hψ : HasMarginRate μ (fun ω => g ω x) ψ ρ ε) (hεθ : ε < θ)
    {σ Θ : ι → ℝ} {i j : ι} {s : S i} (hσ : σ i ≤ dist s (x i)) (hΘ : dist s (x i) < Θ i)
    (hs : L * dist s (x i) < ρ)
    (hfac : ∀ ω, ψ (g ω (Function.update x i s)) = ψ (g ω x) →
      π j (f ω (Function.update x i s)) = π j (f ω x)) :
    ¬ CoupledAtNoiseFloor μ f π x σ Θ θ i j :=
  fun h => (hεθ.trans_le (h.1 s hσ hΘ)).not_ge (shiftResponse_le_of_factors hg hψ hfac hs)

end PhysicsOfConsciousness.PhysicalUnity

/-! ## P over carriers, per content window

The criterion above is universal: every change of a region above its noise must
move the other region's content by `θ`. Read at the grain of single carriers — a
membrane, a spike time — a noisy carrier meets it only near its threshold, so a
region made of many carriers meets the universal form almost nowhere. What
unites two regions is that *some* of the carriers joining them pass, and that
some pass within every window of the content's time scale.

* **`ReachesAtNoiseFloor region … a b`.** Carriers `ι` belong to regions `R`
  through `region`. Region `a` reaches region `b` at a micro state when some
  carrier of `b` depends gradedly above noise on some carrier of `a`.
* **`EnforcedByCarriers O …`.** Every pair of regions that `O` says overlap is
  joined in this way; for a symmetric `O`, in both directions. Such regions are
  one system (`EnforcedByCarriers.regionSameSystem`).
* **`EnforcedAtNoiseFloor.enforcedByCarriers`.** The universal criterion, read
  over carriers, implies this one wherever every region has a carrier, so the
  carrier form is the weaker premise; `Examples/PhysicalUnity.lean` exhibits a
  state where it holds and the universal form fails.
* **`not_reachesAtNoiseFloor_of_bits`.** A machine whose contents are read from
  bits with error rate below `θ`, each carrier admitting a change above its
  noise inside the margin, has no carrier of any region reaching any other, so
  it fails the carrier form at any overlap (`not_enforcedByCarriers_of_bits`)
  and each region is a system of its own (`regionSameSystem_iff_eq_of_bits`).
  Weakening the premise from every carrier to some carrier costs the digital
  exclusion nothing.
* **`measure_not_reachesWithin_le`.** Along trajectories `X ω` of the micro
  state, if `K` events each guarantee that `a` reaches `b` somewhere in the
  window `T`, and the events that they fail are independent with probability at
  most `1 − p` each, then `a` fails to reach `b` in the window with probability
  at most `(1 − p)^K`.
* **`measure_not_reachesWithin_le_variance`.** Without independence: if `N`
  counts the events that occur and has positive mean, `a` fails to reach `b` in
  the window with probability at most the variance of `N` over its squared mean.
  For `K` exchangeable carriers passing with probability `h` and pairwise
  correlation `ρ`, this tends to `ρ(1 − h)/h` as `K` grows, a floor set by the
  correlation.

Scope. Which variables are carriers, and which carriers belong to which region,
is the modeller's choice; the theorems hold for any choice. Independence is a
hypothesis of the geometric window bound, not a result; the variance bound
drops it, and correlated carriers then set its floor. Nothing here computes `p`,
`h` or `ρ`: those are properties of the carriers' dynamics.
-/

namespace PhysicsOfConsciousness.PhysicalUnity

open MeasureTheory

variable {ι : Type*} [DecidableEq ι] {S : ι → Type*}
  [∀ i, PseudoMetricSpace (S i)] {C : Type*} {Ω : Type*} [MeasurableSpace Ω] {R : Type*}

/-- **Reach at the noise floor.** Region `a` reaches region `b` at `x` when some
carrier `j` of `b` has content depending gradedly above noise on some carrier `i`
of `a`. -/
def ReachesAtNoiseFloor (region : ι → R) (μ : Measure Ω) (f : Ω → (∀ i, S i) → ∀ i, S i)
    (π : ι → (∀ i, S i) → C) (x : ∀ i, S i) (σ Θ : ι → ℝ) (θ : ENNReal) (a b : R) : Prop :=
  ∃ i j, region i = a ∧ region j = b ∧ GradedAboveNoise μ f (π j) x i (σ i) (Θ i) θ

/-- **P over carriers.** Every pair of regions that `O` says overlap is joined by
reach at the noise floor. -/
def EnforcedByCarriers (region : ι → R) (O : R → R → Prop) (μ : Measure Ω)
    (f : Ω → (∀ i, S i) → ∀ i, S i) (π : ι → (∀ i, S i) → C) (x : ∀ i, S i)
    (σ Θ : ι → ℝ) (θ : ENNReal) : Prop :=
  ∀ a b, O a b → ReachesAtNoiseFloor region μ f π x σ Θ θ a b

/-- Regions are one system when a chain of mutual reaches joins them. -/
def RegionSameSystem (region : ι → R) (μ : Measure Ω) (f : Ω → (∀ i, S i) → ∀ i, S i)
    (π : ι → (∀ i, S i) → C) (x : ∀ i, S i) (σ Θ : ι → ℝ) (θ : ENNReal) : R → R → Prop :=
  Relation.EqvGen fun a b =>
    ReachesAtNoiseFloor region μ f π x σ Θ θ a b ∧ ReachesAtNoiseFloor region μ f π x σ Θ θ b a

/-- Regions whose overlap P over carriers admits, for a symmetric overlap relation,
are one system. -/
theorem EnforcedByCarriers.regionSameSystem {region : ι → R} {O : R → R → Prop}
    (hO : ∀ a b, O a b → O b a) {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i}
    {π : ι → (∀ i, S i) → C} {x : ∀ i, S i} {σ Θ : ι → ℝ} {θ : ENNReal}
    (h : EnforcedByCarriers region O μ f π x σ Θ θ) {a b : R} (hab : O a b) :
    RegionSameSystem region μ f π x σ Θ θ a b :=
  .rel _ _ ⟨h a b hab, h b a (hO a b hab)⟩

/-- **The universal form implies the carrier form.** If every carrier's content
depends gradedly above noise on every carrier of every region its own region
overlaps, and every region has a carrier, then P over carriers holds. The
converse fails (`Examples/PhysicalUnity.lean`), so the carrier form is strictly
weaker. -/
theorem EnforcedAtNoiseFloor.enforcedByCarriers {region : ι → R} {O : R → R → Prop}
    {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i} {π : ι → (∀ i, S i) → C}
    {x : ∀ i, S i} {σ Θ : ι → ℝ} {θ : ENNReal}
    (h : EnforcedAtNoiseFloor (fun i j => O (region i) (region j)) μ f π x σ Θ θ)
    (hne : ∀ a, ∃ i, region i = a) : EnforcedByCarriers region O μ f π x σ Θ θ := by
  intro a b hab
  obtain ⟨i, rfl⟩ := hne a
  obtain ⟨j, rfl⟩ := hne b
  exact ⟨i, j, rfl, rfl, h i j hab⟩

/-- **A bit-read content depends on no carrier above its noise.** Under the
hypotheses of `sameSystem_iff_eq_of_bits`, for carrier `i` alone: if `i` admits a
change above its noise and below its threshold-crossing change that stays within
the margin's width, no content read from the bits depends gradedly above noise on
`i`. -/
theorem not_gradedAboveNoise_of_bits [Fintype ι] {κ : Type*} {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {v : κ → (∀ i, S i) → ℝ} {Lv : NNReal} (hv : ∀ k, LipschitzWith Lv (v k))
    (hLv : 0 < (Lv : ℝ)) (c : κ → ℝ) (q : (κ → Bool) → C) {δ : ℝ}
    {x : ∀ i, S i} {ε θ : ENNReal} (hε : μ {ω | ∃ k, |v k (f ω x) - c k| < δ} ≤ ε)
    (hεθ : ε < θ) {i : ι} {σ Θ : ℝ}
    (hs : ∃ s : S i, σ ≤ dist s (x i) ∧ dist s (x i) < Θ ∧ L * dist s (x i) < δ / Lv) :
    ¬ GradedAboveNoise μ f (fun y => q fun k => decide (c k < v k y)) x i σ Θ θ := by
  intro hg
  obtain ⟨s, hσ, hΘ, hr⟩ := hs
  refine (hεθ.trans_le (hg s hσ hΘ)).not_ge (iSup_le fun A => tsub_le_iff_left.mpr ?_)
  exact (bits_law_le_of_lipschitz hf hv hLv c q hε i s hr A).1

/-- **Bits reach nowhere.** Under the hypotheses of `sameSystem_iff_eq_of_bits`,
with every carrier admitting a change above its noise inside the margin, no region
reaches any region, itself included. -/
theorem not_reachesAtNoiseFloor_of_bits [Fintype ι] {κ : Type*} {region : ι → R}
    {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {v : κ → (∀ i, S i) → ℝ} {Lv : NNReal} (hv : ∀ k, LipschitzWith Lv (v k))
    (hLv : 0 < (Lv : ℝ)) (c : κ → ℝ) (q : ι → (κ → Bool) → C) {δ : ℝ}
    {x : ∀ i, S i} {ε θ : ENNReal} (hε : μ {ω | ∃ k, |v k (f ω x) - c k| < δ} ≤ ε)
    (hεθ : ε < θ) {σ Θ : ι → ℝ}
    (hs : ∀ i, ∃ s : S i, σ i ≤ dist s (x i) ∧ dist s (x i) < Θ i ∧
      L * dist s (x i) < δ / Lv) (a b : R) :
    ¬ ReachesAtNoiseFloor region μ f (fun j y => q j fun k => decide (c k < v k y)) x σ Θ θ a b :=
  fun ⟨i, j, _, _, hg⟩ => not_gradedAboveNoise_of_bits hf hv hLv c (q j) hε hεθ (hs i) hg

/-- **Bits fail P over carriers** at any overlap relation that relates two regions. -/
theorem not_enforcedByCarriers_of_bits [Fintype ι] {κ : Type*} {region : ι → R}
    {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {v : κ → (∀ i, S i) → ℝ} {Lv : NNReal} (hv : ∀ k, LipschitzWith Lv (v k))
    (hLv : 0 < (Lv : ℝ)) (c : κ → ℝ) (q : ι → (κ → Bool) → C) {δ : ℝ}
    {x : ∀ i, S i} {ε θ : ENNReal} (hε : μ {ω | ∃ k, |v k (f ω x) - c k| < δ} ≤ ε)
    (hεθ : ε < θ) {σ Θ : ι → ℝ}
    (hs : ∀ i, ∃ s : S i, σ i ≤ dist s (x i) ∧ dist s (x i) < Θ i ∧
      L * dist s (x i) < δ / Lv) {O : R → R → Prop} {a b : R} (hab : O a b) :
    ¬ EnforcedByCarriers region O μ f (fun j y => q j fun k => decide (c k < v k y)) x σ Θ θ :=
  fun h => not_reachesAtNoiseFloor_of_bits hf hv hLv c q hε hεθ hs a b (h a b hab)

/-- **A bit word's regions are as many systems as there are regions.** -/
theorem regionSameSystem_iff_eq_of_bits [Fintype ι] {κ : Type*} {region : ι → R}
    {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i} {L : NNReal} (hf : ∀ ω, LipschitzWith L (f ω))
    {v : κ → (∀ i, S i) → ℝ} {Lv : NNReal} (hv : ∀ k, LipschitzWith Lv (v k))
    (hLv : 0 < (Lv : ℝ)) (c : κ → ℝ) (q : ι → (κ → Bool) → C) {δ : ℝ}
    {x : ∀ i, S i} {ε θ : ENNReal} (hε : μ {ω | ∃ k, |v k (f ω x) - c k| < δ} ≤ ε)
    (hεθ : ε < θ) {σ Θ : ι → ℝ}
    (hs : ∀ i, ∃ s : S i, σ i ≤ dist s (x i) ∧ dist s (x i) < Θ i ∧
      L * dist s (x i) < δ / Lv) {a b : R} :
    RegionSameSystem region μ f (fun j y => q j fun k => decide (c k < v k y)) x σ Θ θ a b ↔
      a = b := by
  refine ⟨fun hs' => ?_, fun hab => hab ▸ .refl _⟩
  induction hs' with
  | rel a b hab => exact absurd hab.1 (not_reachesAtNoiseFloor_of_bits hf hv hLv c q hε hεθ hs a b)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Region `a` reaches region `b` at some time of the window `T` along the
trajectory `X ω` of micro states. -/
def ReachesWithin {Ω' τ : Type*} (region : ι → R) (μ : Measure Ω)
    (f : Ω → (∀ i, S i) → ∀ i, S i) (π : ι → (∀ i, S i) → C) (X : Ω' → τ → ∀ i, S i)
    (T : Set τ) (σ Θ : ι → ℝ) (θ : ENNReal) (a b : R) (ω : Ω') : Prop :=
  ∃ t ∈ T, ReachesAtNoiseFloor region μ f π (X ω t) σ Θ θ a b

/-- **Some carrier within every window.** Let each of `K` events `E k` of
trajectories guarantee that `a` reaches `b` within the window `T` — carrier pair
`k` visits a state from which it passes — and let the events that they fail be
independent, each of probability at most `1 − p`. Then `a` fails to reach `b`
within the window with probability at most `(1 − p)^K`.

The physical content is in the hypotheses: that the carriers' failures are
independent, which correlated membranes weaken, and the per-carrier probability
`p`, which the carrier's dynamics sets and this theorem does not compute. -/
theorem measure_not_reachesWithin_le {Ω' τ : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    {region : ι → R} {μ : Measure Ω} {f : Ω → (∀ i, S i) → ∀ i, S i}
    {π : ι → (∀ i, S i) → C} {X : Ω' → τ → ∀ i, S i} {T : Set τ} {σ Θ : ι → ℝ}
    {θ : ENNReal} {a b : R} {κ : Type*} [Fintype κ] {E : κ → Set Ω'}
    (hE : ∀ k, E k ⊆ {ω | ReachesWithin region μ f π X T σ Θ θ a b ω})
    (hind : ProbabilityTheory.iIndepSet (fun k => (E k)ᶜ) P) {p : ENNReal}
    (hp : ∀ k, P (E k)ᶜ ≤ 1 - p) :
    P {ω | ¬ ReachesWithin region μ f π X T σ Θ θ a b ω} ≤ (1 - p) ^ Fintype.card κ := by
  calc P {ω | ¬ ReachesWithin region μ f π X T σ Θ θ a b ω}
      ≤ P (⋂ k ∈ (Finset.univ : Finset κ), (E k)ᶜ) :=
        measure_mono fun ω hω => by
          simp only [Finset.mem_univ, Set.iInter_true, Set.mem_iInter, Set.mem_compl_iff]
          exact fun k hk => hω (hE k hk)
    _ = ∏ k ∈ (Finset.univ : Finset κ), P (E k)ᶜ := hind.meas_biInter _
    _ ≤ (1 - p) ^ (Finset.univ : Finset κ).card :=
        Finset.prod_le_pow_card _ _ _ fun k _ => hp k
    _ = (1 - p) ^ Fintype.card κ := by rw [Finset.card_univ]

/-- **Some carrier within every window, without independence.** Let each of the
measurable events `E k` of trajectories guarantee that `a` reaches `b` within the
window `T`, and let `N ω` count the events that occur. If `N` has positive mean,
then `a` fails to reach `b` within the window with probability at most the
variance of `N` over its squared mean. The events may be correlated in any way.

The bound holds because failing to reach forces `N = 0`, which lies a full mean
away from the mean. For `K` exchangeable carriers, each passing with probability
`h` and with pairwise correlation `ρ` of passing, the bound is
`(1 − h)(1 + (K − 1)ρ)/(K h)`, which tends to `ρ(1 − h)/h` as `K` grows: a floor
set by the correlation, not by the number of carriers. For independent carriers
it is `(1 − h)/(K h)`, weaker than the `(1 − h)^K` of
`measure_not_reachesWithin_le`, which pays for its rate with its independence
hypothesis. The mean and variance of `N` are properties of the carriers'
dynamics, which this theorem does not compute. -/
theorem measure_not_reachesWithin_le_variance {Ω' τ : Type*} [MeasurableSpace Ω']
    {P : Measure Ω'} [IsFiniteMeasure P] {region : ι → R} {μ : Measure Ω}
    {f : Ω → (∀ i, S i) → ∀ i, S i} {π : ι → (∀ i, S i) → C} {X : Ω' → τ → ∀ i, S i}
    {T : Set τ} {σ Θ : ι → ℝ} {θ : ENNReal} {a b : R} {κ : Type*} [Fintype κ]
    {E : κ → Set Ω'} (hEm : ∀ k, MeasurableSet (E k))
    (hE : ∀ k, E k ⊆ {ω | ReachesWithin region μ f π X T σ Θ θ a b ω})
    (hpos : 0 < ∫ ω, ∑ k, (E k).indicator (1 : Ω' → ℝ) ω ∂P) :
    P {ω | ¬ ReachesWithin region μ f π X T σ Θ θ a b ω} ≤
      ENNReal.ofReal (ProbabilityTheory.variance
        (fun ω => ∑ k, (E k).indicator (1 : Ω' → ℝ) ω) P /
          (∫ ω, ∑ k, (E k).indicator (1 : Ω' → ℝ) ω ∂P) ^ 2) := by
  refine (measure_mono fun ω hω => ?_).trans (ProbabilityTheory.meas_ge_le_variance_div_sq
    (memLp_finsetSum _ fun k _ =>
      ((memLp_const 1).indicator (hEm k) : MemLp ((E k).indicator (1 : Ω' → ℝ)) 2 P)) hpos)
  have h0 : ∑ k, (E k).indicator (1 : Ω' → ℝ) ω = 0 :=
    Finset.sum_eq_zero fun k _ => Set.indicator_of_notMem (fun h => hω (hE k h)) _
  change _ ≤ |∑ k, (E k).indicator (1 : Ω' → ℝ) ω - _|
  rw [h0, zero_sub, abs_neg, abs_of_pos hpos]

end PhysicsOfConsciousness.PhysicalUnity

/-! ## Laws that cross once

Whether P is decided by the smallest change above the noise depends on how the
response grows with the change. The response to a change is the largest rise, over
events, from the law of the next content to its law after the change. When the two
laws cross once, the second falling short of the first below some point and
exceeding it above, the rise is largest on an upper half-line, and a law moved
further along its family gives every upper half-line at least as much probability.
So the response grows with the change on each side of the current state, and the
criterion is decided by one change of the size of the noise in each direction.

* **`lawRise`** and **`rise_le_of_restrict`.** The largest rise from `P` to `Q`,
  over every set as in `shiftResponse`, is at most the rise on any measurable set
  that carries the whole excess of `Q` (Scheffé's argument).
* **`SingleCrossing P Q`.** An upper set carries the whole excess of `Q` over `P`.
  `SingleCrossing.le_of_isUpperSet` and `.le_of_isLowerSet`: between probability
  laws, `Q` then dominates `P` stochastically.
* **`lawRise_le_of_crossing`.** In a family of probability laws on `ℝ` any two of
  which cross once in the order of the parameter, the rise from `θ₀` grows as the
  parameter moves away from `θ₀` on either side.
* **`singleCrossing_withDensity`**, **`singleCrossing_of_mlr`** and
  **`singleCrossing_expFamily`.** Densities against any reference law cross once
  when, once the second exceeds the first, it never falls below it; monotone
  likelihood ratio implies this, and so do the densities `h y exp (θ y − A θ)` of a
  one-parameter exponential family in its natural parameter. Poisson spike counts,
  binomial release and gamma intervals of fixed shape are of this form, against
  counting measure or Lebesgue measure, and their variance changes with the state.
* **`singleCrossing_shift_of_unimodal`** and
  **`lawRise_map_add_mono_of_unimodal`.** Additive noise with a density that rises
  to one peak and falls after it: a shift of the density crosses the unshifted one
  once, and the rise grows with the size of the shift in either direction, because
  under additive noise the rise is the same for a shift and its negative
  (`lawRise_map_add_le_neg`). Log-concavity is not needed: Gaussian, Laplace,
  logistic, uniform, Cauchy and Student-t noise all qualify. Some hypothesis is:
  under noise `±1` with probability `1/2` each, a shift by `1` has rise `1` and a
  shift by `2` has rise `1/2`.
* **`gradedAboveNoise_iff_of_sides`** and **`gradedAboveNoise_iff_of_crossing`.**
  Where the response grows on each side of a real micro state, graded dependence
  above the noise floor holds exactly when the changes `+σ` and `−σ` move the
  content by `θ`; this is the case when the next content's law runs along a family
  whose laws cross once, through a parameter that the region's state moves
  monotonically. Nonlinear dynamics enter only through that parameter, a
  hypothesis on the dynamics and not on the noise.

Vector-valued contents fall outside this section: an upper set of the plane is not
a half-line, and a single crossing does not order the rises. For a symmetric
unimodal law in several dimensions Anderson's theorem gives growth along each ray,
and the criterion becomes the smallest response over changes of size `σ`.
-/

namespace PhysicsOfConsciousness.PhysicalUnity

open MeasureTheory

/-- The largest rise, over events, in probability from the law `P` to the law `Q`.
Probability is outer measure, as in `shiftResponse`. -/
noncomputable def lawRise {α : Type*} [MeasurableSpace α] (P Q : Measure α) : ENNReal :=
  ⨆ A : Set α, Q A - P A

/-- **Scheffé's bound.** If `Q` exceeds `P` on every part of the measurable set `G`
and falls short of it on every part of its complement, no set, measurable or not,
gains more probability from `P` to `Q` than `G` does. -/
lemma rise_le_of_restrict {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsFiniteMeasure P] {G : Set α} (hG : MeasurableSet G) (hPG : P.restrict G ≤ Q.restrict G)
    (hQG : Q.restrict Gᶜ ≤ P.restrict Gᶜ) (A : Set α) : Q A - P A ≤ Q G - P G := by
  have hB := measurableSet_toMeasurable P A
  set B := toMeasurable P A
  have h1 : Q (B \ G) ≤ P (B \ G) := by
    have := Measure.le_iff'.mp hQG (B \ G)
    rwa [Measure.restrict_eq_self _ (fun y hy => hy.2),
      Measure.restrict_eq_self _ (fun y hy => hy.2)] at this
  have h2 : P (G \ B) ≤ Q (G \ B) := by
    have := Measure.le_iff'.mp hPG (G \ B)
    rwa [Measure.restrict_eq_self _ Set.sdiff_subset,
      Measure.restrict_eq_self _ Set.sdiff_subset] at this
  have hGle : P G ≤ Q G := by
    have := Measure.le_iff'.mp hPG G
    rwa [Measure.restrict_eq_self _ subset_rfl, Measure.restrict_eq_self _ subset_rfl] at this
  have key : Q B + P G ≤ P B + Q G := by
    rw [← measure_inter_add_sdiff (μ := Q) B hG, ← measure_inter_add_sdiff (μ := P) G hB,
      ← measure_inter_add_sdiff (μ := P) B hG, ← measure_inter_add_sdiff (μ := Q) G hB,
      Set.inter_comm G B]
    calc Q (B ∩ G) + Q (B \ G) + (P (B ∩ G) + P (G \ B))
        ≤ Q (B ∩ G) + P (B \ G) + (P (B ∩ G) + Q (G \ B)) := by gcongr
      _ = P (B ∩ G) + P (B \ G) + (Q (B ∩ G) + Q (G \ B)) := by ring
  calc Q A - P A ≤ Q B - P B := by
        rw [measure_toMeasurable]; gcongr; exact subset_toMeasurable _ _
    _ ≤ Q G - P G := by
        rw [tsub_le_iff_left]
        refine (ENNReal.add_le_add_iff_right (measure_ne_top P G)).mp ?_
        rw [add_assoc, tsub_add_cancel_of_le hGle]
        exact key

/-- Two laws on `ℝ` **cross once** when an upper set carries the whole excess of
`Q` over `P`: `Q` exceeds `P` on every part of it and falls short of `P` on every
part of its complement. -/
def SingleCrossing (P Q : Measure ℝ) : Prop :=
  ∃ G : Set ℝ, IsUpperSet G ∧ P.restrict G ≤ Q.restrict G ∧ Q.restrict Gᶜ ≤ P.restrict Gᶜ

/-- Between probability laws that cross once, the second gives every upper set at
least the probability the first gives it. -/
lemma SingleCrossing.le_of_isUpperSet {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (h : SingleCrossing P Q) {U : Set ℝ} (hU : IsUpperSet U) :
    P U ≤ Q U := by
  obtain ⟨G, hG, hPG, hQG⟩ := h
  have hUm : MeasurableSet U := hU.ordConnected.measurableSet
  rcases hU.total hG with hUG | hGU
  · have := Measure.le_iff'.mp hPG U
    rwa [Measure.restrict_eq_self _ hUG, Measure.restrict_eq_self _ hUG] at this
  · have := Measure.le_iff'.mp hQG Uᶜ
    rw [Measure.restrict_eq_self _ (Set.compl_subset_compl.mpr hGU),
      Measure.restrict_eq_self _ (Set.compl_subset_compl.mpr hGU),
      prob_compl_eq_one_sub hUm, prob_compl_eq_one_sub hUm] at this
    exact (ENNReal.sub_le_sub_iff_left prob_le_one ENNReal.one_ne_top).mp this

/-- Between probability laws that cross once, the first gives every lower set at
least the probability the second gives it. -/
lemma SingleCrossing.le_of_isLowerSet {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (h : SingleCrossing P Q) {L : Set ℝ} (hL : IsLowerSet L) :
    Q L ≤ P L := by
  have hLm : MeasurableSet L := hL.ordConnected.measurableSet
  have := h.le_of_isUpperSet hL.compl
  rw [prob_compl_eq_one_sub hLm, prob_compl_eq_one_sub hLm] at this
  exact (ENNReal.sub_le_sub_iff_left prob_le_one ENNReal.one_ne_top).mp this

/-- **In a family of laws that cross once, the rise grows along the parameter.**
If any two laws of the family cross once in the order of their parameters, the
rise from the law at `θ₀` to the law at `θ₁` is at most the rise to the law at any
`θ₂` beyond `θ₁` on the same side of `θ₀`. -/
theorem lawRise_le_of_crossing {P : ℝ → Measure ℝ} [∀ θ, IsProbabilityMeasure (P θ)]
    (hP : ∀ θ θ', θ ≤ θ' → SingleCrossing (P θ) (P θ')) {θ₀ θ₁ θ₂ : ℝ}
    (h : θ₀ ≤ θ₁ ∧ θ₁ ≤ θ₂ ∨ θ₂ ≤ θ₁ ∧ θ₁ ≤ θ₀) :
    lawRise (P θ₀) (P θ₁) ≤ lawRise (P θ₀) (P θ₂) := by
  rcases h with ⟨h01, h12⟩ | ⟨h21, h10⟩
  · obtain ⟨G, hG, hPG, hQG⟩ := hP θ₀ θ₁ h01
    refine iSup_le fun A => (rise_le_of_restrict hG.ordConnected.measurableSet hPG hQG A).trans ?_
    exact (tsub_le_tsub_right ((hP θ₁ θ₂ h12).le_of_isUpperSet hG) _).trans
      (le_iSup (fun A => P θ₂ A - P θ₀ A) G)
  · obtain ⟨G, hG, hPG, hQG⟩ := hP θ₁ θ₀ h10
    have hGc : MeasurableSet Gᶜ := hG.compl.ordConnected.measurableSet
    refine iSup_le fun A => (rise_le_of_restrict hGc hQG (by rwa [compl_compl]) A).trans ?_
    exact (tsub_le_tsub_right ((hP θ₂ θ₁ h21).le_of_isLowerSet hG.compl) _).trans
      (le_iSup (fun A => P θ₂ A - P θ₀ A) Gᶜ)

/-- **Densities that cross once.** Against any reference law `ρ`, densities `f`
and `g` cross once when, once `g` has exceeded `f` at some point, it falls below
`f` at no point above it. -/
theorem singleCrossing_withDensity (ρ : Measure ℝ) {f g : ℝ → ENNReal}
    (h : ∀ z y, z ≤ y → f z < g z → f y ≤ g y) :
    SingleCrossing (ρ.withDensity f) (ρ.withDensity g) := by
  set G : Set ℝ := {y | ∃ z, z ≤ y ∧ f z < g z}
  have hG : IsUpperSet G := fun a b hab ⟨z, hz, hfz⟩ => ⟨z, hz.trans hab, hfz⟩
  have hGm : MeasurableSet G := hG.ordConnected.measurableSet
  refine ⟨G, hG, ?_, ?_⟩
  · rw [restrict_withDensity hGm, restrict_withDensity hGm]
    refine withDensity_mono ((ae_restrict_iff' hGm).mpr (.of_forall ?_))
    rintro y ⟨z, hzy, hz⟩
    exact h z y hzy hz
  · rw [restrict_withDensity hGm.compl, restrict_withDensity hGm.compl]
    refine withDensity_mono ((ae_restrict_iff' hGm.compl).mpr (.of_forall fun y hy => ?_))
    exact not_lt.mp fun hlt => hy ⟨y, le_rfl, hlt⟩

/-- **Monotone likelihood ratio crosses once.** If `g / f` never falls, stated
without division as `g y f y' ≤ g y' f y` for `y ≤ y'`, the laws cross once. -/
theorem singleCrossing_of_mlr (ρ : Measure ℝ) {f g : ℝ → ENNReal}
    (h : ∀ y y', y ≤ y' → g y * f y' ≤ g y' * f y) :
    SingleCrossing (ρ.withDensity f) (ρ.withDensity g) := by
  refine singleCrossing_withDensity ρ fun z y hzy hz => not_lt.mp fun hy => ?_
  have := ENNReal.mul_lt_mul hy hz
  exact (h z y hzy).not_gt (by rwa [mul_comm (g z)])

/-- **Exponential families cross once.** Laws with densities
`h y exp (θ y − A θ)` against any reference law `ρ` have monotone likelihood ratio
in the natural parameter `θ`, so a law of the family crosses once every law of it
with a larger parameter. -/
theorem singleCrossing_expFamily (ρ : Measure ℝ) {h : ℝ → ℝ} (hh : ∀ y, 0 ≤ h y)
    (A : ℝ → ℝ) {θ θ' : ℝ} (hθ : θ ≤ θ') :
    SingleCrossing (ρ.withDensity fun y => ENNReal.ofReal (h y * Real.exp (θ * y - A θ)))
      (ρ.withDensity fun y => ENNReal.ofReal (h y * Real.exp (θ' * y - A θ'))) := by
  refine singleCrossing_of_mlr ρ fun y y' hy => ?_
  rw [← ENNReal.ofReal_mul (mul_nonneg (hh _) (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (mul_nonneg (hh _) (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have key : Real.exp (θ' * y - A θ') * Real.exp (θ * y' - A θ) ≤
      Real.exp (θ' * y' - A θ') * Real.exp (θ * y - A θ) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc h y * Real.exp (θ' * y - A θ') * (h y' * Real.exp (θ * y' - A θ))
      = h y * h y' * (Real.exp (θ' * y - A θ') * Real.exp (θ * y' - A θ)) := by ring
    _ ≤ h y * h y' * (Real.exp (θ' * y' - A θ') * Real.exp (θ * y - A θ)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg (hh y) (hh y'))
    _ = _ := by ring

/-- **A shift of a unimodal density crosses once.** If `p` rises up to `M` and
falls after it, the density moved by `θ'` crosses the one moved by `θ ≤ θ'` once. -/
theorem singleCrossing_shift_of_unimodal (ρ : Measure ℝ) {p : ℝ → ENNReal} {M : ℝ}
    (hup : MonotoneOn p (Set.Iic M)) (hdown : AntitoneOn p (Set.Ici M)) {θ θ' : ℝ}
    (hθ : θ ≤ θ') :
    SingleCrossing (ρ.withDensity fun y => p (y - θ)) (ρ.withDensity fun y => p (y - θ')) := by
  refine singleCrossing_withDensity ρ fun z y hzy hz => ?_
  have hd : y - θ' ≤ y - θ := by linarith
  have hz' : M < z - θ := by
    by_contra hle
    push Not at hle
    exact hz.not_ge (hup (show z - θ' ∈ Set.Iic M by simp; linarith) (by simpa using hle)
      (by linarith))
  rcases le_or_gt M (y - θ') with hM | hM
  · exact hdown (show M ≤ y - θ' from hM) (show M ≤ y - θ by linarith) hd
  · calc p (y - θ) ≤ p (z - θ) := hdown (le_of_lt hz') (by simp; linarith) (by linarith)
      _ ≤ p (z - θ') := hz.le
      _ ≤ p (y - θ') := hup (by simp; linarith) (by simp; linarith) (by linarith)

/-- A law moved by `θ` gives every set the probability the law gives its translate. -/
lemma map_add_apply (ν : Measure ℝ) (θ : ℝ) (A : Set ℝ) :
    ν.map (θ + ·) A = ν ((θ + ·) ⁻¹' A) :=
  (MeasurableEquiv.addLeft θ).map_apply A

/-- A law with density `p` against Lebesgue measure, moved by `θ`, has density
`p (· − θ)`. -/
lemma map_add_withDensity (p : ℝ → ENNReal) (θ : ℝ) :
    (volume.withDensity p).map (θ + ·) = volume.withDensity fun y => p (y - θ) := by
  ext s hs
  rw [map_add_apply, withDensity_apply _ (measurable_const_add θ hs), withDensity_apply _ hs,
    ← (measurePreserving_add_left volume θ).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.addLeft θ).measurableEmbedding (fun y => p (y - θ))]
  simp

/-- **Under additive noise a shift and its negative rise as far.** The event that
gains most from the shift by `b` is carried, by complement and translation, to one
that gains as much from the shift by `−b`. -/
lemma lawRise_map_add_le_neg (ν : Measure ℝ) [IsProbabilityMeasure ν] (c b : ℝ) :
    lawRise (ν.map (c + ·)) (ν.map ((c + b) + ·)) ≤
      lawRise (ν.map (c + ·)) (ν.map ((c - b) + ·)) := by
  refine iSup_le fun A => ?_
  have hB := measurableSet_toMeasurable (ν.map (c + ·)) A
  set B := toMeasurable (ν.map (c + ·)) A
  set B' : Set ℝ := (· + b) ⁻¹' Bᶜ
  have e1 : ν.map ((c - b) + ·) B' = 1 - ν.map (c + ·) B := by
    rw [map_add_apply, map_add_apply, ← prob_compl_eq_one_sub (measurable_const_add c hB)]
    congr 1; ext z; simp [B', sub_add_cancel, add_right_comm]
  have e2 : ν.map (c + ·) B' = 1 - ν.map ((c + b) + ·) B := by
    rw [map_add_apply, map_add_apply, ← prob_compl_eq_one_sub (measurable_const_add _ hB)]
    congr 1; ext z; simp [B', add_right_comm]
  calc ν.map ((c + b) + ·) A - ν.map (c + ·) A
      ≤ ν.map ((c + b) + ·) B - ν.map (c + ·) B := by
        rw [measure_toMeasurable]; gcongr; exact subset_toMeasurable _ _
    _ = ν.map ((c - b) + ·) B' - ν.map (c + ·) B' := by
        rw [e1, e2, ENNReal.sub_sub_sub_cancel_left ENNReal.one_ne_top prob_le_one]
    _ ≤ _ := le_iSup (fun A => ν.map ((c - b) + ·) A - ν.map (c + ·) A) B'

/-- **Under additive unimodal noise the rise grows with the shift.** For noise with
a density that rises to one peak and falls after it, shifting the noise's law by `b`
raises no event's probability more than the largest rise a shift by `a` makes, when
`|b| ≤ |a|`, whatever the signs of `a` and `b`. -/
theorem lawRise_map_add_mono_of_unimodal {p : ℝ → ENNReal}
    [IsProbabilityMeasure (volume.withDensity p)] {M : ℝ}
    (hup : MonotoneOn p (Set.Iic M)) (hdown : AntitoneOn p (Set.Ici M)) (c : ℝ) {a b : ℝ}
    (hab : |b| ≤ |a|) :
    lawRise ((volume.withDensity p).map (c + ·)) ((volume.withDensity p).map ((c + b) + ·)) ≤
      lawRise ((volume.withDensity p).map (c + ·)) ((volume.withDensity p).map ((c + a) + ·)) := by
  set ν := volume.withDensity p
  have : ∀ θ, IsProbabilityMeasure (ν.map (θ + ·)) := fun θ =>
    (Measure.isProbabilityMeasure_map_iff (measurable_const_add θ).aemeasurable).mpr inferInstance
  have hP : ∀ θ θ', θ ≤ θ' → SingleCrossing (ν.map (θ + ·)) (ν.map (θ' + ·)) :=
    fun θ θ' h => by
      simp only [ν, map_add_withDensity]; exact singleCrossing_shift_of_unimodal _ hup hdown h
  have mono : ∀ {θ₁ θ₂ : ℝ}, c ≤ θ₁ ∧ θ₁ ≤ θ₂ ∨ θ₂ ≤ θ₁ ∧ θ₁ ≤ c →
      lawRise (ν.map (c + ·)) (ν.map (θ₁ + ·)) ≤ lawRise (ν.map (c + ·)) (ν.map (θ₂ + ·)) :=
    fun h => lawRise_le_of_crossing (P := fun θ => ν.map (θ + ·)) hP h
  have neg : ∀ d, lawRise (ν.map (c + ·)) (ν.map ((c + d) + ·)) ≤
      lawRise (ν.map (c + ·)) (ν.map ((c - d) + ·)) := lawRise_map_add_le_neg ν c
  rcases le_total 0 b with hb | hb <;> rcases le_total 0 a with ha | ha
  · exact mono (.inl ⟨by linarith, by rw [abs_of_nonneg hb, abs_of_nonneg ha] at hab; linarith⟩)
  · rw [abs_of_nonneg hb, abs_of_nonpos ha] at hab
    refine (mono (θ₂ := c - a) (.inl ⟨by linarith, by linarith⟩)).trans ?_
    simpa [sub_eq_add_neg] using neg (-a)
  · rw [abs_of_nonpos hb, abs_of_nonneg ha] at hab
    exact (neg b).trans (mono (θ₂ := c + a) (.inl ⟨by linarith, by linarith⟩))
  · rw [abs_of_nonpos hb, abs_of_nonpos ha] at hab
    exact mono (.inr ⟨by linarith, by linarith⟩)

section sides

variable {ι : Type*} [DecidableEq ι] {C : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- **Where the response grows on each side, P is decided by two changes.** For a
region with a real micro state, if the response grows with the change above the
current state and with the change below it, then for `0 ≤ σ < Θ` graded dependence
above the noise floor holds exactly when the changes `+σ` and `−σ` both move the
content by at least `θ`. -/
theorem gradedAboveNoise_iff_of_sides {μ : Measure Ω} {f : Ω → (ι → ℝ) → ι → ℝ}
    {π : (ι → ℝ) → C} {x : ι → ℝ} {i : ι} {σ Θ : ℝ} {θ : ENNReal}
    (hup : ∀ s t, x i ≤ s → s ≤ t →
      shiftResponse (S := fun _ : ι => ℝ) μ f π x i s ≤
        shiftResponse (S := fun _ : ι => ℝ) μ f π x i t)
    (hdown : ∀ s t, t ≤ s → s ≤ x i →
      shiftResponse (S := fun _ : ι => ℝ) μ f π x i s ≤
        shiftResponse (S := fun _ : ι => ℝ) μ f π x i t)
    (hσ : 0 ≤ σ) (hσΘ : σ < Θ) :
    GradedAboveNoise (S := fun _ : ι => ℝ) μ f π x i σ Θ θ ↔
      θ ≤ shiftResponse (S := fun _ : ι => ℝ) μ f π x i (x i + σ) ∧
        θ ≤ shiftResponse (S := fun _ : ι => ℝ) μ f π x i (x i - σ) := by
  refine ⟨fun h => ⟨h _ (by simp [abs_of_nonneg hσ]) (by simp [abs_of_nonneg hσ, hσΘ]),
    h _ (by simp [abs_of_nonneg hσ]) (by simp [abs_of_nonneg hσ, hσΘ])⟩,
    fun ⟨hp, hm⟩ s hs _ => ?_⟩
  rw [Real.dist_eq] at hs
  rcases le_total (x i) s with hxs | hsx
  · rw [abs_of_nonneg (by linarith)] at hs
    exact hp.trans (hup _ _ (by linarith) (by linarith))
  · rw [abs_of_nonpos (by linarith)] at hs
    exact hm.trans (hdown _ _ (by linarith) (by linarith))

/-- **Laws that cross once decide P by two changes.** Let the next content be real,
with law `P (φ s)` when region `i` is set to `s`, for a family `P` any two of whose
laws cross once in the order of the parameter, and a parameter `φ` that the
region's state moves monotonically, up or down. Then graded dependence above the
noise floor holds exactly when the changes `+σ` and `−σ` both move the content by
at least `θ`. -/
theorem gradedAboveNoise_iff_of_crossing {μ : Measure Ω} {f : Ω → (ι → ℝ) → ι → ℝ}
    {π : (ι → ℝ) → ℝ} {x : ι → ℝ} {i : ι} {P : ℝ → Measure ℝ}
    [∀ θ, IsProbabilityMeasure (P θ)] (hP : ∀ θ θ', θ ≤ θ' → SingleCrossing (P θ) (P θ'))
    {φ : ℝ → ℝ} (hφ : Monotone φ ∨ Antitone φ)
    (hlaw : ∀ s A, μ {ω | π (f ω (Function.update x i s)) ∈ A} = P (φ s) A)
    {σ Θ : ℝ} (hσ : 0 ≤ σ) (hσΘ : σ < Θ) {θ : ENNReal} :
    GradedAboveNoise (S := fun _ : ι => ℝ) μ f π x i σ Θ θ ↔
      θ ≤ lawRise (P (φ (x i))) (P (φ (x i + σ))) ∧
        θ ≤ lawRise (P (φ (x i))) (P (φ (x i - σ))) := by
  have hR : ∀ s, shiftResponse (S := fun _ : ι => ℝ) μ f π x i s =
      lawRise (P (φ (x i))) (P (φ s)) := by
    intro s
    unfold shiftResponse lawRise
    congr 1; ext A
    have hx := hlaw (x i) A
    rw [Function.update_eq_self] at hx
    rw [hlaw, hx]
  have between : ∀ s t, (x i ≤ s ∧ s ≤ t ∨ t ≤ s ∧ s ≤ x i) →
      φ (x i) ≤ φ s ∧ φ s ≤ φ t ∨ φ t ≤ φ s ∧ φ s ≤ φ (x i) := by
    rintro s t (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases hφ with hφ | hφ
    exacts [.inl ⟨hφ h1, hφ h2⟩, .inr ⟨hφ h2, hφ h1⟩, .inr ⟨hφ h1, hφ h2⟩, .inl ⟨hφ h2, hφ h1⟩]
  simp only [← hR]
  refine gradedAboveNoise_iff_of_sides (fun s t h1 h2 => ?_) (fun s t h1 h2 => ?_) hσ hσΘ
  · rw [hR, hR]; exact lawRise_le_of_crossing hP (between s t (.inl ⟨h1, h2⟩))
  · rw [hR, hR]; exact lawRise_le_of_crossing hP (between s t (.inr ⟨h1, h2⟩))

end sides

end PhysicsOfConsciousness.PhysicalUnity

/-! ## The Gaussian carrier

A Gaussian density rises to its mean and falls after it, so the previous section
applies: under a linear micro dynamics with independent Gaussian noise on every
region, graded dependence above the noise floor, and with it coupling at the noise
floor, is decided by one change of the size of the noise.

* **`gaussianPDF_unimodal`** and **`gaussian_shift_le`.** The Gaussian density is
  unimodal, so a shift of a Gaussian by `b` raises no event's probability by more
  than the largest rise a shift by `a` makes, when `|b| ≤ |a|`.
* **`gaussLin`** and **`stdNoise`.** The micro dynamics `y ↦ W y + τ ω` with
  `ω` standard Gaussian on each region; `stdNoise_apply` gives the law of any
  region's next quantity.
* **`shiftResponse_gaussLin_mono`.** Under it, the response of region `j`'s
  next quantity to a change of region `i` grows with the size of the change.
* **`gaussLin_gradedAboveNoise_iff`** and **`gaussLin_coupledAtNoiseFloor_iff`.**
  Hence, for noise scales `0 ≤ σ < Θ`, graded dependence above noise holds
  exactly when the change of size `σ` moves the content by `θ`, and two regions
  are coupled exactly when each one's change of its own noise size moves the
  other's content by `θ`.
-/

namespace PhysicsOfConsciousness.PhysicalUnity

open MeasureTheory ProbabilityTheory NNReal


/-- The Gaussian density rises to its mean and falls after it. -/
lemma gaussianPDF_unimodal (v : ℝ≥0) :
    MonotoneOn (gaussianPDF 0 v) (Set.Iic 0) ∧ AntitoneOn (gaussianPDF 0 v) (Set.Ici 0) := by
  have key : ∀ x y : ℝ, x ^ 2 ≤ y ^ 2 → gaussianPDF 0 v y ≤ gaussianPDF 0 v x := by
    intro x y h
    simp only [gaussianPDF, gaussianPDFReal_def, sub_zero]
    gcongr ENNReal.ofReal (_ * Real.exp ?_)
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine ⟨fun x hx y hy hxy => key _ _ ?_, fun x hx y hy hxy => key _ _ ?_⟩
  · simp only [Set.mem_Iic] at hx hy; nlinarith
  · simp only [Set.mem_Ici] at hx hy; nlinarith

/-- **A smaller Gaussian shift moves no event more than a larger one.** The
Gaussian of variance `v ≠ 0` is its centred law moved to its mean, and that law
has a unimodal density, so `lawRise_map_add_mono_of_unimodal` applies. -/
lemma gaussian_shift_le (v : ℝ≥0) (hv : v ≠ 0) (c a b : ℝ) (hab : |b| ≤ |a|) (A : Set ℝ) :
    gaussianReal (c + b) v A - gaussianReal c v A ≤
      ⨆ B : Set ℝ, gaussianReal (c + a) v B - gaussianReal c v B := by
  have hG : ∀ m, gaussianReal m v = (volume.withDensity (gaussianPDF 0 v)).map (m + ·) := by
    intro m; rw [← gaussianReal_of_var_ne_zero 0 hv, gaussianReal_map_const_add, zero_add]
  have : IsProbabilityMeasure (volume.withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]; infer_instance
  have h := lawRise_map_add_mono_of_unimodal (gaussianPDF_unimodal v).1
    (gaussianPDF_unimodal v).2 c hab
  simp only [lawRise, ← hG] at h
  exact (le_iSup (fun B => gaussianReal (c + b) v B - gaussianReal c v B) A).trans h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Linear micro dynamics with Gaussian noise: region `k` moves to
`∑ l, W k l * y l + τ ω k`. -/
noncomputable def gaussLin (W : ι → ι → ℝ) (τ : ℝ≥0) (ω : ι → ℝ) (y : ι → ℝ) : ι → ℝ :=
  fun k => ∑ l, W k l * y l + τ * ω k

/-- The standard Gaussian noise on every region. -/
noncomputable abbrev stdNoise (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- Region `j`'s noisy quantity `m + τ ω j` has the Gaussian law of mean `m` and
variance `τ²`, on every set. -/
lemma stdNoise_apply {τ : ℝ≥0} (hτ : τ ≠ 0) (m : ℝ) (j : ι) (A : Set ℝ) :
    stdNoise ι {ω | m + τ * ω j ∈ A} = gaussianReal m (τ ^ 2) A := by
  set E : Set ℝ := {z | m + τ * z ∈ A}
  have hset : {ω : ι → ℝ | m + τ * ω j ∈ A} =
      Set.univ.pi (Function.update (fun _ => Set.univ) j E) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h k
      rcases eq_or_ne k j with rfl | hk
      · simpa [E] using h
      · simp [Function.update_of_ne hk]
    · intro h; simpa [E] using h j
  have he : MeasurableEmbedding fun z : ℝ => m + τ * z :=
    ((Homeomorph.mulLeft₀ (τ : ℝ) (by exact_mod_cast hτ)).trans
      (Homeomorph.addLeft m)).measurableEmbedding
  rw [hset, Measure.pi_pi, Finset.prod_eq_single j (fun k _ hk => by
    simp [Function.update_of_ne hk]) (by simp)]
  simp only [Function.update_self]
  change gaussianReal 0 1 ((fun z : ℝ => m + τ * z) ⁻¹' A) = _
  rw [← he.map_apply]
  rw [show (fun z : ℝ => m + τ * z) = (m + ·) ∘ ((τ : ℝ) * ·) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp only [mul_zero, zero_add, mul_one]
  congr 1

/-- Changing one coordinate moves a linear form by its weight times the change. -/
lemma sum_update_mul (w : ι → ℝ) (x : ι → ℝ) (i : ι) (s : ℝ) :
    ∑ l, w l * Function.update x i s l = ∑ l, w l * x l + w i * (s - x i) := by
  have h : ∀ l, Function.update x i s l = x l + (Pi.single i (s - x i) : ι → ℝ) l := by
    intro l; rcases eq_or_ne l i with rfl | hl
    · simp
    · simp [hl]
  simp_rw [h, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The response of region `j`'s next quantity to a change of region `i` under the
linear Gaussian dynamics: the largest rise that shifting a Gaussian of variance
`τ²` by `W j i (s − x i)` makes in the probability of any event. -/
lemma shiftResponse_gaussLin (W : ι → ι → ℝ) {τ : ℝ≥0} (hτ : τ ≠ 0) (x : ι → ℝ) (i j : ι)
    (s : ℝ) :
    shiftResponse (S := fun _ : ι => ℝ) (stdNoise ι) (gaussLin W τ) (fun y => y j) x i s =
      ⨆ A : Set ℝ, gaussianReal (∑ l, W j l * x l + W j i * (s - x i)) (τ ^ 2) A -
        gaussianReal (∑ l, W j l * x l) (τ ^ 2) A := by
  unfold shiftResponse
  congr 1; ext A
  simp only [gaussLin]
  rw [stdNoise_apply hτ, stdNoise_apply hτ, sum_update_mul]

/-- **Under linear Gaussian dynamics the response grows with the change.** -/
theorem shiftResponse_gaussLin_mono (W : ι → ι → ℝ) {τ : ℝ≥0} (hτ : τ ≠ 0) (x : ι → ℝ)
    (i j : ι) {s t : ℝ} (hst : dist s (x i) ≤ dist t (x i)) :
    shiftResponse (S := fun _ : ι => ℝ) (stdNoise ι) (gaussLin W τ) (fun y => y j) x i s ≤
      shiftResponse (S := fun _ : ι => ℝ) (stdNoise ι) (gaussLin W τ) (fun y => y j) x i t := by
  rw [shiftResponse_gaussLin W hτ, shiftResponse_gaussLin W hτ]
  refine iSup_le fun A => gaussian_shift_le _ (pow_ne_zero 2 hτ) _ _ _ ?_ A
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.dist_eq] using hst) (abs_nonneg _)

/-- **Under linear Gaussian dynamics, P is decided at the noise.** For
`0 ≤ σ < Θ`, every change of region `i` above its noise moves region `j`'s next
quantity by at least `θ` exactly when the change of size `σ` does. -/
theorem gaussLin_gradedAboveNoise_iff (W : ι → ι → ℝ) {τ : ℝ≥0} (hτ : τ ≠ 0) (x : ι → ℝ)
    (i j : ι) {σ Θ : ℝ} (hσ : 0 ≤ σ) (hσΘ : σ < Θ) {θ : ENNReal} :
    GradedAboveNoise (S := fun _ : ι => ℝ) (stdNoise ι) (gaussLin W τ) (fun y => y j) x i
        σ Θ θ ↔
      θ ≤ shiftResponse (S := fun _ : ι => ℝ) (stdNoise ι) (gaussLin W τ) (fun y => y j) x i
        (x i + σ) :=
  gradedAboveNoise_iff_of_mono (fun _ _ h => shiftResponse_gaussLin_mono W hτ x i j h)
    (by simp [abs_of_nonneg hσ]) hσΘ

/-- **Coupling under linear Gaussian dynamics.** Two regions are coupled at the
noise floor exactly when a change of each by its own noise moves the other's
next quantity by at least `θ`. -/
theorem gaussLin_coupledAtNoiseFloor_iff (W : ι → ι → ℝ) {τ : ℝ≥0} (hτ : τ ≠ 0)
    (x : ι → ℝ) {σ Θ : ι → ℝ} (hσ : ∀ k, 0 ≤ σ k) (hσΘ : ∀ k, σ k < Θ k) {θ : ENNReal}
    (i j : ι) :
    CoupledAtNoiseFloor (S := fun _ : ι => ℝ) (stdNoise ι) (gaussLin W τ) (fun j y => y j) x
        σ Θ θ i j ↔
      θ ≤ shiftResponse (S := fun _ : ι => ℝ) (stdNoise ι) (gaussLin W τ) (fun y => y j) x i
          (x i + σ i) ∧
        θ ≤ shiftResponse (S := fun _ : ι => ℝ) (stdNoise ι) (gaussLin W τ) (fun y => y i) x j
          (x j + σ j) :=
  and_congr (gaussLin_gradedAboveNoise_iff W hτ x i j (hσ i) (hσΘ i))
    (gaussLin_gradedAboveNoise_iff W hτ x j i (hσ j) (hσΘ j))

end PhysicsOfConsciousness.PhysicalUnity

/-! ## Additive unimodal noise

The Gaussian carrier's reduction holds for any additive noise whose density rises
to one peak and falls after it, heavy-tailed noise included, and each region may
carry its own noise law.

* **`noisyLin`**, **`pi_add_apply`** and **`shiftResponse_noisyLin`.** The micro
  dynamics `y ↦ W y + ω` with independent noise `ω k` of law `ν k` on each region;
  the response of region `j`'s next quantity to a change of region `i` is the rise
  from region `j`'s noise law moved to its mean to the same law moved further by
  `W j i (s − x i)`.
* **`shiftResponse_noisyLin_mono`**, **`noisyLin_gradedAboveNoise_iff`** and
  **`noisyLin_coupledAtNoiseFloor_iff`.** With unimodal noise densities the
  response grows with the size of the change, so graded dependence above noise and
  coupling at the noise floor are decided by one change of the size of the noise.
-/

namespace PhysicsOfConsciousness.PhysicalUnity

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Linear micro dynamics with additive noise: region `k` moves to
`∑ l, W k l * y l + ω k`. -/
def noisyLin (W : ι → ι → ℝ) (ω : ι → ℝ) (y : ι → ℝ) : ι → ℝ :=
  fun k => ∑ l, W k l * y l + ω k

/-- Region `j`'s noisy quantity `m + ω j` has region `j`'s noise law moved to `m`,
on every set. -/
lemma pi_add_apply (ν : ι → Measure ℝ) [∀ k, IsProbabilityMeasure (ν k)] (m : ℝ) (j : ι)
    (A : Set ℝ) : Measure.pi ν {ω | m + ω j ∈ A} = (ν j).map (m + ·) A := by
  have hset : {ω : ι → ℝ | m + ω j ∈ A} =
      Set.univ.pi (Function.update (fun _ => Set.univ) j ((m + ·) ⁻¹' A)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h k
      rcases eq_or_ne k j with rfl | hk
      · simpa using h
      · simp [Function.update_of_ne hk]
    · intro h; simpa using h j
  rw [hset, Measure.pi_pi, Finset.prod_eq_single j (fun k _ hk => by
    simp [Function.update_of_ne hk]) (by simp), Function.update_self, map_add_apply]

/-- The response of region `j`'s next quantity to a change of region `i` under
linear dynamics with additive noise: the rise from region `j`'s noise law moved to
its mean to the same law moved further by `W j i (s − x i)`. -/
lemma shiftResponse_noisyLin (W : ι → ι → ℝ) (ν : ι → Measure ℝ)
    [∀ k, IsProbabilityMeasure (ν k)] (x : ι → ℝ) (i j : ι) (s : ℝ) :
    shiftResponse (S := fun _ : ι => ℝ) (Measure.pi ν) (noisyLin W) (fun y => y j) x i s =
      lawRise ((ν j).map ((∑ l, W j l * x l) + ·))
        ((ν j).map ((∑ l, W j l * x l + W j i * (s - x i)) + ·)) := by
  unfold shiftResponse lawRise
  congr 1; ext A
  simp only [noisyLin, sum_update_mul]
  rw [← pi_add_apply, ← pi_add_apply]

/-- **Under linear dynamics with additive unimodal noise the response grows with
the change.** -/
theorem shiftResponse_noisyLin_mono (W : ι → ι → ℝ) {p : ι → ℝ → ENNReal}
    [∀ k, IsProbabilityMeasure (volume.withDensity (p k))] {M : ι → ℝ}
    (hup : ∀ k, MonotoneOn (p k) (Set.Iic (M k))) (hdown : ∀ k, AntitoneOn (p k) (Set.Ici (M k)))
    (x : ι → ℝ) (i j : ι) {s t : ℝ} (hst : dist s (x i) ≤ dist t (x i)) :
    shiftResponse (S := fun _ : ι => ℝ) (Measure.pi fun k => volume.withDensity (p k))
        (noisyLin W) (fun y => y j) x i s ≤
      shiftResponse (S := fun _ : ι => ℝ) (Measure.pi fun k => volume.withDensity (p k))
        (noisyLin W) (fun y => y j) x i t := by
  rw [shiftResponse_noisyLin, shiftResponse_noisyLin]
  refine lawRise_map_add_mono_of_unimodal (hup j) (hdown j) _ ?_
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.dist_eq] using hst) (abs_nonneg _)

/-- **Under linear dynamics with additive unimodal noise, P is decided at the
noise.** For `0 ≤ σ < Θ`, every change of region `i` above its noise moves region
`j`'s next quantity by at least `θ` exactly when the change of size `σ` does. -/
theorem noisyLin_gradedAboveNoise_iff (W : ι → ι → ℝ) {p : ι → ℝ → ENNReal}
    [∀ k, IsProbabilityMeasure (volume.withDensity (p k))] {M : ι → ℝ}
    (hup : ∀ k, MonotoneOn (p k) (Set.Iic (M k))) (hdown : ∀ k, AntitoneOn (p k) (Set.Ici (M k)))
    (x : ι → ℝ) (i j : ι) {σ Θ : ℝ} (hσ : 0 ≤ σ) (hσΘ : σ < Θ) {θ : ENNReal} :
    GradedAboveNoise (S := fun _ : ι => ℝ) (Measure.pi fun k => volume.withDensity (p k))
        (noisyLin W) (fun y => y j) x i σ Θ θ ↔
      θ ≤ shiftResponse (S := fun _ : ι => ℝ) (Measure.pi fun k => volume.withDensity (p k))
        (noisyLin W) (fun y => y j) x i (x i + σ) :=
  gradedAboveNoise_iff_of_mono (fun _ _ h => shiftResponse_noisyLin_mono W hup hdown x i j h)
    (by simp [abs_of_nonneg hσ]) hσΘ

/-- **Coupling under additive unimodal noise.** Two regions are coupled at the
noise floor exactly when a change of each by its own noise moves the other's next
quantity by at least `θ`. -/
theorem noisyLin_coupledAtNoiseFloor_iff (W : ι → ι → ℝ) {p : ι → ℝ → ENNReal}
    [∀ k, IsProbabilityMeasure (volume.withDensity (p k))] {M : ι → ℝ}
    (hup : ∀ k, MonotoneOn (p k) (Set.Iic (M k))) (hdown : ∀ k, AntitoneOn (p k) (Set.Ici (M k)))
    (x : ι → ℝ) {σ Θ : ι → ℝ} (hσ : ∀ k, 0 ≤ σ k) (hσΘ : ∀ k, σ k < Θ k) {θ : ENNReal}
    (i j : ι) :
    CoupledAtNoiseFloor (S := fun _ : ι => ℝ) (Measure.pi fun k => volume.withDensity (p k))
        (noisyLin W) (fun j y => y j) x σ Θ θ i j ↔
      θ ≤ shiftResponse (S := fun _ : ι => ℝ) (Measure.pi fun k => volume.withDensity (p k))
          (noisyLin W) (fun y => y j) x i (x i + σ i) ∧
        θ ≤ shiftResponse (S := fun _ : ι => ℝ) (Measure.pi fun k => volume.withDensity (p k))
          (noisyLin W) (fun y => y i) x j (x j + σ j) :=
  and_congr (noisyLin_gradedAboveNoise_iff W hup hdown x i j (hσ i) (hσΘ i))
    (noisyLin_gradedAboveNoise_iff W hup hdown x j i (hσ j) (hσΘ j))

end PhysicsOfConsciousness.PhysicalUnity
