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
