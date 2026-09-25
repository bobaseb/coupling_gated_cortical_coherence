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

The theorems say nothing about which readouts cortex uses; that is the
empirical content of the premise. Non-vacuity of both sides — a thresholded
readout that is not constant, and a diffusively coupled pair whose content is
physically enforced — is `Examples/PhysicalUnity.lean`.
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

end PhysicsOfConsciousness.PhysicalUnity
