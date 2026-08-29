import Mathlib
import PhysicsOfConsciousness.Phase7_HardwareComparison

/-!
# Phase 7 (continued) — Wiring rigidity, and what "continuous" can mean

`Phase7_HardwareComparison.lean` proves a reallocation step from the hypothesis
`is_strictly_suboptimal`, which asserts that the given coupling matrix wastes
weight on a badly-correlated pair. That hypothesis carries most of the intended
conclusion, and nothing in that file distinguishes a continuous substrate from a
rigid lattice: both matrices live on one `Fintype`. This file addresses both
defects, in the two ways that are actually available.

## §1–2. Rigidity as a *support constraint* (finite, resource-matched)

An architecture is modelled by the set `S` of site-pairs it has a wire for. A
coupling is *realizable* for that architecture if it is a valid coupling, meets a
resource budget `R`, and vanishes on unwired pairs. Then:

* `totalCorrelation_le_of_realizable` — a realizable coupling cannot beat
  `R · M`, where `M` bounds the phase correlation over the *wired* pairs.
* `exists_realizable_pair` — that bound is attained, by putting the whole budget
  on one wired pair.
* `rigid_is_strictly_suboptimal` — **`is_strictly_suboptimal` is now derived, not
  assumed.** If the best-correlated pair in the substrate is one the architecture
  has no wire for, every realizable coupling satisfies the hypothesis that
  `exists_better_coupling_allocation` needs.
* `rigid_gap` — and the improvement is quantitative: at least
  `R · (best unwired correlation − best wired correlation) > 0`.

This is resource-matched and honest, but it is a statement about *fixed wiring
support*, not about continuity. It says: an architecture whose wires do not reach
the currently best-correlated pair is strictly beaten, at equal resource, by one
that does.

## §3. Continuity as a *measure-theoretic* distinction

Here the two architectures genuinely live in different types. The field
correlation functional integrates a coupling kernel against `μ ⊗ μ` on a
substrate `X`, as in `Phase8_ContinuousField`. An architecture with finitely many
sites is a `Finset X`; a field-coupled patch is a set of positive measure.

* `fieldCorrelation_sited_eq_zero` — on a substrate with no atoms, a kernel
  supported on finitely many sites contributes **exactly zero** field
  correlation, whatever weights it carries.
* `fieldCorrelation_patchKernel` — a patch kernel of strength `c` on `U` achieves
  `c · μ(U)²`.
* `sited_architecture_below_field_optimum` — hence no finite architecture reaches
  what a positive-measure patch reaches.

## What this does and does not establish

§3 is a sharp separation *within the field functional*, and that is exactly its
limit: the comparison is not resource-matched, because a measure-zero substrate
also has zero resource in the `μ ⊗ μ` sense. It says the continuum coupling
energy is blind to a finitely-sited architecture, which is a statement about the
model's observable rather than a proof that digital hardware computes worse. The
resource-matched content is §1–2, and there "continuous" is doing no work — the
operative property is that the wiring support misses the best pair.

Read together: the manuscript's hardware corollary is supported by §1–2 as a
claim about fixed wiring, and by §3 as a claim about which functional a
measure-zero substrate can register in. Neither is a proof that a von Neumann
machine cannot be conscious, and we do not claim one.
-/

open Finset MeasureTheory

namespace PhysicsOfConsciousness

/-! ## 1. Realizable couplings of a wired architecture -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Total phase correlation achieved by a coupling matrix — the quantity
`exists_better_coupling_allocation` increases, and the negative of the Kuramoto
coupling potential up to the factor `-1/2`. -/
noncomputable def totalCorrelation (theta : V → ℝ) (A : V → V → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * Real.cos (theta j - theta i)

/-- The couplings an architecture with wiring pattern `S` can realize at resource
budget `R`: a valid coupling, meeting the budget, and carrying **no weight on
pairs it has no wire for**. The last clause is the formal content of
"rigid": weights are tunable, the wiring is not. -/
def RealizableIn (S : Finset (V × V)) (R : ℝ) (A : V → V → ℝ) : Prop :=
  is_valid_coupling A ∧ total_coupling_resources A = R ∧ ∀ p : V × V, p ∉ S → A p.1 p.2 = 0

/-- **A rigid architecture cannot beat its own best wire.** If every wired pair
has phase correlation at most `M`, no realizable coupling exceeds `R · M`. -/
theorem totalCorrelation_le_of_realizable
    (S : Finset (V × V)) (R M : ℝ) (theta : V → ℝ) (A : V → V → ℝ)
    (hA : RealizableIn S R A)
    (hM : ∀ p ∈ S, Real.cos (theta p.2 - theta p.1) ≤ M) :
    totalCorrelation theta A ≤ R * M := by
  obtain ⟨hvalid, hres, hzero⟩ := hA
  have key : ∀ i : V, ∀ j : V, A i j * Real.cos (theta j - theta i) ≤ A i j * M := by
    intro i j
    by_cases h : (i, j) ∈ S
    · exact mul_le_mul_of_nonneg_left (hM (i, j) h) (hvalid i j).1
    · rw [hzero (i, j) h]; simp
  calc totalCorrelation theta A ≤ ∑ i, ∑ j, A i j * M :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ j, A i j) * M := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    _ = R * M := by rw [show (∑ i, ∑ j, A i j) = R from hres]

/-- The bound is attained: the whole budget on a single wired pair. Also the
construction used to build the strictly better *unwired* allocation in
`rigid_gap`. -/
theorem exists_realizable_pair (S : Finset (V × V)) (R : ℝ) (hR : 0 ≤ R)
    (theta : V → ℝ) (a b : V) (hab : a ≠ b) (ha : (a, b) ∈ S) (hb : (b, a) ∈ S) :
    ∃ A, RealizableIn S R A ∧ totalCorrelation theta A = R * Real.cos (theta b - theta a) := by
  refine ⟨fun i j => if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then R / 2 else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j
    refine ⟨?_, ?_⟩
    · dsimp only; split <;> linarith
    · dsimp only
      refine if_congr ?_ rfl rfl
      constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [right; left; right; left] <;> exact ⟨h2, h1⟩
  · unfold total_coupling_resources
    rw [sum_sym_pair hab (fun _ _ => R / 2)]
    ring
  · rintro ⟨i, j⟩ hp
    dsimp only
    have hnot : ¬ ((i = a ∧ j = b) ∨ (i = b ∧ j = a)) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hp ha
      · exact hp hb
    simp [hnot]
  · unfold totalCorrelation
    have hrw : ∀ i j : V,
        (if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then R / 2 else 0) * Real.cos (theta j - theta i)
          = if (i = a ∧ j = b) ∨ (i = b ∧ j = a)
            then (R / 2) * Real.cos (theta j - theta i) else 0 := by
      intro i j; split <;> simp
    simp_rw [hrw]
    rw [sum_sym_pair hab (fun i j => (R / 2) * Real.cos (theta j - theta i))]
    rw [show theta a - theta b = -(theta b - theta a) by ring, Real.cos_neg]
    ring

/-! ## 2. Rigidity implies the hypothesis Phase 7 had to assume -/

/-- Positive budget forces some wire to carry weight. -/
private lemma exists_pos_of_realizable
    (S : Finset (V × V)) (R : ℝ) (hR : 0 < R) (A : V → V → ℝ) (hA : RealizableIn S R A) :
    ∃ i j, A i j > 0 ∧ (i, j) ∈ S := by
  obtain ⟨hvalid, hres, hzero⟩ := hA
  by_contra hcon
  push Not at hcon
  have hall : ∀ i : V, ∀ j : V, A i j = 0 := by
    intro i j
    by_cases h : (i, j) ∈ S
    · have h1 : ¬ (A i j > 0) := fun hp => hcon i j hp h
      have h2 : (0 : ℝ) ≤ A i j := (hvalid i j).1
      linarith [not_lt.mp h1]
    · exact hzero (i, j) h
  rw [total_coupling_resources] at hres
  simp [hall] at hres
  linarith

/-- **`is_strictly_suboptimal` is derived, not assumed.** If the substrate has a
pair `(k, l)` whose phase correlation strictly exceeds every wired pair's, then
every coupling the architecture can realize at a positive budget is strictly
suboptimal in the sense `exists_better_coupling_allocation` requires. The
hypothesis that file had to take on faith is now a consequence of the wiring. -/
theorem rigid_is_strictly_suboptimal
    (S : Finset (V × V)) (R M : ℝ) (hR : 0 < R) (theta : V → ℝ) (k l : V)
    (A : V → V → ℝ) (hA : RealizableIn S R A)
    (hM : ∀ p ∈ S, Real.cos (theta p.2 - theta p.1) ≤ M)
    (hbetter : M < Real.cos (theta l - theta k)) :
    is_strictly_suboptimal A theta := by
  obtain ⟨i0, j0, hpos, hmem⟩ := exists_pos_of_realizable S R hR A hA
  exact ⟨i0, j0, k, l, hpos, lt_of_le_of_lt (hM (i0, j0) hmem) hbetter⟩

/-- **The rigidity gap is quantitative.** Against any coupling the architecture
can realize, an unconstrained reallocation of the *same* budget onto the best
pair gains at least `R · (best unwired correlation − best wired bound)`, which is
strictly positive. -/
theorem rigid_gap
    (S : Finset (V × V)) (R M : ℝ) (hR : 0 < R) (theta : V → ℝ) (k l : V) (hkl : k ≠ l)
    (A : V → V → ℝ) (hA : RealizableIn S R A)
    (hM : ∀ p ∈ S, Real.cos (theta p.2 - theta p.1) ≤ M)
    (hbetter : M < Real.cos (theta l - theta k)) :
    ∃ A', is_valid_coupling A' ∧ total_coupling_resources A' = R ∧
      0 < R * (Real.cos (theta l - theta k) - M) ∧
      totalCorrelation theta A' - totalCorrelation theta A
        ≥ R * (Real.cos (theta l - theta k) - M) := by
  obtain ⟨A', hA'real, hA'val⟩ :=
    exists_realizable_pair (S := S ∪ {(k, l), (l, k)}) R hR.le theta k l hkl
      (by simp) (by simp)
  obtain ⟨hvalid', hres', _⟩ := hA'real
  refine ⟨A', hvalid', hres', by nlinarith, ?_⟩
  have hub := totalCorrelation_le_of_realizable S R M theta A hA hM
  rw [hA'val]
  nlinarith [hub]

/-! ## 3. The continuous/discrete distinction, at the level of types

In §1–2 both architectures were matrices on one `Fintype`; the operative
difference was the wiring support. Here the difference is genuinely typed: a
finitely-sited architecture is a `Finset X`, a field-coupled region is a set of
positive measure, and the functional they are compared in is the continuum
coupling energy of `Phase8_ContinuousField`. -/

section Continuum

variable {X : Type*} [MeasurableSpace X]

/-- The continuum coupling energy: a kernel integrated against `μ ⊗ μ`. This is
the field-theoretic analogue of `totalCorrelation`. -/
noncomputable def fieldCorrelation (μ : Measure X) (theta : X → ℝ) (K : X → X → ℝ) : ℝ :=
  ∫ x, (∫ y, K x y * Real.cos (theta y - theta x) ∂μ) ∂μ

/-- A *sited* architecture: every coupling it carries originates at one of
finitely many sites. This is the formal content of "discrete hardware" here —
finitely many transistors in a volume of tissue. -/
def SitedOn (F : Finset X) (K : X → X → ℝ) : Prop := ∀ x, x ∉ F → ∀ y, K x y = 0

/-- **A finitely-sited architecture registers nothing in the field functional.**
On a substrate whose measure has no atoms, a kernel supported on finitely many
sites contributes exactly zero coupling energy, whatever weights it carries and
whatever the phase field does. -/
theorem fieldCorrelation_sited_eq_zero (μ : Measure X) [NullSingletonClass μ]
    (F : Finset X) (K : X → X → ℝ) (hK : SitedOn F K) (theta : X → ℝ) :
    fieldCorrelation μ theta K = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [F.finite_toSet.countable.ae_notMem μ] with x hx
  simp [hK x hx]

/-- A patch of field coupling: uniform strength `c` between every pair of points
of `U`. -/
noncomputable def patchKernel (U : Set X) (c : ℝ) : X → X → ℝ :=
  fun x y => c * U.indicator (fun _ => (1 : ℝ)) x * U.indicator (fun _ => (1 : ℝ)) y

omit [MeasurableSpace X] in
lemma patchKernel_symm (U : Set X) (c : ℝ) (x y : X) :
    patchKernel U c x y = patchKernel U c y x := by
  unfold patchKernel; ring

omit [MeasurableSpace X] in
lemma patchKernel_nonneg (U : Set X) {c : ℝ} (hc : 0 ≤ c) (x y : X) :
    0 ≤ patchKernel U c x y := by
  unfold patchKernel
  have h1 : 0 ≤ U.indicator (fun _ => (1 : ℝ)) x := Set.indicator_nonneg (by simp) x
  have h2 : 0 ≤ U.indicator (fun _ => (1 : ℝ)) y := Set.indicator_nonneg (by simp) y
  positivity

/-- A patch of positive measure achieves `c · μ(U)²` at a locked phase field. -/
theorem fieldCorrelation_patchKernel (μ : Measure X) (U : Set X) (hU : MeasurableSet U) (c : ℝ) :
    fieldCorrelation μ (fun _ => 0) (patchKernel U c) = c * (μ U).toReal ^ 2 := by
  have hind : (∫ y, U.indicator (fun _ => (1 : ℝ)) y ∂μ) = (μ U).toReal := by
    rw [integral_indicator_const (1 : ℝ) hU]
    simp [measureReal_def]
  have hinner : ∀ x : X,
      (∫ y, patchKernel U c x y * Real.cos ((0 : ℝ) - 0) ∂μ)
        = (c * U.indicator (fun _ => (1 : ℝ)) x) * (μ U).toReal := by
    intro x
    have hrw : ∀ y : X, patchKernel U c x y * Real.cos ((0 : ℝ) - 0)
        = (c * U.indicator (fun _ => (1 : ℝ)) x) * U.indicator (fun _ => (1 : ℝ)) y := by
      intro y; simp [patchKernel]
    simp_rw [hrw]
    rw [integral_const_mul, hind]
  simp only [fieldCorrelation, hinner]
  rw [integral_mul_const, integral_const_mul, hind]
  ring

/-- **No finitely-sited architecture reaches what a field patch reaches.** The
separation is typed: `F : Finset X` against a set of positive measure. -/
theorem sited_architecture_below_field_optimum (μ : Measure X) [NullSingletonClass μ]
    (F : Finset X) (K : X → X → ℝ) (hK : SitedOn F K) (theta : X → ℝ)
    (U : Set X) (hU : MeasurableSet U) (hUpos : 0 < μ U) (hUfin : μ U ≠ ⊤)
    (c : ℝ) (hc : 0 < c) :
    fieldCorrelation μ theta K < fieldCorrelation μ (fun _ => 0) (patchKernel U c) := by
  rw [fieldCorrelation_sited_eq_zero μ F K hK theta, fieldCorrelation_patchKernel μ U hU c]
  have ht : 0 < (μ U).toReal := ENNReal.toReal_pos hUpos.ne' hUfin
  positivity

end Continuum

end PhysicsOfConsciousness
