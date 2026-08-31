/-
  Phase 1 (continued): what a finite phase space actually buys.

  `Phase1_Primitives.lean` sets up spacetime, a metric, a symmetry group and an
  action principle. Of those, the symmetry group and the metric are consumed by
  nothing: `ContinuousSymmetryGroup` and `PseudoRiemannianManifold` are
  inhabited (`Examples.lean` §11, §12) and no theorem anywhere in the
  development takes either as a hypothesis. That is still true after this file
  and the manuscript says so.

  What the *other half* of the first premise supplies — that the phase space of
  a localized system is finite — is consumed here, and this file exists so that
  the premise is discharged by theorems rather than by a footnote.

  Three things are proved.

  1. **Capacity.** `shannon_entropy_le_log_card`: a distribution on a finite
     type carries at most `log |X|` nats, with equality exactly at the uniform
     distribution (`shannon_entropy_eq_log_card_iff`). This is the sharp form of
     "finite phase space ⟹ bounded information capacity", and it is the
     sentence the manuscript's Axiom 1 section actually needs.

  2. **The source can exceed the capacity.** A stream of `k` perturbations drawn
     from an alphabet `P` has `|P|^k` histories. Once `|X| < |P|^k` the map from
     histories to final states is not injective (`absorb_not_injective`), so two
     distinct histories leave the system in the same state, and the entropy of
     the source strictly exceeds anything the system can hold
     (`source_entropy_exceeds_capacity`). This is Derivation 2's opening
     sentence — "it cannot absorb an infinite sequence of incoming perturbations
     and must overwrite old internal states" — as a theorem.

  3. **Overwriting costs heat.** On a finite phase space, non-surjectivity of the
     update *is* non-injectivity (`is_erasure_of_not_surjective`), so
     `landauers_principle` applies: `finite_phase_space_dissipates`. Finiteness
     is what makes that step go through, and it is the only place in the chain
     where the first premise does work that could not be done without it.

  **What this does not establish.** Nothing here derives finiteness of the phase
  space; it is assumed, as `[Fintype]`. Nothing here concerns the Poincaré
  group, Noether's theorem, or a conserved quantity — see the note on O12 in
  `tasks/todo.md`, which stays closed. And point 3 is not a claim that losing
  the history is *by itself* dissipative: the joint map `(s, w) ↦ (absorb u s w, w)`
  that keeps the record is injective and dissipates nothing. Heat appears when
  the incoming register is refreshed rather than retained, which is what
  `absorbStep` models and what `absorbStep_not_surjective` exhibits. That is the
  Norton / Shenker distinction the manuscript discusses in Derivation 2, and it
  is respected here rather than elided.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics

open BigOperators

namespace PhysicsOfConsciousness

/-! ## 1. The capacity of a finite phase space -/

section Capacity

variable {n : Type*} [Fintype n]

/-- The uniform distribution on a finite type. -/
noncomputable def uniformDist (n : Type*) [Fintype n] : n → ℝ :=
  fun _ => (Fintype.card n : ℝ)⁻¹

theorem is_prob_dist_uniformDist [Nonempty n] : is_prob_dist (uniformDist n) := by
  have hN : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun i => inv_nonneg.mpr (Nat.cast_nonneg _), ?_⟩
  calc ∑ _i : n, uniformDist n _i
      = (Fintype.card n : ℝ) * (Fintype.card n : ℝ)⁻¹ := by
        simp [uniformDist, Finset.card_univ]
    _ = 1 := mul_inv_cancel₀ hN

/-- The uniform distribution attains the bound: `H = log |X|`. -/
theorem shannon_entropy_uniformDist [Nonempty n] :
    shannon_entropy (uniformDist n) = Real.log (Fintype.card n) := by
  have hN : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  show -∑ _i : n, (Fintype.card n : ℝ)⁻¹ * Real.log ((Fintype.card n : ℝ)⁻¹) = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_inv]
  field_simp

/-- The pointwise step of Gibbs' inequality against the uniform distribution:
`log x ≤ x - 1` at `x = 1/(Np)`, multiplied by `p`. The `p = 0` case is
separate because `0 * log 0 = 0` while the bound has slack `1/N` there — which
is exactly why a distribution with a zero cannot attain the capacity. -/
private lemma capacity_term_le {N p : ℝ} (hN : 0 < N) (hp : 0 ≤ p) :
    -p * Real.log p - p * Real.log N ≤ 1 / N - p := by
  rcases hp.eq_or_lt with rfl | hpos
  · norm_num
    positivity
  · have hNp : 0 < N * p := mul_pos hN hpos
    have hinv : 0 < (N * p)⁻¹ := inv_pos.mpr hNp
    have hlog : Real.log ((N * p)⁻¹) ≤ (N * p)⁻¹ - 1 := Real.log_le_sub_one_of_pos hinv
    have hexp : Real.log ((N * p)⁻¹) = -(Real.log N + Real.log p) := by
      rw [Real.log_inv, Real.log_mul hN.ne' hpos.ne']
    have hcancel : p * (N * p)⁻¹ = 1 / N := by field_simp
    calc -p * Real.log p - p * Real.log N
        = p * Real.log ((N * p)⁻¹) := by rw [hexp]; ring
      _ ≤ p * ((N * p)⁻¹ - 1) := mul_le_mul_of_nonneg_left hlog hp
      _ = 1 / N - p := by rw [mul_sub, hcancel]; ring

/-- The strict form: the pointwise bound has slack at every `p ≠ 1/N`. -/
private lemma capacity_term_lt {N p : ℝ} (hN : 0 < N) (hp : 0 ≤ p) (hne : p ≠ 1 / N) :
    -p * Real.log p - p * Real.log N < 1 / N - p := by
  rcases hp.eq_or_lt with rfl | hpos
  · norm_num
    positivity
  · have hNp : 0 < N * p := mul_pos hN hpos
    have hinv : 0 < (N * p)⁻¹ := inv_pos.mpr hNp
    have hne' : (N * p)⁻¹ ≠ 1 := by
      intro h
      apply hne
      have : N * p = 1 := by
        have := congrArg (fun x : ℝ => x⁻¹) h
        simpa [inv_inv] using this
      field_simp at this ⊢
      linarith
    have hlog : Real.log ((N * p)⁻¹) < (N * p)⁻¹ - 1 := Real.log_lt_sub_one_of_pos hinv hne'
    have hexp : Real.log ((N * p)⁻¹) = -(Real.log N + Real.log p) := by
      rw [Real.log_inv, Real.log_mul hN.ne' hpos.ne']
    have hcancel : p * (N * p)⁻¹ = 1 / N := by field_simp
    calc -p * Real.log p - p * Real.log N
        = p * Real.log ((N * p)⁻¹) := by rw [hexp]; ring
      _ < p * ((N * p)⁻¹ - 1) := by
          exact mul_lt_mul_of_pos_left hlog hpos
      _ = 1 / N - p := by rw [mul_sub, hcancel]; ring

/-- Rewriting used by both bounds: with `∑ pᵢ = 1`, the entropy deficit
`H(p) - log N` is a single sum of pointwise terms. -/
private lemma capacity_sum_eq {n : Type*} [Fintype n] {p : n → ℝ} (hsum : ∑ i, p i = 1)
    (N : ℝ) :
    ∑ i, (-p i * Real.log (p i) - p i * Real.log N)
      = shannon_entropy p - Real.log N := by
  have h1 : ∀ i : n, -p i * Real.log (p i) - p i * Real.log N
      = -(p i * Real.log (p i)) - p i * Real.log N := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
      ← Finset.sum_mul, hsum, one_mul, Finset.sum_neg_distrib]
  rfl

private lemma capacity_rhs_sum {n : Type*} [Fintype n] [Nonempty n] {p : n → ℝ}
    (hsum : ∑ i, p i = 1) :
    ∑ _i : n, (1 / (Fintype.card n : ℝ) - p _i) = 0 := by
  have hN : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one_div, div_self hN, sub_self]


/--
**Bounded information capacity.** A probability distribution on a finite phase
space carries at most `log |X|` nats.

This is the theorem the manuscript's first premise needs and the one it did not
have. Its only hypothesis about the system is `[Fintype n]`: finiteness of the
phase space, and nothing else. No symmetry group, no metric, no action.
-/
theorem shannon_entropy_le_log_card {n : Type*} [Fintype n] [Nonempty n]
    (p : n → ℝ) (hp : is_prob_dist p) :
    shannon_entropy p ≤ Real.log (Fintype.card n) := by
  obtain ⟨hnn, hsum⟩ := hp
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have hle := Finset.sum_le_sum (s := (Finset.univ : Finset n))
    (fun i _ => capacity_term_le hN (hnn i))
  rw [capacity_sum_eq hsum _, capacity_rhs_sum hsum] at hle
  linarith

/--
**The bound is strict away from the uniform distribution.** One state carrying
the wrong weight is enough.
-/
theorem shannon_entropy_lt_log_card_of_ne_uniform {n : Type*} [Fintype n] [Nonempty n]
    (p : n → ℝ) (hp : is_prob_dist p) (j : n) (hj : p j ≠ (Fintype.card n : ℝ)⁻¹) :
    shannon_entropy p < Real.log (Fintype.card n) := by
  obtain ⟨hnn, hsum⟩ := hp
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have hj' : p j ≠ 1 / (Fintype.card n : ℝ) := by rwa [one_div]
  have hlt := Finset.sum_lt_sum (s := (Finset.univ : Finset n))
    (fun i _ => capacity_term_le hN (hnn i))
    ⟨j, Finset.mem_univ j, capacity_term_lt hN (hnn j) hj'⟩
  rw [capacity_sum_eq hsum _, capacity_rhs_sum hsum] at hlt
  linarith

/--
**Capacity is attained exactly at the uniform distribution.**

The `←` direction is `shannon_entropy_uniformDist`; the `→` direction is the
contrapositive of the strict bound. Together they say that `log |X|` is not a
crude over-estimate of what a finite phase space can hold but the exact figure,
reached by one distribution and no other.
-/
theorem shannon_entropy_eq_log_card_iff {n : Type*} [Fintype n] [Nonempty n]
    (p : n → ℝ) (hp : is_prob_dist p) :
    shannon_entropy p = Real.log (Fintype.card n) ↔ p = uniformDist n := by
  constructor
  · intro heq
    by_contra hne
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    exact absurd heq (ne_of_lt (shannon_entropy_lt_log_card_of_ne_uniform p hp j hj))
  · rintro rfl
    exact shannon_entropy_uniformDist

end Capacity

/-! ## 2. A finite phase space cannot record an unbounded stream -/

section Overwriting

/-- The state reached from `s₀` after absorbing the perturbation word `w`. The
update `u` is arbitrary: nothing below assumes it is injective, reversible, or
even that it depends on the perturbation. -/
def absorb {sys P : Type*} (u : sys → P → sys) (s₀ : sys) {k : ℕ} (w : Fin k → P) : sys :=
  List.foldl u s₀ (List.ofFn w)

/--
**Histories collide.** Once the number of perturbation histories exceeds the
number of states, the map from histories to final states is not injective.

This is pigeonhole and nothing more, which is the point: the physical content is
carried entirely by `Fintype.card sys < Fintype.card P ^ k`, i.e. by the phase
space being finite while the stream is not.
-/
theorem absorb_not_injective {sys P : Type*} [Fintype sys] [Fintype P]
    (u : sys → P → sys) (s₀ : sys) (k : ℕ)
    (h : Fintype.card sys < Fintype.card P ^ k) :
    ¬ Function.Injective (fun w : Fin k → P => absorb u s₀ w) := by
  apply Fintype.not_injective_of_card_lt
  rwa [Fintype.card_fun, Fintype.card_fin]

/-- The same statement with the two indistinguishable histories produced. -/
theorem exists_indistinguishable_histories {sys P : Type*} [Fintype sys] [Fintype P]
    (u : sys → P → sys) (s₀ : sys) (k : ℕ)
    (h : Fintype.card sys < Fintype.card P ^ k) :
    ∃ w₁ w₂ : Fin k → P, w₁ ≠ w₂ ∧ absorb u s₀ w₁ = absorb u s₀ w₂ := by
  obtain ⟨w₁, w₂, heq, hne⟩ := Function.not_injective_iff.mp (absorb_not_injective u s₀ k h)
  exact ⟨w₁, w₂, hne, heq⟩

/--
**The source outruns the capacity.** Under the same hypothesis, the entropy of
the uniform law on histories strictly exceeds the entropy of *every* law on the
system's states.

This is the entropic form of the collision above, and it is where §1 and §2 meet:
the left-hand side is bounded by `log |sys|` because the phase space is finite,
and the right-hand side is `log (|P|^k)`, which the hypothesis makes larger.
-/
theorem source_entropy_exceeds_capacity {sys P : Type*} [Fintype sys] [Nonempty sys]
    [Fintype P] [Nonempty P] (k : ℕ)
    (h : Fintype.card sys < Fintype.card P ^ k)
    (p : sys → ℝ) (hp : is_prob_dist p) :
    shannon_entropy p < shannon_entropy (uniformDist (Fin k → P)) := by
  have hcard : Fintype.card (Fin k → P) = Fintype.card P ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hpos : (0 : ℝ) < Fintype.card sys := Nat.cast_pos.mpr Fintype.card_pos
  calc shannon_entropy p
      ≤ Real.log (Fintype.card sys) := shannon_entropy_le_log_card p hp
    _ < Real.log (Fintype.card (Fin k → P)) := by
        apply Real.log_lt_log hpos
        rw [hcard]
        exact_mod_cast h
    _ = shannon_entropy (uniformDist (Fin k → P)) := shannon_entropy_uniformDist.symm

end Overwriting

/-! ## 3. On a finite phase space, an unreachable state means dissipated heat -/

section Dissipation

/--
**Finiteness turns "cannot reach" into "erases".** On a finite phase space a
non-surjective update is non-injective, which is exactly `is_erasure`.

On an infinite phase space this is false — `Nat.succ` misses `0` and is
injective — so this lemma is the point at which the first premise is doing work
that could not be done without it.
-/
theorem is_erasure_of_not_surjective {X : Type*} [Finite X] (t : X → X)
    (h : ¬ Function.Surjective t) : is_erasure t :=
  fun hinj => h (Finite.injective_iff_surjective.mp hinj)

/--
**Derivation 2, with its first premise supplied by Derivation 1's other half.**
An update of a finite phase space that cannot reach every state dissipates
strictly positive heat.

The heat itself comes from `landauers_principle`, which is `StatisticalMechanics`
plus `landauer_from_reversibility`; what finiteness contributes is the step from
the physically checkable hypothesis (some state is unreachable) to the hypothesis
Landauer's argument wants (the update is many-to-one).
-/
theorem finite_phase_space_dissipates {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [StatisticalMechanics X] (t : X → X) (h : ¬ Function.Surjective t) :
    heat_dissipation t > 0 :=
  landauers_principle t (is_erasure_of_not_surjective t h)

/-- One step of absorption on the joint register `(state, incoming perturbation)`,
with the incoming slot refreshed to `p₀` rather than retained. -/
def absorbStep {sys P : Type*} (u : sys → P → sys) (p₀ : P) : sys × P → sys × P :=
  fun sp => (u sp.1 sp.2, p₀)

/-- **Refreshing the incoming register makes the joint step non-surjective**, as
soon as the perturbation alphabet has more than one letter: every value has `p₀`
in its second slot, so `(s, p₁)` is unreachable. -/
theorem absorbStep_not_surjective {sys P : Type*} [Nonempty sys]
    (u : sys → P → sys) {p₀ p₁ : P} (hne : p₁ ≠ p₀) :
    ¬ Function.Surjective (absorbStep u p₀) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (Classical.arbitrary sys, p₁)
  exact hne (congrArg Prod.snd hx).symm

/-- Hence absorbing a perturbation onto a refreshed register is an erasure. The
record-keeping map `(s, w) ↦ (absorb u s w, w)` is injective and would dissipate
nothing; this one is not, and that difference — not the loss of the history as
such — is what Landauer's bound charges for. -/
theorem absorbStep_is_erasure {sys P : Type*} [Finite sys] [Finite P] [Nonempty sys]
    (u : sys → P → sys) {p₀ p₁ : P} (hne : p₁ ≠ p₀) :
    is_erasure (absorbStep u p₀) :=
  is_erasure_of_not_surjective _ (absorbStep_not_surjective u hne)

end Dissipation

end PhysicsOfConsciousness
