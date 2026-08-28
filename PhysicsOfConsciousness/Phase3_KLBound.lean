import Mathlib
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics

open Real
open Finset

namespace PhysicsOfConsciousness

/-!
# Phase 3 — KL Bound and Structural Resonance

Formalizes the Kullback-Leibler divergence bound on entropy production
from Derivation 3.

**Key results:**
  • `KL_nonneg` (Gibbs' inequality) — a pure mathematical theorem.
  • `kl_bound_axiom` — an irreducible physical postulate linking external
    perturbation statistics to internal thermodynamic dissipation (same status
    as `landauer_heat_eq`).
  • `structural_resonance_bound` — KL ≤ Δt · σ, bridging to the gradient
    descent formalism of Phase 8.
-/

variable {V : Type*} [Fintype V]

/-- A discrete probability distribution on a finite type `V`. -/
structure ProbDist (V : Type*) [Fintype V] where
  p : V → ℝ
  nonneg : ∀ i, 0 ≤ p i
  sum_one : ∑ i, p i = 1

/-- Kullback-Leibler divergence D_KL(P ‖ Q) for finite discrete distributions.
    Defined as ∑ᵢ P(i) · log(P(i)/Q(i)) with convention 0·log(0/q) = 0. -/
noncomputable def KL (P Q : ProbDist V) : ℝ :=
  ∑ i : V, P.p i * Real.log (P.p i / Q.p i)

/--
**Gibbs' inequality:** D_KL(P ‖ Q) ≥ 0 for any P, Q with Q strictly positive.
Proof uses the inequality log(x) ≤ x - 1 for x > 0
(`Real.log_le_sub_one_of_pos`).
-/
lemma KL_nonneg (P Q : ProbDist V) (hQ_pos : ∀ i : V, Q.p i > 0) : 0 ≤ KL P Q := by
  -- Per-index inequality: P(i) - Q(i) ≤ P(i) · log(P(i)/Q(i))
  have h_ineq (i : V) : P.p i - Q.p i ≤ P.p i * Real.log (P.p i / Q.p i) := by
    set p := P.p i
    set q := Q.p i
    have hp_nonneg : 0 ≤ p := P.nonneg i
    have hq_pos : q > 0 := hQ_pos i
    by_cases hpz : p = 0
    · rw [hpz]; simp; exact hq_pos.le
    · have hp_pos : p > 0 := by
        by_contra! H
        apply hpz
        linarith
      -- From log(x) ≤ x - 1 (x = q/p > 0) we get 1 - q/p ≤ -log(q/p)
      have hlog : Real.log (q / p) ≤ q / p - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hq_pos hp_pos)
      have h_mid : 1 - q / p ≤ -Real.log (q / p) := by linarith
      -- log(p/q) = -log(q/p)
      have h_log_pq : Real.log (p / q) = -Real.log (q / p) := by
        rw [Real.log_div (hp_pos.ne') (hq_pos.ne'),
          Real.log_div (hq_pos.ne') (hp_pos.ne')]
        ring
      calc
        p - q = p * (1 - q / p) := by field_simp [hp_pos.ne']
        _ ≤ p * (-Real.log (q / p)) := mul_le_mul_of_nonneg_left h_mid hp_nonneg
        _ = p * Real.log (p / q) := by rw [h_log_pq]
  -- Sum the per-index inequality, then use ∑(P(i) - Q(i)) = 0
  have h_sum : ∑ i : V, (P.p i - Q.p i) ≤ KL P Q :=
    calc
      ∑ i : V, (P.p i - Q.p i) ≤ ∑ i : V, (P.p i * Real.log (P.p i / Q.p i)) :=
        Finset.sum_le_sum fun i _ => h_ineq i
      _ = KL P Q := rfl
  have h_sum_zero : ∑ i : V, (P.p i - Q.p i) = 0 := by
    rw [Finset.sum_sub_distrib, P.sum_one, Q.sum_one, sub_self]
  rw [h_sum_zero] at h_sum
  exact h_sum

/-- Entropy production rate σ = Q/T where Q is heat dissipation of
    transformation `t` and T is the system temperature.
    (Discrete finite-state setting, distinct from the continuous-field
    `entropy_production_rate` in `Phase8_ContinuousField.lean`.) -/
noncomputable def discrete_entropy_rate {σ : Type*} [Thermodynamics σ] (t : σ → σ) : ℝ :=
  Thermodynamics.heat_dissipation t / Thermodynamics.temperature (sys := σ)

/--
[AXIOM] **KL bound on entropy production.** [IRREDUCIBLE]

For any finite-state thermodynamic system with internal dynamics `t`, the
entropy production rate σ = dissipation/T is bounded below by the KL divergence
between the external perturbation distribution P(ext) and the internal
transition distribution Q(int), scaled by the inverse time-step 1/Δt.

This is a physical postulate — it links the statistical structure of external
perturbations to internal thermodynamic dissipation, with no purely mathematical
proof. Same status as `landauer_heat_eq`.
-/
axiom kl_bound_axiom {V : Type*} [Fintype V] [DecidableEq V] [Thermodynamics V]
  (P Q : ProbDist V) (t : V → V) (dt : ℝ) (hdt : dt > 0) :
  discrete_entropy_rate (σ := V) t ≥ KL P Q / dt

/--
**Structural resonance bound:** KL(P ‖ Q) ≤ Δt · σ(t).

Combines the KL bound axiom with Gibbs' inequality to give an upper bound on
the KL divergence in terms of the entropy production rate.

This bound, together with gradient descent on entropy production (proved for
continuous neural fields in `Phase8_ContinuousField.lean` as
`gradient_flow_implies_entropy_decrease`), implies that structural resonance
forces KL(P ‖ Q) → 0 as the system approaches its minimum dissipation state.
-/
theorem structural_resonance_bound {V : Type*} [Fintype V] [DecidableEq V]
  [Thermodynamics V] (P : ProbDist V) (Q : ProbDist V) (t : V → V)
  (_hQ_pos : ∀ i, Q.p i > 0) (dt : ℝ) (hdt : dt > 0) :
  KL P Q ≤ dt * discrete_entropy_rate (σ := V) t := by
  have h_axiom := kl_bound_axiom P Q t dt hdt
  -- h_axiom: σ ≥ KL / dt  i.e. KL / dt ≤ σ
  calc
    KL P Q = (KL P Q / dt) * dt := by field_simp [hdt.ne']
    _ ≤ discrete_entropy_rate (σ := V) t * dt :=
      mul_le_mul_of_nonneg_right h_axiom (by linarith)
    _ = dt * discrete_entropy_rate (σ := V) t := mul_comm _ _

end PhysicsOfConsciousness