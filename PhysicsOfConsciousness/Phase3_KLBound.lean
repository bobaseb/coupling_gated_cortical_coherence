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
  • `StructuralResonance` — an irreducible physical postulate, carried as a
    class field rather than an `axiom`, linking external perturbation statistics
    to internal thermodynamic dissipation. See its doc-string for why the
    `axiom` formulation was inconsistent.
  • `structural_resonance_bound` — KL ≤ Δt · σ, a rearrangement of the axiom,
    bridging to the gradient descent formalism of Phase 8.
  • `discrete_entropy_rate_nonneg` — 0 ≤ σ, the one result that genuinely
    combines Gibbs' inequality with the postulate.
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
**Structural resonance as an instance obligation.** [IRREDUCIBLE PHYSICAL POSTULATE]

The physical claim of Derivation 3 is that, for a *given* system, the entropy
production rate of its internal dynamics is bounded below by the KL divergence
between the environment's perturbation statistics `P_ext` and the system's own
internal transition statistics `Q_int`, scaled by 1/Δt.

**Why this is a class and not an `axiom`.** An earlier version of this file
declared

    axiom kl_bound_axiom (P Q : ProbDist V) (t : V → V) (dt : ℝ) (hdt : dt > 0) :
      discrete_entropy_rate t ≥ KL P Q / dt

which is *inconsistent*: `discrete_entropy_rate t` is a fixed real determined by
the free class field `Thermodynamics.heat_dissipation`, while `KL P Q` ranges
over an unbounded set as `P` and `Q` vary. Instantiating `Thermodynamics` with
`heat_dissipation := fun _ => 0`, `temperature := 1` and taking `P` a point mass
against uniform `Q` gives `0 ≥ log 2`, hence `False`. Quantifying over all `P`,
`Q` turned a statement about one system into a claim about every distribution
pair simultaneously.

Bundling the postulate as a class fixes this: `P_ext`, `Q_int`, `transition` and
`dt` are the *system's* data, and `kl_bound` constrains only that system. See
`Examples.lean` for an instance witnessing that the class is inhabited.
-/
class StructuralResonance (V : Type*) [Fintype V] [DecidableEq V]
    [Thermodynamics V] where
  /-- Statistics of external environmental perturbations, P(ext). -/
  P_ext : ProbDist V
  /-- The system's internal transition statistics, Q(int). -/
  Q_int : ProbDist V
  /-- `Q_int` is strictly positive (required for Gibbs' inequality). -/
  Q_int_pos : ∀ i, Q_int.p i > 0
  /-- The internal dynamics whose dissipation is being bounded. -/
  transition : V → V
  /-- The physical time-step over which the comparison is made. -/
  dt : ℝ
  dt_pos : dt > 0
  /-- **The postulate.** Entropy production dominates KL divergence per unit time. -/
  kl_bound : discrete_entropy_rate (σ := V) transition ≥ KL P_ext Q_int / dt

/--
**Structural resonance bound:** KL(P ‖ Q) ≤ Δt · σ.

This is `StructuralResonance.kl_bound` rearranged (multiplying through by
Δt > 0); it carries exactly the content of that postulate and no independent
mathematical content. Gibbs' inequality is *not* used here — for the two-sided
sandwich 0 ≤ KL(P ‖ Q) ≤ Δt · σ see `discrete_entropy_rate_nonneg` below.

This bound, together with gradient descent on entropy production (proved for
continuous neural fields in `Phase8_ContinuousField.lean` as
`gradient_flow_implies_entropy_decrease`), is what the informal argument of
Derivation 3 appeals to when it claims structural resonance forces
KL(P ‖ Q) → 0. Note that the limit itself is *not* formalized: Phase 8's
gradient-flow theorems are stated over an abstract inner-product space and are
not linked to `discrete_entropy_rate`.
-/
theorem structural_resonance_bound {V : Type*} [Fintype V] [DecidableEq V]
  [Thermodynamics V] [R : StructuralResonance V] :
  KL R.P_ext R.Q_int ≤ R.dt * discrete_entropy_rate (σ := V) R.transition := by
  have hdt : R.dt > 0 := R.dt_pos
  have h_bound := R.kl_bound
  calc
    KL R.P_ext R.Q_int = (KL R.P_ext R.Q_int / R.dt) * R.dt := by field_simp
    _ ≤ discrete_entropy_rate (σ := V) R.transition * R.dt :=
      mul_le_mul_of_nonneg_right h_bound (by linarith)
    _ = R.dt * discrete_entropy_rate (σ := V) R.transition := mul_comm _ _

/--
**Second law in discrete form:** 0 ≤ σ.

This is the one place where Gibbs' inequality does real work. `KL_nonneg`
(a theorem) gives KL(P ‖ Q) ≥ 0; `StructuralResonance.kl_bound` gives
σ ≥ KL(P ‖ Q)/Δt. Chaining them yields non-negativity of the entropy production
rate — so the postulate is at least consistent with the second law rather than
assuming it separately.
-/
theorem discrete_entropy_rate_nonneg {V : Type*} [Fintype V] [DecidableEq V]
  [Thermodynamics V] [R : StructuralResonance V] :
  0 ≤ discrete_entropy_rate (σ := V) R.transition := by
  have h_gibbs : 0 ≤ KL R.P_ext R.Q_int := KL_nonneg R.P_ext R.Q_int R.Q_int_pos
  have h_bound := R.kl_bound
  have h_div : 0 ≤ KL R.P_ext R.Q_int / R.dt := div_nonneg h_gibbs R.dt_pos.le
  linarith

end PhysicsOfConsciousness
