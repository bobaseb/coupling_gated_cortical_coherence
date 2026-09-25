import PhysicsOfConsciousness.Phase6_Locality

/-!
# Phase 10 — the unity window: agreement no earlier than the cone, no later than relaxation

Agreement between two regions is bounded in time from both sides. It cannot be
*guaranteed* before a change at one region can reach the other: that is the
causal-cone deadline of `Phase6_Locality`. It is *reached* no later than the
coupling relaxes the disagreement: with a per-step contraction factor `κ`, a
discrepancy `d₀` falls below `ε` after `log (d₀ / ε) / log (1 / κ)` steps. A
content that must be unified on some time scale needs that scale to exceed both
edges; this module states the two edges in the form the paper uses them.

* **`mem_ball_of_reconstructs`** (the lower edge). If a reading site's report
  tracks a change at `w` to within half the separation of two values the change
  might take, then `w` lies in the site's causal past for that many rounds. It
  is `not_reconstructs_of_outside_past` read forward.
* **`disc_iterate_le`** (relaxation). A discrepancy contracted by `κ` at every
  step on an invariant set is at most `κⁿ d₀` after `n` steps.
* **`disc_iterate_le_of_log_le`** (the upper edge). With `0 < κ < 1` it is at
  most `ε` once `n ≥ log (d₀ / ε) / log (1 / κ)`.
* **`le_disc_iterate`** and **`lt_disc_iterate_of_lt_log`** (relaxation is no
  faster than its rate). If the discrepancy shrinks by at most a factor `ρ` per
  step, it is still above `ε` for every `n < log (d₀ / ε) / log (1 / ρ)`: the
  upper edge cannot be moved earlier than the slowest rate allows.

What is not formalised: that the relaxation rate is the spectral gap of the
coupling, or scales with the effective resistance of
`Phase10_AgreementResistance`; those identifications are linear-response
statements about a particular dynamics and are made in the text. Non-vacuity —
a halving map meeting the upper edge exactly at its predicted step — is
`Examples/UnityWindow.lean`.
-/

namespace PhysicsOfConsciousness.PhysicalUnity

open PhysicsOfConsciousness.Reconstruction PhysicsOfConsciousness.Locality

section Cone

variable {V S M Q : Type*} [DecidableEq V]

/-- **The lower edge.** A report at `v` that tracks every value of the world at
`w` to within `ε`, for two values more than `2ε` apart, is possible by round `T`
only if `w` is in `v`'s causal past for `T` rounds. -/
theorem mem_ball_of_reconstructs [PseudoMetricSpace Q] (N : Network V S M) (base : V → S)
    {w v : V} (inj : Q → S) {T : ℕ} (report : S → Q) (relevant : Set Q) {ε : ℝ} {q q' : Q}
    (hq : q ∈ relevant) (hq' : q' ∈ relevant) (hsep : 2 * ε < dist q q')
    (h : (worldEncoding N base w inj v T report relevant).Reconstructs ε) :
    w ∈ ball N.nbhd T v := by
  by_contra hw
  exact not_reconstructs_of_outside_past N base inj report relevant hw hq hq' hsep h

end Cone

section Relaxation

variable {X : Type*} {f : X → X} {disc : X → ℝ} {D : Set X}

/-- **Relaxation.** A discrepancy contracted by `κ ≥ 0` at every step, on a set
the dynamics keeps, is at most `κⁿ` times its initial value after `n` steps. -/
theorem disc_iterate_le (hD : Set.MapsTo f D D) {κ : ℝ} (hκ : 0 ≤ κ)
    (hc : ∀ y ∈ D, disc (f y) ≤ κ * disc y) {x : X} (hx : x ∈ D) (n : ℕ) :
    disc (f^[n] x) ≤ κ ^ n * disc x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    calc disc (f (f^[n] x)) ≤ κ * disc (f^[n] x) := hc _ (hD.iterate n hx)
      _ ≤ κ * (κ ^ n * disc x) := mul_le_mul_of_nonneg_left ih hκ
      _ = κ * κ ^ n * disc x := by ring

/-- **Relaxation is no faster than its rate.** A discrepancy that shrinks by at
most the factor `ρ ≥ 0` per step, on a set the dynamics keeps, is at least `ρⁿ`
times its initial value after `n` steps. -/
theorem le_disc_iterate (hD : Set.MapsTo f D D) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hc : ∀ y ∈ D, ρ * disc y ≤ disc (f y)) {x : X} (hx : x ∈ D) (n : ℕ) :
    ρ ^ n * disc x ≤ disc (f^[n] x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    calc ρ * ρ ^ n * disc x = ρ * (ρ ^ n * disc x) := by ring
      _ ≤ ρ * disc (f^[n] x) := mul_le_mul_of_nonneg_left ih hρ
      _ ≤ disc (f (f^[n] x)) := hc _ (hD.iterate n hx)

/-- `κⁿ d₀ ≤ ε` exactly when `n` is at least the relaxation time. -/
lemma pow_mul_le_iff_log {κ d₀ ε : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hd : 0 < d₀) (hε : 0 < ε)
    (n : ℕ) : κ ^ n * d₀ ≤ ε ↔ Real.log (d₀ / ε) / Real.log (1 / κ) ≤ n := by
  have hl : 0 < Real.log (1 / κ) := Real.log_pos (by rw [lt_div_iff₀ hκ0]; linarith)
  rw [div_le_iff₀ hl, Real.log_div hd.ne' hε.ne', one_div, Real.log_inv,
    ← le_div_iff₀ hd, ← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_pow, Real.log_div hε.ne' hd.ne']
  constructor <;> intro h <;> linarith

/-- **The upper edge.** With a contraction factor `0 < κ < 1` and an initial
discrepancy at most `d₀`, the discrepancy is at most `ε` from step
`log (d₀ / ε) / log (1 / κ)` on. -/
theorem disc_iterate_le_of_log_le (hD : Set.MapsTo f D D) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ < 1) (hc : ∀ y ∈ D, disc (f y) ≤ κ * disc y) {x : X} (hx : x ∈ D)
    {d₀ ε : ℝ} (hx0 : disc x ≤ d₀) (hd : 0 < d₀) (hε : 0 < ε) {n : ℕ}
    (hn : Real.log (d₀ / ε) / Real.log (1 / κ) ≤ n) : disc (f^[n] x) ≤ ε :=
  (disc_iterate_le hD hκ0.le hc hx n).trans <|
    (mul_le_mul_of_nonneg_left hx0 (by positivity)).trans
      ((pow_mul_le_iff_log hκ0 hκ1 hd hε n).mpr hn)

/-- **Agreement is not reached before the slowest rate allows.** If the
discrepancy shrinks by at most the factor `0 < ρ < 1` per step and starts at
`d₀ > 0`, it is still above `ε` at every step before
`log (d₀ / ε) / log (1 / ρ)`. -/
theorem lt_disc_iterate_of_lt_log (hD : Set.MapsTo f D D) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hc : ∀ y ∈ D, ρ * disc y ≤ disc (f y)) {x : X} (hx : x ∈ D)
    {ε : ℝ} (hd : 0 < disc x) (hε : 0 < ε) {n : ℕ}
    (hn : (n : ℝ) < Real.log (disc x / ε) / Real.log (1 / ρ)) : ε < disc (f^[n] x) :=
  (lt_of_not_ge fun h => absurd ((pow_mul_le_iff_log hρ0 hρ1 hd hε n).mp h)
    (not_le.mpr hn)).trans_le (le_disc_iterate hD hρ0.le hc hx n)

end Relaxation

end PhysicsOfConsciousness.PhysicalUnity
