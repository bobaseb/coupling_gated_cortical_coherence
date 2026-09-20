/-
  Phase 5 (continued): the lift obstruction measured around cortical phase
  singularities.

  `Phase5_TwistedGluing.lean` studies circle-valued offsets between patches. Any
  offsets obtained by subtracting absolute patch phases are a coboundary. The
  physical observable identified in F3 has a different type: experimental phase
  maps are locally unwrapped to real phases, and neighbouring unwraps can differ
  by an integer number of turns. Around an electrode loop those integer jumps
  sum to the measured winding number.

  This file formalizes the discrete loop calculation only. It neither constructs
  a Čech complex nor identifies winding with cognitive or phenomenal content.
-/
import PhysicsOfConsciousness.Phase5_TwistedGluing
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace PhysicsOfConsciousness

/-! ## Integer transitions on a measured loop -/

/-- The winding measured around a loop of `n + 1` overlapping phase patches.

Each integer records the number of full turns between two neighbouring local
real-valued phase lifts. Summing the transitions is the discrete winding number
used for an electrode loop around a phase singularity. -/
def loopWinding {n : ℕ} (transition : Fin (n + 1) → ℤ) : ℤ :=
  ∑ i, transition i

/-- **The loop transitions come from one globally consistent real lift.**

The first `n` equations relate consecutive vertices and the final equation
closes the loop. This is deliberately a predicate rather than a strengthened
data structure: the existence of a global lift is exactly what winding tests. -/
def HasGlobalLift {n : ℕ} (transition : Fin (n + 1) → ℤ) : Prop :=
  ∃ lift : ℕ → ℤ,
    (∀ i : Fin n, transition i.castSucc = lift i - lift (i + 1)) ∧
      transition (Fin.last n) = lift n - lift 0

/-- **A globally lifted phase has zero loop winding.**

The local integer transitions telescope around the closed loop. Consequently a
non-zero measured winding obstructs a single real-valued phase lift. This proves
only the discrete obstruction. It does not prove that a cortical singularity is
stable, dynamically generated, or a carrier of phenomenal content. -/
theorem loopWinding_eq_zero_of_hasGlobalLift {n : ℕ} {transition : Fin (n + 1) → ℤ}
    (h : HasGlobalLift transition) : loopWinding transition = 0 := by
  obtain ⟨lift, hedge, hclose⟩ := h
  rw [loopWinding, Fin.sum_univ_castSucc]
  simp_rw [hedge]
  rw [show (∑ i : Fin n, (lift i - lift (i + 1))) =
      lift 0 - lift n by
    calc
      _ = ∑ k ∈ Finset.range n, (lift k - lift (k + 1)) :=
        Fin.sum_univ_eq_sum_range (fun k => lift k - lift (k + 1)) n
      _ = lift 0 - lift n := Finset.sum_range_sub' lift n]
  rw [hclose]
  abel

/-- **Non-zero winding forbids a global real phase lift.**

This is the experimentally usable form: compute the integer winding from a
closed electrode loop; if it is non-zero, no choice of patchwise unwrapping can
make one global real phase on that loop. -/
theorem not_hasGlobalLift_of_loopWinding_ne_zero {n : ℕ}
    {transition : Fin (n + 1) → ℤ} (h : loopWinding transition ≠ 0) :
    ¬ HasGlobalLift transition :=
  fun hlift => h (loopWinding_eq_zero_of_hasGlobalLift hlift)

/-! ## A non-trivial three-electrode witness -/

/-- Three overlap transitions with one net turn around the loop. This is the
smallest discrete witness of the phase-singularity measurement: two adjacent
unwraps agree and the closing overlap crosses the branch cut once. -/
def threeElectrodeWinding : Fin 3 → ℤ :=
  ![0, 0, 1]

/-- The three-electrode witness has winding number one. -/
theorem threeElectrodeWinding_loopWinding : loopWinding threeElectrodeWinding = 1 := by
  decide

/-- The non-zero witness cannot arise from a global real-valued lift. -/
theorem threeElectrodeWinding_not_hasGlobalLift : ¬ HasGlobalLift threeElectrodeWinding :=
  not_hasGlobalLift_of_loopWinding_ne_zero (by rw [threeElectrodeWinding_loopWinding]; norm_num)

/-! ## The winding state's own transitions

The results above take the integer transitions as measured data. The winding
state of `Phase4_KuramotoDynamics` §6 supplies them instead, so the loop winding
is computed from a state the dynamics holds stationary rather than postulated of
an electrode array.

`winding n q` puts phase `2πq·k/n` at site `k`, and its site index is a residue:
going once around the ring, the affine continuation of the lift arrives at
`2πq` and the value there is `0`. `winding_succ` is that statement site by site
— the lift advances by `2πq/n` at every step except across the wrap, where it
also drops `q` whole turns — and `ringTransition` is the integer it drops.
Summed around the ring those integers are the winding number
(`loopWinding_ringTransition`), so the state has no global real-valued phase
lift whenever `q ≠ 0`.

What this buys is the pairing in `winding_degree_obstructs`. On the same state,
at the same coupling, the global resultant is exactly zero while the degree is
`q`. The resultant is an average over the sites and changes when the sites are
reweighted or the patches redrawn; the degree is an integer that telescopes, so
no redrawing of the loop's intermediate transitions changes it. That is the
sense in which the winding state is an invariant and not only a counterexample.

Scope is the ring's. `ZMod n` has no interior, so this is a loop's worth of
winding and not a spiral, and the transitions are those of the affine local
lifts rather than of a locally unwrapped measurement. Nothing here identifies
the integer with a cortical observable; `Phase4_KuramotoDynamics` §6's scope
notes govern, unchanged. -/

/-- The whole turns the ring's lift drops between consecutive sites: zero inside
the ring, `q` across the wrap. Defined from the residue arithmetic rather than
posited, which is what `winding_succ` checks. -/
def ringTransition (n : ℕ) (q : ℤ) (k : ℕ) : ℤ := q * (((k + 1) / n : ℕ) : ℤ)

lemma ringTransition_of_lt {n k : ℕ} (q : ℤ) (h : k + 1 < n) : ringTransition n q k = 0 := by
  rw [ringTransition, Nat.div_eq_of_lt h]
  simp

/-- **The lift advances uniformly, except for whole turns.** At every site the
`q`-fold winding's phase rises by `2πq/n`, less `2π` times the transition — which
is zero except across the wrap, where the residue resets. -/
lemma winding_succ (n : ℕ) [NeZero n] (q : ℤ) {k : ℕ} (hk : k < n) :
    winding n q ((k : ZMod n) + 1)
      = winding n q (k : ZMod n) + 2 * Real.pi * q / n
        - 2 * Real.pi * (ringTransition n q k : ℝ) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hcast : ((k : ZMod n) + 1) = ((k + 1 : ℕ) : ZMod n) := by push_cast; ring
  have hval1 : ((k : ZMod n) + 1).val = (k + 1) % n := by rw [hcast, ZMod.val_natCast]
  have hval0 : (k : ZMod n).val = k := ZMod.val_natCast_of_lt hk
  have hmod : (((k + 1) % n : ℕ) : ℝ) = (k : ℝ) + 1 - (n : ℝ) * (((k + 1) / n : ℕ) : ℝ) := by
    have h := Nat.div_add_mod (k + 1) n
    have h' : ((n * ((k + 1) / n) + (k + 1) % n : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := congrArg _ h
    push_cast at h'
    linarith
  set D : ℕ := (k + 1) / n with hDdef
  have hRT : ((ringTransition n q k : ℤ) : ℝ) = (q : ℝ) * (D : ℝ) := by
    rw [ringTransition, ← hDdef]
    push_cast
    ring
  simp only [winding, hval1, hval0, hmod, hRT]
  field_simp

/-- **The ring's transitions sum to its winding number.** One term survives, the
one across the wrap. -/
theorem loopWinding_ringTransition (n : ℕ) (q : ℤ) :
    loopWinding (fun i : Fin (n + 1) => ringTransition (n + 1) q i.val) = q := by
  rw [loopWinding, Finset.sum_eq_single (Fin.last n)]
  · rw [ringTransition]
    simp [Nat.div_self]
  · intro b _ hb
    refine ringTransition_of_lt q ?_
    have hbn : b.val ≠ n := fun h => hb (Fin.ext h)
    have := b.isLt
    omega
  · intro h
    exact absurd (Finset.mem_univ (Fin.last n)) h

/-- **A nonzero winding number has no global lift**, on the dynamical state
rather than on a measured loop. -/
theorem not_hasGlobalLift_ringTransition {n : ℕ} {q : ℤ} (hq : q ≠ 0) :
    ¬ HasGlobalLift (fun i : Fin (n + 1) => ringTransition (n + 1) q i.val) :=
  not_hasGlobalLift_of_loopWinding_ne_zero (by rw [loopWinding_ringTransition]; exact hq)

/-- **The degree and the resultant, on one state.** A winding that does not close
on the ring is read by the global order parameter as complete incoherence, and
carries winding number `q`, which obstructs every global real-valued phase lift.
The first quantity is an average over sites; the second is an integer that
telescopes around the loop. A cover redrawn to make the first look coherent
leaves the second where it was. -/
theorem winding_degree_obstructs {n : ℕ} [Fact (1 < n + 1)] {q : ℤ}
    (hq : ¬ (((n + 1 : ℕ) : ℤ) ∣ q)) :
    order_parameter_r_sq (winding (n + 1) q) = 0 ∧
      loopWinding (fun i : Fin (n + 1) => ringTransition (n + 1) q i.val) = q ∧
      ¬ HasGlobalLift (fun i : Fin (n + 1) => ringTransition (n + 1) q i.val) := by
  have hq0 : q ≠ 0 := fun h => hq (h ▸ dvd_zero _)
  exact ⟨order_parameter_r_sq_winding hq, loopWinding_ringTransition n q,
    not_hasGlobalLift_ringTransition hq0⟩

#print axioms winding_succ
#print axioms loopWinding_ringTransition
#print axioms not_hasGlobalLift_ringTransition
#print axioms winding_degree_obstructs

end PhysicsOfConsciousness
