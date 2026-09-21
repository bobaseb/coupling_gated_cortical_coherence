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

  The last section reads the same integer off a real-valued phase field rather
  than off measured transitions, and shows it survives any perturbation inside
  an explicit margin — exactly, because there is nothing between one integer and
  the next. That margin closes as the winding fills the ring, and the protection
  is of an integer carried by a ring of sites, not of any cortical observable.
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

/-! ## The degree is stable, and what that buys

`winding_degree_obstructs` reads the degree off `ringTransition`, which is
residue arithmetic on the exact state. A field is never exactly that state, so
an integer that exists only there is an invariant of nothing. This section reads
the degree off the phases themselves and shows it does not move.

`phaseTurns x` is the whole turns in a real phase difference — the integer `m`
for which `x - 2πm` lands in `[-π, π)` — and `ringPhaseTransition θ` collects
those integers between consecutive ring sites. Two facts make it an observable
rather than an artefact of a chosen lift:

* `loopWinding_ringPhaseTransition_relift` — re-lifting any site by any whole
  number of turns leaves the loop sum where it was. The per-overlap integers
  move; their cyclic sum telescopes.
* `ringPhaseTransition_winding` — on the `q`-fold winding the integers are
  `ringTransition`, so the transitions read off the phases and the transitions
  computed from the residue arithmetic are the same integers, and
  `loopWinding_ringTransition` carries over.

The stability is `ringPhaseTransition_eq_of_close`: move every site by anything
strictly inside `windingMargin n q = π/2 - π|q|/n`, and every overlap's integer
is unchanged — exactly, not approximately, because there is nothing between one
integer and the next. `winding_degree_stable` is the consequence the article
rests on: the perturbed field still has degree `q` and still admits no global
real-valued phase lift. No element of the medium is digital and no quantity is
rounded; the discreteness is the degree's own.

**Scope.** Three limits, and none is small.

The margin is a half turn less what the winding already spends per site, so it
is positive exactly when `2|q| < n` and closes as the winding fills the ring: a
degree that turns nearly once per site is protected against nothing. The
protection is against perturbations *inside* the margin and against nothing
else — `loopWinding_uniform_ne_winding` exhibits two states of the same ring
with different degrees, so the hypothesis cannot be dropped, only weakened. And
the state perturbed here is a real-valued phase field on a ring of sites;
nothing here says a cortical field is one, or that the integer is observable in
tissue. `Phase4_KuramotoDynamics` §6's scope notes govern what the winding state
is, unchanged. -/

/-- The whole turns in a real phase difference: the integer `m` for which
`x - 2πm` lies in `[-π, π)`. This is the unwrapping an experimenter performs on
a measured phase difference, written so that the branch cut is explicit. -/
noncomputable def phaseTurns (x : ℝ) : ℤ := ⌊(x + Real.pi) / (2 * Real.pi)⌋

/-- What is left of a phase difference after its whole turns are removed. Its
distance from a half turn is the room a perturbation has before the integer
moves, which is what `phaseTurns_eq_of_abs_sub_lt` spends. -/
noncomputable def principalPhase (x : ℝ) : ℝ := x - 2 * Real.pi * (phaseTurns x : ℝ)

/-- **Landing in the window determines the integer.** The defining property of
`phaseTurns`, in the form every computation below uses. -/
theorem phaseTurns_eq_of_mem {x : ℝ} {m : ℤ} (h1 : -Real.pi ≤ x - 2 * Real.pi * (m : ℝ))
    (h2 : x - 2 * Real.pi * (m : ℝ) < Real.pi) : phaseTurns x = m := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [phaseTurns, Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hpi]; linarith
  · rw [div_lt_iff₀ hpi]; linarith

theorem principalPhase_eq_of_mem {x : ℝ} {m : ℤ} (h1 : -Real.pi ≤ x - 2 * Real.pi * (m : ℝ))
    (h2 : x - 2 * Real.pi * (m : ℝ) < Real.pi) :
    principalPhase x = x - 2 * Real.pi * (m : ℝ) := by
  rw [principalPhase, phaseTurns_eq_of_mem h1 h2]

/-- **The integer does not move inside its window.** A perturbation smaller than
the distance from the principal part to a half turn leaves the whole-turn count
exactly where it was. This is the whole of the stability: an integer-valued
quantity that is locally constant is locally constant *exactly*, and the margin
is the only thing that has to be estimated. -/
theorem phaseTurns_eq_of_abs_sub_lt {x y : ℝ}
    (h : |y - x| < Real.pi - |principalPhase x|) : phaseTurns y = phaseTurns x := by
  have hp : principalPhase x = x - 2 * Real.pi * ((phaseTurns x : ℤ) : ℝ) := rfl
  have hrw : y - 2 * Real.pi * ((phaseTurns x : ℤ) : ℝ) = principalPhase x + (y - x) := by
    rw [hp]; ring
  have hb : |y - 2 * Real.pi * ((phaseTurns x : ℤ) : ℝ)| < Real.pi := by
    rw [hrw]
    calc |principalPhase x + (y - x)| ≤ |principalPhase x| + |y - x| := abs_add_le _ _
      _ < Real.pi := by linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  exact phaseTurns_eq_of_mem (le_of_lt hlo) hhi

/-- Adding whole turns to a phase difference adds them to its count, and changes
nothing else. -/
theorem phaseTurns_add_int_mul (x : ℝ) (k : ℤ) :
    phaseTurns (x + 2 * Real.pi * (k : ℝ)) = phaseTurns x + k := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [phaseTurns, phaseTurns,
    show (x + 2 * Real.pi * (k : ℝ) + Real.pi) / (2 * Real.pi)
        = (x + Real.pi) / (2 * Real.pi) + (k : ℝ) by field_simp; ring,
    Int.floor_add_intCast]

/-- The loop transitions of a real-valued phase field on a ring, in the sign
convention `HasGlobalLift` uses: the turns dropped going from site `i` to site
`i + 1`, with the ring's wrap supplied by `ZMod`. -/
noncomputable def ringPhaseTransition {n : ℕ} (θ : ZMod n → ℝ) (i : Fin n) : ℤ :=
  phaseTurns (θ ((i.val : ℕ) : ZMod n) - θ (((i.val : ℕ) : ZMod n) + 1))

/-- A cyclic difference of integers sums to zero around the ring. The residue
arithmetic is doing the work: the affine continuation's value at site `n` is its
value at site `0`. -/
theorem sum_ring_relift {n : ℕ} [NeZero n] (m : ZMod n → ℤ) :
    ∑ i : Fin n, (m ((i.val : ℕ) : ZMod n) - m (((i.val : ℕ) : ZMod n) + 1)) = 0 := by
  have hcast : ∀ k : ℕ, ((k : ZMod n) + 1) = ((k + 1 : ℕ) : ZMod n) := by
    intro k; push_cast; ring
  calc ∑ i : Fin n, (m ((i.val : ℕ) : ZMod n) - m (((i.val : ℕ) : ZMod n) + 1))
      = ∑ k ∈ Finset.range n, (m ((k : ZMod n)) - m (((k + 1 : ℕ) : ZMod n))) := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun k : ℕ => m ((k : ZMod n)) - m (((k + 1 : ℕ) : ZMod n))) n]
        exact Finset.sum_congr rfl fun i _ => by rw [hcast]
    _ = (fun k : ℕ => m ((k : ZMod n))) 0 - (fun k : ℕ => m ((k : ZMod n))) n :=
        Finset.sum_range_sub' (fun k : ℕ => m ((k : ZMod n))) n
    _ = 0 := by simp

/-- Re-lifting the sites by whole turns shifts the overlap integers by the
corresponding cyclic difference. -/
theorem ringPhaseTransition_relift {n : ℕ} (θ : ZMod n → ℝ) (m : ZMod n → ℤ) (i : Fin n) :
    ringPhaseTransition (fun k => θ k + 2 * Real.pi * (m k : ℝ)) i
      = ringPhaseTransition θ i
        + (m ((i.val : ℕ) : ZMod n) - m (((i.val : ℕ) : ZMod n) + 1)) := by
  show phaseTurns _ = _
  rw [show (θ ((i.val : ℕ) : ZMod n) + 2 * Real.pi * (m ((i.val : ℕ) : ZMod n) : ℝ))
        - (θ (((i.val : ℕ) : ZMod n) + 1) + 2 * Real.pi * (m (((i.val : ℕ) : ZMod n) + 1) : ℝ))
      = (θ ((i.val : ℕ) : ZMod n) - θ (((i.val : ℕ) : ZMod n) + 1))
        + 2 * Real.pi * ((m ((i.val : ℕ) : ZMod n) - m (((i.val : ℕ) : ZMod n) + 1) : ℤ) : ℝ) by
      push_cast; ring,
    phaseTurns_add_int_mul]
  rfl

/-- **The degree is a property of the field, not of the lift chosen for it.**
Re-lifting each site by any whole number of turns moves the individual overlap
integers and leaves their loop sum exactly where it was. Without this the
quantity below would be an artefact of how the phases were unwrapped; with it,
two experimenters who unwrap differently report the same degree. -/
theorem loopWinding_ringPhaseTransition_relift {n : ℕ} (θ : ZMod (n + 1) → ℝ)
    (m : ZMod (n + 1) → ℤ) :
    loopWinding (ringPhaseTransition (fun k => θ k + 2 * Real.pi * (m k : ℝ)))
      = loopWinding (ringPhaseTransition θ) := by
  rw [loopWinding, loopWinding,
    Finset.sum_congr rfl (fun i _ => ringPhaseTransition_relift θ m i),
    Finset.sum_add_distrib, sum_ring_relift, add_zero]

/-- The room each site of a `q`-fold winding on `n` sites has before an overlap
transition crosses a half turn: half of `π - 2π|q|/n`, the distance from the
winding's per-site advance to a half turn. The halving is the triangle
inequality — an overlap sees two sites' errors. Positive exactly when
`2|q| < n`, and closing as the winding fills the ring. -/
noncomputable def windingMargin (n : ℕ) (q : ℤ) : ℝ :=
  Real.pi / 2 - Real.pi * |(q : ℝ)| / n

section RingStability

variable {n : ℕ} [NeZero n] {q : ℤ}

omit [NeZero n] in
theorem two_mul_abs_cast (hq : 2 * |q| < (n : ℤ)) : 2 * |(q : ℝ)| < (n : ℝ) := by
  have h : ((2 * |q| : ℤ) : ℝ) < ((n : ℤ) : ℝ) := by exact_mod_cast hq
  push_cast at h
  exact h

theorem cast_pos_of_neZero : (0 : ℝ) < (n : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

/-- The margin is positive in the regime this section assumes, so the stability
hypothesis below is satisfiable rather than empty. -/
theorem windingMargin_pos (hq : 2 * |q| < (n : ℤ)) : 0 < windingMargin n q := by
  have hn := cast_pos_of_neZero (n := n)
  have h := two_mul_abs_cast (n := n) hq
  have hpi := Real.pi_pos
  rw [windingMargin, sub_pos, div_lt_iff₀ hn]
  nlinarith

theorem abs_winding_step :
    |2 * Real.pi * (q : ℝ) / n| = 2 * Real.pi * |(q : ℝ)| / n := by
  have hn := cast_pos_of_neZero (n := n)
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [abs_div, abs_of_pos hn, abs_mul, abs_of_pos hpi]

/-- Below `2|q| < n` the winding advances less than a half turn per site, which
is what puts the transitions inside a single branch of the unwrapping. -/
theorem winding_step_lt (hq : 2 * |q| < (n : ℤ)) :
    |2 * Real.pi * (q : ℝ) / n| < Real.pi := by
  have hn := cast_pos_of_neZero (n := n)
  have h := two_mul_abs_cast (n := n) hq
  have hpi := Real.pi_pos
  rw [abs_winding_step, div_lt_iff₀ hn]
  nlinarith

theorem winding_sub_succ {k : ℕ} (hk : k < n) :
    winding n q ((k : ZMod n)) - winding n q ((k : ZMod n) + 1)
      = 2 * Real.pi * ((ringTransition n q k : ℤ) : ℝ) - 2 * Real.pi * (q : ℝ) / n := by
  rw [winding_succ n q hk]; ring

/-- **The transitions read off the phases are the residue arithmetic's.** Below
`2|q| < n` the unwrapping of the winding state's own phase differences returns
`ringTransition`, so the degree computed from a phase field and the degree
computed from the state's residues are the same integer. -/
theorem ringPhaseTransition_winding (hq : 2 * |q| < (n : ℤ)) (i : Fin n) :
    ringPhaseTransition (winding n q) i = ringTransition n q i.val := by
  have hdiff := winding_sub_succ (n := n) (q := q) i.isLt
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (winding_step_lt (n := n) hq)
  rw [ringPhaseTransition]
  refine phaseTurns_eq_of_mem ?_ ?_ <;> rw [hdiff] <;> linarith

theorem principalPhase_winding (hq : 2 * |q| < (n : ℤ)) (i : Fin n) :
    principalPhase (winding n q ((i.val : ℕ) : ZMod n)
        - winding n q (((i.val : ℕ) : ZMod n) + 1))
      = - (2 * Real.pi * (q : ℝ) / n) := by
  have hdiff := winding_sub_succ (n := n) (q := q) i.isLt
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (winding_step_lt (n := n) hq)
  rw [principalPhase_eq_of_mem (m := ringTransition n q i.val) (by rw [hdiff]; linarith)
    (by rw [hdiff]; linarith), hdiff]
  ring

/-- **Every overlap integer survives a perturbation inside the margin.** Move
each site by anything strictly less than `windingMargin n q` and the whole-turn
count at every overlap is unchanged. The two site errors enter through the
triangle inequality, which is why the margin is half the room a single
transition has. -/
theorem ringPhaseTransition_eq_of_close (hq : 2 * |q| < (n : ℤ)) {θ : ZMod n → ℝ}
    (hθ : ∀ k, |θ k - winding n q k| < windingMargin n q) (i : Fin n) :
    ringPhaseTransition θ i = ringTransition n q i.val := by
  rw [← ringPhaseTransition_winding hq i, ringPhaseTransition, ringPhaseTransition]
  refine phaseTurns_eq_of_abs_sub_lt ?_
  rw [principalPhase_winding hq i, abs_neg, abs_winding_step]
  have h1 := hθ ((i.val : ℕ) : ZMod n)
  have h2 := hθ (((i.val : ℕ) : ZMod n) + 1)
  have hn := cast_pos_of_neZero (n := n)
  have key : |(θ ((i.val : ℕ) : ZMod n) - θ (((i.val : ℕ) : ZMod n) + 1))
      - (winding n q ((i.val : ℕ) : ZMod n) - winding n q (((i.val : ℕ) : ZMod n) + 1))|
      ≤ |θ ((i.val : ℕ) : ZMod n) - winding n q ((i.val : ℕ) : ZMod n)|
        + |θ (((i.val : ℕ) : ZMod n) + 1) - winding n q (((i.val : ℕ) : ZMod n) + 1)| := by
    have hsplit : (θ ((i.val : ℕ) : ZMod n) - θ (((i.val : ℕ) : ZMod n) + 1))
        - (winding n q ((i.val : ℕ) : ZMod n) - winding n q (((i.val : ℕ) : ZMod n) + 1))
        = (θ ((i.val : ℕ) : ZMod n) - winding n q ((i.val : ℕ) : ZMod n))
          - (θ (((i.val : ℕ) : ZMod n) + 1) - winding n q (((i.val : ℕ) : ZMod n) + 1)) := by
      ring
    have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
    rw [hsplit]
    exact habs _ _
  have hm : windingMargin n q = Real.pi / 2 - Real.pi * |(q : ℝ)| / n := rfl
  rw [hm] at h1 h2
  have htwo : 2 * Real.pi * |(q : ℝ)| / n = 2 * (Real.pi * |(q : ℝ)| / n) := by ring
  rw [htwo]
  linarith

end RingStability

/-- **The loop degree of a perturbed winding.** Summing
`ringPhaseTransition_eq_of_close` around the ring. -/
theorem loopWinding_ringPhaseTransition_of_close {n : ℕ} {q : ℤ}
    (hq : 2 * |q| < ((n + 1 : ℕ) : ℤ)) {θ : ZMod (n + 1) → ℝ}
    (hθ : ∀ k, |θ k - winding (n + 1) q k| < windingMargin (n + 1) q) :
    loopWinding (ringPhaseTransition θ) = q := by
  have hall : (ringPhaseTransition θ) = fun i : Fin (n + 1) => ringTransition (n + 1) q i.val := by
    funext i
    exact ringPhaseTransition_eq_of_close hq hθ i
  rw [hall, loopWinding_ringTransition]

/-- The exact winding state is the `θ = winding` case. -/
theorem loopWinding_ringPhaseTransition_winding {n : ℕ} {q : ℤ}
    (hq : 2 * |q| < ((n + 1 : ℕ) : ℤ)) :
    loopWinding (ringPhaseTransition (winding (n + 1) q)) = q := by
  have hall : ringPhaseTransition (winding (n + 1) q)
      = fun i : Fin (n + 1) => ringTransition (n + 1) q i.val := by
    funext i
    exact ringPhaseTransition_winding hq i
  rw [hall, loopWinding_ringTransition]

/-- **A discrete integer held by a continuous medium, and stable in it.** Every
site of the `q`-fold winding may be moved by anything strictly inside the
margin: the loop degree is still `q`, and the perturbed field still admits no
global real-valued phase lift. Nothing was rounded and no element of the state
is discrete — the integer is the degree's own, and it is exactly, not
approximately, unchanged.

Read against `winding_degree_obstructs`, which pairs this degree with a global
resultant of zero on the same state: the average over sites is a continuous
function of the phases and moves with any of them; the degree does not move at
all until the margin is crossed. -/
theorem winding_degree_stable {n : ℕ} {q : ℤ} (hq0 : q ≠ 0)
    (hq : 2 * |q| < ((n + 1 : ℕ) : ℤ)) {θ : ZMod (n + 1) → ℝ}
    (hθ : ∀ k, |θ k - winding (n + 1) q k| < windingMargin (n + 1) q) :
    loopWinding (ringPhaseTransition θ) = q ∧ ¬ HasGlobalLift (ringPhaseTransition θ) := by
  refine ⟨loopWinding_ringPhaseTransition_of_close hq hθ, ?_⟩
  exact not_hasGlobalLift_of_loopWinding_ne_zero
    (by rw [loopWinding_ringPhaseTransition_of_close hq hθ]; exact hq0)

/-! ### That the hypothesis is neither empty nor free

A stability theorem is worth what its hypothesis excludes. `windingPerturbed`
inhabits it with a state that is not the winding — one site displaced, the rest
left alone — so the theorem is not about the exact state in disguise.
`loopWinding_uniform_ne_winding` is the other fence: the uniform state and the
`q`-fold winding live on the same ring and have different degrees, so no
perturbation bound can be dropped from the statement above. -/

/-- The winding with one site displaced by `c`. -/
noncomputable def windingPerturbed (n : ℕ) (q : ℤ) (c : ℝ) : ZMod n → ℝ :=
  fun k => winding n q k + if k = 0 then c else 0

theorem windingPerturbed_close {n : ℕ} {q : ℤ} {c : ℝ}
    (hc : |c| < windingMargin n q) (k : ZMod n) :
    |windingPerturbed n q c k - winding n q k| < windingMargin n q := by
  have h0 : (0 : ℝ) < windingMargin n q := lt_of_le_of_lt (abs_nonneg c) hc
  rw [windingPerturbed]
  by_cases h : k = 0
  · simpa [h] using hc
  · simpa [h] using h0

/-- The displaced state is a different state. -/
theorem windingPerturbed_ne {n : ℕ} [NeZero n] {q : ℤ} {c : ℝ} (hc : c ≠ 0) :
    windingPerturbed n q c ≠ winding n q := by
  intro h
  have hzero := congrFun h (0 : ZMod n)
  simp [windingPerturbed] at hzero
  exact hc hzero

theorem loopWinding_windingPerturbed {n : ℕ} {q : ℤ}
    (hq : 2 * |q| < ((n + 1 : ℕ) : ℤ)) {c : ℝ} (hc : |c| < windingMargin (n + 1) q) :
    loopWinding (ringPhaseTransition (windingPerturbed (n + 1) q c)) = q :=
  loopWinding_ringPhaseTransition_of_close hq (windingPerturbed_close hc)

/-- **The degree is not constant on the ring's states.** The uniform phase and
the `q`-fold winding differ in it, so `winding_degree_stable` is a statement
about a neighbourhood and cannot be extended to the whole state space. -/
theorem loopWinding_uniform_ne_winding {n : ℕ} {q : ℤ} (hq0 : q ≠ 0)
    (hq : 2 * |q| < ((n + 1 : ℕ) : ℤ)) :
    loopWinding (ringPhaseTransition (winding (n + 1) (0 : ℤ)))
      ≠ loopWinding (ringPhaseTransition (winding (n + 1) q)) := by
  rw [loopWinding_ringPhaseTransition_winding hq,
    loopWinding_ringPhaseTransition_winding (q := 0) (by simp)]
  exact fun h => hq0 h.symm

#print axioms winding_succ
#print axioms loopWinding_ringTransition
#print axioms not_hasGlobalLift_ringTransition
#print axioms winding_degree_obstructs
#print axioms loopWinding_ringPhaseTransition_relift
#print axioms ringPhaseTransition_winding
#print axioms winding_degree_stable
#print axioms loopWinding_uniform_ne_winding

end PhysicsOfConsciousness
