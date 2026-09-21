/-
  Examples/Locality.lean — two networks, and what each can promise

  §25. One value is written into the far end of a three-site chain and read at
  the near end. The chain's middle site is a delay register: the value is
  unavailable at round one and exact at round two, and the negative result at
  round one is the causal-past theorem rather than a property of this readout.
  The controls fence the three ways the result could be trivial: a cut path
  never delivers, a constant report never satisfies responsiveness, and a report
  that is right about one fixed world stays right about it. The same deadline
  separates two claims about the reading region's contents rather than about a
  report: at round one they are not the value the world was given, and at round
  two they are.

  §31. The same machinery on a deployed architecture: the sites of a
  decoder-only forward pass, indexed by token position and layer, with the
  neighbourhood the causal mask gives. The causal past never reaches a later
  position at any depth, so the rejection holds at every deadline rather than at
  a chosen one; the controls are that the graph delivers backwards at round one
  and that a report on an earlier position is exact there. One forward pass
  only — the autoregressive loop is bounded by the code count of
  `Phase6_Reconstruction`, not by anything here.
-/

import PhysicsOfConsciousness.Phase6_Locality

namespace PhysicsOfConsciousness
namespace Examples
namespace Locality

open PhysicsOfConsciousness.Locality
open PhysicsOfConsciousness.Reconstruction

/-! ## 25. A delay line, its deadline and its controls

Three sites in a line: `0` hears from `1`, `1` hears from `2`, and `2` hears
from nobody. Every message is the sender's state and every update overwrites the
receiver with the message it got, so site `1` is exactly a one-round delay
register for the value held at `2`. -/

/-- The chain `0 ← 1 ← 2`. -/
def line : Network (Fin 3) ℝ ℝ where
  nbhd := ![{1}, {2}, ∅]
  msg := fun _ _ s => s
  step := fun v s inc => (inc (v + 1)).getD s

/-- The baseline configuration: every site at rest. -/
def base : Fin 3 → ℝ := fun _ => 0

/-- The causal past of the reading site after one round reaches the delay
register and no further. -/
theorem ball_line_one : ball line.nbhd 1 0 = {0, 1} := by decide

/-- After two rounds it reaches the far end. -/
theorem ball_line_two : ball line.nbhd 2 0 = {0, 1, 2} := by decide

theorem far_notMem_one : (2 : Fin 3) ∉ ball line.nbhd 1 0 := by decide

/-- **The source tracks the quantity from the start.** The value is in the
network at round zero; what the negative result is about is its arrival, not its
existence. -/
theorem source_holds (q : ℝ) : line.run (intervene base 2 id q) 0 2 = q := by
  simp [Network.run, intervene]

/-- At round one the reading site still holds the baseline: the value is one hop
away, sitting in the delay register. -/
theorem read_one (q : ℝ) : line.run (intervene base 2 id q) 1 0 = 0 := by
  simp [Network.run, Network.round, Network.incoming, line, intervene, base,
    Function.update]

/-- At round two it is exact. -/
theorem read_two (q : ℝ) : line.run (intervene base 2 id q) 2 0 = q := by
  simp [Network.run, Network.round, Network.incoming, line, intervene, base,
    Function.update]

/-- The declared family of values the world might be given, and the two members
that separate it. -/
def values : Set ℝ := {0, 10}

theorem zero_mem : (0 : ℝ) ∈ values := Or.inl rfl
theorem ten_mem : (10 : ℝ) ∈ values := Or.inr rfl

theorem values_separated : 2 * (1 : ℝ) < dist (0 : ℝ) 10 := by
  rw [Real.dist_eq]
  norm_num

/-- **No guarantee at the deadline.** However the reading site's report is
chosen, it cannot be within one of the world's value at round one: the site the
world was changed at is outside the reading site's causal past, so the report
has the same input in both worlds. -/
theorem no_guarantee_at_one (report : ℝ → ℝ) :
    ¬ (worldEncoding line base 2 id 0 1 report values).Reconstructs 1 :=
  not_reconstructs_of_outside_past line base id report values far_notMem_one
    zero_mem ten_mem values_separated

/-- **The positive control: one more round suffices.** Reading the state
directly, the report is exact for every value the world might have been given —
not merely for the two the rejection uses. -/
theorem guarantee_at_two : (worldEncoding line base 2 id 0 2 id Set.univ).Reconstructs 0 := by
  intro q _
  rw [worldEncoding_error, read_two, id_eq, dist_self]

/-- **Coincidental compatibility survives.** On a one-element family the report
is exact at round one as well: the negative result forbids a guarantee across
interventions, not the existence of agreement in one world. -/
theorem coincidental_at_one :
    (worldEncoding line base 2 id 0 1 id ({0} : Set ℝ)).Reconstructs 0 := by
  intro q hq
  have hq0 : q = 0 := hq
  subst hq0
  rw [worldEncoding_error, read_one, id_eq, dist_self]

/-- **A constant report does not satisfy responsiveness**, at any round and on
any network: it is right about at most one of two separated values. -/
theorem const_report_fails (T : ℕ) (r : ℝ) :
    ¬ (worldEncoding line base 2 id 0 T (fun _ => r) values).Reconstructs 1 :=
  Encoding.not_reconstructs_of_const_readout (fun _ => rfl) zero_mem ten_mem values_separated

/-! ### What the region holds, and when

The results above are about a *report*: a readout at the near end, and whether it
can be accurate. These two are about the region's contents, with no report, no
tolerance and no metric on the state. The declared reference is that the reading
region holds the value the world was given; restriction resonance is the claim
that it does.

At round one it does not, and the obstruction is the same causal past. At round
two it does. The deadline is what separates them. -/

/-- The reading region: the near end alone. -/
def readRegion : Finset (Fin 3) := {0}

theorem mem_readRegion {v : Fin 3} (hv : v ∈ readRegion) : v = 0 := by
  simpa [readRegion] using hv

/-- **The region does not hold the world's value at round one.** Not "the report
is wrong": the near end is in the same state in both worlds, so its contents are
not the value the world was given, for either of two values it might have been
given. -/
theorem no_resonance_at_one :
    ¬ Resonates (regionReading line base 2 id readRegion 1) (fun q _ => q) := by
  refine not_resonates_regionReading_of_outside_past line base id _ ?_ (q := 0) (q' := 10) ?_
  · intro v hv
    rw [mem_readRegion hv]
    exact far_notMem_one
  · intro h
    have h0 := congrFun h ⟨0, Finset.mem_singleton_self 0⟩
    norm_num at h0

/-- **The positive control: one more round and it does.** The reference is met
exactly, so the rejection above is about the deadline and not about the
reference. -/
theorem resonance_at_two :
    Resonates (regionReading line base 2 id readRegion 2) (fun q _ => q) := by
  intro q
  funext v
  show line.run (intervene base 2 id q) 2 v.1 = q
  rw [mem_readRegion v.2]
  exact read_two q

/-! ### The cut path

The same three sites with the middle link removed. No number of rounds brings
the far end into the reading site's causal past, so the deadline can be pushed
back indefinitely and the guarantee still fails. -/

/-- The chain with its second link cut: `0 ← 1`, and `2` talks to nobody. -/
def cut : Network (Fin 3) ℝ ℝ where
  nbhd := ![{1}, ∅, ∅]
  msg := fun _ _ s => s
  step := fun v s inc => (inc (v + 1)).getD s

theorem cut_ball_one : ∀ T : ℕ, ball cut.nbhd T 1 = {1} := by
  intro T
  induction T with
  | zero => rfl
  | succ n ih =>
    rw [ball_succ]
    show insert (1 : Fin 3) ((∅ : Finset (Fin 3)).biUnion (ball cut.nbhd n)) = {1}
    simp

theorem cut_ball_zero : ∀ T : ℕ, ball cut.nbhd (T + 1) 0 = {0, 1} := by
  intro T
  rw [ball_succ]
  show insert (0 : Fin 3) (({1} : Finset (Fin 3)).biUnion (ball cut.nbhd T)) = {0, 1}
  rw [Finset.singleton_biUnion, cut_ball_one T]

theorem cut_far_notMem (T : ℕ) : (2 : Fin 3) ∉ ball cut.nbhd (T + 1) 0 := by
  rw [cut_ball_zero T]
  decide

/-- **The cut rejection.** For every deadline, and for every report, the
responsiveness premise fails: no waiting repairs a missing path. -/
theorem cut_no_guarantee (T : ℕ) (report : ℝ → ℝ) :
    ¬ (worldEncoding cut base 2 id 0 (T + 1) report values).Reconstructs 1 :=
  not_reconstructs_of_outside_past cut base id report values (cut_far_notMem T)
    zero_mem ten_mem values_separated

/-! ## 31. A causal mask, and what no depth reaches

The delay line above is a chain of sites chosen to carry a delay. This is a
*deployed* architecture: the sites of a decoder-only forward pass, indexed by
token position and layer, with the neighbourhood the causal mask gives. The
activation at position `t` and layer `ℓ` reads positions at most `t` at layer
`ℓ - 1` and nothing else, so the causal past is read off the architecture rather
than chosen by interpretation.

The headline is `mask_ball_subset_le`, and it is stronger than a latency claim:
the causal past never reaches a later position **at any depth**. Paired with
`not_outside_past_of_isFullSupport` — one round of a full-support kernel reaches
every site — that is the asymmetry stated on both sides.

The neighbourhood is spelled `u.2.val + 1 = v.2.val` rather than with a
subtraction, because `Fin` subtraction wraps: this way the embedding layer reads
nothing as a consequence (`mask_nbhd_layer_zero`) rather than by a case split.

**Scope, and it is load-bearing.** This is *one forward pass*. Across token steps
a model does read its own prior output, so nothing here says anything about the
autoregressive loop; what that loop carries between steps is bounded by
`Reconstruction.Encoding.card_le_card_tokens` instead, and by nothing proved
here. Nor is any of this about latency: `ball` counts hops, and no result in this
development is about time to solution. The controls fence the two ways the
rejection could be trivial — the graph delivers backwards at round one
(`mask_backward_mem_ball`), and a report reading an earlier position is exact at
round one (`mask_reads_earlier_position`), so what fails forwards fails by
direction and not by a missing path. -/

/-- The sites of a decoder-only forward pass: `P` token positions by `L` layers,
each site hearing from positions at most its own at the layer below. The update
adds what arrives to what the site holds, so a value that reaches a site is
visible in its state. -/
def mask (P L : ℕ) : Network (Fin P × Fin L) ℝ ℝ where
  nbhd := fun v => Finset.univ.filter (fun u => u.1 ≤ v.1 ∧ u.2.val + 1 = v.2.val)
  msg := fun _ _ s => s
  step := fun _ s inc => s + ∑ u, (inc u).getD 0

/-- The baseline forward pass: every activation at rest. -/
def maskBase (P L : ℕ) : Fin P × Fin L → ℝ := fun _ => 0

@[simp] theorem mem_mask_nbhd_iff {P L : ℕ} {u v : Fin P × Fin L} :
    u ∈ (mask P L).nbhd v ↔ u.1 ≤ v.1 ∧ u.2.val + 1 = v.2.val := by
  simp [mask]

/-- **The embedding layer hears from nobody.** A consequence of the
neighbourhood, not a case in its definition. -/
theorem mask_nbhd_layer_zero {P L : ℕ} {v : Fin P × Fin L} (hv : v.2.val = 0) :
    (mask P L).nbhd v = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun u hu => ?_
  rw [mem_mask_nbhd_iff, hv] at hu
  exact Nat.succ_ne_zero _ hu.2

/-- The mask, as the rank hypothesis of `ball_rank_le`: no site hears from a
later position. This is where the architecture enters, and it is checked against
the neighbourhood rather than declared of it. -/
theorem mask_nbhd_pos_le {P L : ℕ} (v : Fin P × Fin L) :
    ∀ u ∈ (mask P L).nbhd v, u.1 ≤ v.1 :=
  fun _ hu => (mem_mask_nbhd_iff.1 hu).1

/-- **The causal past never reaches a later position, at any depth.** Not that it
grows slowly: for every number of rounds, every site whose initial activation can
reach `v` sits at a position at most `v`'s. Depth buys reach across layers and
none across positions. -/
theorem mask_ball_subset_le {P L : ℕ} (n : ℕ) (v : Fin P × Fin L) :
    ball (mask P L).nbhd n v ⊆ Finset.univ.filter (fun u => u.1 ≤ v.1) :=
  fun u hu => Finset.mem_filter.2 ⟨Finset.mem_univ u, ball_rank_le mask_nbhd_pos_le n v u hu⟩

/-- A site at a strictly later position is outside the causal past, at every
deadline: the hypothesis both negative results of `Phase6_Locality` run on,
supplied by the architecture with an explicit site rather than declared. -/
theorem mask_forward_notMem_ball {P L : ℕ} (n : ℕ) {v w : Fin P × Fin L} (h : v.1 < w.1) :
    w ∉ ball (mask P L).nbhd n v :=
  notMem_ball_of_rank_lt mask_nbhd_pos_le h

/-- **No waiting repairs it.** For every deadline, every baseline and every
report, a report at position `t` cannot be within one of a value written into a
later position: the two forward passes leave the reading site identical, so the
readout has the same input in both.

What this does not say: that the model is inaccurate about its own earlier
positions, which `mask_reads_earlier_position` shows it can be exact about; or
anything about a second forward pass, in which the later position's token is part
of the input. -/
theorem mask_no_guarantee {P L : ℕ} (T : ℕ) {v w : Fin P × Fin L} (h : v.1 < w.1)
    (base : Fin P × Fin L → ℝ) (report : ℝ → ℝ) :
    ¬ (worldEncoding (mask P L) base w id v T report values).Reconstructs 1 :=
  not_reconstructs_of_outside_past (mask P L) base id report values
    (mask_forward_notMem_ball T h) zero_mem ten_mem values_separated

/-! ### The controls: the mask delivers, backwards

A cut graph would reject the same way for the wrong reason. These two say the
graph is not cut: the past reaches the layer below at round one, and on the
smallest instance a report on an earlier position is exact there. -/

/-- **The graph delivers backwards at round one.** A site one layer below, at a
position at most `v`'s, is in `v`'s causal past immediately. -/
theorem mask_backward_mem_ball {P L : ℕ} {v u : Fin P × Fin L} (hpos : u.1 ≤ v.1)
    (hlay : u.2.val + 1 = v.2.val) : u ∈ ball (mask P L).nbhd 1 v := by
  rw [ball_succ]
  exact Finset.mem_insert_of_mem
    (Finset.mem_biUnion.2 ⟨u, mem_mask_nbhd_iff.2 ⟨hpos, hlay⟩, self_mem_ball _ 0 u⟩)

/-- Two positions and two layers: the smallest instance in which both directions
have something to say. The value written into position `0` of the embedding layer
is at position `1` of the next layer after one round, exactly. -/
theorem mask_read_earlier (q : ℝ) :
    (mask 2 2).run (intervene (maskBase 2 2) (0, 0) id q) 1 (1, 1) = q := by
  simp [Network.run, Network.round, Network.incoming, mask, maskBase, intervene,
    Function.update, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **The positive control.** Reading the activation directly, the report is exact
for every value the world might have been given — not merely for the two the
rejection uses. The obstruction above is therefore about direction. -/
theorem mask_reads_earlier_position :
    (worldEncoding (mask 2 2) (maskBase 2 2) (0, 0) id (1, 1) 1 id Set.univ).Reconstructs 0 := by
  intro q _
  rw [worldEncoding_error, mask_read_earlier q, id_eq, dist_self]

/-- **The same instance, forwards.** Position `0` at the layer above cannot be
guaranteed to track a value written into position `1` below it, at any deadline.
One network, one round: exact backwards, unreachable forwards. -/
theorem mask_forward_no_guarantee (T : ℕ) (report : ℝ → ℝ) :
    ¬ (worldEncoding (mask 2 2) (maskBase 2 2) (1, 0) id (0, 1) T report values).Reconstructs 1 :=
  mask_no_guarantee T (by decide) _ report

#print axioms ball_line_one
#print axioms ball_line_two
#print axioms source_holds
#print axioms read_one
#print axioms read_two
#print axioms no_guarantee_at_one
#print axioms guarantee_at_two
#print axioms coincidental_at_one
#print axioms const_report_fails
#print axioms cut_ball_zero
#print axioms cut_no_guarantee
#print axioms no_resonance_at_one
#print axioms resonance_at_two
#print axioms mask_nbhd_layer_zero
#print axioms mask_ball_subset_le
#print axioms mask_forward_notMem_ball
#print axioms mask_no_guarantee
#print axioms mask_backward_mem_ball
#print axioms mask_read_earlier
#print axioms mask_reads_earlier_position
#print axioms mask_forward_no_guarantee

end Locality
end Examples
end PhysicsOfConsciousness
