/-
  Examples/Locality.lean — a three-site delay line, and what it can promise

  §25. One value is written into the far end of a three-site chain and read at
  the near end. The chain's middle site is a delay register: the value is
  unavailable at round one and exact at round two, and the negative result at
  round one is the causal-past theorem rather than a property of this readout.
  The controls fence the three ways the result could be trivial: a cut path
  never delivers, a constant report never satisfies responsiveness, and a report
  that is right about one fixed world stays right about it.
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

end Locality
end Examples
end PhysicsOfConsciousness
