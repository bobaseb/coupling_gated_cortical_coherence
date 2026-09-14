/-
  Examples/RegisterBudget.lean — one register, its operations and its ledger

  The witness for `RegisterLedger`, the common resource model of the active
  chain's n3 → n4 edge. The register is §1's one-bit eraser, at temperature one
  and with Landauer heat `log 2`; its operations act on a lamp bit through one
  log-odds family, and their heats sum to exactly that dissipation. The
  controlled operation's budget is then derived, not compared.

  The regressions fence both physical inputs: a compressive operation can
  exceed the register's whole dissipation, and a ledger whose other operation
  draws heat out of the reservoir allocates more than the whole to its
  controlled one.
-/

import PhysicsOfConsciousness.Examples.Bit
import PhysicsOfConsciousness.Phase3_AgencyThermodynamics

namespace PhysicsOfConsciousness.Examples

section GenericRegression

variable {sys S : Type*} {n : ℕ} [Fintype sys] [Fintype S] [Nonempty S] [Thermodynamics sys]
  (L : RegisterLedger sys S n)

example (i : Fin n) (h : L.Compressive i) : 0 ≤ L.opHeat i :=
  L.opHeat_nonneg_of_compressive i h

example (a : Fin n) (h : ∀ i, i ≠ a → L.Compressive i) :
    L.opHeat a ≤ heat_dissipation L.update :=
  L.opHeat_le_dissipation a h

end GenericRegression

example {sys S : Type*} {n : ℕ} [Fintype sys] [DecidableEq sys] [Fintype S]
    [StatisticalMechanics sys] (L : RegisterLedger sys S n) :
    ∑ i, L.opHeat i = Thermodynamics.temperature (sys := sys) *
      (boltzmann_entropy (BipartiteEnvironment.final_bath L.update) -
        boltzmann_entropy (BipartiteEnvironment.initial_bath L.update)) :=
  L.ledger_bathEntropy

namespace RegisterBudget

/-! ## 1. One log-odds family of register operations -/

/-- Initial law: the register's bit is uniform and the environment agrees with
it with probability `w`. -/
noncomputable def law (w : ℝ) (h0 : 0 < w := by norm_num) (h1 : w < 1 := by norm_num) :
    ProbDist (Bool × Bool) where
  p z := if z.1 = z.2 then w / 2 else (1 - w) / 2
  nonneg z := by split <;> linarith
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]; ring

/-- Channel: the environment relaxes toward agreement with the held register
bit at odds `a : 1 - a`, independently of its current value. -/
noncomputable def chan (a : ℝ) (h0 : 0 < a := by norm_num) (h1 : a < 1 := by norm_num)
    (x : Bool) (_s : Bool) : ProbDist Bool where
  p t := if t = x then a else 1 - a
  nonneg t := by split <;> linarith
  sum_one := by cases x <;> norm_num [Fintype.sum_bool]

/-- The channel's log-odds gap, which is the interaction energy of disagreement
at thermal scale one. -/
noncomputable def gap (a : ℝ) : ℝ := Real.log (a / (1 - a))

/-- Interaction energy: agreeing with the register's bit is lower by `gap a`. -/
noncomputable def energy (a : ℝ) (z : Bool × Bool) : ℝ :=
  if z.1 = z.2 then 0 else gap a

/-- Outward heat is the interaction-energy drop. These relaxations are
autonomous and require no external work, so the operations' energy source is
explicit rather than an assigned cost. -/
noncomputable def heat (a : ℝ) (x s t : Bool) : ℝ := energy a (x, s) - energy a (x, t)

/-- One operation of the register: the channel `a` acting on the law `law w`. -/
noncomputable def op (a w : ℝ) (ha0 : 0 < a := by norm_num) (ha1 : a < 1 := by norm_num)
    (hw0 : 0 < w := by norm_num) (hw1 : w < 1 := by norm_num) :
    FiniteFeedbackStep Bool Bool :=
  ⟨law w hw0 hw1, chan a ha0 ha1⟩

theorem op_positive (a w : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hw0 : 0 < w) (hw1 : w < 1) :
    (op a w ha0 ha1 hw0 hw1).Positive := by
  constructor
  · intro z
    show 0 < (if z.1 = z.2 then w / 2 else (1 - w) / 2)
    split <;> linarith
  · intro x s t
    show 0 < (if t = x then a else 1 - a)
    split <;> linarith

private lemma log_reverse (a : ℝ) : Real.log ((1 - a) / a) = -gap a := by
  rw [gap, ← Real.log_inv, inv_div]

/-- The log-odds gap is the reservoir's log-ratio: local detailed balance holds
at thermal scale one for this whole family. -/
theorem op_local_balance (a w : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hw0 : 0 < w) (hw1 : w < 1) :
    (op a w ha0 ha1 hw0 hw1).LocalDetailedBalance 1 (heat a) := by
  have hane : a ≠ 0 := ne_of_gt ha0
  have hbne : (1 : ℝ) - a ≠ 0 := ne_of_gt (by linarith)
  intro x s t
  show heat a x s t = 1 * Real.log ((chan a ha0 ha1 x s).p t / (chan a ha0 ha1 x t).p s)
  cases x <;> cases s <;> cases t <;>
    simp [heat, energy, chan, div_self hane, div_self hbne, log_reverse, gap]

/-- The law after one operation is the law of the channel's own odds. -/
theorem op_final (a w : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hw0 : 0 < w) (hw1 : w < 1) :
    (op a w ha0 ha1 hw0 hw1).final = law a ha0 ha1 := by
  apply ProbDist.ext
  funext z
  rcases z with ⟨x, t⟩
  cases x <;> cases t <;>
    norm_num [FiniteFeedbackStep.final, op, law, chan, Fintype.sum_bool] <;> ring

/-- The operation's actual mean heat, on its own path law. -/
theorem op_meanHeat (a w : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hw0 : 0 < w) (hw1 : w < 1) :
    (op a w ha0 ha1 hw0 hw1).meanHeat (heat a) = gap a * (a - w) := by
  norm_num [FiniteFeedbackStep.meanHeat, FiniteFeedbackStep.forward, op, law, chan,
    heat, energy, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- The joint entropy of the family's laws: one uniform register bit and the
binary entropy of agreement. -/
theorem law_entropy (w : ℝ) (h0 : 0 < w) (h1 : w < 1) :
    shannon_entropy (law w h0 h1).p =
      Real.log 2 - w * Real.log w - (1 - w) * Real.log (1 - w) := by
  have hw : w ≠ 0 := ne_of_gt h0
  have hw' : (1 : ℝ) - w ≠ 0 := ne_of_gt (by linarith)
  have e1 : Real.log (w / 2) = Real.log w - Real.log 2 :=
    Real.log_div hw two_ne_zero
  have e2 : Real.log ((1 - w) / 2) = Real.log (1 - w) - Real.log 2 :=
    Real.log_div hw' two_ne_zero
  simp only [shannon_entropy, law, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [e1, e2]
  ring

/-! ## 2. The register's two operations and its ledger -/

/-- The controlled operation: the register drives the environment toward its own
bit at odds 2 : 1, from a law in which the two mostly disagree. -/
noncomputable def act : FiniteFeedbackStep Bool Bool := op (2 / 3) (4 / 15)

/-- The register's other operation: it relaxes the uniform law toward agreement
at odds 4 : 1. This one compresses the joint law, and pays heat for it. -/
noncomputable def rest : FiniteFeedbackStep Bool Bool := op (4 / 5) (1 / 2)

theorem gap_act : gap (2 / 3) = Real.log 2 := by norm_num [gap]

theorem gap_rest : gap (4 / 5) = 2 * Real.log 2 := by
  rw [gap]
  norm_num
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

theorem act_heat : act.meanHeat (heat (2 / 3)) = 2 / 5 * Real.log 2 := by
  rw [act, op_meanHeat, gap_act]
  ring

theorem rest_heat : rest.meanHeat (heat (4 / 5)) = 3 / 5 * Real.log 2 := by
  rw [rest, op_meanHeat, gap_rest]
  ring

/-- §1's one-bit eraser dissipates `log 2` at temperature one. -/
theorem boolRegister_heat : heat_dissipation (fun _ : Bool => true) = Real.log 2 := rfl

/-- **The register's ledger.** Both operations are controlled by this register,
both exchange heat with its reservoir at its temperature, and their heats sum to
exactly its dissipated heat. -/
noncomputable def cycle : RegisterLedger Bool Bool 2 where
  update := fun _ => true
  step := ![act, rest]
  heat := ![heat (2 / 3), heat (4 / 5)]
  positive := by
    intro i
    fin_cases i
    · exact op_positive _ _ _ _ _ _
    · exact op_positive _ _ _ _ _ _
  balance := by
    intro i
    fin_cases i
    · exact op_local_balance _ _ _ _ _ _
    · exact op_local_balance _ _ _ _ _ _
  ledger := by
    rw [Fin.sum_univ_two]
    show Real.log 2 = act.meanHeat (heat (2 / 3)) + rest.meanHeat (heat (4 / 5))
    rw [act_heat, rest_heat]
    ring

/-! ## 3. The derived allocation, and what it rests on -/

private lemma log_five : Real.log 5 ≤ 13 / 5 * Real.log 2 := by
  have h : Real.log ((5 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 13) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- The register's other operation compresses the joint law: the second law
then makes its share of the budget nonnegative. -/
theorem rest_compressive : cycle.Compressive 1 := by
  have hf : rest.final = law (4 / 5) (by norm_num) (by norm_num) :=
    op_final _ _ _ _ _ _
  have h45 : Real.log (4 / 5) = 2 * Real.log 2 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h15 : Real.log (1 / 5 : ℝ) = -Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have h12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  show shannon_entropy rest.final.p ≤ shannon_entropy rest.initial.p
  rw [hf]
  show shannon_entropy (law (4 / 5) (by norm_num) (by norm_num)).p ≤
    shannon_entropy (law (1 / 2) (by norm_num) (by norm_num)).p
  rw [law_entropy, law_entropy]
  norm_num [h45, h15, h12]
  linarith [log_five]

theorem act_others_compressive : ∀ i, i ≠ (0 : Fin 2) → cycle.Compressive i := by
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · exact rest_compressive

/-- The allocation, on the witness: the controlled operation's actual heat is
within the named register's dissipation, derived from the ledger and the second
law rather than compared across models. -/
theorem act_within_budget : cycle.opHeat 0 ≤ heat_dissipation cycle.update :=
  cycle.opHeat_le_dissipation 0 act_others_compressive

private lemma log_eleven : 15 * Real.log 5 + 2 * Real.log 2 < 11 * Real.log 11 := by
  have h : Real.log ((5 : ℝ) ^ 15 * 2 ^ 2) < Real.log ((11 : ℝ) ^ 11) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  push_cast at h
  linarith

/-- **The controlled operation is not compressive.** It increases the joint
entropy, so its own second law gives it no nonnegative heat and no upper bound
either: the allocation genuinely consumes the register's ledger. -/
theorem act_not_compressive : ¬ cycle.Compressive 0 := by
  have hf : act.final = law (2 / 3) (by norm_num) (by norm_num) :=
    op_final _ _ _ _ _ _
  have h23 : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have h13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have h415 : Real.log (4 / 15 : ℝ) = 2 * Real.log 2 - Real.log 3 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
      show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    push_cast
    ring
  have h1115 : Real.log (11 / 15 : ℝ) = Real.log 11 - Real.log 3 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  show ¬ shannon_entropy act.final.p ≤ shannon_entropy act.initial.p
  rw [hf]
  show ¬ shannon_entropy (law (2 / 3) (by norm_num) (by norm_num)).p ≤
    shannon_entropy (law (4 / 15) (by norm_num) (by norm_num)).p
  rw [law_entropy, law_entropy, not_le]
  norm_num [h23, h13, h415, h1115]
  linarith [log_eleven]

/-- The controlled operation really is controlled: its transition depends on the
register's state, so the register is not a bystander of an autonomous relaxation. -/
theorem act_depends_on_register :
    (cycle.step 0).transition true false ≠ (cycle.step 0).transition false false := by
  intro h
  have h' : (2 : ℝ) / 3 = 1 - 2 / 3 :=
    congrArg (fun P : ProbDist Bool => P.p true) h
  norm_num at h'

/-! ## 4. Both physical inputs are load-bearing -/

/-- Compressiveness alone does not bound an operation by the register's budget:
this one preserves the joint entropy exactly and still delivers `(7/3) log 2`.
Only the ledger excludes it from this register's operations. -/
theorem compressive_exceeds_budget :
    shannon_entropy (op (8 / 9) (1 / 9)).final.p ≤
      shannon_entropy (op (8 / 9) (1 / 9)).initial.p ∧
    heat_dissipation (fun _ : Bool => true) <
      (op (8 / 9) (1 / 9)).meanHeat (heat (8 / 9)) := by
  have hgap : gap (8 / 9) = 3 * Real.log 2 := by
    rw [gap]
    norm_num
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have hf : (op (8 / 9) (1 / 9)).final = law (8 / 9) (by norm_num) (by norm_num) :=
      op_final _ _ _ _ _ _
    rw [hf]
    show shannon_entropy (law (8 / 9) (by norm_num) (by norm_num)).p ≤
      shannon_entropy (law (1 / 9) (by norm_num) (by norm_num)).p
    rw [law_entropy, law_entropy]
    norm_num
    linarith
  · rw [op_meanHeat, hgap, boolRegister_heat]
    norm_num
    linarith

/-- A second ledger for the same register, whose other operation increases the
joint entropy and draws heat out of the reservoir. Positivity, local detailed
balance and the accounting identity all still hold. -/
noncomputable def leaky : RegisterLedger Bool Bool 2 where
  update := fun _ => true
  step := ![op (4 / 5) (13 / 60), op (2 / 3) (5 / 6)]
  heat := ![heat (4 / 5), heat (2 / 3)]
  positive := by
    intro i
    fin_cases i
    · exact op_positive _ _ _ _ _ _
    · exact op_positive _ _ _ _ _ _
  balance := by
    intro i
    fin_cases i
    · exact op_local_balance _ _ _ _ _ _
    · exact op_local_balance _ _ _ _ _ _
  ledger := by
    rw [Fin.sum_univ_two]
    show Real.log 2 = (op (4 / 5) (13 / 60)).meanHeat (heat (4 / 5)) +
      (op (2 / 3) (5 / 6)).meanHeat (heat (2 / 3))
    rw [op_meanHeat, op_meanHeat, gap_act, gap_rest]
    ring

/-- **The ledger alone does not bound the controlled operation.** Without the
compressiveness of the register's other operations, the accounting identity
allocates more than the register's whole dissipation to this one. -/
theorem leaky_exceeds_budget : heat_dissipation (fun _ : Bool => true) < leaky.opHeat 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  show Real.log 2 < (op (4 / 5) (13 / 60)).meanHeat (heat (4 / 5))
  rw [op_meanHeat, gap_rest]
  norm_num
  linarith

/-- The operation that pays for it is exactly the one the derivation excludes:
a negative share cannot come from a compressive operation. -/
theorem leaky_other_not_compressive : ¬ leaky.Compressive 1 := by
  intro h
  have hnn := leaky.opHeat_nonneg_of_compressive 1 h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : leaky.opHeat 1 = -(1 / 6) * Real.log 2 := by
    show (op (2 / 3) (5 / 6)).meanHeat (heat (2 / 3)) = -(1 / 6) * Real.log 2
    rw [op_meanHeat, gap_act]
    ring
  rw [this] at hnn
  linarith

end RegisterBudget

/-! ## Regression specifications -/

namespace RegisterBudget

example : cycle.update = (fun _ : Bool => true) := rfl

example : cycle.opHeat 0 = 2 / 5 * Real.log 2 := act_heat

example : cycle.opHeat 1 = 3 / 5 * Real.log 2 := rest_heat

example : heat_dissipation cycle.update = cycle.opHeat 0 + cycle.opHeat 1 := by
  rw [cycle.ledger, Fin.sum_univ_two]
  rfl

example : cycle.Compressive 1 := rest_compressive

example : ¬ cycle.Compressive 0 := act_not_compressive

example : cycle.opHeat 0 ≤ heat_dissipation cycle.update := act_within_budget

example : heat_dissipation (fun _ : Bool => true) < leaky.opHeat 0 := leaky_exceeds_budget

example : ¬ leaky.Compressive 1 := leaky_other_not_compressive

example : (cycle.step 0).transition true false ≠ (cycle.step 0).transition false false :=
  act_depends_on_register

end RegisterBudget

#print axioms RegisterLedger.opHeat_le_dissipation
#print axioms RegisterBudget.act_within_budget
#print axioms RegisterBudget.act_not_compressive
#print axioms RegisterBudget.leaky_exceeds_budget

end PhysicsOfConsciousness.Examples
