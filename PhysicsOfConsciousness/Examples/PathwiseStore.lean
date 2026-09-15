import PhysicsOfConsciousness.Phase3_ContinuingAgent

/-!
# A store on the trajectory: witnesses and regression specifications

Two stores over the same three readings — two units, one unit, and overdrawn —
and the same declared parameter type, which nothing here reads.

The *gambler* spends a unit or idles with equal probability. Its declared
allowance covers its expected draw at every prefix, so the mean ledger's
`ContinuingProcess.Sustains` holds; two spends in a row are nonetheless a path
it has, so `PathwiseStore.Solvent` fails. The converse of
`PathwiseStore.totalDraw_le_of_solvent` is therefore false, and the expected
allowance is not a battery.

The *charger* spends a unit and is given it back, deterministically, forever.
It is solvent at every horizon while the work it has drawn grows without bound,
so no finite store bounds a replenished agent's cumulative work. It satisfies
neither hypothesis of the two replenishment theorems — it does not cover each
draw as it is made, and its net draw is not uniformly positive — which is what
places it strictly between them. Its supply is load-bearing: the same protocol
and the same reading, with the supply removed, is not a ledger at all.
-/

namespace PhysicsOfConsciousness.Examples

namespace Store

/-! ## The readings, and the states that carry them -/

/-- The store's three readings. Only the third is overdrawn. -/
noncomputable def reading : Fin 3 → ℝ := ![1, 0, -1]

@[simp] theorem reading_zero : reading 0 = 1 := rfl
@[simp] theorem reading_one : reading 1 = 0 := rfl
@[simp] theorem reading_two : reading 2 = -1 := rfl

/-- The law that puts the store at a declared reading, with the parameter
carrying no information. -/
noncomputable def atReading (i : Fin 3) : ProbDist (Unit × Fin 3) where
  p z := if z.2 = i then 1 else 0
  nonneg z := by split <;> norm_num
  sum_one := by
    simp only [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
    simp

@[simp] theorem atReading_apply (i : Fin 3) (z : Unit × Fin 3) :
    (atReading i).p z = if z.2 = i then 1 else 0 := rfl

/-! ## The gambler: an allowance that holds in expectation -/

/-- Idle or spend one unit, with equal probability, until the store is
overdrawn, after which nothing further happens. -/
noncomputable def spend (s : Fin 3) : ProbDist (Fin 3) where
  p t := ![![1 / 2, 1 / 2, 0], ![0, 1 / 2, 1 / 2], ![0, 0, 1]] s t
  nonneg t := by fin_cases s <;> fin_cases t <;> simp [Matrix.cons_val]
  sum_one := by
    fin_cases s <;> simp [Fin.sum_univ_three, Matrix.cons_val] <;> norm_num

/-- A spend costs one unit and an idle costs nothing. -/
noncomputable def spendDraw (_n : ℕ) (_x : Unit) (s t : Fin 3) : ℝ :=
  if t = s then 0 else 1

noncomputable def gamblerProtocol : FiniteProtocol Unit (Fin 3) :=
  ⟨atReading 0, fun _ _ => spend⟩

/-- The gambler's store: it draws, and nothing replenishes it. -/
noncomputable def gambler : PathwiseStore Unit (Fin 3) :=
  ⟨gamblerProtocol, reading, spendDraw, fun _ _ _ _ => 0⟩

@[simp] theorem gambler_stage (n : ℕ) (x : Unit) :
    gamblerProtocol.stage n x = spend := rfl

theorem gambler_law_one (u : Unit) (i : Fin 3) :
    (gamblerProtocol.law 1).p (u, i) = ![1 / 2, 1 / 2, 0] i := by
  rw [gamblerProtocol.law_succ_apply 0 (u, i)]
  simp only [FiniteProtocol.law_zero, gamblerProtocol, atReading_apply,
    Fin.sum_univ_three]
  fin_cases i <;> simp [spend, Matrix.cons_val]

theorem gambler_law_two (u : Unit) (i : Fin 3) :
    (gamblerProtocol.law 2).p (u, i) = ![1 / 4, 1 / 2, 1 / 4] i := by
  rw [gamblerProtocol.law_succ_apply 1 (u, i)]
  simp only [gambler_law_one, gambler_stage, Fin.sum_univ_three]
  fin_cases i <;> simp [spend, Matrix.cons_val] <;> norm_num

/-- The reading is the ledger: a spend lowers it by one and an idle leaves it,
on every transition the gambler can execute. -/
theorem gambler_ledgered : gambler.Ledgered := by
  rintro n x s t - ht
  have ht' : 0 < (spend s).p t := ht
  show reading t = reading s - spendDraw n x s t + 0
  fin_cases s <;> fin_cases t <;>
    simp_all [spend, spendDraw, reading, Matrix.cons_val]

/-- The first stage is funded: the gambler holds a unit and spends at most one. -/
theorem gambler_funded_zero : gambler.Funded 0 := by
  intro x s t hs ht
  have hs' : 0 < (atReading 0).p (x, s) := hs
  have ht' : 0 < (spend s).p t := ht
  show spendDraw 0 x s t ≤ reading s + 0
  fin_cases s <;> fin_cases t <;>
    simp_all [spend, spendDraw, reading, atReading, Matrix.cons_val]

/-- The gambler is solvent after one stage. -/
theorem gambler_solvent_one : gambler.Solvent 1 := by
  refine gambler.solvent_succ gambler_ledgered 0 ?_ gambler_funded_zero
  rintro k hk ⟨u, i⟩ hz
  have hk0 : k = 0 := Nat.le_zero.1 hk
  subst hk0
  have hz' : 0 < (atReading 0).p (u, i) := hz
  show (0 : ℝ) ≤ reading i
  fin_cases i <;> simp_all [atReading, reading]

/-- **The second stage is not funded.** The gambler can reach the reading one
with a spend still available to it, and one unit is more than nothing. -/
theorem gambler_not_funded : ¬ gambler.Funded 1 := by
  intro h
  have hs : gamblerProtocol.Reachable 1 ((), 1) := by
    show 0 < (gamblerProtocol.law 1).p ((), 1)
    rw [gambler_law_one]
    norm_num
  have ht : 0 < (gamblerProtocol.stage 1 () 1).p 2 := by
    show 0 < (spend 1).p 2
    simp [spend, Matrix.cons_val]
  have := h () 1 2 hs ht
  simp only [gambler, spendDraw, reading] at this
  simp at this
  norm_num at this

/-- **And it is not solvent.** Two spends in a row are a path the gambler has,
and at its end the store is overdrawn. -/
theorem gambler_not_solvent : ¬ gambler.Solvent 2 := by
  intro h
  have hz : gamblerProtocol.Reachable 2 ((), 2) := by
    show 0 < (gamblerProtocol.law 2).p ((), 2)
    rw [gambler_law_two]
    simp [Matrix.cons_val]
  have := h 2 le_rfl ((), 2) hz
  simp only [gambler, reading] at this
  simp [Matrix.cons_val] at this
  norm_num at this

/-! ### The same run, on the mean ledger -/

/-- The gambler as a resource process of the existing mean ledger. Its energy
is the store's reading with the opposite sign and its stages deliver no heat,
so the work each stage supplies is exactly the work it draws. -/
noncomputable def gamblerProcess : ContinuingProcess Unit (Fin 3) :=
  ⟨gamblerProtocol, fun z => -reading z.2, fun _ _ _ _ => 0, 1, 1⟩

/-- The two ledgers charge the same run the same expected work. -/
theorem gamblerProcess_totalWork (N : ℕ) :
    gamblerProcess.totalWork N = gambler.totalDraw N := by
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (gamblerProtocol.step k).meanHeat_congr_support ?_
  intro x s t _ ht
  have ht' : 0 < (spend s).p t := ht
  show -reading t - -reading s + 0 = spendDraw k x s t
  fin_cases s <;> fin_cases t <;>
    simp_all [spend, spendDraw, reading, Matrix.cons_val]

theorem gambler_totalDraw_one : gambler.totalDraw 1 = 1 / 2 := by
  show ∑ k ∈ Finset.range 1, (gamblerProtocol.step k).meanHeat (gambler.draw k) = 1 / 2
  rw [Finset.sum_range_one, gamblerProtocol.meanHeat_apply]
  simp only [FiniteProtocol.law_zero, gamblerProtocol, atReading_apply,
    Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_three]
  simp [spend, gambler, spendDraw, reading, Matrix.cons_val]

theorem gambler_totalDraw_two : gambler.totalDraw 2 = 1 := by
  show ∑ k ∈ Finset.range 2, (gamblerProtocol.step k).meanHeat (gambler.draw k) = 1
  rw [Finset.sum_range_succ]
  have h1 : ∑ k ∈ Finset.range 1, (gamblerProtocol.step k).meanHeat (gambler.draw k)
      = 1 / 2 := gambler_totalDraw_one
  rw [h1, gamblerProtocol.meanHeat_apply]
  simp only [gambler_law_one, gambler_stage, Finset.univ_unique, Finset.sum_singleton,
    Fin.sum_univ_three]
  simp [spend, gambler, spendDraw, reading, Matrix.cons_val]
  norm_num

/-- **The expected allowance never runs out.** The mean ledger's own predicate
holds over the whole run: the gambler has drawn at most its declared store at
every prefix. -/
theorem gambler_mean_sustains : gamblerProcess.Sustains 2 := by
  intro k hk
  show 0 ≤ (1 : ℝ) - gamblerProcess.totalWork k
  rw [gamblerProcess_totalWork]
  interval_cases k
  · simp [PathwiseStore.totalDraw]
  · rw [gambler_totalDraw_one]; norm_num
  · rw [gambler_totalDraw_two]; norm_num

/-- **The expectation is not a battery.** The mean ledger reports an allowance
that was never overdrawn, and the store was overdrawn on a path of probability
one quarter. The refinement `totalDraw_le_of_solvent` therefore runs one way
only: its conclusion holds here — with equality — and its hypothesis fails. -/
theorem sustained_not_solvent :
    gamblerProcess.Sustains 2 ∧ gambler.totalDraw 2 ≤
        gambler.meanBalance 0 + gambler.totalSupply 2 ∧ ¬ gambler.Solvent 2 := by
  refine ⟨gambler_mean_sustains, ?_, gambler_not_solvent⟩
  have hm : gambler.meanBalance 0 = 1 := by
    show ∑ z, (gamblerProtocol.law 0).p z * reading z.2 = 1
    simp only [FiniteProtocol.law_zero, gamblerProtocol, atReading_apply,
      Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_three]
    simp [reading]
  have hs : gambler.totalSupply 2 = 0 := by
    show ∑ k ∈ Finset.range 2, (gamblerProtocol.step k).meanHeat (gambler.supply k) = 0
    simp [FiniteFeedbackStep.meanHeat, gambler]
  rw [gambler_totalDraw_two, hm, hs]
  norm_num

/-! ## The charger: replenishment, and an unbounded draw -/

/-- Spend a unit, be given it back, repeat. Nothing is random and no mass is
positive off the cycle, so this is a store the pathwise account handles and a
positivity hypothesis would exclude. -/
noncomputable def cycle (s : Fin 3) : ProbDist (Fin 3) where
  p t := ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]] s t
  nonneg t := by fin_cases s <;> fin_cases t <;> simp [Matrix.cons_val]
  sum_one := by fin_cases s <;> simp [Fin.sum_univ_three, Matrix.cons_val]

/-- Leaving the full reading costs a unit; every other transition costs nothing. -/
noncomputable def cycleDraw (_n : ℕ) (_x : Unit) (s _t : Fin 3) : ℝ :=
  if s = 0 then 1 else 0

/-- The declared supply: a unit arrives on the return transition. It is an
input of the model in exactly the way `ContinuingProcess.stored` is. -/
noncomputable def cycleSupply (_n : ℕ) (_x : Unit) (s _t : Fin 3) : ℝ :=
  if s = 1 then 1 else 0

noncomputable def chargerProtocol : FiniteProtocol Unit (Fin 3) :=
  ⟨atReading 0, fun _ _ => cycle⟩

noncomputable def charger : PathwiseStore Unit (Fin 3) :=
  ⟨chargerProtocol, reading, cycleDraw, cycleSupply⟩

@[simp] theorem charger_stage (n : ℕ) (x : Unit) :
    chargerProtocol.stage n x = cycle := rfl

theorem charger_ledgered : charger.Ledgered := by
  rintro n x s t - ht
  have ht' : 0 < (cycle s).p t := ht
  show reading t = reading s - cycleDraw n x s t + cycleSupply n x s t
  fin_cases s <;> fin_cases t <;>
    simp_all [cycle, cycleDraw, cycleSupply, reading, Matrix.cons_val]

/-- The overdrawn reading is never reached: the cycle has no path into it. -/
theorem charger_reach : ∀ (n : ℕ) (u : Unit) (i : Fin 3),
    chargerProtocol.Reachable n (u, i) → i = 0 ∨ i = 1 := by
  intro n
  induction n with
  | zero =>
    intro u i h
    have h' : 0 < (atReading 0).p (u, i) := h
    fin_cases i <;> simp_all [atReading]
  | succ n ih =>
    intro u i h
    obtain ⟨s, hsr, hst⟩ := chargerProtocol.exists_pred_of_reachable n u i h
    have hst' : 0 < (cycle s).p i := hst
    rcases ih u s hsr with hs | hs <;> subst hs <;>
      fin_cases i <;> simp_all [cycle, Matrix.cons_val]

/-- Every stage is funded: the full reading covers the unit it spends, and the
empty one draws nothing while the supply arrives. -/
theorem charger_funded (k : ℕ) : charger.Funded k := by
  intro x s t hs ht
  have ht' : 0 < (cycle s).p t := ht
  show cycleDraw k x s t ≤ reading s + cycleSupply k x s t
  rcases charger_reach k x s hs with h | h <;> subst h <;>
    simp [cycleDraw, cycleSupply, reading]

/-- **Solvent at every horizon.** Derived from the generic pathwise theorem,
not recomputed. -/
theorem charger_solvent (N : ℕ) : charger.Solvent N := by
  refine charger.solvent_of_funded charger_ledgered ?_ charger_funded N
  rintro ⟨u, i⟩ hz
  show (0 : ℝ) ≤ reading i
  rcases charger_reach 0 u i hz with h | h <;> subst h <;>
    simp [reading]

/-! ### The work it has drawn is unbounded -/

theorem charger_law_even (m : ℕ) : chargerProtocol.law (2 * m) = atReading 0 ∧
    chargerProtocol.law (2 * m + 1) = atReading 1 := by
  induction m with
  | zero =>
    refine ⟨rfl, ?_⟩
    refine ProbDist.ext ?_
    funext z
    obtain ⟨u, i⟩ := z
    rw [chargerProtocol.law_succ_apply 0 (u, i)]
    simp only [FiniteProtocol.law_zero, chargerProtocol,
      atReading_apply, Fin.sum_univ_three]
    fin_cases i <;> simp [cycle, Matrix.cons_val]
  | succ m ih =>
    have h2 : chargerProtocol.law (2 * m + 2) = atReading 0 := by
      refine ProbDist.ext ?_
      funext z
      obtain ⟨u, i⟩ := z
      rw [chargerProtocol.law_succ_apply (2 * m + 1) (u, i), ih.2]
      simp only [charger_stage, atReading_apply, Fin.sum_univ_three]
      fin_cases i <;> simp [cycle, Matrix.cons_val]
    refine ⟨by rw [show 2 * (m + 1) = 2 * m + 2 by ring]; exact h2, ?_⟩
    refine ProbDist.ext ?_
    funext z
    obtain ⟨u, i⟩ := z
    rw [show 2 * (m + 1) + 1 = 2 * m + 2 + 1 by ring,
      chargerProtocol.law_succ_apply (2 * m + 2) (u, i), h2]
    simp only [charger_stage, atReading_apply, Fin.sum_univ_three]
    fin_cases i <;> simp [cycle, Matrix.cons_val]

theorem charger_stage_draw_even (m : ℕ) :
    (chargerProtocol.step (2 * m)).meanHeat (charger.draw (2 * m)) = 1 := by
  rw [chargerProtocol.meanHeat_apply, (charger_law_even m).1]
  simp only [charger_stage, atReading_apply, Finset.univ_unique, Finset.sum_singleton,
    Fin.sum_univ_three]
  simp [cycle, charger, cycleDraw, Matrix.cons_val]

theorem charger_stage_draw_odd (m : ℕ) :
    (chargerProtocol.step (2 * m + 1)).meanHeat (charger.draw (2 * m + 1)) = 0 := by
  rw [chargerProtocol.meanHeat_apply, (charger_law_even m).2]
  simp only [charger_stage, atReading_apply, Finset.univ_unique, Finset.sum_singleton,
    Fin.sum_univ_three]
  simp [cycle, charger, cycleDraw, Matrix.cons_val]

/-- Each completed cycle draws one more unit than the last. -/
theorem charger_totalDraw (m : ℕ) : charger.totalDraw (2 * m) = m := by
  induction m with
  | zero => simp [PathwiseStore.totalDraw]
  | succ m ih =>
    show ∑ k ∈ Finset.range (2 * (m + 1)),
      (chargerProtocol.step k).meanHeat (charger.draw k) = _
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, charger_stage_draw_even m, charger_stage_draw_odd m]
    have : ∑ k ∈ Finset.range (2 * m),
        (chargerProtocol.step k).meanHeat (charger.draw k) = m := ih
    rw [this]
    push_cast
    ring

/-- **No finite store bounds a replenished agent's work.** The charger is
solvent at every horizon and has drawn more than any declared allowance by
some horizon. Sustained operation is a claim about the supply, and the supply
here is declared. -/
theorem charger_draw_unbounded (b : ℝ) : ∃ N, charger.Solvent N ∧ b < charger.totalDraw N := by
  obtain ⟨m, hm⟩ := exists_nat_gt b
  exact ⟨2 * m, charger_solvent _, by rw [charger_totalDraw]; exact hm⟩

/-! ### It satisfies neither replenishment hypothesis -/

/-- The supply does not cover each draw as it is made: the spending transition
is not replenished at all. -/
theorem charger_not_covered :
    ¬ ∀ n x s t, chargerProtocol.Reachable n (x, s) →
      0 < (chargerProtocol.stage n x s).p t →
      charger.draw n x s t ≤ charger.supply n x s t := by
  intro h
  have hs : chargerProtocol.Reachable 0 ((), 0) := by
    show 0 < (atReading 0).p ((), 0)
    norm_num [atReading]
  have ht : 0 < (chargerProtocol.stage 0 () 0).p 1 := by
    show 0 < (cycle 0).p 1
    simp [cycle]
  have := h 0 () 0 1 hs ht
  simp only [charger, cycleDraw, cycleSupply] at this
  norm_num at this

/-- Nor is the net draw uniformly positive: the return transition supplies more
than it draws. So the horizon bound does not apply, and the charger sits
strictly between the two replenishment hypotheses. -/
theorem charger_no_uniform_cost (c : ℝ) (hc : 0 < c) :
    ¬ ∀ n x s t, chargerProtocol.Reachable n (x, s) →
      0 < (chargerProtocol.stage n x s).p t →
      c ≤ charger.draw n x s t - charger.supply n x s t := by
  intro h
  have hs : chargerProtocol.Reachable 1 ((), 1) := by
    show 0 < (chargerProtocol.law 1).p ((), 1)
    rw [show (1 : ℕ) = 2 * 0 + 1 by ring, (charger_law_even 0).2]
    norm_num [atReading]
  have ht : 0 < (chargerProtocol.stage 1 () 1).p 0 := by
    show 0 < (cycle 1).p 0
    simp [cycle]
  have := h 1 () 1 0 hs ht
  simp only [charger, cycleDraw, cycleSupply] at this
  norm_num at this
  linarith

/-- **The supply is load-bearing.** The same protocol and the same reading,
with the supply removed, is not a ledger: a reading that does not record what
arrives is not recording the store. -/
noncomputable def unsupplied : PathwiseStore Unit (Fin 3) :=
  ⟨chargerProtocol, reading, cycleDraw, fun _ _ _ _ => 0⟩

theorem unsupplied_not_ledgered : ¬ unsupplied.Ledgered := by
  intro h
  have hs : chargerProtocol.Reachable 1 ((), 1) := by
    show 0 < (chargerProtocol.law 1).p ((), 1)
    rw [show (1 : ℕ) = 2 * 0 + 1 by ring, (charger_law_even 0).2]
    norm_num [atReading]
  have ht : 0 < (chargerProtocol.stage 1 () 1).p 0 := by
    show 0 < (cycle 1).p 0
    simp [cycle]
  have := h 1 () 1 0 hs ht
  simp only [unsupplied, cycleDraw, reading] at this
  norm_num at this

end Store

end PhysicsOfConsciousness.Examples
