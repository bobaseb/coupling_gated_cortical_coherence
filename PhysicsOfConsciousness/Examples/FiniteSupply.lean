import PhysicsOfConsciousness.Examples.PathwiseStore

/-!
# A finite source behind replenishment

A source, buffer and output load have bit energies zero and one. A fourth bit
selects whether to swap source and buffer; the buffer is then swapped with the
load. Both gates are energy-conserving involutions. The initial selector is
uniform, the source is charged, and the buffer and load are empty. Half the
paths deliver a unit and half deliver nothing, despite the available energy.

This is one attempted transfer followed by idling, with its uncertainty in the
initial selector. It is not a model of recurrent random arrivals, preparation,
gate-control costs, sensor memory or the learning agent's particular hardware.
Work drawn is energy deposited in this ideal load, not heat. Regression
specifications follow the constructions.
-/

namespace PhysicsOfConsciousness

namespace Examples.FiniteSupply

/-! ## The resource coordinates and reversible gates -/

/-- Buffer, source, load and selector, respectively. -/
abbrev State := Bool × (Bool × (Bool × Bool))

def seed (charged selector : Bool) : State := (false, charged, false, selector)

noncomputable def bitEnergy (b : Bool) : ℝ := if b then 1 else 0

theorem bitEnergy_nonneg (b : Bool) : 0 ≤ bitEnergy b := by
  cases b <;> norm_num [bitEnergy]

noncomputable def buffer (s : State) : ℝ := bitEnergy s.1
noncomputable def reserve (s : State) : ℝ := bitEnergy s.2.1
noncomputable def output (s : State) : ℝ := bitEnergy s.2.2.1
noncomputable def totalEnergy (s : State) : ℝ := buffer s + reserve s + output s

/-- The selector controls a swap of source and buffer. Its two values are
energetically degenerate, and preparing or switching the gate is outside this
ideal finite energy model. -/
def charge (s : State) : State :=
  if s.2.2.2 then (s.2.1, s.1, s.2.2.1, s.2.2.2) else s

/-- Move the buffer's energy into the load when the load starts empty. On an
arbitrary state this swap can return energy, so it is a reversible gate. -/
def deliver (s : State) : State := (s.2.2.1, s.2.1, s.1, s.2.2.2)

theorem charge_involutive : Function.Involutive charge := by
  rintro ⟨b, r, l, c⟩
  cases c <;> rfl

theorem deliver_involutive : Function.Involutive deliver := fun _ => rfl

/-- Each gate conserves the energy of the complete finite system. No entropy
inequality or claim about the physical cost of gate control follows. -/
theorem charge_conserves (s : State) : totalEnergy (charge s) = totalEnergy s := by
  rcases s with ⟨b, r, l, c⟩
  cases c <;> simp [charge, totalEnergy, buffer, reserve, output, add_comm]

theorem deliver_conserves (s : State) : totalEnergy (deliver s) = totalEnergy s := by
  simp only [deliver, totalEnergy, buffer, reserve, output]
  ring

/-! ## One evolving law: the selector is sampled only at preparation -/

/-- The pushforward of a uniform selector, retaining all four coordinates.
Coincident images are allowed; their masses add. -/
noncomputable def coinLaw (f : Bool → State) : ProbDist (Unit × State) where
  p z := (if z.2 = f false then 1 / 2 else 0) +
    (if z.2 = f true then 1 / 2 else 0)
  nonneg z := by positivity
  sum_one := by
    simp [Fintype.sum_prod_type, Finset.sum_add_distrib]
    norm_num

theorem expect_coinLaw (f : Bool → State) (E : State → ℝ) :
    ∑ z, (coinLaw f).p z * E z.2 = (1 / 2) * E (f false) + (1 / 2) * E (f true) := by
  simp [coinLaw, Fintype.sum_prod_type, add_mul, ite_mul, Finset.sum_add_distrib]

def gate : ℕ → State → State
  | 0 => charge
  | 1 => deliver
  | _ + 2 => id

theorem gate_conserves (n : ℕ) (s : State) : totalEnergy (gate n s) = totalEnergy s := by
  cases n with
  | zero => exact charge_conserves s
  | succ n =>
    cases n with
    | zero => exact deliver_conserves s
    | succ n => rfl

noncomputable def protocol (charged : Bool) : FiniteProtocol Unit State :=
  ⟨coinLaw (seed charged), fun n _ s => ProbDist.dirac (gate n s)⟩

def stateAt (charged : Bool) : ℕ → Bool → State
  | 0 => seed charged
  | 1 => fun c => charge (seed charged c)
  | _ + 2 => fun c => deliver (charge (seed charged c))

theorem stateAt_succ (charged : Bool) (n : ℕ) (c : Bool) :
    gate n (stateAt charged n c) = stateAt charged (n + 1) c := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

/-- The actual law at every horizon is the two possible prepared selectors
carried through the executed gates. There is no resampling between stages. -/
theorem law_eq_coin (charged : Bool) (n : ℕ) :
    (protocol charged).law n = coinLaw (stateAt charged n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply ProbDist.ext
    funext z
    rw [(protocol charged).law_succ_apply, ih]
    simp only [coinLaw, protocol, ProbDist.dirac_apply, add_mul, ite_mul,
      zero_mul, Finset.sum_add_distrib]
    simp [stateAt_succ, mul_ite]

/-! ## Source loss, store solvency and work received by the load -/

/-- The supplied work is the source's energy loss and the drawn work is the
load's energy gain on the very same transition. Gate energy conservation, not
an assigned cost per operation, discharges the buffer ledger. -/
noncomputable def store (charged : Bool) : PathwiseStore Unit State :=
  ⟨protocol charged, buffer, fun _ _ s t => output t - output s,
    fun _ _ s t => reserve s - reserve t⟩

theorem source_ledgered (charged : Bool) : (store charged).SourceLedgered reserve := by
  intro n x s t _ _
  change reserve t = reserve s - (reserve s - reserve t)
  ring

/-- The buffer's pathwise ledger follows from the gates' conserved total
energy. This ideal output load is the only recipient of drawn work. -/
theorem store_ledgered (charged : Bool) : (store charged).Ledgered := by
  intro n x s t _ ht
  have heq : t = gate n s := by
    by_contra h
    simp [store, protocol, ProbDist.dirac_apply, h] at ht
  subst t
  have h := gate_conserves n s
  unfold totalEnergy at h
  change buffer (gate n s) = buffer s - (output (gate n s) - output s) +
    (reserve s - reserve (gate n s))
  linarith

theorem store_solvent (charged : Bool) (N : ℕ) : (store charged).Solvent N := by
  intro k hk z hz
  exact bitEnergy_nonneg z.2.1

/-- Cumulative work drawn is exactly the energy gained by the physical load.
Its value is obtained from the evolving law, not from a requested workload. -/
theorem draw_eq_output_gain (charged : Bool) (N : ℕ) :
    (store charged).totalDraw N =
      (∑ z, ((protocol charged).law N).p z * output z.2) -
        ∑ z, ((protocol charged).law 0).p z * output z.2 :=
  (protocol charged).sum_energyTransfer (fun z => output z.2) N

theorem draw_two : (store true).totalDraw 2 = 1 / 2 := by
  rw [draw_eq_output_gain, law_eq_coin, law_eq_coin, expect_coinLaw, expect_coinLaw]
  norm_num [stateAt, seed, charge, deliver, output, bitEnergy]

/-- Half the paths leave the source charged and the load empty. Initial
capacity does not guarantee that a finite supply delivers on demand. -/
theorem undelivered_mass : ((protocol true).law 2).p ((), seed true false) = 1 / 2 := by
  rw [law_eq_coin]
  norm_num [coinLaw, stateAt, seed, charge, deliver]

theorem delivered_mass :
    ((protocol true).law 2).p ((), (false, false, true, true)) = 1 / 2 := by
  rw [law_eq_coin]
  norm_num [coinLaw, stateAt, seed, charge, deliver]

theorem supply_one : (store true).totalSupply 1 = 1 / 2 := by
  rw [(store true).totalSupply_eq_source_loss reserve (source_ledgered true)]
  change (∑ z, ((protocol true).law 0).p z * reserve z.2) -
    (∑ z, ((protocol true).law 1).p z * reserve z.2) = 1 / 2
  rw [law_eq_coin, law_eq_coin, expect_coinLaw, expect_coinLaw]
  norm_num [stateAt, seed, charge, reserve, bitEnergy]

/-- Closing the resource boundary gives a finite draw bound at every horizon.
Solvency at later horizons is just idling after one attempted delivery. -/
theorem draw_le_capacity (N : ℕ) : (store true).totalDraw N ≤ 1 := by
  have h := (store true).totalDraw_le_initial_resources reserve (store_ledgered true)
    (source_ledgered true) N (store_solvent true N)
    (fun _ _ z _ => bitEnergy_nonneg z.2.2.1)
  have h0 : (store true).meanBalance 0 = 0 := by
    change (∑ z, ((protocol true).law 0).p z * buffer z.2) = 0
    rw [law_eq_coin, expect_coinLaw]
    norm_num [stateAt, seed, buffer, bitEnergy]
  rw [h0, zero_add] at h
  change (store true).totalDraw N ≤ ∑ z, ((protocol true).law 0).p z * reserve z.2 at h
  rw [law_eq_coin, expect_coinLaw] at h
  norm_num [stateAt, seed, reserve, bitEnergy] at h
  exact h

/-! ## Negative controls -/

/-- The attempted ledger claims a unit of work at the delivery stage even
on a path whose selector has left the buffer empty. -/
noncomputable def forced : PathwiseStore Unit State :=
  { store true with draw := fun n _ _ _ => if n = 1 then 1 else 0 }

theorem forced_not_ledgered : ¬ forced.Ledgered := by
  intro h
  have hs : (protocol true).Reachable 1 ((), seed true false) := by
    show 0 < ((protocol true).law 1).p ((), seed true false)
    rw [law_eq_coin]
    norm_num [coinLaw, stateAt, seed, charge]
  have ht : 0 < ((protocol true).stage 1 () (seed true false)).p (seed true false) := by
    norm_num [protocol, gate, deliver, seed, ProbDist.dirac_apply]
  have hf := h 1 () (seed true false) (seed true false) hs ht
  norm_num [forced, store, buffer, reserve, seed, bitEnergy] at hf

/-- With no energy in the prepared source, these same gates deliver nothing.
Preparing that energy is an input; reversibility alone does not supply it. -/
theorem empty_source_draw : (store false).totalDraw 2 = 0 := by
  rw [draw_eq_output_gain, law_eq_coin, law_eq_coin, expect_coinLaw, expect_coinLaw]
  norm_num [stateAt, seed, charge, deliver, output, bitEnergy]

/-- The unbounded charger cannot obtain its supply from any nonnegative finite
source coordinate on its state. Its external replenishment is load-bearing;
the finite-source theorem cannot be invoked for it with a fictitious reserve. -/
theorem charger_no_finite_source (R : Fin 3 → ℝ) (hR : ∀ s, 0 ≤ R s) :
    ¬ Store.charger.SourceLedgered R := by
  intro hr
  obtain ⟨N, hs, hgt⟩ := Store.charger_draw_unbounded
    (Store.charger.meanBalance 0 + ∑ z, (Store.charger.protocol.law 0).p z * R z.2)
  have hle := Store.charger.totalDraw_le_initial_resources R Store.charger_ledgered
    hr N hs (fun _ _ z _ => hR z.2)
  exact (not_lt_of_ge hle) hgt

/-! ## A positive-cost finite run, followed by idling -/

/-- A direct transfer between a source and a complementary ideal load. The
state bit is the source excitation and the load energy is `1 - bitEnergy s`.
The first gate exchanges them; later stages idle. The intervening buffer holds
zero and passes the transferred energy directly to the load. This minimal
control exercises the positive-cost horizon premise over a finite run. -/
noncomputable def direct : PathwiseStore Unit Bool where
  protocol :=
    ⟨ProbDist.dirac ((), true), fun n _ s => ProbDist.dirac (if n = 0 then !s else s)⟩
  balance := fun _ => 0
  draw := fun _ _ s t => bitEnergy s - bitEnergy t
  supply := fun _ _ s t => bitEnergy s - bitEnergy t

theorem direct_ledgered : direct.Ledgered := by
  intro n x s t _ _
  change (0 : ℝ) = 0 - (bitEnergy s - bitEnergy t) + (bitEnergy s - bitEnergy t)
  ring

theorem direct_source_ledgered : direct.SourceLedgered bitEnergy := by
  intro n x s t _ _
  change bitEnergy t = bitEnergy s - (bitEnergy s - bitEnergy t)
  ring

theorem direct_law_one (x : Unit) (s : Bool) :
    (direct.protocol.law 1).p (x, s) = if s = false then 1 else 0 := by
  rw [direct.protocol.law_succ_apply]
  cases x
  cases s <;> norm_num [direct, FiniteProtocol.law_zero, ProbDist.dirac_apply,
    Fintype.sum_bool]

theorem direct_draw_one : direct.totalDraw 1 = 1 := by
  change ∑ k ∈ Finset.range 1, (direct.protocol.step k).meanHeat (direct.draw k) = 1
  rw [Finset.sum_range_one, direct.protocol.meanHeat_apply]
  norm_num [direct, FiniteProtocol.law_zero, ProbDist.dirac_apply,
    Fintype.sum_bool, bitEnergy]

/-- A unit-cost run saturates the finite-source horizon bound. The cost
hypothesis covers only its one executed stage; the protocol can idle later. -/
theorem direct_horizon : direct.totalDraw 1 ≤ 1 := by
  have bound : ((1 : ℕ) : ℝ) * 1 ≤ 1 := by
    apply direct.horizon_le_of_finite_source bitEnergy direct_ledgered
      direct_source_ledgered 1 1 ?_ 1 ?_ ?_ ?_
    · rintro ⟨x, s⟩ _
      cases s <;> norm_num [direct, bitEnergy]
    · intro n hn x s t hs ht
      have hn0 : n = 0 := Nat.lt_one_iff.1 hn
      subst n
      cases x
      cases s <;> cases t <;>
        simp_all [direct, FiniteProtocol.Reachable, FiniteProtocol.law_zero,
          ProbDist.dirac_apply, bitEnergy]
    · intro k hk z hz
      exact le_rfl
    · intro k hk z hz
      exact bitEnergy_nonneg z.2
  simpa only [Nat.cast_one, one_mul, direct_draw_one] using bound

/-- The same physical run fails the unbounded positive-cost premise: after
spending its unit it idles. A horizon theorem requiring that premise would
miss this elementary finite-source example. -/
theorem direct_not_uniform_cost :
    ¬ ∀ n x s t, direct.protocol.Reachable n (x, s) →
      0 < (direct.protocol.stage n x s).p t → 1 ≤ direct.draw n x s t := by
  intro h
  have hs : direct.protocol.Reachable 1 ((), false) := by
    show 0 < (direct.protocol.law 1).p ((), false)
    rw [direct_law_one]
    norm_num
  have ht : 0 < (direct.protocol.stage 1 () false).p false := by
    norm_num [direct, ProbDist.dirac_apply]
  have hf := h 1 () false false hs ht
  norm_num [direct] at hf

end Examples.FiniteSupply

section Specifications

variable {X S : Type*} [Fintype X] [Fintype S]

example (B : PathwiseStore X S) (R : S → ℝ)
    (hb : B.Ledgered) (hr : B.SourceLedgered R) : (B.withSource R).Ledgered :=
  B.withSource_ledgered R hb hr

example (B : PathwiseStore X S) (R : S → ℝ) (hr : B.SourceLedgered R) (N : ℕ) :
    B.totalSupply N = (∑ z, (B.protocol.law 0).p z * R z.2) -
      ∑ z, (B.protocol.law N).p z * R z.2 :=
  B.totalSupply_eq_source_loss R hr N

example (B : PathwiseStore X S) (R : S → ℝ)
    (hb : B.Ledgered) (hr : B.SourceLedgered R) (N : ℕ) (hs : B.Solvent N)
    (hR : ∀ k ≤ N, ∀ z, B.protocol.Reachable k z → 0 ≤ R z.2) :
    B.totalDraw N ≤ B.meanBalance 0 + ∑ z, (B.protocol.law 0).p z * R z.2 :=
  B.totalDraw_le_initial_resources R hb hr N hs hR

example (B : PathwiseStore X S) (R : S → ℝ)
    (hb : B.Ledgered) (hr : B.SourceLedgered R) (c b : ℝ)
    (h0 : ∀ z, B.protocol.Reachable 0 z → B.balance z.2 + R z.2 ≤ b)
    (N : ℕ)
    (hc : ∀ n < N, ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → c ≤ B.draw n x s t)
    (hs : B.Solvent N)
    (hR : ∀ k ≤ N, ∀ z, B.protocol.Reachable k z → 0 ≤ R z.2) :
    (N : ℝ) * c ≤ b :=
  B.horizon_le_of_finite_source R hb hr c b h0 N hc hs hR

example (B : PathwiseStore X S) (hb : B.Ledgered) (c b : ℝ)
    (h0 : ∀ z, B.protocol.Reachable 0 z → B.balance z.2 ≤ b) (N : ℕ)
    (hc : ∀ n < N, ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → c ≤ B.draw n x s t - B.supply n x s t)
    (hs : B.Solvent N) : (N : ℝ) * c ≤ b :=
  B.horizon_le_of_net_cost hb c b h0 N hc hs

end Specifications

namespace Examples.FiniteSupply

example : Function.Involutive charge ∧ Function.Involutive deliver :=
  ⟨charge_involutive, deliver_involutive⟩

example (s : State) : totalEnergy (charge s) = totalEnergy s ∧
    totalEnergy (deliver s) = totalEnergy s :=
  ⟨charge_conserves s, deliver_conserves s⟩

example : (store true).totalDraw 2 = 1 / 2 ∧
    ((protocol true).law 2).p ((), seed true false) = 1 / 2 :=
  ⟨draw_two, undelivered_mass⟩

example : ¬ forced.Ledgered := forced_not_ledgered

example : (store false).totalDraw 2 = 0 := empty_source_draw

example (R : Fin 3 → ℝ) (hR : ∀ s, 0 ≤ R s) :
    ¬ Store.charger.SourceLedgered R := charger_no_finite_source R hR

example : direct.totalDraw 1 = 1 := direct_draw_one

example : direct.totalDraw 1 ≤ 1 := direct_horizon

example : ¬ ∀ n x s t, direct.protocol.Reachable n (x, s) →
    0 < (direct.protocol.stage n x s).p t → 1 ≤ direct.draw n x s t :=
  direct_not_uniform_cost

end Examples.FiniteSupply

end PhysicsOfConsciousness
