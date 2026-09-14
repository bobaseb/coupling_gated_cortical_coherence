import PhysicsOfConsciousness.Phase3_ContinuingAgent

/-!
# A register's microscopic bath and the limits of a map-indexed heat budget

One register bit and one bath bit. The register's levels are degenerate and the
bath's gap is `2 log 2`, at thermal scale one. Each of the four deterministic
maps of the register is realized by a *permutation* of the pair acting on a bath
prepared `false`: the two injective maps move the register alone, and the two
erasures swap the register's bit into the bath. Heat is the bath's actual mean
energy gain along the executed paths, so it is computed from the dynamics rather
than assigned to the map.

What comes out is `log 2` for an erasure, `0` for an injective map, and three
obstructions to reading a heat budget off the register's map. The same gate
executed twice returns the energy and restores the register, so an eraser is not
reusable without re-preparing its bath. A drive that leaves the register alone
excites the bath, so the map does not determine the cost. And the gate's own
transition log-ratios vanish on every realized path while the bath gains
`log 2`, so `RegisterLedger`'s positivity and local-detailed-balance premises do
not follow from microscopic reversibility: they are additional physical inputs,
which is what that model says they are.

The `StatisticalMechanics Bool` instance built here is kept local to this file.
It is sharper than `Examples/Bit.lean`'s — an injective map of this register
dissipates nothing — and that file's witness and its consumers are unchanged.

Regression specifications for the generic accounting, the reversible eraser and
the obstructions are collected at the end.
-/

namespace PhysicsOfConsciousness.Examples

namespace RegisterBath

/-! ## 1. One reversible gate for each deterministic map of the register -/

/-- Each map of a bit, realized by a permutation of register and bath: an
injective map acts on the register alone, and a constant map swaps the
register's bit into the bath, writing the map's value in its place. -/
def lift (t : Bool → Bool) (z : Bool × Bool) : Bool × Bool :=
  if t false = t true then (xor (t false) z.2, z.1) else (t z.1, z.2)

/-- The microscopic dynamics is reversible for every one of the four maps,
including the two that are not injective on the register alone. -/
theorem lift_injective (t : Bool → Bool) : Function.Injective (lift t) := by
  revert t
  decide

/-- On a bath prepared `false` the gate performs the requested map. -/
theorem lift_realizes (t : Bool → Bool) (s : Bool) : (lift t (s, false)).1 = t s := by
  revert t s
  decide

/-- An injective map leaves the bath where it found it. -/
theorem lift_of_injective {t : Bool → Bool} (h : t false ≠ t true) (z : Bool × Bool) :
    lift t z = (t z.1, z.2) := ite_eq_right h

/-- An erasure moves the register's bit into the bath. -/
theorem lift_of_const {t : Bool → Bool} (h : t false = t true) (z : Bool × Bool) :
    lift t z = (xor (t false) z.2, z.1) := ite_eq_left h

/-- The eraser to `false` is the swap of register and bath, hence an
involution: the gate is its own inverse. -/
theorem lift_erase (z : Bool × Bool) : lift (fun _ => false) z = (z.2, z.1) := by
  simp [lift]

/-! ## 2. The prepared law, the bath's energy and the executed protocol -/

/-- The prepared state: the register's bit is uniform and the bath is pure.
Preparing this state is supplied here, not derived. -/
noncomputable def prepared : ProbDist (Unit × (Bool × Bool)) where
  p z := if z.2.2 then 0 else 1 / 2
  nonneg z := by rcases z with ⟨_, _, b⟩; cases b <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The gate as a deterministic channel. The parameter coordinate is trivial:
this model holds nothing unknown fixed. -/
def gate (t : Bool → Bool) (_u : Unit) (z : Bool × Bool) : ProbDist (Bool × Bool) :=
  ProbDist.dirac (lift t z)

/-- The gate executed on the prepared law, and again on whatever it produced. -/
noncomputable def protocol (t : Bool → Bool) : FiniteProtocol Unit (Bool × Bool) where
  initial := prepared
  stage := fun _ => gate t

/-- The bath's energy: its excited state costs `2 log 2`, so a uniform bath
holds `log 2`. The gap is a model input, and with it the numerical value of
every heat below. -/
noncomputable def bathEnergy (z : Unit × (Bool × Bool)) : ℝ :=
  if z.2.2 then 2 * Real.log 2 else 0

/-- The register's own levels are degenerate: the joint energy is the bath's,
so no register map changes the system's energy by itself and every bath gain is
supplied from outside. -/
theorem bathEnergy_register_degenerate (r r' b : Bool) :
    bathEnergy ((), (r, b)) = bathEnergy ((), (r', b)) := rfl

/-- Expectations against a deterministic gate are sums over the actual paths:
one term for each state the law charges, at the state the gate sends it to. -/
theorem meanHeat_gate (t : Bool → Bool) (n : ℕ)
    (q : Unit → Bool × Bool → Bool × Bool → ℝ) :
    ((protocol t).step n).meanHeat q =
      ∑ s, ((protocol t).law n).p ((), s) * q () s (lift t s) := by
  rw [(protocol t).meanHeat_apply]
  have hinner : ∀ s : Bool × Bool,
      (∑ s' : Bool × Bool, ((protocol t).law n).p ((), s) *
        ((protocol t).stage n () s).p s' * q () s s') =
      ((protocol t).law n).p ((), s) * q () s (lift t s) := by
    intro s
    rw [Finset.sum_eq_single_of_mem (lift t s) (Finset.mem_univ _)]
    · simp [protocol, gate]
    · intro b _ hb
      simp [protocol, gate, hb]
  simp only [Finset.univ_unique, Finset.sum_singleton, hinner]

/-! ## 3. The heat of each map, from the paths it actually runs -/

/-- The heat of one execution: the bath's actual mean energy gain when the gate
runs once on the prepared law. -/
noncomputable def operationHeat (t : Bool → Bool) : ℝ :=
  ((protocol t).step 0).meanHeat ((protocol t).energyTransfer bathEnergy)

/-- **The map-indexed heat of this register.** An injective map dissipates
nothing and an erasure dissipates `log 2`, on the same gate, the same prepared
bath and the same energy gap. -/
theorem operationHeat_formula (t : Bool → Bool) :
    operationHeat t = if t false = t true then Real.log 2 else 0 := by
  rw [operationHeat, meanHeat_gate]
  by_cases hc : t false = t true
  · rw [ite_eq_left hc]
    simp only [lift_of_const hc, FiniteProtocol.energyTransfer, prepared, bathEnergy,
      FiniteProtocol.law_zero, protocol, Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
    ring
  · rw [ite_eq_right hc]
    simp only [lift_of_injective hc, FiniteProtocol.energyTransfer, prepared, bathEnergy,
      FiniteProtocol.law_zero, protocol, Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num

theorem idle_heat : operationHeat id = 0 := by
  rw [operationHeat_formula]
  norm_num

theorem negate_heat : operationHeat not = 0 := by
  rw [operationHeat_formula]
  norm_num

theorem erase_heat : operationHeat (fun _ => false) = Real.log 2 := by
  rw [operationHeat_formula]
  norm_num

theorem set_heat : operationHeat (fun _ => true) = Real.log 2 := by
  rw [operationHeat_formula]
  norm_num

/-- The heat of an erasure is strictly positive at a positive energy gap: the
bath's preparation, not the register's map, is what makes it so. -/
theorem erase_heat_pos : 0 < operationHeat (fun _ => false) := by
  rw [erase_heat]
  exact Real.log_pos (by norm_num)

/-! ## 4. The same gate twice: an eraser is not reusable -/

/-- After one execution the register is `false` and its bath carries the bit
that was there: this is the erasure. -/
theorem erase_law_one (z : Unit × (Bool × Bool)) :
    ((protocol (fun _ => false)).law 1).p z = if z.2.1 then 0 else 1 / 2 := by
  rw [(protocol (fun _ => false)).law_succ_apply 0]
  rcases z with ⟨u, r, b⟩
  simp only [FiniteProtocol.law_zero, protocol, gate, ProbDist.dirac_apply, lift_erase,
    prepared, Fintype.sum_prod_type, Fintype.sum_bool]
  cases r <;> cases b <;> norm_num

/-- **The bath is no longer prepared, so the second execution un-erases.** The
same gate run twice returns the register's bit from the bath and restores the
law it started from. -/
theorem erase_law_two : (protocol (fun _ => false)).law 2 = prepared := by
  apply ProbDist.ext
  funext z
  rw [(protocol (fun _ => false)).law_succ_apply 1]
  simp only [erase_law_one]
  rcases z with ⟨u, r, b⟩
  simp only [protocol, gate, ProbDist.dirac_apply, lift_erase, prepared,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases r <;> cases b <;> norm_num

/-- The register is uniform again after the second execution: two executions of
this eraser have erased nothing. -/
theorem erase_not_erased :
    ((protocol (fun _ => false)).law 2).p ((), (true, false)) = 1 / 2 := by
  rw [erase_law_two]
  norm_num [prepared]

/-- The first execution delivers `log 2` to the bath. -/
theorem erase_first_heat :
    ((protocol (fun _ => false)).step 0).meanHeat
      ((protocol (fun _ => false)).energyTransfer bathEnergy) = Real.log 2 :=
  erase_heat

/-- The second execution takes the same energy back out of the bath. -/
theorem reused_bath_heat :
    ((protocol (fun _ => false)).step 1).meanHeat
      ((protocol (fun _ => false)).energyTransfer bathEnergy) = -Real.log 2 := by
  rw [meanHeat_gate]
  simp only [erase_law_one, FiniteProtocol.energyTransfer, bathEnergy, lift_erase,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring

/-- **The two executions' shares sum to nothing**, and this is the generic bath
ledger of `FiniteProtocol.sum_energyTransfer` rather than a separate
calculation: the bath ends where it started. -/
theorem two_stage_heat :
    (∑ k ∈ Finset.range 2, ((protocol (fun _ => false)).step k).meanHeat
      ((protocol (fun _ => false)).energyTransfer bathEnergy)) = 0 := by
  rw [(protocol (fun _ => false)).sum_energyTransfer bathEnergy 2, erase_law_two]
  show (∑ z, prepared.p z * bathEnergy z) - ∑ z, prepared.p z * bathEnergy z = 0
  exact sub_self _

/-- The first share exceeds the total and the second is negative: a share of a
finite bath's ledger is neither bounded by that ledger nor nonnegative. -/
theorem shares_exceed_total :
    (∑ k ∈ Finset.range 2, ((protocol (fun _ => false)).step k).meanHeat
        ((protocol (fun _ => false)).energyTransfer bathEnergy)) <
      ((protocol (fun _ => false)).step 0).meanHeat
        ((protocol (fun _ => false)).energyTransfer bathEnergy) ∧
    ((protocol (fun _ => false)).step 1).meanHeat
        ((protocol (fun _ => false)).energyTransfer bathEnergy) < 0 := by
  rw [two_stage_heat, erase_first_heat, reused_bath_heat]
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact ⟨h, by linarith⟩

/-! ## 5. The work that pays for it -/

/-- The external work supplied to a run, when the modelled bath is the only
reservoir: the register's levels are degenerate, so it is the bath's whole
energy gain. A protocol with no work supply is not one of these. -/
noncomputable def suppliedWork (P : FiniteProtocol Unit (Bool × Bool)) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (P.step k).meanHeat (protocolWork bathEnergy (fun _ _ _ _ => 0) k)

theorem suppliedWork_eq (P : FiniteProtocol Unit (Bool × Bool)) (N : ℕ) :
    suppliedWork P N =
      (∑ z, (P.law N).p z * bathEnergy z) - ∑ z, P.initial.p z * bathEnergy z := by
  have h := P.sum_first_law bathEnergy (fun _ _ _ _ => 0) N
  simpa [suppliedWork, FiniteFeedbackStep.meanHeat] using h

/-- Erasing the register costs `log 2` of work, and delivers it to the bath as
heat. Nothing here is free: the gate is reversible, and the cost is the
preparation's. -/
theorem erase_work : suppliedWork (protocol (fun _ => false)) 1 = Real.log 2 := by
  rw [suppliedWork_eq]
  simp only [erase_law_one]
  simp only [protocol, prepared, bathEnergy, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring

/-- **Two executions cost nothing in total and erase nothing.** A reusable
eraser would need its bath prepared again, which this protocol never does. -/
theorem reuse_work : suppliedWork (protocol (fun _ => false)) 2 = 0 := by
  rw [suppliedWork_eq, erase_law_two]
  show (∑ z, prepared.p z * bathEnergy z) - ∑ z, prepared.p z * bathEnergy z = 0
  exact sub_self _

/-! ## 6. A register map does not determine the cost -/

/-- A reversible drive that leaves the register where it is and excites its
bath. On the prepared bath its logical update is the identity. -/
def driveGate (z : Bool × Bool) : Bool × Bool := (z.1, !z.2)

theorem driveGate_injective : Function.Injective driveGate := by decide

/-- The register is untouched, path by path. -/
theorem driveGate_register (z : Bool × Bool) : (driveGate z).1 = z.1 := rfl

/-- On the prepared bath the drive performs the identity map, exactly as the
idle gate does. -/
theorem driveGate_realizes (s : Bool) : (driveGate (s, false)).1 = id s := rfl

/-- The drive, executed on the same prepared law as the gates. -/
noncomputable def driven : FiniteProtocol Unit (Bool × Bool) where
  initial := prepared
  stage := fun _ _ z => ProbDist.dirac (driveGate z)

theorem meanHeat_driven (n : ℕ) (q : Unit → Bool × Bool → Bool × Bool → ℝ) :
    (driven.step n).meanHeat q =
      ∑ s, (driven.law n).p ((), s) * q () s (driveGate s) := by
  rw [driven.meanHeat_apply]
  have hinner : ∀ s : Bool × Bool,
      (∑ s' : Bool × Bool, (driven.law n).p ((), s) *
        (driven.stage n () s).p s' * q () s s') =
      (driven.law n).p ((), s) * q () s (driveGate s) := by
    intro s
    rw [Finset.sum_eq_single_of_mem (driveGate s) (Finset.mem_univ _)]
    · simp [driven]
    · intro b _ hb
      simp [driven, hb]
  simp only [Finset.univ_unique, Finset.sum_singleton, hinner]

/-- The drive's heat, on its own actual paths. -/
noncomputable def drivenIdleHeat : ℝ :=
  (driven.step 0).meanHeat (driven.energyTransfer bathEnergy)

theorem drivenIdleHeat_eq : drivenIdleHeat = 2 * Real.log 2 := by
  rw [drivenIdleHeat, meanHeat_driven]
  simp only [FiniteProtocol.energyTransfer, FiniteProtocol.law_zero, driven, prepared,
    bathEnergy, driveGate, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring

/-- **The register's map does not identify a protocol's cost.** This drive and
the idle gate perform the same update of the register on the same prepared bath,
and deliver different heat. -/
theorem same_update_different_heat : operationHeat id ≠ drivenIdleHeat := by
  rw [idle_heat, drivenIdleHeat_eq]
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro hcontra
  linarith

/-- The drive is not free either: its bath gain is supplied as work. -/
theorem driven_work : suppliedWork driven 1 = 2 * Real.log 2 := by
  rw [suppliedWork, Finset.sum_range_one, meanHeat_driven]
  simp only [protocolWork, FiniteProtocol.law_zero, driven, prepared, bathEnergy,
    driveGate, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring

theorem driven_work_pos : 0 < suppliedWork driven 1 := by
  rw [driven_work]
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ## 7. What reversibility does not supply -/

/-- Every gate sends one state to one state, so its channel charges nothing to
any other: a deterministic reduced channel is not strictly positive, whatever
law it is started from. -/
theorem gate_channel_zero (t : Bool → Bool) :
    ((protocol t).stage 0 () (false, false)).p (false, true) = 0 := by
  have h : (false, true) ≠ lift t (false, false) := by
    intro hc
    have hsnd := congrArg Prod.snd hc
    revert hsnd
    by_cases hcc : t false = t true
    · simp [lift_of_const hcc]
    · simp [lift_of_injective hcc]
  simp [protocol, gate, h]

/-- A deterministic gate's reduced step is not strictly positive: the forward
and reverse path-likelihood conditions `RegisterLedger` assumes are not
consequences of microscopic reversibility. The channel fails them by
`gate_channel_zero`, and the pure bath the gate is prepared with fails them
again. -/
theorem gate_not_positive (t : Bool → Bool) : ¬ ((protocol t).step 0).Positive := by
  intro h
  have h1 := h.2 () (false, false) (false, true)
  rw [FiniteProtocol.step_transition, gate_channel_zero] at h1
  exact absurd h1 (lt_irrefl 0)

/-- The swap gate's transition log-ratio vanishes on *every* path: a realized
path has equal forward and reverse masses because the gate is an involution, and
an unrealized one has none. -/
theorem erase_stageHeat_zero (θ : ℝ) (u : Unit) (s s' : Bool × Bool) :
    (protocol (fun _ => false)).stageHeat θ 0 u s s' = 0 := by
  rcases s with ⟨r, b⟩
  rcases s' with ⟨r', b'⟩
  by_cases h : (r', b') = (b, r)
  · simp [protocol, FiniteProtocol.stageHeat, gate, lift_erase, h]
  · have h' : (r, b) ≠ (b', r') := by
      intro hrb
      exact h (by simp_all [Prod.ext_iff])
    simp [protocol, FiniteProtocol.stageHeat, gate, lift_erase, h, h']

private theorem erase_stageHeat_meanHeat (θ : ℝ) :
    ((protocol (fun _ => false)).step 0).meanHeat
      ((protocol (fun _ => false)).stageHeat θ 0) = 0 := by
  rw [FiniteFeedbackStep.meanHeat]
  exact Finset.sum_eq_zero fun z _ => by rw [erase_stageHeat_zero, mul_zero]

/-- **Local detailed balance does not identify this bath's heat.** The declared
log-ratio heat of the reversible eraser is zero at every thermal scale, while
the bath it actually drives gains `log 2`. -/
theorem erase_stageHeat_not_bath_heat (θ : ℝ) :
    ((protocol (fun _ => false)).step 0).meanHeat
        ((protocol (fun _ => false)).stageHeat θ 0) ≠
      ((protocol (fun _ => false)).step 0).meanHeat
        ((protocol (fun _ => false)).energyTransfer bathEnergy) := by
  rw [erase_stageHeat_meanHeat, erase_first_heat]
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro hcontra
  linarith

/-- The generic correction of `FiniteProtocol.reported_heat_eq`, on this
protocol: a ledger that reports the gate's log-ratio heat leaves the bath's
whole energy gain uncounted. -/
theorem erase_reported_correction (θ : ℝ) :
    ((protocol (fun _ => false)).step 0).meanHeat
      (fun u s t => (protocol (fun _ => false)).stageHeat θ 0 u s t -
        (protocol (fun _ => false)).energyTransfer bathEnergy u s t) = -Real.log 2 := by
  have hsplit : ((protocol (fun _ => false)).step 0).meanHeat
      (fun u s t => (protocol (fun _ => false)).stageHeat θ 0 u s t -
        (protocol (fun _ => false)).energyTransfer bathEnergy u s t) =
      ((protocol (fun _ => false)).step 0).meanHeat
          ((protocol (fun _ => false)).stageHeat θ 0) -
        ((protocol (fun _ => false)).step 0).meanHeat
          ((protocol (fun _ => false)).energyTransfer bathEnergy) := by
    simp only [FiniteFeedbackStep.meanHeat, mul_sub, Finset.sum_sub_distrib]
  rw [hsplit, erase_stageHeat_meanHeat, erase_first_heat, zero_sub]

/-! ## 8. The register's own sharper instance, local to this file -/

/-- Temperature one, and the heat of a map is the one its gate actually delivers
to the bath: `0` for the injective maps, `log 2` for the erasures. -/
noncomputable local instance bathThermo : Thermodynamics Bool where
  heat_dissipation := operationHeat
  temperature := 1
  temperature_pos := by norm_num

/-- The bath starts pure and ends on the states the gate can actually reach: the
whole bath for an erasure, the prepared state alone for an injective map. -/
local instance bathEnv : BipartiteEnvironment Bool where
  bath := Bool
  dec_bath := inferInstance
  U := lift
  U_inj := lift_injective
  initial_bath := fun _ => {false}
  final_bath := fun t => if t false = t true then Finset.univ else {false}
  h_evolve := by
    intro t p hp
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ,
      Finset.mem_singleton, true_and] at hp
    obtain ⟨⟨a, b⟩, hq, rfl⟩ := hp
    have hb : b = false := hq
    subst hb
    refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩, ?_⟩
    · exact (lift_realizes t a).symm
    · by_cases hc : t false = t true
      · simp [hc]
      · simp [hc, lift_of_injective hc]
  h_bath_nonempty := fun _ => ⟨false, Finset.mem_singleton_self _⟩

/-- Landauer's heat equation is discharged by computation here: both sides are
read off the same reversible gate and the same prepared bath. -/
noncomputable local instance bathStatMech : StatisticalMechanics Bool where
  heat_eq := by
    intro t
    show operationHeat t = 1 * (boltzmann_entropy
      (if t false = t true then (Finset.univ : Finset Bool) else {false}) -
        boltzmann_entropy ({false} : Finset Bool))
    rw [operationHeat_formula]
    by_cases hc : t false = t true
    · simp [hc, boltzmann_entropy]
    · simp [hc, boltzmann_entropy]

/-- The sharpening: the identity map of this register dissipates nothing.
`Examples/Bit.lean`'s bath charges `log 2` for every map, including this one;
that instance and its consumers are untouched, because this one is local. -/
theorem idle_dissipation : heat_dissipation (id : Bool → Bool) = 0 := idle_heat

theorem erase_dissipation : heat_dissipation (fun _ : Bool => false) = Real.log 2 := erase_heat

/-- The general Landauer bound, on this instance: erasing the register's bit
dissipates at least the register's own entropy drop. -/
theorem erase_landauer :
    heat_dissipation (fun _ : Bool => false) ≥
      Thermodynamics.temperature (sys := Bool) *
        (entropy (id : Bool → Bool) - entropy (fun _ : Bool => false)) :=
  landauer_bound _

/-! The instance's own regressions stay inside this namespace: the instance is
local to it, so a specification outside cannot see the register's temperature. -/

example : heat_dissipation (id : Bool → Bool) = 0 := idle_dissipation

example : heat_dissipation (fun _ : Bool => false) = Real.log 2 := erase_dissipation

example : heat_dissipation (fun _ : Bool => false) ≥
    Thermodynamics.temperature (sys := Bool) *
      (entropy (id : Bool → Bool) - entropy (fun _ : Bool => false)) :=
  erase_landauer

end RegisterBath

/-! ## Regression specifications -/

section GenericRegression

variable {X S : Type*} [Fintype X] [Fintype S] (P : FiniteProtocol X S)

example (E : X × S → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (P.step k).meanHeat (P.energyTransfer E)) =
      (∑ z, (P.law N).p z * E z) - (∑ z, P.initial.p z * E z) :=
  P.sum_energyTransfer E N

example (E : X × S → ℝ) (q : ℕ → X → S → S → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (P.step k).meanHeat (q k)) =
      (∑ z, (P.law N).p z * E z) - (∑ z, P.initial.p z * E z) +
        ∑ k ∈ Finset.range N,
          (P.step k).meanHeat (fun x s t => q k x s t - P.energyTransfer E x s t) :=
  P.reported_heat_eq E q N

end GenericRegression

namespace RegisterBath

example (t : Bool → Bool) : Function.Injective (lift t) := lift_injective t

example (t : Bool → Bool) (s : Bool) : (lift t (s, false)).1 = t s :=
  lift_realizes t s

example : operationHeat id = 0 := idle_heat

example : operationHeat (fun _ => false) = Real.log 2 := erase_heat

example :
    ((protocol (fun _ => false)).step 1).meanHeat
      ((protocol (fun _ => false)).energyTransfer bathEnergy) = -Real.log 2 :=
  reused_bath_heat

example :
    (∑ k ∈ Finset.range 2, ((protocol (fun _ => false)).step k).meanHeat
      ((protocol (fun _ => false)).energyTransfer bathEnergy)) = 0 :=
  two_stage_heat

example : operationHeat id ≠ drivenIdleHeat := same_update_different_heat

example : operationHeat not = 0 := negate_heat

example : operationHeat (fun _ => true) = Real.log 2 := set_heat

example : (protocol (fun _ => false)).law 2 = prepared := erase_law_two

example : suppliedWork (protocol (fun _ => false)) 1 = Real.log 2 := erase_work

example : suppliedWork (protocol (fun _ => false)) 2 = 0 := reuse_work

example : 0 < suppliedWork driven 1 := driven_work_pos

example (t : Bool → Bool) : ¬ ((protocol t).step 0).Positive := gate_not_positive t

example (t : Bool → Bool) :
    ((protocol t).stage 0 () (false, false)).p (false, true) = 0 := gate_channel_zero t

example (θ : ℝ) :
    ((protocol (fun _ => false)).step 0).meanHeat
        ((protocol (fun _ => false)).stageHeat θ 0) ≠
      ((protocol (fun _ => false)).step 0).meanHeat
        ((protocol (fun _ => false)).energyTransfer bathEnergy) :=
  erase_stageHeat_not_bath_heat θ

example (θ : ℝ) :
    ((protocol (fun _ => false)).step 0).meanHeat
      (fun u s t => (protocol (fun _ => false)).stageHeat θ 0 u s t -
        (protocol (fun _ => false)).energyTransfer bathEnergy u s t) = -Real.log 2 :=
  erase_reported_correction θ

end RegisterBath

#print axioms FiniteProtocol.sum_energyTransfer
#print axioms FiniteProtocol.reported_heat_eq
#print axioms RegisterBath.operationHeat_formula
#print axioms RegisterBath.erase_law_two
#print axioms RegisterBath.same_update_different_heat
#print axioms RegisterBath.erase_stageHeat_not_bath_heat

end PhysicsOfConsciousness.Examples
