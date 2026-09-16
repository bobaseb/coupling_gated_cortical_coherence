import PhysicsOfConsciousness.Phase3_LocalActuator
import PhysicsOfConsciousness.Phase3_ContinuingAgent
import PhysicsOfConsciousness.Phase9_EMIdentification

/-!
# Phase 9 — the installed coupling and the coherence threshold

`Phase3_LocalActuator.lean` installs a product-space kernel from declared mode
occupancies and converges its cell-pair energies to
`KernelArrangement.continuumEnergy`. `Phase8_ContinuousField.lean` states the
synchronization threshold `critical_coupling D = 2 * D` against
`mean_field_coupling`, the kernel averaged over both of its arguments. Until
this module those two limits were separate numbers, and the microscopic
branch's limit was never read as a coupling constant.

Three steps compose them.

1. `KernelArrangement.continuumEnergy_eq_mean_field_coupling` — the two
   integrals are one integral. This is Fubini on a compact substrate of finite
   mass with a continuous kernel, and it is what makes the arrangement's limit
   a coupling constant rather than a number beside one.
2. `PricedArrangement.continuumEnergy_le_installedEnergy` — the installed
   kernel factorizes over the response modes, so its continuum energy is
   `∑ᵢ cᵢ (∫ φᵢ)²` while the installation energy is `∑ᵢ uᵢ cᵢ`. A declared
   constant `κ` satisfying `(∫ φᵢ)² ≤ κ uᵢ` at every mode, together with
   nonnegative occupancies, bounds the first by `κ` times the second.
3. `PricedArrangement.no_coherence_of_installedEnergy` — an arrangement whose
   installed energy satisfies `κ U ≤ 2 D` does not exhibit the phase
   transition; the incoherent state is then the only nonnegative solution of
   the stationary self-consistency equation, and no Fourier mode of the uniform
   density grows.

`Examples/InstalledCoupling.lean` discharges all three on the thermal switch of
`Examples/MicroscopicCoupling.lean`, on both sides of the line.

## What the bound is about, and what it is not

**Installed energy is not dissipated heat.** `U` is `LocalActuator.storedEnergy`
averaged over the configuration law: the energy sitting in the installed modes,
not heat delivered to a reservoir. `Examples/RegisterBath.lean` is why the
distinction is forced rather than fastidious — a deterministic reversible gate
has vanishing transition log-ratios on every realized path, so local detailed
balance assigns it none of the heat its bath receives, and a reversible
energy transfer can occur at zero entropy production. No version of K3 licenses
reading `U` as a dissipation.

**`κ` is declared hardware data.** It is a field of `PricedArrangement`,
constrained only by the profiles and prices through `mode_priced`, in the same
way as `ActuatedCoupling`'s `gain` and `base`. Changing the prices or the
profiles at fixed process changes the bound. No heat bound supplies `κ`, and a
`κ` fitted below what the hardware permits is rejected by `mode_priced` —
`Examples/InstalledCoupling.lean`'s `fitted_couplingPerEnergy_rejected` shows
that on the witness every admissible `κ` puts the executed arrangement *above*
the threshold.

The type does not enforce when a number was chosen: independence from the noise
threshold is a modelling requirement. Positivity excludes negative conversion
factors and, together with `mode_priced`, forces nonnegative prices.

**One direction only.** The conclusion is a no-go: insufficient installed energy
forbids the coherent branch. `κ U > 2 D` bounds the coupling from the wrong
side and K2's inequality does not reverse, so nothing here says that sufficient
energy produces coherence. `converse_rejected` in the witness file exhibits an
arrangement above the line that does not exhibit the transition.

**`E56` is untouched.** That a physical field's kernel *is* the installed one
remains a physical commitment, stated in `Chain.E56` and discharged by nothing
here. These theorems constrain a declared arrangement; no object in them
denotes cortex.

## The fuel form of the same no-go

K3 bounds coherence by the energy *standing in* the installed modes. It says
nothing about where that energy came from, so an arrangement can satisfy it
with an installed energy nobody could have paid for. `PathwiseStore` is the
other half of that account: a store carried as a coordinate of the protocol's
own state, drawn down by each executed transition and replenished by a declared
source. Until `totalDraw_eq_installation` the two halves shared no theorem —
`PathwiseStore` appeared in no file that installs a kernel.

The bridge is an identification, not a construction: a store whose `draw` at
every stage *is* `LocalActuator.pathWork` has a cumulative draw that
`FiniteProtocol.sum_first_law` already telescopes into the installed-energy
change plus the run's heat. `installedEnergy_le_resources` then reads
`totalDraw_le_initial_resources` backwards — a solvent run funded by a finite
source cannot have installed more than that source held — and
`PricedArrangement.no_coherence_of_funded_source` feeds the result to K3. The
conclusion is a **fuel** no-go: a source too small does not reach the threshold
at any horizon.

Three things it does not say. The heat term enters only through
`0 ≤ meanHeat`, so the bound is loose by exactly the heat the run delivered and
is not an equality. `κ` is still declared hardware data, so this relocates the
same input K2 and R7 relocate rather than discharging it. And the direction is
unchanged: a *sufficient* source supplies no coherence, for the reason
`converse_rejected` gives.

## What a run-level no-go needs, and what it must not be weakened to

`no_coherence_of_run` is the stagewise corollary: an evolving arrangement whose
installed energy satisfies `κ Uₙ ≤ 2 D` at *every* stage exhibits the transition
at none of them. The hypothesis is a supremum over stages and cannot be softened
to a mean — `Examples/EvolvingCoupling.lean` exhibits a stage sequence whose mean
installed energy is subcritical and one of whose stages exhibits the transition.

`installedEnergy_congr` is why a spent source does not undo an installation:
installed energy is a functional of the actuator and the configuration law, and
of nothing else. A store's reading is not among its arguments, so no balance
falling to zero moves it. Decay would require a declared maintenance channel —
a stage whose executed transitions lower the occupancies — and this development
declares none. Naming the missing mechanism is all that is claimed here.
-/

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness

/-- A continuous real function on a compact substrate of finite mass is
integrable: it is bounded by its sup norm and the constant is integrable. -/
theorem integrable_of_continuous_compact {N : Type*} [TopologicalSpace N] [CompactSpace N]
    [MeasurableSpace N] [BorelSpace N] (μ : Measure N) [IsFiniteMeasure μ]
    {f : N → ℝ} (hf : Continuous f) : Integrable f μ := by
  let g : C(N, ℝ) := ⟨f, hf⟩
  exact Integrable.mono' (integrable_const ‖g‖) hf.aestronglyMeasurable
    (ae_of_all _ fun x => g.norm_coe_le_norm x)

namespace KernelArrangement

variable {M X S I : Type*} [TopologicalSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [Fintype X] [Fintype S] [Fintype I]

/-- The installed kernel is integrable against the substrate's product measure. -/
theorem kernel_integrable (A : KernelArrangement M X S I) :
    Integrable (fun z : M × M => A.kernel z.1 z.2) (A.volume.prod A.volume) :=
  haveI := A.volume_finite
  integrable_of_continuous_compact _ A.kernel_continuous

/-- **The spatial mass of one response mode**: its profile's substrate integral.
Hardware data — it is computed from the declared profile and the substrate
measure, and no thermodynamic quantity enters it. -/
noncomputable def modeMass (A : KernelArrangement M X S I) (i : I) : ℝ :=
  ∫ x, A.actuator.profile i x ∂A.volume

/-- **The arrangement's expected installed energy**: `LocalActuator.storedEnergy`
averaged over the configuration law the hardware actually sits in.

This is energy standing in the installed modes, not heat delivered to a
reservoir. `LocalActuator.installation_first_law` splits the external work of
an executed step into a change in this quantity and the step's mean heat; only
the first half appears here. -/
noncomputable def installedEnergy (A : KernelArrangement M X S I) : ℝ :=
  ∑ z, A.law.p z * A.actuator.storedEnergy z

/-- **The installed kernel's continuum energy, mode by mode.**

`LocalActuator.kernel` is a sum of rank-one products `φᵢ(x) φᵢ(y)`, so the
double integral factorizes and each mode contributes its occupancy times the
square of its spatial mass. The configuration law passes through as a weight:
the ensemble kernel is the mean of the pathwise ones, and its energy is the
mean of theirs.

This identity uses the arrangement's profiles, occupancies, measure and
configuration law. It involves neither installation prices nor heat; the mode
price condition enters only in K2's subsequent inequality. -/
theorem continuumEnergy_eq_modes (A : KernelArrangement M X S I) :
    A.continuumEnergy =
      ∑ z, A.law.p z * ∑ i, A.actuator.occupancy z i * A.modeMass i ^ 2 := by
  have := A.volume_finite
  have hint : ∀ (z : X × S) (i : I),
      Integrable (fun w : M × M => A.law.p z * A.actuator.occupancy z i *
        (A.actuator.profile i w.1 * A.actuator.profile i w.2))
        (A.volume.prod A.volume) := by
    intro z i
    exact integrable_of_continuous_compact _
      (continuous_const.mul (((A.profile_continuous i).comp continuous_fst).mul
        ((A.profile_continuous i).comp continuous_snd)))
  have hsplit : ∀ w : M × M, A.kernel w.1 w.2 =
      ∑ z, ∑ i, A.law.p z * A.actuator.occupancy z i *
        (A.actuator.profile i w.1 * A.actuator.profile i w.2) := by
    intro w
    simp only [KernelArrangement.kernel, LocalActuator.expectedKernel, LocalActuator.kernel,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ => by ring
  rw [KernelArrangement.continuumEnergy]
  simp_rw [hsplit]
  rw [integral_finsetSum _ fun z _ =>
    integrable_finsetSum _ fun i _ => hint z i]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_finsetSum _ fun i _ => hint z i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_prod_mul, modeMass]
  ring

end KernelArrangement

/--
**One microscopic arrangement, with its installation priced.**

`KernelArrangement`'s doc-string records that no field of it is a budget, and
that stays true: this structure adds no budget either. What it adds is the one
further piece of *hardware* data that lets an installation energy cap a
coupling — a constant `couplingPerEnergy` relating each mode's spatial mass to
its price — together with the sign condition on occupancies that a physical
count satisfies.

The added fields divide as `ActuatedCoupling`'s do. `mode_priced`
is a constitutive relation between declared profiles and declared prices;
`occupancy_nonneg` is a property of the hardware's readout; and
`couplingPerEnergy` is a positive number nothing in this development derives. A heat
allowance supplies none of them, and relocating a commitment is not the same as
discharging one — which is why the manuscript names `κ` where it states the
bound.
-/
structure PricedArrangement (M X S I : Type*) [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [Fintype X] [Fintype S] [Fintype I]
    extends KernelArrangement M X S I where
  /-- Coupling installed per unit installation energy. Declared hardware data. -/
  couplingPerEnergy : ℝ
  /-- A positive conversion factor gives the energy threshold `2 D / κ` its meaning. -/
  couplingPerEnergy_pos : 0 < couplingPerEnergy
  /-- Occupancies are physical counts of installed modes. -/
  occupancy_nonneg : ∀ z i, 0 ≤ actuator.occupancy z i
  /-- Each mode's spatial mass is within its price's budgeted share. -/
  mode_priced : ∀ i,
    toKernelArrangement.modeMass i ^ 2 ≤ couplingPerEnergy * actuator.price i

namespace PricedArrangement

variable {M X S I : Type*} [TopologicalSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [Fintype X] [Fintype S] [Fintype I]

/-- Nonnegative prices follow from positive conversion and the mode bound.
No positivity of heat or thermodynamic pricing law is inferred. -/
theorem price_nonneg (A : PricedArrangement M X S I) (i : I) :
    0 ≤ A.actuator.price i := by
  have := A.mode_priced i
  have := A.couplingPerEnergy_pos
  nlinarith [sq_nonneg (A.toKernelArrangement.modeMass i)]

/-- Expected stored energy is nonnegative under the hardware sign conditions;
it remains a state observable rather than the heat of a transition. -/
theorem installedEnergy_nonneg (A : PricedArrangement M X S I) :
    0 ≤ A.installedEnergy := by
  unfold KernelArrangement.installedEnergy LocalActuator.storedEnergy
  exact Finset.sum_nonneg fun z _ => mul_nonneg (A.law.nonneg z)
    (Finset.sum_nonneg fun i _ => mul_nonneg (A.price_nonneg i) (A.occupancy_nonneg z i))

/--
**K2 — the installed coupling is bounded by the installation energy.**

Termwise from `continuumEnergy_eq_modes`: each mode contributes
`cᵢ (∫ φᵢ)² ≤ cᵢ κ uᵢ` by `mode_priced` and `occupancy_nonneg`, and the
configuration average preserves the inequality because the law is a probability
distribution.

`κ` is not bounded, derived or supplied by anything thermodynamic; it is read
off the profiles and prices before any threshold is consulted. The inequality
is an upper bound only, and it does not reverse. -/
theorem continuumEnergy_le_installedEnergy (A : PricedArrangement M X S I) :
    A.toKernelArrangement.continuumEnergy ≤
      A.couplingPerEnergy * A.toKernelArrangement.installedEnergy := by
  rw [A.toKernelArrangement.continuumEnergy_eq_modes,
    KernelArrangement.installedEnergy, Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  have key : ∑ i, A.actuator.occupancy z i * A.toKernelArrangement.modeMass i ^ 2 ≤
      A.couplingPerEnergy * A.actuator.storedEnergy z := by
    rw [LocalActuator.storedEnergy, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc A.actuator.occupancy z i * A.toKernelArrangement.modeMass i ^ 2
        ≤ A.actuator.occupancy z i * (A.couplingPerEnergy * A.actuator.price i) :=
          mul_le_mul_of_nonneg_left (A.mode_priced i) (A.occupancy_nonneg z i)
      _ = A.couplingPerEnergy * (A.actuator.price i * A.actuator.occupancy z i) := by ring
  calc A.law.p z * ∑ i, A.actuator.occupancy z i * A.toKernelArrangement.modeMass i ^ 2
      ≤ A.law.p z * (A.couplingPerEnergy * A.actuator.storedEnergy z) :=
        mul_le_mul_of_nonneg_left key (A.law.nonneg z)
    _ = A.couplingPerEnergy * (A.law.p z * A.actuator.storedEnergy z) := by ring

/-- The installed coupling is nonnegative: every mode contributes a nonnegative
occupancy times a square. No mode price condition is needed; this
lets the subcritical self-consistency results, which require
`0 ≤ K`, apply to the arrangement's own coupling. -/
theorem continuumEnergy_nonneg (A : PricedArrangement M X S I) :
    0 ≤ A.toKernelArrangement.continuumEnergy := by
  rw [A.toKernelArrangement.continuumEnergy_eq_modes]
  refine Finset.sum_nonneg fun z _ => mul_nonneg (A.law.nonneg z) ?_
  exact Finset.sum_nonneg fun i _ => mul_nonneg (A.occupancy_nonneg z i) (sq_nonneg _)

end PricedArrangement

section MeanField

variable {M X S I : Type*} [MeasureSpace M] [TopologicalSpace M] [CompactSpace M]
  [BorelSpace M] [SecondCountableTopology M]
  [Fintype X] [Fintype S] [Fintype I]

/--
**K1 — the installed kernel's continuum energy is the field's mean-field
coupling.**

`KernelArrangement.continuumEnergy` integrates against `volume.prod volume` and
`mean_field_coupling` is the iterated `∫ x, ∫ y`. They are the same number, by
Fubini: the kernel is jointly continuous (`kernel_continuous`), the substrate is
compact and `volume_finite` gives the mass, so `kernel_integrable` discharges
the side condition.

**Scope.** This is about the two integrals and nothing else. It does not assert
that any physical field's kernel *is* the installed one; `hker` supplies that
identification, and making it for a cortical field is `Chain.E56`, a physical
commitment this theorem leaves exactly where it was. The normalization in which
the right-hand side is a coupling *strength* rather than a coupling times a
size is `IsProbabilityMeasure volume`, which `exhibits_phase_transition` and
`IsEMFieldCoupling.domain_probability` both require and which K3 assumes. -/
theorem KernelArrangement.continuumEnergy_eq_mean_field_coupling
    (A : KernelArrangement M X S I) (sys : StochasticNeuralField M)
    (hvol : A.volume = (MeasureSpace.volume : Measure M)) (hker : sys.K = A.kernel) :
    A.continuumEnergy = mean_field_coupling sys := by
  have := A.volume_finite
  rw [mean_field_coupling, hker, KernelArrangement.continuumEnergy, ← hvol]
  exact integral_prod _ A.kernel_integrable

/--
**K3 — a minimum installed energy for coherence.**

An arrangement whose installed energy satisfies `κ U ≤ 2 D` cannot reach the
synchronization threshold. Three conclusions, one contrapositive and two
consequences of it:

* `exhibits_phase_transition` fails, by K1 and K2 against `critical_coupling`;
* the incoherent solution is the only nonnegative solution of the stationary
  self-consistency equation at this arrangement's own coupling
  (`fixed_point_eq_zero_of_le_critical`, which covers the threshold itself);
* no Fourier mode of the uniform density grows
  (`FokkerPlanck.incoherent_instability_iff`). This is linearization of the
  scalar mean-field equation, not stability of a heterogeneous spatial field.

**The direction matters.** This is a no-go: insufficient installed energy
forbids the coherent branch. It is *not* the claim that sufficient installed
energy produces coherence — `κ U > 2 D` bounds the coupling from above by a
number above the threshold, which constrains nothing, and K2's inequality does
not reverse. `Examples/InstalledCoupling.lean`'s `converse_rejected` exhibits an
arrangement with `κ U > 2 D` that does not exhibit the transition.

**What `U` is.** Installed energy, not dissipated heat; see the module header
and `Examples/RegisterBath.lean`. And `hker` identifies the field's kernel with
the arrangement's, which is supplied rather than derived. -/
theorem PricedArrangement.no_coherence_of_installedEnergy
    [IsProbabilityMeasure (MeasureSpace.volume : Measure M)]
    (A : PricedArrangement M X S I) (sys : StochasticNeuralField M)
    (hvol : A.volume = (MeasureSpace.volume : Measure M)) (hker : sys.K = A.kernel)
    (hU : A.couplingPerEnergy * A.installedEnergy ≤ critical_coupling sys.D) :
    ¬ exhibits_phase_transition sys ∧
    (∀ r : ℝ, 0 ≤ r → r = selfConsistency (mean_field_coupling sys) sys.D r → r = 0) ∧
    ¬ ∃ n : ℕ, 0 < n ∧ 0 < FokkerPlanck.incoherentRate sys.D (mean_field_coupling sys) n := by
  have hid : mean_field_coupling sys = A.toKernelArrangement.continuumEnergy :=
    (A.toKernelArrangement.continuumEnergy_eq_mean_field_coupling sys hvol hker).symm
  have hle : mean_field_coupling sys ≤ critical_coupling sys.D :=
    hid ▸ A.continuumEnergy_le_installedEnergy.trans hU
  have hnn : 0 ≤ mean_field_coupling sys := hid ▸ A.continuumEnergy_nonneg
  refine ⟨not_lt.mpr hle, fun r hr hfix =>
    fixed_point_eq_zero_of_le_critical sys.h_D_pos hnn hle hr hfix, ?_⟩
  intro hgrow
  have := (FokkerPlanck.incoherent_instability_iff sys.h_D_pos _).mp hgrow
  rw [critical_coupling] at hle
  linarith

/-- At or below the installed-energy bound, any positive classical stationary
density reproducing its nonnegative mean magnitude is the uniform von Mises
density. The cosine drift is the scalar mean-field model in a frame with mean
direction zero. No spatial-field dynamics, trajectory convergence, or cortical
identification follows from its stationary classification. -/
theorem PricedArrangement.stationary_eq_incoherent_of_installedEnergy
    [IsProbabilityMeasure (MeasureSpace.volume : Measure M)]
    (A : PricedArrangement M X S I) (sys : StochasticNeuralField M)
    (hvol : A.volume = (MeasureSpace.volume : Measure M)) (hker : sys.K = A.kernel)
    (hU : A.couplingPerEnergy * A.installedEnergy ≤ critical_coupling sys.D)
    {r : ℝ} (hr : 0 ≤ r) {ρ : ℝ → ℝ}
    (hstat : FokkerPlanck.IsStationary sys.D
      (FokkerPlanck.drift (mean_field_coupling sys) r) ρ)
    (hmean : circularOrderParameter ρ = (r : ℂ)) :
    r = 0 ∧ ρ = vonMisesDensity 0 := by
  have hρ := (FokkerPlanck.stationary_iff_vonMises sys.h_D_pos
    (mean_field_coupling sys) r ρ).mp hstat
  rw [hρ] at hmean
  have hfix := (fixedPoint_iff_selfReproducing (mean_field_coupling sys) sys.D r).mpr hmean
  have hr0 := (A.no_coherence_of_installedEnergy sys hvol hker hU).2.1 r hr hfix
  exact ⟨hr0, by simpa only [hr0, mul_zero, zero_div] using hρ⟩

end MeanField

/-! ## A funded installation: what the source caps -/

section Funded

variable {M X S I : Type*} [Fintype X] [Fintype S] [Fintype I]

omit [Fintype X] [Fintype S] in
/-- The actuator's path work at a fixed stage observable *is* the protocol's
work with the stored energy as the common energy. Both sides are
`E (x, t) - E (x, s) + q k x s t`; naming them separately is the only reason
this needs stating. -/
theorem LocalActuator.pathWork_eq_protocolWork (A : LocalActuator M X S I)
    (q : ℕ → X → S → S → ℝ) (k : ℕ) :
    A.pathWork (q k) = protocolWork A.storedEnergy q k := rfl

/-- **The cumulative draw of an installing run is its installed-energy change
plus its heat.** This is `FiniteProtocol.sum_first_law` read through the store:
the hypothesis identifies the work each executed transition takes from the store
with the work that transition's installation requires, and nothing else is
assumed about either. -/
theorem PathwiseStore.totalDraw_eq_installation (A : LocalActuator M X S I)
    (B : PathwiseStore X S) (q : ℕ → X → S → S → ℝ)
    (hdraw : ∀ k, B.draw k = A.pathWork (q k)) (N : ℕ) :
    B.totalDraw N =
      (∑ z, (B.protocol.law N).p z * A.storedEnergy z) -
        (∑ z, (B.protocol.law 0).p z * A.storedEnergy z) +
        ∑ k ∈ Finset.range N, (B.protocol.step k).meanHeat (q k) := by
  have h := B.protocol.sum_first_law A.storedEnergy q N
  unfold PathwiseStore.totalDraw
  simp_rw [hdraw, A.pathWork_eq_protocolWork q]
  exact h

/-- **A finite source caps the installed energy at every horizon.**

`totalDraw_le_initial_resources` bounds the work a solvent run can have drawn
by the resources it started with; `totalDraw_eq_installation` says what that
work went into. The heat enters only by its sign, so the bound is loose by the
heat the run delivered — an installation that dissipates reaches *less* than
this cap, never more.

The initial law, the store's initial reading and the source are declared, as
they are everywhere in `Phase3_ContinuingAgent`; nothing here prepares or
refuels any of them. -/
theorem PathwiseStore.installedEnergy_le_resources (A : LocalActuator M X S I)
    (B : PathwiseStore X S) (q : ℕ → X → S → S → ℝ) (R : S → ℝ) (N : ℕ)
    (hdraw : ∀ k, B.draw k = A.pathWork (q k))
    (hq : ∀ k < N, 0 ≤ (B.protocol.step k).meanHeat (q k))
    (hb : B.Ledgered) (hr : B.SourceLedgered R) (hs : B.Solvent N)
    (hR : ∀ k ≤ N, ∀ z, B.protocol.Reachable k z → 0 ≤ R z.2) :
    (∑ z, (B.protocol.law N).p z * A.storedEnergy z) ≤
      (∑ z, (B.protocol.law 0).p z * A.storedEnergy z) + B.meanBalance 0 +
        ∑ z, (B.protocol.law 0).p z * R z.2 := by
  have h1 := B.totalDraw_le_initial_resources R hb hr N hs hR
  have h2 := B.totalDraw_eq_installation A q hdraw N
  have h3 : 0 ≤ ∑ k ∈ Finset.range N, (B.protocol.step k).meanHeat (q k) :=
    Finset.sum_nonneg fun k hk => hq k (Finset.mem_range.1 hk)
  linarith

/-- **Nothing installed comes back out by itself.** If no transition stage `n`
can execute lowers the stored energy, the installed energy does not fall across
that stage. The proof is termwise on the executed paths: the next law's mass at
`(x, t)` is the previous law's mass at `(x, s)` carried through the channel, and
every term compares `storedEnergy (x, s)` with `storedEnergy (x, t)` at the same
nonnegative weight. -/
theorem LocalActuator.storedEnergy_mono_of_stage (A : LocalActuator M X S I)
    (P : FiniteProtocol X S) (n : ℕ)
    (h : ∀ x s t, 0 < (P.law n).p (x, s) → 0 < (P.stage n x s).p t →
      A.storedEnergy (x, s) ≤ A.storedEnergy (x, t)) :
    (∑ z, (P.law n).p z * A.storedEnergy z) ≤
      ∑ z, (P.law (n + 1)).p z * A.storedEnergy z := by
  have hlhs : (∑ z, (P.law n).p z * A.storedEnergy z) =
      ∑ x, ∑ s, ∑ t, (P.law n).p (x, s) * (P.stage n x s).p t * A.storedEnergy (x, s) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, (P.stage n x s).sum_one, mul_one]
  have hrhs : (∑ z, (P.law (n + 1)).p z * A.storedEnergy z) =
      ∑ x, ∑ s, ∑ t, (P.law n).p (x, s) * (P.stage n x s).p t * A.storedEnergy (x, t) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => by
        rw [P.law_succ_apply n (x, t), Finset.sum_mul]]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [hlhs, hrhs]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => ?_
  rcases eq_or_lt_of_le ((P.law n).nonneg (x, s)) with hl | hl
  · rw [← hl, zero_mul, zero_mul, zero_mul]
  rcases eq_or_lt_of_le ((P.stage n x s).nonneg t) with hs | hs
  · rw [← hs, mul_zero, zero_mul, zero_mul]
  exact mul_le_mul_of_nonneg_left (h x s t hl hs) (mul_nonneg hl.le hs.le)

/-- **A decay needs a maintenance channel.** Contrapositive of the previous
theorem: an installed energy that falls across a stage identifies an executed
transition that lowers the stored energy — a stage of the protocol that
*uninstalls*.

This development declares no such stage. That is the whole of the claim: the
mechanism is named and left unsupplied, which is also why exhaustion of a source
does not undo an installation. A store's reading is not an occupancy. -/
theorem LocalActuator.exists_lowering_of_installedEnergy_lt (A : LocalActuator M X S I)
    (P : FiniteProtocol X S) (n : ℕ)
    (h : (∑ z, (P.law (n + 1)).p z * A.storedEnergy z) <
      ∑ z, (P.law n).p z * A.storedEnergy z) :
    ∃ x s t, 0 < (P.law n).p (x, s) ∧ 0 < (P.stage n x s).p t ∧
      A.storedEnergy (x, t) < A.storedEnergy (x, s) := by
  by_contra hc
  push Not at hc
  exact absurd (A.storedEnergy_mono_of_stage P n
    fun x s t hl hs => hc x s t hl hs) (not_le.2 h)

/-- **Installed energy is a functional of the law.** Two arrangements with the
same actuator and the same configuration law have the same installed energy,
whatever else differs between them — in particular, whatever their stores hold.

This is the sense in which *exhaustion does not uninstall*: a store's reading is
not an argument of `installedEnergy`, so a balance falling to zero cannot move
it. A decay would have to come from a stage whose executed transitions lower the
occupancies, and this development declares no such maintenance channel. -/
theorem KernelArrangement.installedEnergy_congr [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (A A' : KernelArrangement M X S I) (hact : A.actuator = A'.actuator)
    (hlaw : A.law = A'.law) : A.installedEnergy = A'.installedEnergy := by
  unfold KernelArrangement.installedEnergy
  rw [hact, hlaw]

end Funded

section FundedMeanField

variable {M X S I : Type*} [MeasureSpace M] [TopologicalSpace M] [CompactSpace M]
  [BorelSpace M] [SecondCountableTopology M] [Fintype X] [Fintype S] [Fintype I]
  [IsProbabilityMeasure (MeasureSpace.volume : Measure M)]

/--
**N10 — the fuel no-go.** A run funded by a declared finite source, whose store
pays exactly the installation work of the transitions it executes, cannot reach
the coherence threshold at any horizon its resources could not have paid for.

K3 asks for the installed energy; this asks for the fuel, and the composition is
`installedEnergy_le_resources`. What changes is the side of the ledger the
hypothesis sits on — `hcap` mentions the initial law, the store's initial
reading and the source, and mentions no energy standing anywhere at stage `N`.

**One direction only, still.** A sufficient source does not supply coherence,
for the same reason a sufficient installed energy does not; `κ` remains declared
hardware data, so this relocates that input rather than discharging it; and the
bound is loose by the run's heat. -/
theorem PricedArrangement.no_coherence_of_funded_source
    (A : PricedArrangement M X S I) (B : PathwiseStore X S) (sys : StochasticNeuralField M)
    (q : ℕ → X → S → S → ℝ) (R : S → ℝ) (N : ℕ)
    (hvol : A.volume = (MeasureSpace.volume : Measure M)) (hker : sys.K = A.kernel)
    (hlaw : A.law = B.protocol.law N)
    (hdraw : ∀ k, B.draw k = A.actuator.pathWork (q k))
    (hq : ∀ k < N, 0 ≤ (B.protocol.step k).meanHeat (q k))
    (hb : B.Ledgered) (hr : B.SourceLedgered R) (hs : B.Solvent N)
    (hR : ∀ k ≤ N, ∀ z, B.protocol.Reachable k z → 0 ≤ R z.2)
    (hcap : A.couplingPerEnergy *
        ((∑ z, (B.protocol.law 0).p z * A.actuator.storedEnergy z) + B.meanBalance 0 +
          ∑ z, (B.protocol.law 0).p z * R z.2) ≤ critical_coupling sys.D) :
    ¬ exhibits_phase_transition sys ∧
    (∀ r : ℝ, 0 ≤ r → r = selfConsistency (mean_field_coupling sys) sys.D r → r = 0) ∧
    ¬ ∃ n : ℕ, 0 < n ∧
      0 < FokkerPlanck.incoherentRate sys.D (mean_field_coupling sys) n := by
  refine A.no_coherence_of_installedEnergy sys hvol hker (le_trans ?_ hcap)
  have hle := B.installedEnergy_le_resources A.actuator q R N hdraw hq hb hr hs hR
  have hU : A.installedEnergy = ∑ z, (B.protocol.law N).p z * A.actuator.storedEnergy z := by
    rw [KernelArrangement.installedEnergy, hlaw]
  rw [hU]
  exact mul_le_mul_of_nonneg_left hle A.couplingPerEnergy_pos.le

/--
**N11 — the run-level no-go.** An evolving arrangement subcritical at *every*
stage exhibits the transition at none of them.

The hypothesis is a supremum over stages. It cannot be weakened to a mean:
`Examples/EvolvingCoupling.lean` exhibits a stage sequence whose mean installed
energy is subcritical and one of whose stages does exhibit the transition, so
the mean-substituted statement is false rather than merely unproved.

This is a statement about the stationary problem each stage poses, one stage at a
time. It licenses nothing about the phase trajectory: kernel convergence implies
neither trajectory convergence nor preservation of the threshold along a run. -/
theorem PricedArrangement.no_coherence_of_run
    (A : ℕ → PricedArrangement M X S I) (sys : ℕ → StochasticNeuralField M)
    (hvol : ∀ n, (A n).volume = (MeasureSpace.volume : Measure M))
    (hker : ∀ n, (sys n).K = (A n).kernel)
    (hU : ∀ n, (A n).couplingPerEnergy * (A n).installedEnergy ≤ critical_coupling (sys n).D)
    (n : ℕ) :
    ¬ exhibits_phase_transition (sys n) ∧
    (∀ r : ℝ, 0 ≤ r → r = selfConsistency (mean_field_coupling (sys n)) (sys n).D r → r = 0) ∧
    ¬ ∃ k : ℕ, 0 < k ∧
      0 < FokkerPlanck.incoherentRate (sys n).D (mean_field_coupling (sys n)) k :=
  (A n).no_coherence_of_installedEnergy (sys n) (hvol n) (hker n) (hU n)

end FundedMeanField

#print axioms KernelArrangement.continuumEnergy_eq_modes
#print axioms KernelArrangement.continuumEnergy_eq_mean_field_coupling
#print axioms PricedArrangement.continuumEnergy_le_installedEnergy
#print axioms PricedArrangement.no_coherence_of_installedEnergy
#print axioms PricedArrangement.stationary_eq_incoherent_of_installedEnergy
#print axioms PathwiseStore.totalDraw_eq_installation
#print axioms PathwiseStore.installedEnergy_le_resources
#print axioms LocalActuator.storedEnergy_mono_of_stage
#print axioms LocalActuator.exists_lowering_of_installedEnergy_lt
#print axioms KernelArrangement.installedEnergy_congr
#print axioms PricedArrangement.no_coherence_of_funded_source
#print axioms PricedArrangement.no_coherence_of_run

end PhysicsOfConsciousness
