/-
  Examples.lean — Non-vacuity witnesses

  Every physical postulate in this development is now carried as a *class field*
  rather than a standalone `axiom` (see `Axioms.lean` §5 for why: the standalone
  formulations were inconsistent). That change is only an improvement if the
  classes can actually be inhabited — an uninhabitable class makes every theorem
  about it vacuously true, which is no better than an inconsistent axiom.

  This file discharges that obligation for the finite-state parts of the theory
  by exhibiting concrete instances.

  **Coverage — every class carrying a physical postulate is now inhabited.**
    ✓ `StatisticalMechanics` — a one-bit erasure model with a genuine bath.
    ✓ `StructuralResonance`  — a perfectly-resonant system (KL = 0).
    ✓ `ActionPrinciples`     — a scalar field on a one-point spacetime.
    ✓ `LocalSectionSynchronization` / `ThermodynamicCover` — two overlapping
      patches on a three-site substrate, with sections of the sheafified
      probability presheaf built from a phase-dependent invariant measure (§4).

  §5 additionally exercises the Phase 8 gradient-flow link on a two-site
  substrate: counting measure, a non-zero gradient, and an explicit non-constant
  flow along which entropy production decays as `e^{-2t}`.

  §6 witnesses `IsRegularTriangulation` (`Phase2_MeshConvergence`) with the uniform
  partition of `[0,1)`, and runs `mesh_refinement_convergence` on it. Its
  disjoint-yet-covering-yet-anchored conditions are in tension, so an instance is
  the only proof they are simultaneously satisfiable.

  §7 witnesses the rotating-frame reduction (`Phase4_RotatingFrame`) on a
  two-oscillator system with a common natural frequency, running
  `rotating_frame_chain` with every hypothesis discharged, and exhibits a system
  for which the full Kuramoto potential provably has no minimum.

  Every declaration in this file depends only on `propext`, `Classical.choice`
  and `Quot.sound`.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_KLBound
import PhysicsOfConsciousness.Phase5_GlobalSection
import PhysicsOfConsciousness.Phase8_ContinuousField
import PhysicsOfConsciousness.Phase2_MeshConvergence
import PhysicsOfConsciousness.Phase4_RotatingFrame

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 1. A one-bit erasure system satisfying Landauer's heat equation -/

/-- Temperature 1, and every operation dumps exactly `log 2` of heat — which is
    what `heat_eq` will force, given the bath below. -/
noncomputable instance boolThermo : Thermodynamics Bool where
  heat_dissipation := fun _ => Real.log 2
  temperature := 1
  temperature_pos := by norm_num

/-- The bath starts in one known state and ends anywhere in a two-state space:
    exactly one bit of bath entropy per operation.

    `U t` is a genuine bijection of `Bool × Bool`. It routes the system's state
    into the bath (`(s, false) ↦ (t false, s)`), which is what lets a
    non-injective `t` coexist with globally reversible dynamics — the Norton /
    Shenker point the manuscript makes in Derivation 2. -/
instance boolBath : BipartiteEnvironment Bool where
  bath := Bool
  dec_bath := inferInstance
  U := fun t p => (if p.2 = false then t false else !(t false), p.1)
  U_inj := by decide
  initial_bath := fun _ => {false}
  final_bath := fun _ => Finset.univ
  h_evolve := by
    intro t p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_singleton] at hq
    simp only [Finset.mem_product, Finset.mem_univ, and_true, hq.2]
    exact Finset.mem_image.mpr ⟨false, Finset.mem_univ _, rfl⟩
  h_bath_nonempty := fun _ => ⟨false, Finset.mem_singleton_self _⟩

noncomputable instance boolStatMech : StatisticalMechanics Bool where
  heat_eq := by
    intro t
    show Real.log 2 = 1 * (boltzmann_entropy (Finset.univ : Finset Bool)
                            - boltzmann_entropy ({false} : Finset Bool))
    simp [boltzmann_entropy]

/-- Sanity check: the general theory, applied to this instance, reproduces the
    expected physics — erasing a bit dissipates strictly positive heat. -/
example : heat_dissipation (fun _ => false : Bool → Bool) > 0 :=
  landauers_principle _ (by
    intro h
    exact absurd (h (a₁ := true) (a₂ := false) rfl) (by simp))

/-! ## 2. A perfectly resonant system -/

/-- Uniform internal statistics matched to uniform external statistics: the
    system has reached structural resonance, so KL = 0 and the postulate holds
    with room to spare. -/
noncomputable def uniformBool : ProbDist Bool where
  p := fun _ => 1/2
  nonneg := by intro i; norm_num
  sum_one := by simp

noncomputable instance boolResonance : StructuralResonance Bool where
  P_ext := uniformBool
  Q_int := uniformBool
  Q_int_pos := by intro i; norm_num [uniformBool]
  transition := id
  dt := 1
  dt_pos := one_pos
  kl_bound := by
    have hKL : KL uniformBool uniformBool = 0 := by
      unfold KL uniformBool
      simp
    show discrete_entropy_rate (σ := Bool) id ≥ KL uniformBool uniformBool / 1
    rw [hKL]
    rw [zero_div]
    have h : discrete_entropy_rate (σ := Bool) id = Real.log 2 / 1 := rfl
    rw [h, div_one]
    positivity

/-! ## 3. A scalar field on a one-point spacetime -/

/-- `V v = v²`, minimised at `v = 0`. Spacetime is a single point carrying the
    Dirac probability measure, so `∫ V (phi x) = V (phi ())`. -/
noncomputable instance unitAction :
    ActionPrinciples Unit ℝ (fun _ => 0) (fun phi => ∫ x, (phi x)^2 ∂(Measure.dirac ()))
      (fun phi => ∫ x, (phi x)^2 ∂(Measure.dirac ())) (fun v => v^2) (Measure.dirac ()) where
  total_eq := by intro phi; simp
  kinetic_nonneg := by intro phi; norm_num
  kinetic_const := by intro v; rfl
  potential_integral := by intro phi; rfl
  potential_integrable := by
    intro phi
    exact Integrable.of_finite

/-- The one-point spacetime really does witness the vacuum theorem: the constant
    zero field minimises the energy, and lands in the vacuum manifold. -/
example : (0 : ℝ) ∈ DynamicalVacuum (fun v : ℝ => v^2) := by
  intro v'
  simpa using sq_nonneg v'

/-! ## 4. A thermodynamic cover: two overlapping patches on a three-site substrate

  This is the witness that was missing until now. `LocalSectionSynchronization`
  and `ThermodynamicCover` carry the gluing hypotheses of Derivation 5, and
  `global_section_from_thermodynamics` is stated for an arbitrary instance of the
  latter; until an instance existed, that theorem was conditional on a structure
  of unknown realizability.

  The substrate is deliberately the smallest one that is not degenerate: three
  sites, covered by two *overlapping* open patches, so the gluing that the
  theorem performs is a genuine two-patch gluing across a nonempty intersection
  rather than a relabelling of a single global section.

  **What the witness does and does not establish.** It shows the class is
  inhabitable, so Derivation 5's conclusions are not vacuous. It does not show
  that a *biological* cortex satisfies the class: the phase field here is
  constant (every patch already locked at phase 0), which is what makes
  `thermodynamic_equilibrium` discharge from `phase_locked_minimizes_potential`.
  Getting a physical system to that configuration is the content of the informal
  dynamical argument in the manuscript, not of this file.
-/

/-- Three sites. `mid` is the one shared by both patches. -/
inductive Site : Type
  | left | mid | right
  deriving DecidableEq

instance : Fintype Site :=
  ⟨{Site.left, Site.mid, Site.right}, by intro x; cases x <;> decide⟩

/-- Discrete topology, and the Borel σ-algebra it generates — so `BorelSpace`
    holds by `rfl` rather than by a compatibility argument. -/
instance : TopologicalSpace Site := ⊥
instance : DiscreteTopology Site := ⟨rfl⟩
instance : MeasurableSpace Site := borel Site
instance : BorelSpace Site := ⟨rfl⟩

/-- The substrate as an object of `TopCat`. `abbrev` (not `def`) so that the
    `MeasurableSpace`/`BorelSpace` instances above are found through the
    coercion `↥Cortex`. -/
abbrev Cortex : TopCat.{0} := TopCat.of Site

/-- A triangulation. As documented on `TriangulatedManifold`, the class does not
    tie `edge_region` to `complex`; here we make them agree anyway — the region
    of the edge `{u, v}` is the pair `{u, v}` itself, which is open (discrete
    topology) and symmetric on the nose. -/
instance : TriangulatedManifold ↥Cortex where
  V := Site
  complex := { faces := Set.univ, downward_closed := fun _ _ => trivial }
  embedding := id
  edge_region := fun u v => {u, v}
  edge_region_symm := fun u v => Set.pair_comm u v

/-- Two patches: everything but `right`, and everything but `left`. They cover
    `Cortex` and overlap exactly in `mid`. -/
def patch : Bool → Opens ↥Cortex
  | false => ⟨{x : Site | x ≠ Site.right}, isOpen_discrete _⟩
  | true  => ⟨{x : Site | x ≠ Site.left}, isOpen_discrete _⟩

theorem patch_cover : iSup patch = ⊤ := by
  ext x
  simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
  cases x
  · exact ⟨false, show Site.left ≠ Site.right by decide⟩
  · exact ⟨false, show Site.mid ≠ Site.right by decide⟩
  · exact ⟨true, show Site.right ≠ Site.left by decide⟩

/-- The cover is a genuine one: the two patches meet, and meet in one site. -/
theorem patch_overlap : (patch false ⊓ patch true : Opens ↥Cortex) = ⟨{Site.mid}, isOpen_discrete _⟩ := by
  ext x
  cases x <;> simp [patch]

/-- The shared site, viewed as a point of the whole substrate. -/
def midPt : ↥(⊤ : Opens ↥Cortex) := ⟨Site.mid, trivial⟩

noncomputable def midDirac : FiniteMeasure ↥(⊤ : Opens ↥Cortex) :=
  ⟨Measure.dirac midPt, inferInstance⟩

/-- The invariant measure attached to a macroscopic phase `t`: unit mass at the
    shared site, scaled by `(1 + cos t)⁺`.

    The point of the `cos` is that the family genuinely *depends* on the phase
    (see `phaseMeasure_not_const`). A constant family would satisfy
    `phase_invariant_periodic` for trivial reasons and would witness nothing. -/
noncomputable def phaseMeasure (t : ℝ) : FiniteMeasure ↥(⊤ : Opens ↥Cortex) :=
  (Real.toNNReal (1 + Real.cos t)) • midDirac

theorem midDirac_mass : midDirac Set.univ = 1 := by
  rw [FiniteMeasure.coeFn_def]
  simp [midDirac]

theorem phaseMeasure_mass (t : ℝ) :
    (phaseMeasure t) Set.univ = Real.toNNReal (1 + Real.cos t) := by
  rw [phaseMeasure, FiniteMeasure.smul_apply, midDirac_mass, smul_eq_mul, mul_one]

/-- Non-degeneracy: the invariant measure really varies with the phase. -/
theorem phaseMeasure_not_const : phaseMeasure 0 ≠ phaseMeasure Real.pi := by
  intro h
  have h2 : (phaseMeasure 0) Set.univ = (phaseMeasure Real.pi) Set.univ := by rw [h]
  rw [phaseMeasure_mass, phaseMeasure_mass, Real.cos_zero, Real.cos_pi] at h2
  norm_num at h2

/-- 2π-periodicity, which is what `phase_invariant_periodic` demands. -/
theorem phaseMeasure_periodic {x y : ℝ} (h : Real.cos (x - y) = 1) :
    phaseMeasure x = phaseMeasure y := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp h
  have hx : x = y + (n : ℝ) * (2 * Real.pi) := by linarith [hn]
  rw [phaseMeasure, phaseMeasure, hx, Real.cos_add_int_mul_two_pi]

/-- The global section of the sheafified probability presheaf carried by phase
    `t`: the germ family of `phaseMeasure t`. -/
noncomputable def globalSect (t : ℝ) : (probabilityPresheaf Cortex).obj (op ⊤) :=
  (TopCat.Presheaf.toSheafify (probabilityPresheaf_pre Cortex)).app (op ⊤) (phaseMeasure t)

/-- All patches locked at phase 0, each carrying the restriction of the global
    invariant measure. `sync_to_section_eq` then holds by `rfl` — the local
    sections *are* restrictions, which is the modelling assumption the field
    records. -/
noncomputable instance cortexSync : LocalSectionSynchronization Cortex where
  I := Bool
  cover := patch
  is_cover := patch_cover
  phase := fun _ => 0
  sync_to_section := fun i =>
    (probabilityPresheaf Cortex).map (homOfLE (le_top : patch i ≤ ⊤)).op (globalSect 0)
  phase_invariant_measure := globalSect
  phase_invariant_periodic := fun _ _ h => by
    unfold globalSect
    rw [phaseMeasure_periodic h]
  sync_to_section_eq := fun _ => rfl

/-- Uniform unit coupling between the two patches. The configuration `phase = 0`
    is a global minimum of the Kuramoto potential by
    `phase_locked_minimizes_potential`, so `thermodynamic_equilibrium` is
    discharged rather than assumed here. -/
noncomputable instance cortexCover : ThermodynamicCover Cortex where
  toLocalSectionSynchronization := cortexSync
  I_fintype := inferInstanceAs (Fintype Bool)
  I_decidable := inferInstanceAs (DecidableEq Bool)
  A := fun _ _ => 1
  A_symm := fun _ _ => rfl
  A_pos := fun _ _ => one_pos
  thermodynamic_equilibrium := fun theta =>
    phase_locked_minimizes_potential (V := Bool)
      ⟨fun _ => 0, fun _ _ => 1, fun _ _ => rfl⟩ (fun _ _ => one_pos) theta

/-- Derivation 5, applied to the witness: the two patch-local sections glue to a
    unique global section. Not vacuous — `cortexCover` above is a real instance. -/
example : ∃! s : GlobalSection (X := Cortex),
    ∀ i : Bool, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : cortexCover.cover i ≤ ⊤)).op s = cortexCover.sync_to_section i :=
  global_section_from_thermodynamics (X := Cortex)

/-! ## 5. The Phase 8 link, exercised on a concrete two-site substrate

  `Phase8_ContinuousField.lean` §7 shows that entropy production σ, read as a
  functional of the coupling kernel, is Fréchet differentiable with an explicit
  gradient, and transports the abstract descent theorems onto
  `entropy_production_rate` itself. Three things could still make that link
  hollow, and this section rules out each:

  * the bridge hypothesis `volume = Measure.count` might not be satisfiable
    alongside `Fintype`/`MeasureSpace`/`TopologicalSpace` — `duo_volume`
    discharges it by `rfl`;
  * `gradSigma` might be identically zero, making the "descent" trivial —
    `duo_grad` computes it to be `e^{-t}` off the diagonal;
  * the flow hypothesis `∀ t, HasDerivAt K_t (- gradSigma …) t` might have no
    non-constant solution — `duoFlow_hasDerivAt` exhibits one, and
    `duoFlow_not_const` shows it moves.

  The system: two sites, no natural frequencies, phases pinned at `0` and `π/2`
  (so the phase mismatch is maximal), diffusion `D = 2`. The coupling relaxes as
  `K(a,b) = K(b,a) = e^{-t}`, and σ decays as `e^{-2t}` — strictly, not merely
  monotonically (`sigma_duoFlow`, and the `StrictAnti` example below).
-/

inductive Duo : Type
  | a | b
  deriving DecidableEq

instance : Fintype Duo := ⟨{Duo.a, Duo.b}, by intro x; cases x <;> decide⟩
instance : TopologicalSpace Duo := ⊥

/-- Counting measure on the two sites — the hypothesis the bridge lemma needs. -/
noncomputable instance : MeasureSpace Duo :=
  { (⊤ : MeasurableSpace Duo) with volume := @Measure.count Duo ⊤ }

instance : MeasurableSingletonClass Duo := ⟨fun _ => trivial⟩

theorem duo_volume : (volume : Measure Duo) = Measure.count := rfl

lemma duo_sum {α : Type*} [AddCommMonoid α] (f : Duo → α) :
    ∑ y : Duo, f y = f Duo.a + f Duo.b := by
  show ∑ y ∈ ({Duo.a, Duo.b} : Finset Duo), f y = _
  rw [Finset.sum_pair (by decide)]

/-- Two sites, no natural drift, diffusion `D = 2`. -/
noncomputable def duoSys : StochasticNeuralField Duo where
  omega := fun _ => 0
  K := fun _ _ => 0
  tau := 1
  D := 2
  h_D_pos := by norm_num
  Omega_avg := 0

/-- Phases `0` and `π/2`: the mismatch `sin (θ_b − θ_a)` is `±1`, so the coupling
    entries genuinely feel the gradient. -/
noncomputable def duoTheta : Duo → ℝ
  | Duo.a => 0
  | Duo.b => Real.pi / 2

/-- The bridge fires: the differentiated functional is `entropy_production_rate`. -/
example (K : CouplingSpace Duo) :
    sigmaOfKernel duoSys duoTheta K = entropy_production_rate (duoSys.withKernel K) duoTheta :=
  sigmaOfKernel_eq_entropy_production_rate duo_volume duoSys duoTheta K

/-- Exponentially relaxing coupling: off-diagonal entries decay as `e^{-t}`,
    diagonal entries stay at `0` (their gradient component vanishes, since a site
    has no phase mismatch with itself). -/
noncomputable def duoFlow (t : ℝ) : CouplingSpace Duo :=
  WithLp.toLp 2 (fun p : Duo × Duo => if p.1 = p.2 then 0 else Real.exp (-t))

lemma duo_drift_a (t : ℝ) : drift duoSys duoTheta (duoFlow t) Duo.a = Real.exp (-t) := by
  simp [drift, duoSys, duoFlow, duoTheta, duo_sum]

lemma duo_drift_b (t : ℝ) : drift duoSys duoTheta (duoFlow t) Duo.b = -Real.exp (-t) := by
  simp [drift, duoSys, duoFlow, duoTheta, duo_sum]

/-- The gradient is *not* identically zero: off the diagonal it is `e^{-t}`. -/
lemma duo_grad (t : ℝ) (p : Duo × Duo) :
    (gradSigma duoSys duoTheta (duoFlow t)) p = if p.1 = p.2 then 0 else Real.exp (-t) := by
  obtain ⟨x, y⟩ := p
  cases x <;> cases y <;>
    simp [gradSigma, show duoSys.D = 2 from rfl, duoTheta, duo_drift_a, duo_drift_b]

/-- `duoFlow` really is a gradient flow of σ. -/
lemma duoFlow_hasDerivAt (t : ℝ) :
    HasDerivAt duoFlow (- gradSigma duoSys duoTheta (duoFlow t)) t := by
  have hg : HasDerivAt
      (fun t : ℝ => (fun p : Duo × Duo => if p.1 = p.2 then (0 : ℝ) else Real.exp (-t)))
      (fun p : Duo × Duo => if p.1 = p.2 then (0 : ℝ) else -Real.exp (-t)) t := by
    rw [hasDerivAt_pi]
    intro p
    by_cases h : p.1 = p.2
    · simp only [h, ite_true]
      exact hasDerivAt_const t 0
    · simp only [h, ite_false]
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
        simpa using ((hasDerivAt_id t).neg).exp
      exact hexp
  have hcomp := (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Duo × Duo => ℝ)).symm
      : (Duo × Duo → ℝ) ≃L[ℝ] CouplingSpace Duo).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt
      t hg
  have hEq : - gradSigma duoSys duoTheta (duoFlow t)
      = WithLp.toLp 2 (fun p : Duo × Duo => if p.1 = p.2 then (0 : ℝ) else -Real.exp (-t)) := by
    ext p
    have hp := duo_grad t p
    show -(gradSigma duoSys duoTheta (duoFlow t)) p = _
    rw [hp]
    by_cases h : p.1 = p.2 <;> simp [h]
  rw [hEq]
  exact hcomp

/-- Entropy production along the flow, in closed form: `σ(t) = e^{-2t}`. -/
theorem sigma_duoFlow (t : ℝ) :
    sigmaOfKernel duoSys duoTheta (duoFlow t) = Real.exp (-t) ^ 2 := by
  simp [sigmaOfKernel, duo_sum, duo_drift_a, duo_drift_b, show duoSys.D = 2 from rfl]
  ring

/-- The flow is not constant, so the descent statement is not about a fixed point. -/
theorem duoFlow_not_const : duoFlow 0 ≠ duoFlow 1 := by
  intro h
  have h2 : (duoFlow 0) (Duo.a, Duo.b) = (duoFlow 1) (Duo.a, Duo.b) := by rw [h]
  simp only [duoFlow, WithLp.ofLp_toLp, ite_false, show (Duo.a = Duo.b) = False by simp] at h2
  have := Real.exp_eq_exp.mp h2
  norm_num at this

/-- The Phase 8 link, applied: `entropy_production_rate` is non-increasing along
    this concrete flow. -/
example : Antitone (fun t => entropy_production_rate (duoSys.withKernel (duoFlow t)) duoTheta) :=
  entropy_production_antitone_of_gradient_flow duo_volume duoSys duoTheta duoFlow
    duoFlow_hasDerivAt

/-- And here the descent is strict, so `Antitone` is not being satisfied by a
    constant. -/
example : StrictAnti (fun t => sigmaOfKernel duoSys duoTheta (duoFlow t)) := by
  intro a b hab
  simp only [sigma_duoFlow, ← Real.exp_nat_mul]
  exact Real.exp_lt_exp.mpr (by push_cast; linarith)


/-! ## 6. A refining sequence of triangulations of `[0,1)`

`Phase2_MeshConvergence.mesh_refinement_convergence` proves that the discrete energy of a
sequence of `IsRegularTriangulation`s converges to the continuous energy. That is worth
nothing if `IsRegularTriangulation` cannot be inhabited — and its conditions do pull against
each other: the cells must be pairwise **disjoint** yet **cover** the region, while every
vertex must be **anchored** to each of its edges' regions. A vertex shared by two cells can
belong to at most one of them, which is exactly why `anchored` is stated with `closure`.

This section discharges the obligation with the uniform partition of `[0,1)` into `N`
half-open cells `[i/N, (i+1)/N)` on `N+1` vertices embedded at `i/N`, and then runs the
convergence theorem on it. The witness is checked to be non-degenerate in three ways:

* cells have measure `1/N`, so they are not empty (`gridCell_measure`);
* the mesh really shrinks — `m n = 1/(n+1) → 0`, not `0` from the start;
* the approximations really move: for the tent function `x ↦ |x - ½|` the discrete energy
  is `1/2` at `N = 1` and `1/4` at `N = 2`, so the limit is not being reached by a constant
  sequence (`tent_energy_one`, `tent_energy_two`).

The triangulation is one-dimensional. Nothing here witnesses the manifold-valued case of
`DiscreteThermodynamics`, whose edge weights integrate a stress-energy magnitude over a
genuinely 2- or 3-dimensional region.
-/


/-- The `i`-th cell of the uniform partition of `[0,1)` into `N` pieces. -/
def gridCell (N i : ℕ) : Set ℝ := Set.Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N)

/-- Faces: sets of pairwise-consecutive vertices. -/
def gridComplex (N : ℕ) : AbstractSimplicialComplex (Fin (N + 1)) where
  faces := {s | ∀ a ∈ s, ∀ b ∈ s, (a : ℕ) ≤ (b : ℕ) + 1 ∧ (b : ℕ) ≤ (a : ℕ) + 1}
  downward_closed := fun hs hts a ha b hb => hs a (hts ha) b (hts hb)

/-- The uniform triangulation of `[0,1)` by `N` cells and `N+1` vertices. -/
@[reducible] noncomputable def gridTriangulation (N : ℕ) : TriangulatedManifold ℝ where
  V := Fin (N + 1)
  complex := gridComplex N
  embedding := fun i => (i : ℕ) / N
  edge_region := fun u v =>
    if (u : ℕ) + 1 = (v : ℕ) then gridCell N u
    else if (v : ℕ) + 1 = (u : ℕ) then gridCell N v
    else ∅
  edge_region_symm := by
    intro u v
    split_ifs <;> first | rfl | omega

@[simp] theorem gridV (N : ℕ) : (gridTriangulation N).V = Fin (N + 1) := rfl

instance instFintypeGridV (N : ℕ) : Fintype (gridTriangulation N).V :=
  (inferInstance : Fintype (Fin (N + 1)))

instance instLinearOrderGridV (N : ℕ) : LinearOrder (gridTriangulation N).V :=
  (inferInstance : LinearOrder (Fin (N + 1)))

theorem gridCell_subset (N i : ℕ) (h : i + 1 ≤ N) : gridCell N i ⊆ Set.Ico (0:ℝ) 1 := by
  have hN : (0:ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  intro x hx
  rw [gridCell, Set.mem_Ico] at hx
  rw [Set.mem_Ico]
  constructor
  · refine le_trans ?_ hx.1
    positivity
  · refine lt_of_lt_of_le hx.2 ?_
    rw [div_le_one hN]
    exact_mod_cast h

theorem gridCell_dist (N i : ℕ) {x y : ℝ} (hx : x ∈ gridCell N i) (hy : y ∈ gridCell N i) :
    dist x y ≤ 1 / N := by
  rw [gridCell, Set.mem_Ico] at hx hy
  have h := Real.dist_le_of_mem_Icc (x := x) (y := y)
    ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩
  refine h.trans (le_of_eq ?_)
  ring

@[simp] theorem grid_edge_region (N : ℕ) (u v : Fin (N + 1)) :
    (gridTriangulation N).edge_region u v =
      if (u : ℕ) + 1 = (v : ℕ) then gridCell N u
      else if (v : ℕ) + 1 = (u : ℕ) then gridCell N v else ∅ := rfl

@[simp] theorem grid_embedding (N : ℕ) (u : Fin (N + 1)) :
    (gridTriangulation N).embedding u = (u : ℕ) / N := rfl

theorem gridCell_disjoint (N : ℕ) (hN : 0 < N) {i j : ℕ} (h : i ≠ j) :
    Disjoint (gridCell N i) (gridCell N j) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [gridCell, gridCell, Set.Ico_disjoint_Ico]
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 : ((i : ℝ) + 1) / N ≤ (j : ℝ) / N := by
      refine (div_le_div_iff_of_pos_right hNR).2 ?_
      exact_mod_cast hlt
    calc min (((i : ℝ) + 1) / N) (((j : ℝ) + 1) / N) ≤ ((i : ℝ) + 1) / N := min_le_left _ _
      _ ≤ (j : ℝ) / N := h1
      _ ≤ max ((i : ℝ) / N) ((j : ℝ) / N) := le_max_right _ _
  · have h1 : ((j : ℝ) + 1) / N ≤ (i : ℝ) / N := by
      refine (div_le_div_iff_of_pos_right hNR).2 ?_
      exact_mod_cast hlt
    calc min (((i : ℝ) + 1) / N) (((j : ℝ) + 1) / N) ≤ ((j : ℝ) + 1) / N := min_le_right _ _
      _ ≤ (i : ℝ) / N := h1
      _ ≤ max ((i : ℝ) / N) ((j : ℝ) / N) := le_max_left _ _

theorem grid_edge_region_lt (N : ℕ) {u v : Fin (N + 1)} (h : u < v) :
    (gridTriangulation N).edge_region u v =
      if (u : ℕ) + 1 = (v : ℕ) then gridCell N u else ∅ := by
  rw [grid_edge_region]
  have hvu : ¬((v : ℕ) + 1 = (u : ℕ)) := by
    rw [Fin.lt_def] at h; omega
  split_ifs <;> rfl

theorem gridRegular (N : ℕ) (hN : 0 < N) :
    IsRegularTriangulation (gridTriangulation N) (Set.Ico (0:ℝ) 1) where
  measurable_region := by
    intro u v
    rw [grid_edge_region]
    split_ifs <;> simp [gridCell]
  no_self_region := by
    intro u
    rw [grid_edge_region]
    split_ifs <;> first | rfl | omega
  face_of_complex := by
    intro u v hne
    have hcond : (u : Fin (N + 1)).val + 1 = (v : Fin (N + 1)).val ∨
        (v : Fin (N + 1)).val + 1 = (u : Fin (N + 1)).val := by
      by_contra hc
      rw [not_or] at hc
      rw [grid_edge_region] at hne
      split_ifs at hne with h1 h2
      · exact hc.1 h1
      · exact hc.2 h2
      · exact Set.not_nonempty_empty hne
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega
  anchored := by
    intro u v hne
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    rw [grid_edge_region] at hne ⊢
    split_ifs at hne ⊢ with h1 h2
    · rw [gridCell, closure_Ico (by intro hc; rw [div_eq_div_iff hNR.ne' hNR.ne'] at hc; linarith)]
      rw [grid_embedding, Set.mem_Icc]
      constructor
      · exact le_refl _
      · gcongr
        linarith
    · rw [gridCell, closure_Ico (by intro hc; rw [div_eq_div_iff hNR.ne' hNR.ne'] at hc; linarith)]
      rw [grid_embedding, Set.mem_Icc]
      have : ((u : Fin (N + 1)).val : ℝ) = ((v : Fin (N + 1)).val : ℝ) + 1 := by
        exact_mod_cast h2.symm
      rw [this]
      constructor
      · gcongr
        linarith
      · exact le_refl _
    · exact absurd hne Set.not_nonempty_empty
  disjoint_region := by
    intro u v u' v' huv huv' hne
    rw [grid_edge_region_lt N huv, grid_edge_region_lt N huv']
    split_ifs with h1 h2 h3
    · refine gridCell_disjoint N hN ?_
      intro hc
      refine hne ?_
      have huu : (u : Fin (N + 1)) = u' := Fin.ext hc
      have hvv : (v : Fin (N + 1)) = v' := Fin.ext (by omega)
      rw [huu, hvv]
    · exact Set.disjoint_empty _
    · exact Set.empty_disjoint _
    · exact Set.empty_disjoint _
  covers := by
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · refine Set.iUnion_subset fun u => Set.iUnion_subset fun v => ?_
      rw [grid_edge_region]
      split_ifs with h1 h2
      · exact gridCell_subset N _ (by have := (v : Fin (N + 1)).isLt; omega)
      · exact gridCell_subset N _ (by have := (u : Fin (N + 1)).isLt; omega)
      · exact Set.empty_subset _
    · rw [Set.mem_Ico] at hx
      have hxN : 0 ≤ x * N := mul_nonneg hx.1 (le_of_lt hNR)
      have h1 : (⌊x * N⌋₊ : ℝ) ≤ x * N := Nat.floor_le hxN
      have h2 : x * N < ⌊x * N⌋₊ + 1 := Nat.lt_floor_add_one _
      have hiN : ⌊x * N⌋₊ < N := by
        refine (Nat.floor_lt hxN).2 ?_
        calc x * N < 1 * N := by exact mul_lt_mul_of_pos_right hx.2 hNR
          _ = N := one_mul _
      refine Set.mem_iUnion.2 ⟨(⟨⌊x * N⌋₊, by omega⟩ : Fin (N + 1)),
        Set.mem_iUnion.2 ⟨(⟨⌊x * N⌋₊ + 1, by omega⟩ : Fin (N + 1)), ?_⟩⟩
      rw [grid_edge_region]
      split_ifs with h3 h4
      · rw [gridCell, Set.mem_Ico]
        refine ⟨(div_le_iff₀ hNR).2 ?_, (lt_div_iff₀ hNR).2 ?_⟩
        · exact h1
        · exact h2
      · simp at h3
      · simp at h3

theorem grid_fine (N : ℕ) (u v : Fin (N + 1)) {x y : ℝ}
    (hx : x ∈ (gridTriangulation N).edge_region u v)
    (hy : y ∈ (gridTriangulation N).edge_region u v) : dist x y ≤ 1 / N := by
  rw [grid_edge_region] at hx hy
  split_ifs at hx hy with h1 h2
  · exact gridCell_dist N _ hx hy
  · exact gridCell_dist N _ hx hy
  · exact absurd hx (Set.notMem_empty x)

theorem grid_mesh_refinement (f : ℝ → ℝ) (hf : UniformContinuous f) :
    Tendsto (fun n : ℕ => discreteEnergy (gridTriangulation (n + 1)) volume f) atTop
      (𝓝 (∫ x in Set.Ico (0:ℝ) 1, f x)) := by
  have hint : IntegrableOn f (Set.Ico (0:ℝ) 1) volume :=
    (hf.continuous.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self
  refine mesh_refinement_convergence volume f hf (by simp) hint
    (fun n => gridTriangulation (n + 1)) (fun n => gridRegular (n + 1) n.succ_pos)
    (fun n => 1 / ((n : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat ?_
  intro n u v x hx y hy
  have h := grid_fine (n + 1) u v hx hy
  push_cast at h
  exact h

/-- Cells are non-degenerate: each has measure `1/N`. -/
theorem gridCell_measure (N : ℕ) (hN : 0 < N) (i : ℕ) :
    volume.real (gridCell N i) = 1 / N := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [gridCell, Real.volume_real_Ico_of_le (by gcongr; linarith)]
  field_simp
  ring

/-- The tent function `x ↦ |x - ½|`, Lipschitz hence uniformly continuous. -/
theorem tent_uniformContinuous : UniformContinuous (fun x : ℝ => |x - 1/2|) := by
  have h : (fun x : ℝ => |x - 1/2|) = fun x : ℝ => dist x (1/2) := by
    funext x; rw [Real.dist_eq]
  rw [h]
  exact (LipschitzWith.dist_left (1/2 : ℝ)).uniformContinuous

example : Tendsto
    (fun n : ℕ => discreteEnergy (gridTriangulation (n + 1)) volume (fun x => |x - 1/2|))
    atTop (𝓝 (∫ x in Set.Ico (0:ℝ) 1, |x - 1/2|)) :=
  grid_mesh_refinement _ tent_uniformContinuous

theorem tent_energy_one :
    discreteEnergy (gridTriangulation 1) volume (fun x => |x - 1/2|) = 1/2 := by
  simp [discreteEnergy, Fin.sum_univ_two, grid_edge_region, grid_embedding, gridCell]
  norm_num

theorem tent_energy_two :
    discreteEnergy (gridTriangulation 2) volume (fun x => |x - 1/2|) = 1/4 := by
  simp [discreteEnergy, Fin.sum_univ_three, grid_edge_region, grid_embedding, gridCell]
  norm_num

/-- The approximations genuinely move: refining the mesh changes the answer, so the
convergence above is not the trivial convergence of a constant sequence. -/
example : discreteEnergy (gridTriangulation 1) volume (fun x => |x - 1/2|)
    ≠ discreteEnergy (gridTriangulation 2) volume (fun x => |x - 1/2|) := by
  rw [tent_energy_one, tent_energy_two]
  norm_num

/-! ## 7. The rotating-frame reduction on a two-oscillator system

`Phase4_RotatingFrame` chains the two Kuramoto potentials, but only for systems
whose natural frequencies are identical, and only at configurations that
minimise the dynamic potential. Both are real restrictions, so the chain is
worth nothing unless something satisfies them. This section exhibits a system
that does, and — on the other side — a system for which the full potential
provably has no minimum at all, which is what forced the reduction in the first
place. -/

/-- Two oscillators, unit coupling, common natural frequency `Ω`. -/
noncomputable def pairSystem (Ω : ℝ) : KuramotoSystem Bool where
  omega := fun _ => Ω
  A := fun _ _ => 1
  symm := fun _ _ => rfl

/-- The fully synchronized trajectory: both phases advance at the common
frequency. -/
noncomputable def pairTrajectory (Ω : ℝ) : ℝ → Bool → ℝ := fun t _ => Ω * t

theorem pairTrajectory_is_trajectory (Ω : ℝ) :
    is_kuramoto_trajectory (pairSystem Ω) (pairTrajectory Ω) := by
  intro i t
  have h : HasDerivAt (fun t : ℝ => Ω * t) Ω t := by
    simpa using (hasDerivAt_id t).const_mul Ω
  have hval : (pairSystem Ω).omega i
      + ∑ j, (pairSystem Ω).A i j
          * Real.sin (pairTrajectory Ω t j - pairTrajectory Ω t i) = Ω := by
    simp [pairSystem, pairTrajectory]
  rw [hval]
  exact h

/-- In the rotating frame the trajectory sits at the origin — where
`phase_locked_minimizes_potential` says the dynamic potential is minimised. -/
theorem rotate_pairTrajectory (Ω : ℝ) (t : ℝ) :
    rotate Ω (pairTrajectory Ω) t = fun _ => 0 := by
  funext i
  simp [rotate, pairTrajectory]

/-- **The chain fires.** Every hypothesis of `rotating_frame_chain` is
discharged concretely: the rotated trajectory solves the zero-frequency
equations, the dynamic potential is non-increasing along it, the original
phases are locked, and the order parameter is `1`. -/
theorem pair_rotating_frame_chain (Ω : ℝ) (t : ℝ) :
    is_kuramoto_trajectory (pairSystem Ω).reduced (rotate Ω (pairTrajectory Ω))
      ∧ deriv (fun t => kuramoto_potential_dynamic (pairSystem Ω)
            (rotate Ω (pairTrajectory Ω) t)) t ≤ 0
      ∧ is_phase_locked (pairTrajectory Ω t)
      ∧ order_parameter_r_sq (pairTrajectory Ω t) = 1 := by
  refine rotating_frame_chain (pairSystem Ω) Ω (fun _ => rfl) (fun _ _ => by
    simp [pairSystem]) (pairTrajectory Ω) (pairTrajectory_is_trajectory Ω) t ?_
  intro phi
  rw [rotate_pairTrajectory]
  exact phase_locked_minimizes_potential (pairSystem Ω) (fun _ _ => by
    simp [pairSystem]) phi

/-- The full potential really is non-constant along the reduction: at the
synchronized configuration it differs from its value at the origin exactly by
the frequency term. -/
example (Ω : ℝ) (t : ℝ) :
    kuramoto_potential (pairSystem Ω) (pairTrajectory Ω t)
      = kuramoto_potential_dynamic (pairSystem Ω) (rotate Ω (pairTrajectory Ω) t)
        - 2 * Ω * (Ω * t) := by
  rw [kuramoto_potential_eq_dynamic_sub, rotate_pairTrajectory]
  simp [kuramoto_potential_dynamic, pairSystem, pairTrajectory]
  ring

/-- **The other side.** With a non-zero natural frequency the full Kuramoto
potential is unbounded below, so "the phase-locked state minimises the Lyapunov
potential" is false of it — there is no minimum to attain. The hypothesis of
`kuramoto_potential_unbounded_below` is satisfiable. -/
example (C : ℝ) : ∃ theta : Bool → ℝ, kuramoto_potential (pairSystem 1) theta < C :=
  kuramoto_potential_unbounded_below (pairSystem 1) ⟨true, by simp [pairSystem]⟩ C

end Examples
end PhysicsOfConsciousness
