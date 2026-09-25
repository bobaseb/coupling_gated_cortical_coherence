import Mathlib

/-!
# Phase 10 — a relative-phase encoder is blind to travelling waves and windings

The chaining bound through overlapping patches is attained by a phase gradient:
an encoder that reads each site's *absolute* phase reports contents that drift
apart linearly along a travelling wave, and on a ring a winding forces two sites
to disagree however strong the coupling. Neither configuration is a failure of
agreement between the local descriptions if each description reads phase
relative to its own neighbourhood. This module states that encoder and proves
what it buys.

* **Sites and phases.** Sites form an additive group `G` (a lattice `ℤ²`, a
  torus `ZMod m × ZMod m`, a ring `ZMod m`), phases an additive group `P` (`ℝ`,
  or the circle `AddCircle`, where a winding lives).
* **`relRead θ e x`.** The phases of the stencil `x + e s` relative to `x`'s
  own. An encoder is *relative* when it reads content through `relRead` only.
* **`IsWave θ`.** A plane wave: a constant plus an additive map `G →+ P`.
  Travelling waves, uniform gradients and, on a torus or ring, windings all have
  this form.

The results:

* **`relRead_wave`.** On a plane wave the relative reading is the same at every
  site, so every relative encoder reports one content everywhere
  (`relContent_eq_of_wave`): the gradient, and a winding, cost nothing.
* **`dist_relContent_le`.** For a plane wave plus a departure `η`, a Lipschitz
  relative encoder's discrepancy between any two sites is bounded by the
  departure's own relative readings at those two sites. The bound involves
  neither the wave's gradient nor the distance between the sites.

The absolute encoder has neither property; the contrast, a winding on a ring of
sites on which the absolute reading is injective and the relative reading
constant, is `Examples/RelativePhase.lean`.
-/

namespace PhysicsOfConsciousness.PhysicalUnity

variable {G σ : Type*} [AddCommGroup G]

section Group

variable {P : Type*} [AddCommGroup P]

/-- The phases of the stencil `x + e s`, relative to the phase at `x`. -/
def relRead (θ : G → P) (e : σ → G) (x : G) : σ → P := fun s => θ (x + e s) - θ x

/-- A plane wave: a constant phase plus an additive map of the sites. -/
def IsWave (θ : G → P) : Prop := ∃ (c : P) (k : G →+ P), ∀ x, θ x = c + k x

/-- **A plane wave reads the same everywhere.** Its relative reading at any site
is the wave's own increment along the stencil. -/
theorem relRead_wave {θ : G → P} {c : P} {k : G →+ P} (hθ : ∀ x, θ x = c + k x)
    (e : σ → G) (x : G) : relRead θ e x = fun s => k (e s) := by
  funext s
  simp only [relRead, hθ, map_add]
  abel

/-- **A relative encoder agrees with itself across a plane wave.** Whatever the
wave's gradient or winding, and however far apart the sites, a content read
through the relative reading is the same at every site. -/
theorem relContent_eq_of_wave {Y : Type*} {θ : G → P} (hθ : IsWave θ) (e : σ → G)
    (Ψ : (σ → P) → Y) (x y : G) : Ψ (relRead θ e x) = Ψ (relRead θ e y) := by
  obtain ⟨c, k, hθ⟩ := hθ
  rw [relRead_wave hθ, relRead_wave hθ]

/-- The relative reading of a sum is the sum of the relative readings. -/
theorem relRead_add (θ η : G → P) (e : σ → G) (x : G) :
    relRead (θ + η) e x = relRead θ e x + relRead η e x := by
  funext s
  simp only [relRead, Pi.add_apply]
  abel

end Group

/-- **Discrepancy is set by the departure from a wave, not by the wave.** Let
the phase field be a plane wave plus a departure `η`, and let the relative
encoder be `L`-Lipschitz for the sup distance on stencil readings. The contents
at any two sites differ by at most `L` times the sum of the departure's relative
readings there. Neither the gradient of the wave nor the separation of the two
sites enters. -/
theorem dist_relContent_le {P : Type*} [SeminormedAddCommGroup P] [Fintype σ]
    {Y : Type*} [PseudoMetricSpace Y] {θ η : G → P} (hθ : IsWave θ) (e : σ → G)
    {Ψ : (σ → P) → Y} {L : NNReal} (hΨ : LipschitzWith L Ψ) (x y : G) :
    dist (Ψ (relRead (θ + η) e x)) (Ψ (relRead (θ + η) e y)) ≤
      L * (‖relRead η e x‖ + ‖relRead η e y‖) := by
  obtain ⟨c, k, hθ⟩ := hθ
  refine (hΨ.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
  rw [relRead_add, relRead_add, relRead_wave hθ, relRead_wave hθ, dist_eq_norm,
    add_sub_add_left_eq_sub]
  exact norm_sub_le _ _

end PhysicsOfConsciousness.PhysicalUnity
