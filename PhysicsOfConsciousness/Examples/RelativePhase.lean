import PhysicsOfConsciousness.Phase10_RelativePhase

/-!
# Examples/RelativePhase.lean — a winding separates the two encoders

§40. A ring of `m` sites, `ZMod m`, with phases on the unit circle.

* **A winding.** Site `x` carries phase `x / m`, once round the circle over the
  ring (`ZMod.toAddCircle`). It is a plane wave in the sense of `IsWave`.
* **The absolute encoder disagrees everywhere.** Reading each site's own phase
  gives distinct contents at every pair of distinct sites, because the winding
  is injective. No coupling strength changes this: the winding is topological.
* **The relative encoder agrees everywhere.** Reading the phase of the next
  site relative to one's own gives the same content, `1 / m`, at every site.

And on the line `ℤ` with real phases, a uniform gradient `δ x` makes the
absolute discrepancy between sites `x` and `y` equal to `|δ| |x − y|`, growing
without bound, while the relative reading is `δ` everywhere.
-/

namespace PhysicsOfConsciousness.PhysicalUnity.Examples

section Ring

variable {m : ℕ} [NeZero m]

/-- One winding round the unit circle over a ring of `m` sites. -/
noncomputable def winding : ZMod m → UnitAddCircle := ZMod.toAddCircle

theorem winding_isWave : IsWave (winding (m := m)) := ⟨0, ZMod.toAddCircle, fun x => by simp [winding]⟩

/-- The absolute encoder reports different contents at any two distinct sites. -/
theorem winding_absolute_ne {x y : ZMod m} (hxy : x ≠ y) : winding x ≠ winding y := by
  simpa [winding] using hxy

/-- The relative encoder, reading the next site, reports one content at every
site. -/
theorem winding_relative_eq (x y : ZMod m) :
    relRead winding (fun _ : Unit => (1 : ZMod m)) x =
      relRead winding (fun _ : Unit => (1 : ZMod m)) y := by
  obtain ⟨c, k, hθ⟩ := winding_isWave (m := m)
  rw [relRead_wave hθ, relRead_wave hθ]

end Ring

/-- A uniform gradient of slope `δ` on the line. -/
def gradient (δ : ℝ) (x : ℤ) : ℝ := δ * x

theorem gradient_isWave (δ : ℝ) : IsWave (gradient δ) :=
  ⟨0, (AddMonoidHom.mulLeft δ).comp (Int.castAddHom ℝ), fun x => by simp [gradient]⟩

/-- The absolute discrepancy along a gradient grows linearly with separation. -/
theorem gradient_absolute_dist (δ : ℝ) (x y : ℤ) :
    dist (gradient δ x) (gradient δ y) = |δ| * |(x : ℝ) - y| := by
  rw [Real.dist_eq, gradient, gradient, ← mul_sub, abs_mul]

/-- The relative reading along a gradient is the slope, at every site. -/
theorem gradient_relative (δ : ℝ) (x : ℤ) :
    relRead (gradient δ) (fun _ : Unit => (1 : ℤ)) x = fun _ => δ := by
  funext s
  simp [relRead, gradient]; ring

end PhysicsOfConsciousness.PhysicalUnity.Examples
