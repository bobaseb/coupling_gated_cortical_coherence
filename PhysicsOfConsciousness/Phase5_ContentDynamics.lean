import PhysicsOfConsciousness.Phase4_MacroscopicScaling

/-!
# Observation-driven local content foundations

Local contents are real-valued fields on a declared cover. Each update mixes a
local field with that patch's observation. Compatible observations contract
disagreement; incompatible observations contribute an explicit residual.
Coverage and exact agreement make a declared patch-selecting readout the unique
global field extending the patches. Approximate agreement yields a readout
error bound, not exact gluing.

These scalar contents are not identified with neural variables or the existing
probability sheaf. Observation compatibility is an input; no theorem here
infers it from task reward, phase coherence or a shared global target state.
The module is deliberately upstream of `Phase5_GlobalSection`: it uses nothing
from the sheaf, and that section's mass-profile agreement is an instance of the
predicate below rather than the other way round.
-/

namespace PhysicsOfConsciousness.LocalContent

variable {I A : Type*}

/-- Pointwise mismatch bound on every overlap, on any index and site types.
Contents may be signed. `ApproximateGluing.compatible_pointwise`
(`Phase5_GlobalSection`) reads the finite nonnegative mass profiles of that
section as such a family, so this is the weaker predicate of the two. -/
def Compatible (U : I → Set A) (s : I → A → ℝ) (ε : ℝ) : Prop :=
  ∀ i j x, x ∈ U i → x ∈ U j → |s i x - s j x| ≤ ε

/-- The observation is the only driving input to the content update. -/
noncomputable def update (η : ℝ) (o s : I → A → ℝ) : I → A → ℝ :=
  fun i x => (1 - η) * s i x + η * o i x

/-- A noisy observation contributes its own overlap residual. Contractive gain
is a declared update rule, not a derived cortical learning mechanism. -/
theorem update_residual (U : I → Set A) (s o : I → A → ℝ) (ε δ η : ℝ)
    (hη : 0 ≤ η) (hη' : η ≤ 1) (hs : Compatible U s ε) (ho : Compatible U o δ) :
    Compatible U (update η o s) ((1 - η) * ε + η * δ) := by
  intro i j x hi hj
  have heq : update η o s i x - update η o s j x =
      (1 - η) * (s i x - s j x) + η * (o i x - o j x) := by
    unfold update
    ring
  rw [heq]
  calc
    _ ≤ |(1 - η) * (s i x - s j x)| + |η * (o i x - o j x)| := abs_add_le _ _
    _ = (1 - η) * |s i x - s j x| + η * |o i x - o j x| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hη'), abs_of_nonneg hη]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (hs i j x hi hj) (sub_nonneg.mpr hη'))
      (mul_le_mul_of_nonneg_left (ho i j x hi hj) hη)

/-- Exact agreement is preserved by compatible observations. The premise on
observations must be obtained from their own sensor model. -/
theorem update_preserves (U : I → Set A) (s o : I → A → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (hη' : η ≤ 1) (hs : Compatible U s 0) (ho : Compatible U o 0) :
    Compatible U (update η o s) 0 := by
  simpa only [mul_zero, add_zero] using update_residual U s o 0 0 η hη hη' hs ho

/-- Evolve contents through the actual successive observations. -/
noncomputable def run (η : ℝ) (o : ℕ → I → A → ℝ) (s : I → A → ℝ) : ℕ → I → A → ℝ
  | 0 => s
  | n + 1 => update η (o n) (run η o s n)

/-- Compatible observations shrink the initial overlap residual geometrically,
even when the common observed value changes over time. It is a conditional
stability result, not convergence to a fixed external content. -/
theorem run_residual (U : I → Set A) (s : I → A → ℝ) (o : ℕ → I → A → ℝ)
    (ε η : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1) (hs : Compatible U s ε)
    (ho : ∀ n, Compatible U (o n) 0) (n : ℕ) :
    Compatible U (run η o s n) ((1 - η) ^ n * ε) := by
  induction n with
  | zero => simpa only [run, pow_zero, one_mul] using hs
  | succ n ih =>
    have h := update_residual U (run η o s n) (o n) ((1 - η) ^ n * ε)
      0 η hη hη' ih (ho n)
    convert h using 1 <;> simp only [run, mul_zero, add_zero, pow_succ]
    ring

/-- A readout declares which patch to read at each site. Coverage is checked by
theorems, rather than hidden in a choice of a pre-existing global content. -/
noncomputable def readout (choose : A → I) (s : I → A → ℝ) : A → ℝ :=
  fun x => s (choose x) x

/-- Approximate agreement controls any readout that actually selects a covering
patch. It does not make that readout an exact extension. -/
theorem readout_residual (U : I → Set A) (choose : A → I) (s : I → A → ℝ) (ε : ℝ)
    (hc : ∀ x, x ∈ U (choose x)) (hs : Compatible U s ε) (i : I) (x : A)
    (hx : x ∈ U i) : |readout choose s x - s i x| ≤ ε :=
  hs (choose x) i x (hc x) hx

/-- At zero residual, the declared readout extends every patch. This is gluing
of scalar fields; it does not supply the manuscript's probability-sheaf bridge. -/
theorem readout_agrees (U : I → Set A) (choose : A → I) (s : I → A → ℝ)
    (hc : ∀ x, x ∈ U (choose x)) (hs : Compatible U s 0) (i : I) (x : A)
    (hx : x ∈ U i) : readout choose s x = s i x := by
  have h := readout_residual U choose s 0 hc hs i x hx
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- Any global extension is this readout, because the chosen patch covers each
site. Existence requires agreement, provided separately by `readout_agrees`. -/
theorem readout_unique (U : I → Set A) (choose : A → I) (s : I → A → ℝ)
    (hc : ∀ x, x ∈ U (choose x)) (f : A → ℝ)
    (hf : ∀ i x, x ∈ U i → f x = s i x) : f = readout choose s := by
  funext x
  exact hf (choose x) x (hc x)

#print axioms update_residual
#print axioms run_residual
#print axioms readout_agrees
#print axioms readout_unique

end PhysicsOfConsciousness.LocalContent
