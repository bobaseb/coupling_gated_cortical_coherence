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


/-! ## Where the observations' own agreement comes from

Everything above takes `Compatible U o δ` as an input. That input is the whole
of the acquire problem: contents that are *given* agreeing observations preserve
agreement, but nothing so far says why two patches should observe compatibly at
all.

This section answers it from coherence. Observations are a declared Lipschitz
function of the local phase, read as a point of the circle; the population's
order parameter then bounds their overlap disagreement, with no compatibility
assumed anywhere. The chain is `cos_gap_le_of_coherence` →
`chord_le_of_coherence` → `compatible_of_coherence` → `update_residual`.

**What is still declared and what is not.** The encoder and its Lipschitz
constant are declared hardware, as the coupling-side actuator's mode profiles
are. What is no longer declared is the *agreement*: it is a theorem about the
phases, and at `r² = 1` it is exact. What this does not do is identify these
scalar contents with any neural variable or with a section of the probability
sheaf; that identification is empirical and is not attempted here. -/

/-- An encoder from circle points to scalar content, with a declared Lipschitz
constant in the chord metric. Phrased on `circlePoint` rather than on `ℝ`, so
that an encoder is automatically a function of the phase and not of a
representative of it. -/
def LipschitzEncoder (e : ℝ × ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ a b : ℝ, |e (circlePoint a) - e (circlePoint b)| ≤ L * chord a b

/-- **Coherence produces observation agreement.** Observations that are a
declared Lipschitz function of each patch's local phase are compatible on every
overlap, at a residual fixed by the population's order parameter alone.

This is the acquire half. No premise of the form `Compatible U o δ` appears:
the residual is computed from the phases. The `N` is inherited from
`cos_gap_le_of_coherence` and is the price of a pointwise guarantee drawn from
a global mean. -/
theorem compatible_of_coherence {V : Type*} [Fintype V] [Nonempty V]
    (U : I → Set A) (patch : I → V) (theta : V → ℝ) (e : ℝ × ℝ → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (he : LipschitzEncoder e L) :
    Compatible U (fun i _ => e (circlePoint (theta (patch i))))
      (L * (Real.sqrt 2 * (Fintype.card V : ℝ) *
        Real.sqrt (1 - order_parameter_r_sq theta))) := by
  intro i j _ _ _
  exact (he _ _).trans
    (mul_le_mul_of_nonneg_left (chord_le_of_coherence theta (patch i) (patch j)) hL)

/-- At perfect locking the derived residual is exactly zero, so the observations
glue and `readout_agrees` applies to what they drive. The quantitative bound has
the exact case as its endpoint rather than as a separate hypothesis. -/
theorem compatible_of_phase_locked {V : Type*} [Fintype V] [Nonempty V]
    (U : I → Set A) (patch : I → V) (theta : V → ℝ) (e : ℝ × ℝ → ℝ) (L : ℝ)
    (he : LipschitzEncoder e L) (hlock : is_phase_locked theta) :
    Compatible U (fun i _ => e (circlePoint (theta (patch i)))) 0 := by
  intro i j _ _ _
  have h := he (theta (patch i)) (theta (patch j))
  rw [chord_eq_zero_of_phase_locked theta hlock, mul_zero] at h
  exact h

/-- **The residual floor.** `run_residual` needs observations that agree
exactly; coherence below one gives observations that agree to `δ`. Iterating the
update then contracts the initial mismatch geometrically onto that floor, and
the arithmetic is exact rather than an estimate: `(1-η)((1-η)^n ε + δ) + ηδ`
is `(1-η)^(n+1) ε + δ`.

The floor does not decay. An agent whose observations disagree by `δ` cannot be
driven to exact agreement by mixing them, however long it runs — which is why
the coherence bound, and not the update rule, is what carries this result. -/
theorem run_residual_floor (U : I → Set A) (s : I → A → ℝ) (o : ℕ → I → A → ℝ)
    (ε δ η : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1) (hδ : 0 ≤ δ) (hs : Compatible U s ε)
    (ho : ∀ n, Compatible U (o n) δ) (n : ℕ) :
    Compatible U (run η o s n) ((1 - η) ^ n * ε + δ) := by
  induction n with
  | zero =>
    intro i j x hi hj
    have h := hs i j x hi hj
    simp only [run, pow_zero, one_mul]
    linarith
  | succ n ih =>
    have h := update_residual U (run η o s n) (o n) ((1 - η) ^ n * ε + δ) δ η hη hη' ih (ho n)
    have heq : (1 - η) * ((1 - η) ^ n * ε + δ) + η * δ = (1 - η) ^ (n + 1) * ε + δ := by
      rw [pow_succ]; ring
    rw [heq] at h
    exact h

/-- The acquire and preserve halves in one statement: contents driven by
observations from a coherent population contract onto a floor set by the order
parameter, with nothing about the observations assumed. -/
theorem run_residual_of_coherence {V : Type*} [Fintype V] [Nonempty V]
    (U : I → Set A) (patch : I → V) (theta : ℕ → V → ℝ) (e : ℝ × ℝ → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (he : LipschitzEncoder e L)
    (s : I → A → ℝ) (ε η δ : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1)
    (hs : Compatible U s ε)
    (hδ : ∀ n, L * (Real.sqrt 2 * (Fintype.card V : ℝ) *
      Real.sqrt (1 - order_parameter_r_sq (theta n))) ≤ δ) (n : ℕ) :
    Compatible U
      (run η (fun n i _ => e (circlePoint (theta n (patch i)))) s n)
      ((1 - η) ^ n * ε + δ) := by
  have hnn : (0 : ℝ) ≤ L * (Real.sqrt 2 * (Fintype.card V : ℝ) *
      Real.sqrt (1 - order_parameter_r_sq (theta 0))) :=
    mul_nonneg hL (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Nat.cast_nonneg _))
      (Real.sqrt_nonneg _))
  exact run_residual_floor U s _ ε δ η hη hη' (hnn.trans (hδ 0)) hs
    (fun m i j x hi hj =>
      (compatible_of_coherence U patch (theta m) e L hL he i j x hi hj).trans (hδ m)) n

#print axioms update_residual
#print axioms run_residual
#print axioms readout_agrees
#print axioms readout_unique
#print axioms compatible_of_coherence
#print axioms run_residual_floor
#print axioms run_residual_of_coherence

end PhysicsOfConsciousness.LocalContent
