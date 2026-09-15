import PhysicsOfConsciousness.Phase3_ResourceFoundations
import PhysicsOfConsciousness.Phase3_SupportedThermodynamics
import PhysicsOfConsciousness.Phase5_ContentDynamics
import PhysicsOfConsciousness.Examples.ContinuingLimit

/-!
# Regression specifications for the agency foundations

These specifications were run before the named foundations existed. Concrete
resource, support and content witnesses are added below during implementation.
This is a Lean-only handoff; no cortical or optimal-control identification is made.
-/

namespace PhysicsOfConsciousness.Examples.AgencyFoundations

example {S : Type*} (s : ℕ → S) (B : S → ℝ) (d u : ℕ → ℝ) (N : ℕ)
    (h : ∀ n < N, B (s (n + 1)) = B (s n) - d n + u n) :
    B (s N) = B (s 0) - ∑ n ∈ Finset.range N, d n + ∑ n ∈ Finset.range N, u n :=
  ResourceTrajectory.balance_sum s B d u N h

example (n : ℕ) : ResourceTrajectory.transferCharge (n, 0) = (0, n) :=
  ResourceTrajectory.transferCharge_sharp n

example {V : Type*} [Fintype V] (P Q : ProbDist V)
    (h : ProbDist.SupportIncluded P Q) : 0 ≤ KL P Q :=
  KL_nonneg_of_support P Q h

example {V : Type*} [Fintype V] (P Q : ProbDist V) (v : V)
    (hp : 0 < P.p v) (hq : Q.p v = 0) : ProbDist.extendedKL P Q = ⊤ :=
  ProbDist.extendedKL_top_of_missing P Q v hp hq

example {X S : Type*} [Fintype X] [Fintype S] (M : FiniteFeedbackStep X S)
    (h : M.ReversibleSupport) :
    M.entropyProduction = shannon_entropy M.final.p -
      shannon_entropy M.initial.p + M.bathEntropy :=
  M.entropy_balance_of_support h

example {I A : Type*} (U : I → Set A) (s o : I → A → ℝ) (ε δ η : ℝ)
    (hη : 0 ≤ η) (hη' : η ≤ 1)
    (hs : LocalContent.Compatible U s ε) (ho : LocalContent.Compatible U o δ) :
    LocalContent.Compatible U (LocalContent.update η o s) ((1 - η) * ε + η * δ) :=
  LocalContent.update_residual U s o ε δ η hη hη' hs ho

example (m : ℕ) :
    65 / 127 - Continuing.agent.performance (3 * (m + 1)) =
      (65 / 127 - 65 / 128) * (1 / 128 : ℝ) ^ m :=
  Continuing.performance_error m

example : Filter.Tendsto (fun m => Continuing.agent.performance (3 * (m + 1)))
    Filter.atTop (nhds (65 / 127 : ℝ)) := Continuing.performance_tendsto

example (b : ℝ) : ∃ m, b < Continuing.process.totalWork (3 * m) :=
  Continuing.work_unbounded b

/-! ## Concrete witnesses

The specifications above are the general statements. These are instances of
them, so that none of the foundations is vacuous: an unbounded state space
carrying an actual trajectory, a feedback step whose support condition holds
where the earlier positivity premise fails, an erasure whose extended
divergence is infinite, and a cover on which the readout actually glues.
-/

namespace Resource

open PhysicsOfConsciousness.ResourceTrajectory

/-- A declared real-valued trajectory drawing one unit per operation from ten.
`horizon_bound` reads its horizon off the initial reading, with no finite state
space anywhere in the statement. -/
example (N : ℕ) (h : 0 ≤ refuel 10 1 0 N) : (N : ℝ) ≤ 10 := by
  have hb := horizon_bound (refuel 10 1 0) id (fun _ => 1) (fun _ => 0) N 1
    (fun n _ => refuel_ledger 10 1 0 n) (fun n _ => by norm_num) h
  simpa [refuel] using hb

/-- Delivery matching the draw sustains the same trajectory at every operation.
The unbounded cumulative delivery is supplied from outside the boundary. -/
example (n : ℕ) : 0 ≤ refuel 5 2 2 n := refuel_nonneg 5 2 2 (by norm_num) le_rfl n

/-- The sharp transfer on a countably infinite state space: a source carrying
seven units is emptied into the buffer, and nothing is created. -/
example : transferCharge (7, 0) = (0, 7) := transferCharge_sharp 7

example (s : ℕ × ℕ) : (transferCharge s).1 + (transferCharge s).2 = s.1 + s.2 :=
  transferCharge_conserves s

end Resource

namespace Support

open PhysicsOfConsciousness

/-- A controller-state law supported on one atom. -/
noncomputable def sparseInitial : ProbDist (Bool × Bool) where
  p z := if z = (true, true) then 1 else 0
  nonneg z := by split <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- A channel that forgets its input completely. -/
noncomputable def coin (_x _s : Bool) : ProbDist Bool where
  p _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- The step whose initial law has zeros and whose reverse support is still
complete: exactly the regime the earlier positivity premise excludes. -/
noncomputable def sparse : FiniteFeedbackStep Bool Bool := ⟨sparseInitial, coin⟩

theorem sparse_not_positive : ¬ sparse.Positive := by
  intro h
  have hz := h.1 (false, false)
  norm_num [sparse, sparseInitial] at hz

theorem sparse_reversibleSupport : sparse.ReversibleSupport := by
  rintro ⟨x, s, t⟩ hz
  revert hz
  cases x <;> cases s <;> cases t <;>
    norm_num [FiniteFeedbackStep.forward, FiniteFeedbackStep.reverse,
      FiniteFeedbackStep.final, sparse, sparseInitial, coin, Fintype.sum_bool]

/-- The entropy balance holds on this step, which `entropy_balance` does not
reach. Nonnegativity of its production follows from the same condition. -/
example : sparse.entropyProduction =
    shannon_entropy sparse.final.p - shannon_entropy sparse.initial.p +
      sparse.bathEntropy :=
  sparse.entropy_balance_of_support sparse_reversibleSupport

example : 0 ≤ sparse.entropyProduction :=
  sparse.entropyProduction_nonneg_of_support sparse_reversibleSupport

/-- A definite bit, and the opposite definite bit. -/
noncomputable def diracTrue : ProbDist Bool where
  p b := if b then 1 else 0
  nonneg b := by cases b <;> norm_num
  sum_one := by norm_num [Fintype.sum_bool]

noncomputable def diracFalse : ProbDist Bool where
  p b := if b then 0 else 1
  nonneg b := by cases b <;> norm_num
  sum_one := by norm_num [Fintype.sum_bool]

noncomputable def uniformBit : ProbDist Bool where
  p _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- Erasure of a definite bit onto the opposite definite bit has no reverse
support, and the extended divergence records that as infinity rather than as a
finite real cost. -/
example : diracTrue.extendedKL diracFalse = ⊤ :=
  ProbDist.extendedKL_top_of_missing _ _ true (by norm_num [diracTrue])
    (by norm_num [diracFalse])

theorem sharp_supported : diracTrue.SupportIncluded uniformBit := by
  intro v _
  norm_num [uniformBit]

/-- Where support is included the extended divergence is the real one, here
one bit. -/
example : (diracTrue.extendedKL uniformBit).toReal = Real.log 2 := by
  rw [ProbDist.extendedKL_toReal_of_support _ _ sharp_supported]
  norm_num [KL, diracTrue, uniformBit, Fintype.sum_bool]

end Support

namespace Content

open PhysicsOfConsciousness.LocalContent

/-- Two patches on three sites, sharing the middle one. -/
def U : Bool → Set (Fin 3)
  | false => {0, 1}
  | true => {1, 2}

/-- Local contents that agree on the shared site and carry different values
away from it, so the glued field is neither patch. -/
noncomputable def s : Bool → Fin 3 → ℝ
  | false => fun x => if x = 0 then 5 else 1
  | true => fun x => if x = 2 then 7 else 1

/-- The readout reads the left patch at the left site and the right patch
elsewhere. -/
def choose : Fin 3 → Bool := fun x => if x = 0 then false else true

theorem covers (x : Fin 3) : x ∈ U (choose x) := by
  fin_cases x <;> simp [U, choose]

theorem compatible : Compatible U s 0 := by
  intro i j x hi hj
  cases i <;> cases j <;> fin_cases x <;> simp_all [U, s]

/-- The declared readout extends both patches, and is the only field that
does. -/
example (i : Bool) (x : Fin 3) (hx : x ∈ U i) : readout choose s x = s i x :=
  readout_agrees U choose s covers compatible i x hx

example (f : Fin 3 → ℝ) (hf : ∀ i x, x ∈ U i → f x = s i x) :
    f = readout choose s :=
  readout_unique U choose s covers f hf

example (x : Fin 3) :
    readout choose s x = if x = 0 then 5 else if x = 2 then 7 else 1 := by
  fin_cases x <;> norm_num [readout, choose, s]

/-- A family that disagrees by one on the shared site: compatible at `ε = 1`
and demonstrably not at `ε = 0`, so the gluing premise is not automatic. -/
noncomputable def t : Bool → Fin 3 → ℝ
  | false => fun _ => 0
  | true => fun _ => 1

theorem t_compatible_one : Compatible U t 1 := by
  intro i j x _ _
  cases i <;> cases j <;> norm_num [t]

example : ¬ Compatible U t 0 := by
  intro h
  have h1 := h false true 1 (by simp [U]) (by simp [U])
  norm_num [t] at h1

/-- Constant observations agree everywhere. -/
theorem const_compatible : Compatible U (fun (_ : Bool) (_ : Fin 3) => (1 : ℝ)) 0 := by
  intro i j x _ _
  norm_num

/-- Under those observations the disagreement of `t` decays by a half per
observation. The limit is the observed value, not an independently chosen
global content. -/
example (n : ℕ) :
    Compatible U (run (1 / 2) (fun _ _ _ => (1 : ℝ)) t n) ((1 / 2 : ℝ) ^ n) := by
  have h := run_residual U t (fun _ _ _ => (1 : ℝ)) 1 (1 / 2) (by norm_num)
    (by norm_num) t_compatible_one (fun _ => const_compatible) n
  norm_num at h
  exact h

end Content

#print axioms Support.sparse_reversibleSupport
#print axioms Support.sparse_not_positive
#print axioms Content.compatible
#print axioms Content.covers

end PhysicsOfConsciousness.Examples.AgencyFoundations
