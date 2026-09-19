import PhysicsOfConsciousness.Phase6_Reconstruction

/-!
# Locality, latency and what a patch can be guaranteed to agree about

The gluing constructions elsewhere in this development are about a *snapshot*:
given local sections that agree on overlaps, there is a global one. Nothing in
the sheaf property says how long agreement takes to establish, or that it can be
re-established after the world changes. This module adds that missing temporal
requirement, in the smallest model that can carry it.

A `Network` is finite data: for each site, the sites it hears from, the message
each of those sends, and a local update from its own state and the messages it
received. `round` applies every local update once; `run N c T` is `T` rounds.
Locality is structural rather than assumed — `round` is *defined* through
`incoming`, which is `none` outside the declared neighbourhood — so the
indistinguishability theorem below is derived and not postulated.

* **`run_eq_of_agree_on_ball`.** Two initial configurations that agree on the
  causal past `ball nbhd T v` give the same state at `v` after `T` rounds.
  `run_eq_on_region_of_agree` is the same statement for a region.
* **`not_reconstructs_of_outside_past`.** Two interventions writing different
  values into a site *outside* that causal past leave the state at `v`
  identical, so no report read off `v` can track both. The obstruction is the
  reconstruction bound of `Phase6_Reconstruction`: the encoding is blind, and a
  blind encoding cannot meet a tolerance smaller than half the separation of the
  values it must distinguish.
* **`not_resonates_regionReading_of_outside_past`.** The same fact refutes a
  different claim, and a stronger one. A reading *region* whose causal past
  misses the intervened site holds the same state in both worlds, so its
  contents are not any declared reference that tells the worlds apart — with no
  metric, no tolerance and no report. Restriction resonance, the hypothesis the
  reflexive fixed point is interpreted through, therefore fails by the declared
  round.

## Latency, and what this is not

A communication delay is a chain of sites: a message crossing `k` hops arrives
at round `k` and not before, and the intermediate sites are delay registers
holding it in the meantime. That is a statement about `ball`, and it needs no
continuous time — `Examples/Locality.lean` §25 exhibits a three-site line where
the same value is unavailable at round one and exact at round two.

The negative result is about a *guarantee across interventions*, not about the
existence of agreement. A report that happens to be right about one world stays
right about it (`Reconstructs` on a one-element family is satisfiable with the
site outside the causal past), so nothing here says a static global section
cannot exist; what fails is the claim that agreement will be *restored* by a
declared round, for whichever value the world turns out to have.

Mapping physical execution, shared memory, host feedback or alternative sensory
paths onto this graph, and choosing a biologically meaningful deadline, are
empirical questions this module does not touch. No verdict about any device
follows from it.
-/

namespace PhysicsOfConsciousness.Locality

open PhysicsOfConsciousness.Reconstruction

variable {V S M Q : Type*}

/-- A finite synchronous message-passing network. Data only: who hears from
whom, what is sent, and how a site updates. No property of the update is
assumed. -/
structure Network (V S M : Type*) where
  /-- The sites `v` hears from. -/
  nbhd : V → Finset V
  /-- The message `u` sends to `v` when `u` is in state `s`. -/
  msg : V → V → S → M
  /-- The local update: own state and received messages only. -/
  step : V → S → (V → Option M) → S

/-- The causal past of `v` after `n` rounds: the sites whose initial state can
reach `v` in `n` hops. Defined from the neighbourhood alone, because that is all
locality is about. -/
def ball [DecidableEq V] (nbhd : V → Finset V) : ℕ → V → Finset V
  | 0, v => {v}
  | n + 1, v => insert v ((nbhd v).biUnion (ball nbhd n))

variable [DecidableEq V]

@[simp] theorem ball_zero (nbhd : V → Finset V) (v : V) : ball nbhd 0 v = {v} := rfl

theorem ball_succ (nbhd : V → Finset V) (n : ℕ) (v : V) :
    ball nbhd (n + 1) v = insert v ((nbhd v).biUnion (ball nbhd n)) := rfl

theorem self_mem_ball (nbhd : V → Finset V) (n : ℕ) (v : V) : v ∈ ball nbhd n v := by
  cases n with
  | zero => simp
  | succ n => exact Finset.mem_insert_self _ _

/-- A neighbour's causal past one round shorter is inside `v`'s. -/
theorem ball_nbhd_subset (nbhd : V → Finset V) (n : ℕ) {u v : V} (hu : u ∈ nbhd v) :
    ball nbhd n u ⊆ ball nbhd (n + 1) v := by
  rw [ball_succ]
  exact (Finset.subset_biUnion_of_mem (ball nbhd n) hu).trans (Finset.subset_insert _ _)

/-- Causal pasts grow with the number of rounds. -/
theorem ball_subset_succ (nbhd : V → Finset V) : ∀ (n : ℕ) (v : V),
    ball nbhd n v ⊆ ball nbhd (n + 1) v := by
  intro n
  induction n with
  | zero =>
    intro v
    simp only [ball_zero, Finset.singleton_subset_iff]
    exact self_mem_ball nbhd 1 v
  | succ n ih =>
    intro v x hx
    rw [ball_succ] at hx ⊢
    rcases Finset.mem_insert.1 hx with h | h
    · exact Finset.mem_insert.2 (Or.inl h)
    · obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.1 h
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_biUnion.2 ⟨u, hu, ih u hxu⟩))

namespace Network

variable (N : Network V S M)

/-- What `v` receives: a message from each declared neighbour, and nothing from
anywhere else. This is where locality is built in. -/
def incoming (c : V → S) (v : V) : V → Option M :=
  fun u => if u ∈ N.nbhd v then some (N.msg u v (c u)) else none

/-- One synchronous round. -/
def round (c : V → S) : V → S := fun v => N.step v (c v) (N.incoming c v)

/-- `T` rounds. -/
def run (c : V → S) (T : ℕ) : V → S := (N.round)^[T] c

@[simp] theorem run_zero (c : V → S) : N.run c 0 = c := rfl

theorem run_succ (c : V → S) (T : ℕ) : N.run c (T + 1) = N.round (N.run c T) :=
  Function.iterate_succ_apply' _ _ _

/-- **Indistinguishability from the causal past.** Two initial configurations
agreeing on `ball nbhd T v` leave `v` in the same state after `T` rounds.

Derived from the construction of `round`: the only inputs to a local update are
the site's own state and the messages from its declared neighbourhood, so the
dependence shrinks by one hop per round. No class field asserts this. -/
theorem run_eq_of_agree_on_ball (c c' : V → S) :
    ∀ (T : ℕ) (v : V), (∀ u ∈ ball N.nbhd T v, c u = c' u) → N.run c T v = N.run c' T v := by
  intro T
  induction T with
  | zero =>
    intro v h
    exact h v (self_mem_ball _ 0 v)
  | succ n ih =>
    intro v h
    have hnb : ∀ u ∈ N.nbhd v, N.run c n u = N.run c' n u := by
      intro u hu
      exact ih u fun x hx => h x (ball_nbhd_subset N.nbhd n hu hx)
    have hv : N.run c n v = N.run c' n v :=
      ih v fun x hx => h x (ball_subset_succ N.nbhd n v hx)
    have hin : N.incoming (N.run c n) v = N.incoming (N.run c' n) v := by
      funext u
      by_cases hu : u ∈ N.nbhd v
      · simp only [incoming, hu, ite_true, hnb u hu]
      · simp only [incoming, hu, ite_false]
    rw [run_succ, run_succ]
    show N.step v _ _ = N.step v _ _
    rw [hv, hin]

/-- The same statement for a region: a patch's whole state at round `T` is fixed
by the union of its sites' causal pasts. -/
theorem run_eq_on_region_of_agree (c c' : V → S) (T : ℕ) (R : Finset V)
    (h : ∀ v ∈ R, ∀ u ∈ ball N.nbhd T v, c u = c' u) :
    ∀ v ∈ R, N.run c T v = N.run c' T v :=
  fun v hv => N.run_eq_of_agree_on_ball c c' T v (h v hv)

end Network

/-! ## Fresh interventions and the responsiveness premise

An intervention writes a value into one site's initial state; the site is fresh
in the sense that nothing else in the configuration changes with it. A patch is
*responsive* at tolerance `ε` if its report at round `T` is within `ε` of the
value the world was given — which is `Reconstructs ε` for the encoding below,
and is exactly the premise the negative result refutes.

Two things this formulation rules out structurally. The report is a function of
the network state at the reading site alone, so it cannot consult the
intervention; and it is required to be accurate for *every* value in the
declared family, so a constant report does not satisfy it
(`Encoding.not_reconstructs_of_const_readout`). -/

/-- The intervened configuration: the declared baseline everywhere, with one
site's initial state carrying the new value. -/
def intervene (base : V → S) (w : V) (inj : Q → S) (q : Q) : V → S :=
  Function.update base w (inj q)

theorem intervene_of_ne (base : V → S) {w : V} (inj : Q → S) (q : Q) {u : V} (hu : u ≠ w) :
    intervene base w inj q u = base u :=
  Function.update_of_ne hu _ _

/-- The reading site's view of the world at round `T`, as a reconstruction
mechanism: the world's value is the state to be recovered, the network state at
`v` after `T` rounds is the code, and `report` is the readout. -/
def worldEncoding [PseudoMetricSpace Q] (N : Network V S M) (base : V → S) (w : V)
    (inj : Q → S) (v : V) (T : ℕ) (report : S → Q) (relevant : Set Q) :
    Encoding Q S where
  relevant := relevant
  encode := fun q => N.run (intervene base w inj q) T v
  readout := report

@[simp] theorem worldEncoding_error [PseudoMetricSpace Q] (N : Network V S M) (base : V → S)
    (w : V) (inj : Q → S) (v : V) (T : ℕ) (report : S → Q) (relevant : Set Q) (q : Q) :
    (worldEncoding N base w inj v T report relevant).error q =
      dist q (report (N.run (intervene base w inj q) T v)) := rfl

/-- **An intervention outside the causal past is invisible.** The two worlds
differ only at `w`, and `w` is not among the sites whose initial state can reach
`v` in `T` rounds, so `v` is in the same state in both. -/
theorem run_intervene_eq_of_notMem (N : Network V S M) (base : V → S) {w v : V}
    (inj : Q → S) {T : ℕ} (hw : w ∉ ball N.nbhd T v) (q q' : Q) :
    N.run (intervene base w inj q) T v = N.run (intervene base w inj q') T v := by
  refine N.run_eq_of_agree_on_ball _ _ T v fun u hu => ?_
  have hne : u ≠ w := fun h => hw (h ▸ hu)
  rw [intervene_of_ne base inj q hne, intervene_of_ne base inj q' hne]

/-- **No guarantee of timely agreement across interventions.** If the site the
world is changed at lies outside the reading site's causal past for `T` rounds,
then for any report whatever, the responsiveness premise fails at every
tolerance below half the separation of two values the world might be given.

The obstruction is the reconstruction bound: the encoding is blind, because the
code is the same in both worlds, and a blind encoding cannot meet a tolerance
below half the separation (`Encoding.not_reconstructs_of_blind`).

What this does not say: that the two patches never agree. It says the agreement
cannot be *guaranteed by round* `T` — for one fixed world a report may be exactly
right, and `Examples/Locality.lean` §25 exhibits that case. -/
theorem not_reconstructs_of_outside_past [PseudoMetricSpace Q] (N : Network V S M)
    (base : V → S) {w v : V} (inj : Q → S) {T : ℕ} (report : S → Q)
    (relevant : Set Q) (hw : w ∉ ball N.nbhd T v) {ε : ℝ} {q q' : Q}
    (hq : q ∈ relevant) (hq' : q' ∈ relevant) (hsep : 2 * ε < dist q q') :
    ¬ (worldEncoding N base w inj v T report relevant).Reconstructs ε :=
  Encoding.not_reconstructs_of_blind
    (r := report (N.run (intervene base w inj q) T v))
    (fun p => congrArg report (run_intervene_eq_of_notMem N base inj hw p q)) hq hq' hsep

/-! ## Restriction resonance, by a declared round

The previous theorem refutes *accuracy*. The same causal-past fact refutes
*resonance*, and it does so without a metric, a tolerance or a readout.

A reading region's state at round `T` is a code: one section of the machine, read
where the avatar sits. Restriction resonance asks that this code be what the
region is supposed to hold — the reference map `ρ` below, which the model
declares and this module does not choose. When the world is changed at a site
outside the region's causal past for `T` rounds, the region holds the same state
in both worlds, so the code confuses two worlds. Any reference separating them is
then not what the region reads, by `Reconstruction.not_resonates_of_confuses`.

What this adds to the reconstruction result is where the failure sits. The
obstruction is not that the report is inaccurate but that the region's contents
cannot be the state the model says they are, before the deadline, for any
encoding whatever. Which sites lie outside a region's causal past is a fact about
the graph and the round; choosing a physically meaningful deadline, and mapping
execution onto this graph, remain the empirical questions this module does not
touch. -/

/-- The reading region's whole state at round `T`, as a function of the value the
world was given. The single-site case is `v` a one-element region. -/
def regionReading (N : Network V S M) (base : V → S) (w : V) (inj : Q → S)
    (R : Finset V) (T : ℕ) : Q → ({v // v ∈ R} → S) :=
  fun q v => N.run (intervene base w inj q) T v.1

/-- **A region whose causal past misses the intervention reads the same in both
worlds.** The regional form of `run_intervene_eq_of_notMem`: every site of the
region is separately blind, so the region's whole state is. -/
theorem regionReading_eq_of_outside_past (N : Network V S M) (base : V → S) {w : V}
    (inj : Q → S) {R : Finset V} {T : ℕ} (hw : ∀ v ∈ R, w ∉ ball N.nbhd T v) (q q' : Q) :
    regionReading N base w inj R T q = regionReading N base w inj R T q' := by
  funext v
  exact run_intervene_eq_of_notMem N base inj (hw v.1 v.2) q q'

/-- **Restriction resonance fails by the declared round.** If the world is changed
outside the reading region's causal past for `T` rounds, the region's state is the
same in both worlds, so it is not any reference that tells them apart.

No metric, no tolerance and no readout: the region's contents are the same object
in the two worlds, and a reference that is not is not them. Compare
`not_reconstructs_of_outside_past`, which refutes accuracy of a report at the same
deadline; this refutes the claim that the region holds what the model says it
holds, which is the hypothesis E89's fixed point is interpreted through. -/
theorem not_resonates_regionReading_of_outside_past (N : Network V S M) (base : V → S)
    {w : V} (inj : Q → S) {R : Finset V} {T : ℕ} (ρ : Q → ({v // v ∈ R} → S))
    (hw : ∀ v ∈ R, w ∉ ball N.nbhd T v) {q q' : Q} (hρ : ρ q ≠ ρ q') :
    ¬ Resonates (regionReading N base w inj R T) ρ :=
  not_resonates_of_confuses (regionReading_eq_of_outside_past N base inj hw q q') hρ

#print axioms Network.run_eq_of_agree_on_ball
#print axioms Network.run_eq_on_region_of_agree
#print axioms run_intervene_eq_of_notMem
#print axioms not_reconstructs_of_outside_past
#print axioms regionReading_eq_of_outside_past
#print axioms not_resonates_regionReading_of_outside_past

end PhysicsOfConsciousness.Locality
