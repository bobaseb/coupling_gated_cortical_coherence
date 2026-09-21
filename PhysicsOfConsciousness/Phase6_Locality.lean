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
* **`ball_rank_le`.** Where a causal past *stops*. If every site hears only
  from sites of rank at most its own, then no number of rounds reaches a site of
  higher rank: the past does not merely grow slowly, it never crosses the rank.
  The hypothesis is about `nbhd` alone, so an architecture that imposes an order
  on its sites discharges it rather than being assumed to satisfy it —
  `Examples/Locality.lean` §31 is the causal mask of a decoder-only forward pass,
  where the rank is the token position.
* **`card_ball_le`.** How fast a causal past grows when nothing orders the
  sites: at most `∑_{i ≤ n} dⁱ` sites after `n` rounds on a graph of fan-in `d`.
  It supplies the obstruction's hypothesis by counting rather than by structure
  (`not_reconstructs_of_bounded_degree`), which is the statement that a
  guarantee by deadline `T` across `N` sites needs `T` of order `log_d N`; and
  read backwards it prices the deadline in wiring instead of rounds
  (`card_le_geomSum_of_reaches`, and `le_degree_of_reaches_one` at one round).

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

* **`not_outside_past_of_isFullSupport`.** The hypothesis both negative results
  run on — a site outside the reading site's causal past — is unsatisfiable on a
  network where every site hears from every site. A coupling of full support has
  no hop structure for a deadline to bite on, so this module's obstruction is
  silent there, and an argument running it against such a kernel is running it
  where its hypothesis cannot hold. What that costs is stated with the theorem:
  a physical field propagates at a finite speed, so the idealization holds only
  while transit is short against the phase time scale, which is a calibration
  and not a theorem.

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

/-! ### A rank no message increases

`ball_subset_succ` says a causal past grows with the rounds; these two say where
it stops growing. A *rank* is any order-valued function on the sites that no
neighbourhood increases, and a past confined below a rank at one round is
confined below it at every round.

The content is where the hypothesis comes from. `∀ v, ∀ u ∈ nbhd v, f u ≤ f v` is
a statement about the declared neighbourhood, so an architecture that orders its
sites — a feed-forward depth, a token position under a causal mask — supplies it
by construction and is not assumed to satisfy it. What the rank is, and whether
the graph is the one a device runs, remain the empirical questions this module
declines. -/

/-- **A monotone rank bounds the causal past at every depth.** If no site hears
from a site of higher rank, then every site whose initial state can reach `v` in
any number of rounds has rank at most `v`'s.

The hypothesis carries the architectural content and nothing else does: `f` is
arbitrary, the order is arbitrary, and no property of `msg` or `step` is used —
the statement is about `ball`, which is defined from `nbhd` alone. Removing the
hypothesis is not possible; weakening it to "rank increases by at most one per
hop" would give a growth rate rather than a barrier, which is the weaker claim
this theorem exists to avoid. -/
theorem ball_rank_le {α : Type*} [Preorder α] {nbhd : V → Finset V} {f : V → α}
    (h : ∀ v, ∀ u ∈ nbhd v, f u ≤ f v) :
    ∀ (n : ℕ) (v : V), ∀ u ∈ ball nbhd n v, f u ≤ f v := by
  intro n
  induction n with
  | zero =>
    intro v u hu
    rw [ball_zero, Finset.mem_singleton] at hu
    exact le_of_eq (congrArg f hu)
  | succ n ih =>
    intro v u hu
    rw [ball_succ] at hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · exact le_rfl
    · obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
      exact (ih w u huw).trans (h v w hw)

/-- **A site of strictly higher rank is outside the causal past, at every
deadline.** The contrapositive form, and the one that fires the negative results
below: it supplies `hw` with a `w` the architecture's own order picks out, at
every `T` at once rather than at a chosen one. -/
theorem notMem_ball_of_rank_lt {α : Type*} [Preorder α] {nbhd : V → Finset V} {f : V → α}
    (h : ∀ v, ∀ u ∈ nbhd v, f u ≤ f v) {n : ℕ} {v w : V} (hlt : f v < f w) :
    w ∉ ball nbhd n v :=
  fun hw => absurd (ball_rank_le h n v w hw) (not_le_of_gt hlt)

/-! ### Bounded fan-in, and what a deadline costs in wiring

`ball_rank_le` says where a causal past stops when the architecture orders its
sites. These say how fast it can grow when nothing orders them. A site hearing
from at most `d` others reaches at most `∑_{i ≤ n} dⁱ` sites in `n` rounds,
because each round adds the site itself and multiplies the frontier by at most
`d`; `card_ball_le_mul_pow` reads the same count as `(n+1)·dⁿ`, which is the
form the logarithm comes out of.

That count supplies the hypothesis the negative results below have to be handed.
`not_reconstructs_of_outside_past` fires on a site *outside* the reading site's
causal past, and an architectural order is one way to produce one; bounded
fan-in is the other, and it produces one by counting rather than by structure.
While the reachable count stays below `Fintype.card V` the causal past is not
everything, so a witness exists: reconstruction by deadline `T` on a degree-`d`
network of `N` sites needs `T` of order `log_d N`.

Read backwards the same count prices the deadline in wiring instead of in
rounds. A network that does reach every site by `T` satisfies
`Fintype.card V ≤ ∑_{i ≤ T} dⁱ`, so meeting a deadline across `N` sites requires
degree of order `N^{1/T}` — and at `T = 1`, by `le_degree_of_reaches_one`, a
site hearing from all but one of the others.

**What is declared, and what is proved.** `d` and `N` are inputs, exactly as the
communication graph and the deadline already are; nothing here says which graph
a device runs or which deadline is physically meaningful. The bound is about a
*guaranteed* response across interventions and not about what one run achieves —
`Examples/Locality.lean` §25 exhibits a report that is exactly right in one world
at a round where no guarantee holds. And what it bounds is the communication
graph a guarantee requires, which is a different question from what hardware is
buildable; this development models the second nowhere. -/

/-- **A degree bound bounds the causal past.** If every site hears from at most
`d` others, the causal past after `n` rounds holds at most `∑_{i ≤ n} dⁱ` sites.

The hypothesis is about `nbhd` alone, as `ball` is, so no property of `msg` or
`step` enters and the bound holds of every network on that communication graph.
The count is of *sites reachable*, not of messages sent or of time elapsed. -/
theorem card_ball_le {nbhd : V → Finset V} {d : ℕ} (hd : ∀ v, (nbhd v).card ≤ d) :
    ∀ (n : ℕ) (v : V), (ball nbhd n v).card ≤ ∑ i ∈ Finset.range (n + 1), d ^ i := by
  intro n
  induction n with
  | zero => intro v; simp [ball_zero]
  | succ n ih =>
    intro v
    rw [ball_succ]
    calc (insert v ((nbhd v).biUnion (ball nbhd n))).card
        ≤ ((nbhd v).biUnion (ball nbhd n)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (∑ u ∈ nbhd v, (ball nbhd n u).card) + 1 := by
          gcongr
          exact Finset.card_biUnion_le
      _ ≤ (∑ _u ∈ nbhd v, ∑ i ∈ Finset.range (n + 1), d ^ i) + 1 := by
          gcongr with u hu
          exact ih u
      _ = (nbhd v).card * ∑ i ∈ Finset.range (n + 1), d ^ i + 1 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ d * ∑ i ∈ Finset.range (n + 1), d ^ i + 1 := by
          gcongr
          exact hd v
      _ = ∑ i ∈ Finset.range (n + 1 + 1), d ^ i := by
          rw [Finset.sum_range_succ' (fun i => d ^ i) (n + 1), Finset.mul_sum]
          simp [pow_succ, mul_comm]

/-- **The same bound with the logarithm visible.** At degree at least one the
geometric sum is at most `(n+1)·dⁿ`, so the reachable count grows exponentially
in the rounds and a deadline `T` reaching `N` sites needs `T` of order
`log_d N`. The looser form is the quotable one; `card_ball_le` is the sharp
one. -/
theorem card_ball_le_mul_pow {nbhd : V → Finset V} {d : ℕ} (hd1 : 1 ≤ d)
    (hd : ∀ v, (nbhd v).card ≤ d) (n : ℕ) (v : V) :
    (ball nbhd n v).card ≤ (n + 1) * d ^ n := by
  refine (card_ball_le hd n v).trans ?_
  calc ∑ i ∈ Finset.range (n + 1), d ^ i
      ≤ ∑ _i ∈ Finset.range (n + 1), d ^ n :=
        Finset.sum_le_sum fun i hi =>
          Nat.pow_le_pow_right hd1 (Nat.le_of_lt_succ (Finset.mem_range.1 hi))
    _ = (n + 1) * d ^ n := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Bounded fan-in produces the witness the obstruction needs.** While the
reachable count stays below the number of sites, some site lies outside the
reading site's causal past at the deadline — so
`not_reconstructs_of_outside_past` fires on a network with no order on its
sites at all, its hypothesis discharged by counting.

Which site it is, is not determined here and does not need to be: the negative
result quantifies over the value written, not over where it is written. -/
theorem exists_notMem_ball_of_bounded_degree [Fintype V] {nbhd : V → Finset V} {d : ℕ}
    (hd : ∀ v, (nbhd v).card ≤ d) {T : ℕ}
    (hlt : ∑ i ∈ Finset.range (T + 1), d ^ i < Fintype.card V) (v : V) :
    ∃ w, w ∉ ball nbhd T v := by
  by_contra h
  have hall : ∀ w, w ∈ ball nbhd T v := fun w => by
    by_contra hw
    exact h ⟨w, hw⟩
  have hsub : (Finset.univ : Finset V) ⊆ ball nbhd T v := fun w _ => hall w
  have hcard : Fintype.card V ≤ (ball nbhd T v).card := by
    simpa [Finset.card_univ] using Finset.card_le_card hsub
  exact absurd (hcard.trans (card_ball_le hd T v)) (not_le_of_gt hlt)

/-- **The interconnect a deadline costs.** The contrapositive: a network whose
causal past at deadline `T` is the whole site set has at most `∑_{i ≤ T} dⁱ`
sites, so reaching `N` of them by round `T` requires degree of order `N^{1/T}`.

This bounds the communication graph a guarantee requires. It says nothing about
what hardware is buildable, or about latency — `ball` counts hops, and nothing
in this development is about time to solution. -/
theorem card_le_geomSum_of_reaches [Fintype V] {nbhd : V → Finset V} {d : ℕ}
    (hd : ∀ v, (nbhd v).card ≤ d) {T : ℕ} {v : V} (h : ∀ w, w ∈ ball nbhd T v) :
    Fintype.card V ≤ ∑ i ∈ Finset.range (T + 1), d ^ i := by
  have hsub : (Finset.univ : Finset V) ⊆ ball nbhd T v := fun w _ => h w
  have hcard : Fintype.card V ≤ (ball nbhd T v).card := by
    simpa [Finset.card_univ] using Finset.card_le_card hsub
  exact hcard.trans (card_ball_le hd T v)

/-- **At one round, a crossbar.** The `T = 1` case of the interconnect bound: a
site whose causal past after a single round is everything hears from all but one
of the other sites. The deadline is purchasable, and this is the wiring it
costs. -/
theorem le_degree_of_reaches_one [Fintype V] {nbhd : V → Finset V} {d : ℕ}
    (hd : ∀ v, (nbhd v).card ≤ d) {v : V} (h : ∀ w, w ∈ ball nbhd 1 v) :
    Fintype.card V ≤ 1 + d := by
  simpa [Finset.sum_range_succ] using card_le_geomSum_of_reaches hd h

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

/-- **The same obstruction, with its hypothesis derived from the degree.** On a
network of bounded fan-in and a deadline too early for the reachable count to
cover the site set, there is a site the world can be changed at that no report
read off `v` tracks by round `T`.

This is the quantitative form: the deadline the guarantee needs grows like
`log_d N`, by `card_ball_le_mul_pow`. What it supplies over
`not_reconstructs_of_outside_past` is that nothing has to be assumed about where
the intervention lands — the counting picks the site out.

It remains a statement about a *guarantee* across two declared values. For one
fixed world a report may be exactly right at any round whatever, which
`Examples/Locality.lean` §25 exhibits, and the graph and the deadline are
declared here as they are everywhere in this module. -/
theorem not_reconstructs_of_bounded_degree [Fintype V] [PseudoMetricSpace Q]
    (N : Network V S M) (base : V → S) (inj : Q → S) (report : S → Q) (relevant : Set Q)
    {d T : ℕ} (hd : ∀ v, (N.nbhd v).card ≤ d)
    (hlt : ∑ i ∈ Finset.range (T + 1), d ^ i < Fintype.card V) (v : V)
    {ε : ℝ} {q q' : Q} (hq : q ∈ relevant) (hq' : q' ∈ relevant) (hsep : 2 * ε < dist q q') :
    ∃ w, ¬ (worldEncoding N base w inj v T report relevant).Reconstructs ε := by
  obtain ⟨w, hw⟩ := exists_notMem_ball_of_bounded_degree hd hlt v
  exact ⟨w, not_reconstructs_of_outside_past N base inj report relevant hw hq hq' hsep⟩

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

/-! ## A kernel with no hop structure

Both negative results above are fired by the same hypothesis: some site lies
*outside* the reading site's causal past for `T` rounds. That hypothesis is
about `nbhd`, and a coupling of full support does not have one to speak of —
every site hears from every site, `incoming` is `some` everywhere, and a
message crosses no hops because there are none to cross.

`ball_eq_univ_of_full` is that, in the only form the obstruction cares about:
after a single round the causal past of any site is the whole network. So on a
full-support network there is no `w` to instantiate `hw` with, at any deadline
but zero, and `not_reconstructs_of_outside_past` and
`not_resonates_regionReading_of_outside_past` have nothing to fire on. This is
the asymmetry the bound's uses have to respect: the results above obstruct an
architecture whose agreement propagates by hops, and a mean-field kernel of full
support is not one.

Against `card_ball_le` the asymmetry is quantitative on both sides. A graph of
fan-in `d` needs `T` of order `log_d N` before its causal past covers `N` sites,
and `le_degree_of_reaches_one` says what a single round costs instead: a site
hearing from all but one of the others. Full support is that crossbar, and
`ball_eq_univ_of_full` is the degree bound at `d = N`, where the count covers
the site set at the first round and the obstruction has no witness left to pick
out.

**What this is not.** It is not a claim that a field escapes latency. A physical
field propagates at a finite speed, so `nbhd v = univ` is a model of one only
while transit across the substrate is short against the phase time scale the
dynamics runs on. That comparison is a calibration — a conduction speed, a
diameter, a frequency — and this module measures none of them. What is proved
is narrower and exact: *given* a network with no neighbourhood structure, the
deadline obstruction of this module has no instance. Whether cortex is such a
network, and at what deadline, is the empirical question the module's header
already declines. -/

/-- Every site hears from every site: the shape a coupling of full support has,
with no neighbourhood for a message to cross. -/
def Network.IsFullSupport [Fintype V] (N : Network V S M) : Prop :=
  ∀ v, N.nbhd v = Finset.univ

/-- **Full support is exactly a total `incoming`.** The predicate is stated on
`nbhd` because `ball` is, and this is the check that it says what it is named
for: a site receives a message from every site, in every configuration. -/
theorem Network.isFullSupport_iff_incoming_isSome [Fintype V] [Nonempty S]
    (N : Network V S M) :
    N.IsFullSupport ↔ ∀ (c : V → S) (v u : V), (N.incoming c v u).isSome := by
  constructor
  · intro h c v u
    simp [Network.incoming, h v]
  · intro h v
    refine Finset.eq_univ_of_forall fun u => ?_
    by_contra hu
    have hsome := h (fun _ => Classical.arbitrary S) v u
    simp [Network.incoming, hu] at hsome

/-- **One round of a full-support kernel reaches everything.** The causal past
after any positive number of rounds is the whole network. -/
theorem ball_eq_univ_of_full [Fintype V] {nbhd : V → Finset V}
    (h : ∀ v, nbhd v = Finset.univ) (n : ℕ) (v : V) :
    ball nbhd (n + 1) v = Finset.univ := by
  rw [ball_succ, h v]
  refine Finset.eq_univ_of_forall fun u => ?_
  exact Finset.mem_insert_of_mem
    (Finset.mem_biUnion.2 ⟨u, Finset.mem_univ u, self_mem_ball nbhd n u⟩)

theorem mem_ball_of_full [Fintype V] {nbhd : V → Finset V}
    (h : ∀ v, nbhd v = Finset.univ) {T : ℕ} (hT : T ≠ 0) (v w : V) :
    w ∈ ball nbhd T v := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT
  rw [ball_eq_univ_of_full h]
  exact Finset.mem_univ w

/-- **No site is outside the causal past**, at any deadline but zero. -/
theorem mem_ball_of_isFullSupport [Fintype V] {N : Network V S M} (h : N.IsFullSupport)
    {T : ℕ} (hT : T ≠ 0) (v w : V) : w ∈ ball N.nbhd T v :=
  mem_ball_of_full h hT v w

/-- **The deadline obstruction has no instance on a full-support kernel.** The
hypothesis `w ∉ ball N.nbhd T v`, which is what fires both
`not_reconstructs_of_outside_past` and
`not_resonates_regionReading_of_outside_past`, is unsatisfiable once every site
hears from every site and the deadline is at least one round.

This does not say the reports are accurate or that the region reads what it is
supposed to. It says this module's obstruction is silent, and that an argument
running it against a full-support kernel is running it where its hypothesis
cannot hold. -/
theorem not_outside_past_of_isFullSupport [Fintype V] {N : Network V S M}
    (h : N.IsFullSupport) {T : ℕ} (hT : T ≠ 0) {v w : V} :
    ¬ w ∉ ball N.nbhd T v :=
  fun hw => hw (mem_ball_of_isFullSupport h hT v w)

#print axioms ball_rank_le
#print axioms notMem_ball_of_rank_lt
#print axioms card_ball_le
#print axioms card_ball_le_mul_pow
#print axioms exists_notMem_ball_of_bounded_degree
#print axioms card_le_geomSum_of_reaches
#print axioms le_degree_of_reaches_one
#print axioms not_reconstructs_of_bounded_degree
#print axioms Network.run_eq_of_agree_on_ball
#print axioms Network.run_eq_on_region_of_agree
#print axioms run_intervene_eq_of_notMem
#print axioms not_reconstructs_of_outside_past
#print axioms regionReading_eq_of_outside_past
#print axioms not_resonates_regionReading_of_outside_past
#print axioms Network.isFullSupport_iff_incoming_isSome
#print axioms ball_eq_univ_of_full
#print axioms not_outside_past_of_isFullSupport

end PhysicsOfConsciousness.Locality
