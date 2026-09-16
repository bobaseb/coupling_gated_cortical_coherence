/-
  Examples/VectorContent.lean — vector-valued contents and the overlap encoder

  §22 carries several independent quantities per patch: a two-component family
  that glues and whose glued field is neither patch, and the rejection that
  makes the vector statement more than a relabelling — one coordinate can agree
  everywhere while the pair does not. §23 is about `SharedEncoder`: two patches
  at the same phase, each encoding the shared site its own way, disagree by a
  fixed vector, so phase order does not supply the overlap obligation.

  The cover is the one of `Examples/AgencyFoundations.lean`: two patches on
  three sites, sharing the middle one. Contents are valued in `ℝ × ℝ`, whose
  norm is the larger of the two coordinates' absolute values.
-/

import PhysicsOfConsciousness.Phase5_ContentDynamics
import PhysicsOfConsciousness.Examples.AgencyFoundations

namespace PhysicsOfConsciousness
namespace Examples
namespace VectorContent

open PhysicsOfConsciousness.LocalContent
open PhysicsOfConsciousness.Examples.AgencyFoundations.Content (U choose covers)

/-! ## 22. Two components at once, and what one of them does not decide

`Compatible` reads a vector family through the norm of the difference, so a
family agrees when *every* coordinate does. The two witnesses here fence that
from both sides: `pair` glues with two genuinely different coordinates, and
`split` shows that the agreement of a fixed linear read-out is strictly weaker
than the agreement it is read from. -/

/-- A two-component content: the first coordinate is the scalar witness of
`Examples/AgencyFoundations.lean`, the second an independent quantity the
patches also report. Neither coordinate is constant across sites. -/
noncomputable def pair : Bool → Fin 3 → ℝ × ℝ
  | false => fun x => if x = 0 then (5, -1) else (1, 2)
  | true => fun x => if x = 2 then (7, 4) else (1, 2)

/-- The patches agree exactly on the site they share, in both coordinates. -/
theorem pair_compatible : Compatible U pair 0 := by
  intro i j x hi hj
  cases i <;> cases j <;> fin_cases x <;> simp_all [U, pair]

/-- The glued field extends both patches… -/
example (i : Bool) (x : Fin 3) (hx : x ∈ U i) : readout choose pair x = pair i x :=
  readout_agrees U choose pair covers pair_compatible i x hx

/-- …and is the only field that does. -/
example (f : Fin 3 → ℝ × ℝ) (hf : ∀ i x, x ∈ U i → f x = pair i x) :
    f = readout choose pair :=
  readout_unique U choose pair covers f hf

/-- The witness is not constant: the glued field takes three different values,
and it is not either patch's field extended blindly. -/
theorem pair_readout_zero : readout choose pair 0 = (5, -1) := by
  simp [readout, choose, pair]

theorem pair_readout_one : readout choose pair 1 = (1, 2) := by
  simp [readout, choose, pair]

theorem pair_readout_two : readout choose pair 2 = (7, 4) := by
  simp [readout, choose, pair]

theorem pair_readout_nonconstant : readout choose pair 0 ≠ readout choose pair 2 := by
  intro h
  have hfst := congrArg Prod.fst h
  rw [pair_readout_zero, pair_readout_two] at hfst
  norm_num at hfst

/-- Both coordinates move, so neither is a decoration on a scalar witness. -/
theorem pair_second_nonconstant :
    (readout choose pair 0).2 ≠ (readout choose pair 1).2 := by
  rw [pair_readout_zero, pair_readout_one]
  norm_num

/-- **A nonexpansive linear read-out of an agreeing family agrees.** This is
`compatible_map`, exercised on the witness that actually satisfies its
hypothesis. -/
theorem pair_fst_compatible :
    Compatible U (fun i x => (LinearMap.fst ℝ ℝ ℝ) (pair i x)) 0 :=
  compatible_map U pair 0 (LinearMap.fst ℝ ℝ ℝ) (fun v => norm_fst_le v) pair_compatible

/-- A family whose first coordinate is the same everywhere and whose second
coordinate separates the two patches. -/
noncomputable def split : Bool → Fin 3 → ℝ × ℝ
  | false => fun _ => (1, 0)
  | true => fun _ => (1, 1)

/-- **The projection agrees.** Reading only the first coordinate, the two
patches are in exact agreement. -/
theorem split_fst_compatible :
    Compatible U (fun i x => (LinearMap.fst ℝ ℝ ℝ) (split i x)) 0 := by
  intro i j x _ _
  cases i <;> cases j <;> simp [split]

/-- **The pair does not.** Agreement of one scalar projection is not agreement
of the vector: the disagreement lives entirely in the coordinate the projection
discards, and it is a full unit. This is what the scalar statement cannot
express, and it is why `compatible_map` runs in one direction only —
`pair_fst_compatible` reads a family that does agree. -/
theorem split_not_compatible : ¬ Compatible U split 0 := by
  intro h
  have h1 := h false true 1 (by simp [U]) (by simp [U])
  simp [split, Prod.norm_def] at h1
  linarith

/-- The gap is not an artefact of demanding exactness: the family is not
compatible at any tolerance below one. -/
theorem split_not_compatible_lt_one {ε : ℝ} (hε : ε < 1) : ¬ Compatible U split ε := by
  intro h
  have h1 := h false true 1 (by simp [U]) (by simp [U])
  rw [show split false 1 - split true 1 = ((0 : ℝ), (-1 : ℝ)) by
    simp [split]] at h1
  rw [Prod.norm_def] at h1
  simp only [Real.norm_eq_abs, abs_zero, abs_neg, abs_one, max_eq_right zero_le_one] at h1
  linarith

/-- Vector contents run through the observation dynamics like scalar ones: the
initial disagreement of `split` contracts geometrically onto the floor its
observations set, with the floor computed in the same norm. -/
example (n : ℕ) :
    Compatible U (run (1 / 2) (fun _ => split) split n)
      ((1 - (1 : ℝ) / 2) ^ n * 1 + 1) :=
  run_residual_floor U split (fun _ => split) 1 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      intro i j x _ _
      cases i <;> cases j <;>
        simp [split, Prod.norm_def])
    (fun _ i j x _ _ => by
      cases i <;> cases j <;>
        simp [split, Prod.norm_def]) n


/-! ## 23. The encoder at an overlap is one function, or the phases do not help

`compatible_of_shared_coherence` lets each site carry its own encoder — a patch
reports what is at the site it reads, not one population-wide scalar — and pays
for it with `SharedEncoder`: where two patches both see a site, they encode that
site's quantity the same way. The premise is not implied by coherence. Here the
population is *perfectly* phase locked, and dropping it still leaves the patches
a full unit apart. -/

open PhysicsOfConsciousness.Examples.AgencyFoundations.Content
  (proj proj_lipschitz locked locked_is_phase_locked patchOf)

/-- A site-dependent second quantity: each site carries its own offset. -/
noncomputable def siteWeight : Fin 3 → ℝ := ![2, 3, 5]

/-- **A shared encoder that is genuinely site-dependent.** Both patches encode
the phase in the first coordinate and the site's own quantity in the second.
Different sites are encoded differently; a site is encoded the same way by
whoever reads it. -/
noncomputable def sharedEnc : Bool → Fin 3 → ℝ × ℝ → ℝ × ℝ :=
  fun _ x p => (proj p, siteWeight x)

theorem sharedEnc_shared : SharedEncoder U sharedEnc := fun _ _ _ _ _ => rfl

theorem sharedEnc_lipschitz : UniformLipschitzEncoder sharedEnc 1 := by
  intro i x a b
  have h := proj_lipschitz a b
  rw [show sharedEnc i x (circlePoint a) - sharedEnc i x (circlePoint b)
      = (proj (circlePoint a) - proj (circlePoint b), (0 : ℝ)) by
    simp [sharedEnc]]
  rw [Prod.norm_def]
  simpa using h

/-- With the obligation met, perfect locking gives exact agreement even though
the encoder varies from site to site. -/
theorem sharedEnc_compatible :
    Compatible U (fun i x => sharedEnc i x (circlePoint (locked (patchOf i)))) 0 :=
  compatible_of_shared_phase_locked U patchOf locked sharedEnc 1
    sharedEnc_shared sharedEnc_lipschitz locked_is_phase_locked

/-- And the reports are not all the same value: the site-dependent coordinate is
what the generalization was for. -/
theorem sharedEnc_nonconstant :
    sharedEnc false 0 (circlePoint (locked (patchOf false)))
      ≠ sharedEnc false 2 (circlePoint (locked (patchOf false))) := by
  simp [sharedEnc, siteWeight, Prod.ext_iff]

/-- **The same population, with the overlap obligation dropped.** The two
patches encode the shared site's second quantity differently — one reports `0`
where the other reports `1` — and nothing else changes. -/
noncomputable def splitEnc : Bool → Fin 3 → ℝ × ℝ → ℝ × ℝ :=
  fun i _ p => (proj p, if i then 1 else 0)

theorem splitEnc_lipschitz : UniformLipschitzEncoder splitEnc 1 := by
  intro i x a b
  have h := proj_lipschitz a b
  rw [show splitEnc i x (circlePoint a) - splitEnc i x (circlePoint b)
      = (proj (circlePoint a) - proj (circlePoint b), (0 : ℝ)) by
    simp [splitEnc]]
  rw [Prod.norm_def]
  simpa using h

/-- The obligation is what fails, and it fails at the shared site. -/
theorem splitEnc_not_shared : ¬ SharedEncoder U splitEnc := by
  intro h
  have h1 := congrFun (h false true 1 (by simp [U]) (by simp [U])) (circlePoint 0)
  simp [splitEnc, Prod.ext_iff] at h1

/-- **Phase order does not rescue it.** The population is phase locked, the
encoder family is uniformly Lipschitz, and the patches still disagree by a full
unit on the site they share. So `SharedEncoder` carries content in
`compatible_of_shared_coherence`, and coherence is not a substitute for it. -/
theorem splitEnc_not_compatible :
    ¬ Compatible U (fun i x => splitEnc i x (circlePoint (locked (patchOf i)))) 0 := by
  intro h
  have h1 := h false true 1 (by simp [U]) (by simp [U])
  rw [show splitEnc false 1 (circlePoint (locked (patchOf false)))
      - splitEnc true 1 (circlePoint (locked (patchOf true))) = ((0 : ℝ), (-1 : ℝ)) by
    simp [splitEnc, proj, circlePoint, locked, patchOf]] at h1
  rw [Prod.norm_def] at h1
  simp only [Real.norm_eq_abs, abs_zero, abs_neg, abs_one, max_eq_right zero_le_one] at h1
  linarith

#print axioms pair_compatible
#print axioms pair_readout_nonconstant
#print axioms pair_second_nonconstant
#print axioms pair_fst_compatible
#print axioms split_fst_compatible
#print axioms split_not_compatible
#print axioms split_not_compatible_lt_one
#print axioms sharedEnc_compatible
#print axioms sharedEnc_nonconstant
#print axioms splitEnc_not_shared
#print axioms splitEnc_not_compatible

end VectorContent
end Examples
end PhysicsOfConsciousness
