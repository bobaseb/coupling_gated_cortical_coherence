# Cover letter — draft

**Status:** draft. The salutation, journal name and any journal-specific
statements are left blank pending the target decision recorded under P4. The
substantive paragraphs below are final and track `main.tex`.

---

Dear Editors,

Please consider the enclosed manuscript, "Coupling-gated cortical coherence:
what a field theory of conscious unity must assume, and what it predicts."

Field accounts of cortical coordination — that distributed neural processes are
coupled in part through the endogenous extracellular electromagnetic field — are
usually assessed as a whole, which makes them hard to test. This manuscript
separates such an account into three parts that can be judged independently: a
prediction that can be tested, a composition that can be checked, and an
identification that can be argued about.

**The testable part.** If cortical coupling is slowly gated, so that recovery of
coherence after sleep is driven by a coupling parameter crossing a
synchronization threshold, then that recovery is not free to take an arbitrary
time course. The stationary theory fixes a square-root onset and a von Mises
concentration–coherence relation with no fitted shape parameter. We give the
six design requirements an adequate test needs, with failure conditions declared
in advance, and we state the framework's sharpest open limitation rather than
working around it: effective coupling and phase diffusion have not been measured
in consistent units in the same cortical regime, so the threshold is not yet an
evaluable statement about cortex. Measuring them is item 1 of the protocol, not
an assumption of it.

**Two results that transfer beyond this framework.** Our numerical controls
restrict the hypothesis rather than support it, and two of them are of general
methodological interest. First, the apparent onset exponent measured from a
finite ramp is a function of ramp speed, so an exponent fitted to a driven
recovery trace reports the drive at least as much as the mechanism — a caution
for any analysis that reads a critical exponent off a driven transition, ours
included. Second, a coupling plasticity that descends a squared-drift objective
preserves coherence while moving *away* from the environmental structure it is
expected to learn, below the level of a shuffled-label comparison. Dissipation
minimization does not imply representational learning in this regime, and we
report the negative result rather than tuning it away.

**The checkable part.** A Lean 4 development composes finite information
capacity, Landauer's bound, a predictive dissipation bound, the noisy Kuramoto
transition, sheaf gluing and Banach's fixed-point theorem into one conditional
theorem, and isolates the eight hypotheses that composition consumes: one
independent physical premise, three formalization gaps, two modelling
assumptions and two physical commitments. A common toy model satisfies all
eight, so their conjunction is consistent — which is not a claim that cortex
realizes it. The development declares no axioms of its own. What formalization
adds beyond a prose list of assumptions is that the list cannot be lost: the
characteristic failure in an argument of this shape is a silent change of
subject, and type-checking forbids reading a theorem about a stationary density
as a claim about a trajectory, or agreement of phases as compatibility of
representations.

**The arguable part.** We state, and defend, the identification of the glued
global section with the unity of a conscious episode and of the reflexive fixed
point with a minimal self. We present this as a philosophical commitment with
reasons, not as a theorem or a simulation result, and we state its costs: it
does not address why any physical condition is accompanied by experience, it is
open to the standard objection that a system could meet every condition while
nothing is experienced, and it is multiply realizable, so no conclusion about
artificial systems follows from the formal results. We also name what would
count against it — dissociation between demonstrable overlap compatibility and
reported unity — and the measurement that is missing before such a test is
possible.

We would welcome review from referees in nonlinear dynamics or statistical
physics of neural populations, and, separately, from a referee willing to
engage with the interpretive commitment on its own terms. The Lean development,
simulation code and saved numerical summaries are public, and every computed
value in the manuscript is generated from the saved artifacts.

The manuscript is original, is not under consideration elsewhere, and its use of
AI assistance is disclosed in the article.

Sincerely,

Sebastian Bobadilla-Suarez
sebastian.bobadilla.s@gmail.com
