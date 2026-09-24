# G24 fixed CPU validation protocol — 2026-09-24

This protocol fixes the next validation runs before their artifacts are
generated. Earlier parity-split runs are exploratory. The synthetic task has
four binary global coordinates: two scene coordinates and two self coordinates.
Two three-value local views overlap on one scene and one self coordinate. The
five-value target is the four coordinates plus the relation self0 minus scene1.
The encoding region is the candidate's measured internal code; the phase
candidate reads node 1 after the declared communication rounds.

Validation runs use the new `scene_pair` split: train on states whose two scene
coordinates agree, and test on states whose two scene coordinates disagree.
This shift is distinct from the exploratory even/odd parity split and can
make the training covariance singular. Seeds are 24, 25 and 26 at zero local
noise, plus seed 24 at noise standard deviation 0.1; each state is repeated
16 times. Fit on training states only. No checkpoint selection uses test scores.

Score mean summed squared error over the five target coordinates, self-relation
squared error, and overlap error. Score self-state shifts of 0.5 and 1.0 while
the scene is fixed, and disagreement of 0.5 and 1.0 introduced only in the
second local view's shared coordinates while the global target is fixed.
Report train and held-out error separately. Compare the linear ranks 0 through
4 against the train-covariance singular tail; a held-out deviation is recorded
as a distribution-shift result, not a failed training theorem. Report the
full-capacity and shuffled-code controls, a decoder fitted to incompatible
targets, and the same-order/different-code phase control.

The nonlinear controls are the existing two-token, width-four, one-head
decoder-only attention block with query/key dimension one and the two-node
phase graph with zero, one or three communication rounds. Use 20 optimizer
iterations and a 120-second CPU fitting budget per candidate. Record the
actual code and its effective rank at relative singular-value tolerance
1e-6, five output scalars, causal past, rounds, parameter count, dense bytes,
fit time and inference latency. Hardware energy is outside this CPU protocol.
An artifact-only audit recomputes scores and ranks from checkpoints and fails
on drift. Outcomes are interpreted for these candidates and splits only.

## Timestamped confirmation batch

After this protocol-only commit, run the same scene-pair split at seeds 27,
28 and 29 with zero noise, and seed 27 with noise standard deviation 0.1.
Each state is repeated 16 times; nonlinear fitting uses 20 iterations.
No result from those seeds has been inspected at the time of this protocol
commit. Save candidate and rank-limited linear checkpoints separately for
each run. Recompute candidate scores, internal codes and linear floors from
saved artifacts. Run the three-node locality control at seed 27 on the same
scene-pair split. Count a numerical replication if every artifact audit passes,
every candidate fits within 120 CPU seconds, and the full linear map's
held-out scene-family squared error exceeds 1 while its training error stays
below 0.1 at all three noiseless seeds. Report the actual values and any
failure of this rule. This threshold checks a split-specific distribution
shift; it is not an architecture comparison or an experience test.

The protocol fixes these source bytes by SHA-256 before the confirmation runs:

| Source | SHA-256 |
|---|---|
| `simulations/g24_shared_task.py` | `16730340d92ffb44db646620d03283755db916cf61a8db05c10f2f91ce8865cb` |
| `simulations/g24_candidates.py` | `28badf602c1bd8832077769af447b8d2f0f2da0b2a7fd3be102786ba3d968ded` |
| `simulations/g24_artifact_audit.py` | `e2c517025b0de31e8acfdc047ed0233cac0eab7cdcc7c2a89a031e0ed827e16b` |
| `simulations/g24_locality.py` | `64944187d06c57fb1434d39d77524a95015a61539daf1e091923f25b473eabec` |
