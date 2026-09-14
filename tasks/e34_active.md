# E34Active — one register's common resource ledger, 2026-09-14

## Intent and constraints

Close the open modelling question recorded for `E34Active`: supply a common
register/controller resource model in which the named energies, the heat budget
and the actual operations are identified, and *derive* the controlled substep's
heat allocation instead of comparing two numbers from unrelated toy components.

The register is named throughout. Every operation in the model is an elementary
`FiniteFeedbackStep` whose controller is that register's own state type, every
operation exchanges heat with that register's reservoir at that register's
temperature, and the budget is that register's dissipated heat. Landauer's
bound stays a lower bound on the total and is not used as an upper bound on a
part.

Out of scope, and to remain open after this change: composing the operations
into one evolving joint law with preparation, resets and a continuing energy
source (the separate "one continuing physical agent" item); learning from
experience; `E45Active`'s spatial coupling convergence; cortical identification.
No new axiom, dependency, Python source, simulation or reference is added.

## Model and success criteria

`RegisterLedger sys S` carries the register's update `update`, a finite index
of operations, each operation's step and heat observable, strict positivity,
local detailed balance for every operation at `Thermodynamics.temperature`, and
one accounting identity:

    heat_dissipation update = ∑ i, (step i).meanHeat (heat i)

`Compressive i` says the operation does not increase the joint
register–environment entropy. The two derived results are:

1. a compressive operation cannot draw heat from the register's reservoir —
   this is the existing path-model second law `heat_bound` at the register's
   own temperature, not a new premise; and
2. **the allocation**: if every other operation is compressive, the remaining
   operation's heat is at most the register's dissipation. `E34Active` for that
   operation then follows with no numerical comparison of separate models.

Under `StatisticalMechanics`, the total is additionally exhibited as the
register's own bath entropy change, so the budget is the named register's
physical bookkeeping rather than an assigned cost.

The witness is the one-bit eraser of `Examples/Bit.lean` — the very register the
active chain already names, at temperature one with Landauer heat `log 2`. Its
two operations act on a lamp bit through the same log-odds family: the
controlled operation drives the lamp toward the register's bit at odds 2 : 1
from a mostly disagreeing law, with heat `(2/5) log 2`; the other operation
relaxes the uniform law toward agreement at odds 4 : 1, with heat `(3/5) log 2`.
The heats sum to `log 2` exactly. These are proposed exact Lean equalities.

Regressions, each of which must fail before the corresponding premise is used:

- The controlled operation is *not* compressive: it increases joint entropy, so
  its own second law gives it no nonnegative-heat bound and the allocation
  genuinely needs the ledger.
- Compressiveness alone does not bound an operation by the register's budget: a
  compressive operation of the same family has heat `(7/3) log 2 > log 2`.
- The ledger alone does not bound it either: a second ledger for the same
  register, whose other operation is entropy-increasing and draws heat from the
  reservoir, satisfies every other field and allocates `(7/6) log 2` to its
  controlled operation, above the register's whole dissipation.
- The controlled operation really is controlled: its transition depends on the
  register's state.

The active branch must compose end to end with the derived edge, joining the
existing mesh, field and cover witnesses.

## Plan

1. [x] Write failing Lean specifications for the ledger structure, the two
   derived results, the witness equalities and the regressions; observe failure.
2. [x] Add `RegisterLedger` and its derivations beside `FiniteFeedbackStep`;
   derive `E34Active` from a ledger in `Chain.lean`.
3. [x] Add the witness and regressions under `Examples/`, and the composed
   active branch that uses the derived edge.
4. [x] Align article, supplement, status tables, primer and ledgers with the
   derived allocation and its remaining premises. Rebuild and inspect the
   tracked PDFs and refresh the assembled arXiv submission.
5. [x] Pass the complete zero-warning Lean build and axiom audit, headline
   axiom checks, applicable publication/freshness gates and `git diff --check`.

## Stop rule

Stop at the derived allocation, its witness and its regressions. The ledger
identity and the compressiveness of the register's other operations are the
model's physical inputs; they are named, and the regressions show each is
load-bearing. Sequencing the operations into one evolving law, deriving the
ledger from a microscopic bipartite dynamics, and `E45Active` remain separate
open work.

## Completed result and verification — 2026-09-14

`RegisterLedger` lives beside `FiniteFeedbackStep` in
`Phase3_AgencyThermodynamics.lean`. `opHeat_nonneg_of_compressive` is the
existing `heat_bound` at the register's temperature;
`opHeat_le_dissipation` derives the allocation from the ledger and that
nonnegativity; `ledger_bathEntropy` exhibits the budget as the register's own
bath entropy change. `Chain.e34Active_of_ledger` turns a ledger into the named
bridge, and `registerBudget_e34Active` discharges it for the one-bit eraser's
ledger without any numerical comparison of separate models.

`Examples/RegisterBudget.lean` supplies the log-odds family
(`op_positive`, `op_local_balance`, `op_final`, `op_meanHeat`, `law_entropy`),
the register's two operations and the exact ledger `(2/5) log 2 + (3/5) log 2 =
log 2`. `act_not_compressive`, `compressive_exceeds_budget`, the `leaky` ledger
with `leaky_exceeds_budget` and `leaky_other_not_compressive`, and
`act_depends_on_register` fence the premises.
`chain_active_budget_jointly_satisfiable` composes the active branch through
the derived edge.

The red specification run failed before the declarations existed. The full
`lake build` has zero warnings; the default axiom audit covers 2,773
declarations in 46 modules with only `propext`, `Classical.choice` and
`Quot.sound`, and the explicit headline axiom checks agree. All applicable
gates pass; the Python hooks correctly skip a change that adds no Python, and
the 143 publication and simulation tests pass.

The rebuilt article, supplement and primer have 41, 36 and 79 pages, one more
each than the pre-change baseline, with no LaTeX warnings or overfull boxes.
The 53-page arXiv submission compiles from its unpacked archive and passes
manifest freshness. Every changed document is committed with its rebuilt PDF,
each PDF is newer than every resolved source dependency, and `git diff --check`
passes.

The edge's budget allocation is now derived inside one named resource model.
What the model still supplies as physical input is the ledger identity and the
compressiveness of the register's other operations; what it does not supply is
a sequential joint law, a continuing energy source, the coupling-convergence
implication of `E45Active`, or any cortical identification.
