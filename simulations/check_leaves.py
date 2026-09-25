#!/usr/bin/env python3
"""Gate: detect modules whose theorems are consumed by nothing outside themselves.

C1's defect — a module that is imported but none of whose theorems are referenced
anywhere outside itself, the witnesses and the root aggregator — is the exact
shape that made ``Phase8_SelfConsistency`` a leaf in the edge graph. The build
certifies that every module compiles, not that any module's results feed into
another.

This script checks, for each phase module, whether any of its declarations is
referenced from a *non-trivial consumer* (any Lean file except the module
itself, ``PhysicsOfConsciousness.lean``, and the witnesses — ``Examples.lean``
and the per-phase files under ``Examples/``). A module with zero such references
is a leaf — its types are imported; its theorems are dead.

## What counts as a reference

A reference is a *resolved constant*, not a token that looks like one. Three
rules make the difference, and each is a way the first implementation counted a
consumer that Lean would not:

* **Only an importer can consume.** A file references a constant of `A` only if
  it imports `A`, directly or transitively; otherwise the name is not in scope
  and whatever the token is, it is not that constant. This is also what rules
  out the reverse direction: the module `A` imports cannot be consuming `A`.
* **A declaration carries its namespaces.** `Widget.ofThing` declared inside
  `namespace Pkg` is `Pkg.Widget.ofThing`, and a file that mentions the
  structure `Widget` — declared elsewhere — has not mentioned it.
* **A name resolves only if it resolves uniquely.** A constant may be spelled
  in full or by any trailing segment of its name, which is also how dot
  notation on a term reaches it. Where two constants visible in the same file
  share a spelling, that spelling resolves to neither: `Network.run` and
  `Trajectory.run` are two constants, and a bare `run` next to both of them is
  a token, not a consumer.

**Comments are stripped before searching.** A name that appears only in a
docstring is exactly the state C1 was in: discussed in prose, unused in code.
Counting prose as consumption would let the gate certify the defect it exists to
find. (The block-comment stripper is a non-greedy match and does not model Lean's
nested ``/- -/``; a nested comment leaves a fragment behind, which can only make
the check stricter, never laxer.)

Every remaining inaccuracy is in the strict direction, and deliberately so: a
lemma reached by the `simp` set rather than by name leaves no token behind, and
an ambiguous spelling is refused rather than credited. The gate can therefore
call a used module a leaf and ask for a decision; it cannot call a dead module
used, which is the failure that matters.

``ALLOWED_LEAVES`` is the recorded baseline: modules that are leaves today, each
with the reason. A leaf outside that set fails the gate, and so does an entry
that has stopped being a leaf — an exemption nobody removes is how a gate rots.

Run: python simulations/check_leaves.py

Exit 0 if the leaf set is exactly ``ALLOWED_LEAVES``, 1 otherwise.
"""

from __future__ import annotations

import re
from pathlib import Path

from repo_root import REPO

LEAN_DIR = REPO / "PhysicsOfConsciousness"

# Modules whose declarations need not be consumed by anything else:
#   Chain.lean — top composition module, no consumer by design.
#   PhysicsOfConsciousness.lean — root aggregator, no content.
#   Axioms.lean — empty of theorems.
NOT_CHECKED = {
    "Chain.lean",
    "PhysicsOfConsciousness.lean",
    "Axioms.lean",
}
# Consumers that do not count as real consumption:
#   PhysicsOfConsciousness.lean — just re-exports, no content.
#   The witnesses — they import everything they inhabit, so consumption there is
#     not usage but presence. Treating one as a consumer would make every module
#     look non-leaf and defeat the check.
NOT_CONSUMERS = {"PhysicsOfConsciousness.lean"}
# The witnesses are ``Examples.lean``, which is now an index, and the per-phase
# files under ``Examples/`` that carry the witnesses themselves. Both halves are
# recognised by *path* rather than by name: a name-based exemption silently stops
# covering a witness the moment one is added in a directory.
WITNESS_DIR = "Examples"

# The recorded baseline. Each entry is a module that is a leaf *and is known to
# be one*, with the reason it is tolerated. Adding to this dict is a decision;
# it should be made in the ledger, not in passing.
ALLOWED_LEAVES: dict[str, str] = {
    "Phase3_FeedbackLedger.lean": (
        "deliberate — a terminal work-store result for one joint phase/register "
        "transition. Routing it into the chain's thermal edge would claim local "
        "detailed balance and a common reservoir for sensing and reset, which "
        "this ledger deliberately prices as declared work instead"
    ),
    "Phase6_CovarianceRank.lean": (
        "deliberate — the covariance-factor singular-tail inequality is a "
        "terminal linear reconstruction limit. The task's covariance and "
        "singular bases are measured inputs; no nonlinear decoder or physical "
        "encoding in the chain satisfies its rank hypothesis by default"
    ),
    "Phase6_SampledRank.lean": (
        "deliberate — the sampled-eigenbasis input law is a terminal witness "
        "that attains the weighted linear floor. No chain edge assumes that "
        "the candidate's inputs follow this law"
    ),
    "Phase8_OrderSpeed.lean": (
        "deliberate — the finite-time magnitude bound is a terminal "
        "probability-current constraint. The chain has no calibrated mapping "
        "from that current cost to heat, work or cortical mode prices"
    ),
    "Phase5_ContentCover.lean": (
        "deliberate — gluing and selection restated over the decodability "
        "cover of content variables. No chain edge rests on it: E78 identifies "
        "the oscillator index with the content cover, and relating a region's "
        "phase order to what it decodes is that assumption, not a theorem here"
    ),
    "Phase6_ConditionedReconstruction.lean": (
        "deliberate — the input-conditioned reconstruction bound is terminal. "
        "E89 is stated for one fixed contraction, and no chain edge supplies "
        "the scene input, its gain or a physical conditioned readout"
    ),
    "Phase3_LandauerBridge.lean": (
        "deliberate — the module is the discharge route for the chain's n3 → n4 "
        "edge, and the edge stays a named hypothesis. `PredictiveDissipation."
        "ofLandauer` derives Still's bound from `landauer_bound`, but only "
        "under the physical identification `(nonpredictiveInfo μ κ).toReal ≤ "
        "erasedEntropy t`, which nothing here derives and "
        "`nonpredictive_eq_zero_of_injective` shows is not free. Routing the "
        "constructor into `chain` would assert that identification for every "
        "dissipating register. `E34`'s docstring names the module as what "
        "would discharge the edge, and `Examples/Phase3.lean` §18 discharges "
        "it on the one-bit eraser, where the inequality is an equality"
    ),
    "Phase3_MeasureFeedback.lean": (
        "deliberate — a generalization, whose consumer is the reader of the "
        "theory it subsumes rather than another module. It carries the path "
        "law to an arbitrary measurable space, and states the bridge "
        "`extendedKL_eq_klDiv` over the finite development it imports, so the "
        "dependency runs from here into the finite theory and cannot run back. "
        "The chain's thermodynamic edges are stated on finite state spaces, "
        "and the entropy form of the balance does not survive the "
        "generalization at all"
    ),
    "Phase3_PhaseSensor.lean": (
        "deliberate, and terminal by content. `channel_eq_of_phase_eq` and "
        "`channel_ne_iff_fiberCount_ne` delimit `Phase3_ObservationalLearning`'s "
        "postulated observation law: they say what a phase-derived channel can "
        "and cannot separate, and that the condition is on the readout's fibre "
        "counts rather than on the order parameter. A consumer would be a "
        "result deriving learning performance from coherence, which is exactly "
        "the implication this module shows does not hold — "
        "`Examples/PhaseSensor.lean` §27 exhibits equal coherence separating "
        "and not separating the same parameters"
    ),
    "Phase3_Preparation.lean": (
        "deliberate — it prices a stage the rest of the development leaves "
        "supplied. `withPreparation` prepends the preparation to a "
        "`FiniteProtocol` and to a `PathwiseStore` so that the existing "
        "telescoped balance and store bounds cover it, so the results are "
        "applied where an agent is built — `Examples/Preparation.lean` — and "
        "not restated downstream. Charging every `prior` in the chain would "
        "assert that each agent's preparation is the constant channel this "
        "module prices"
    ),
    "Phase5_PhaseLifts.lean": (
        "deliberate — F2's results are about the obstruction, and the chain routes "
        "around it rather than through it"
    ),
    "Phase5_TwistedGluing.lean": (
        "deliberate, and terminal by content rather than by omission. The "
        "module's own results are limitative: `isCoboundary_of_phaseField` and "
        "`gluesUpToPhase_of_phaseField` show that any Kuramoto configuration, "
        "twisted or splay, has coboundary offsets and glues, so there is no "
        "obstruction left to route into `chain`. A consumer is constructible "
        "only with the trivial phase action, under which `TwistedFamily` "
        "collapses to `LocalSectionSynchronization` and the link would restate "
        "Phase5_GlobalSection. A non-vacuous one needs `IsFreeOn`, which the "
        "trivial action fails, and that requires enlarging the local state to "
        "carry phase — a modelling decision, not a formalization step, and not "
        "one to be taken to close this gate"
    ),
    "Phase7_FiniteRegion.lean": (
        "deliberate, and terminal by content. The module's results delimit "
        "another module's theorem: `cellKernel_not_sitedOn` says that the "
        "vanishing in `Phase7_Rigidity`'s `fieldCorrelation_sited_eq_zero` is "
        "about measure-zero support rather than about finitely many "
        "components, and `no_forced_gap_of_best_wired` says that the gap in "
        "`rigid_gap` is forced by the missing wire alone. A delimitation has "
        "nothing downstream to feed: its consumers are the reader of the "
        "theorem it bounds and the witnesses of `Examples/FiniteRegion.lean`. "
        "Routing it into `chain` would assert that a cortical architecture is "
        "a finite cell reconstruction, which is a physical identification this "
        "development does not make"
    ),
    "Phase10_PhysicalUnity.lean": (
        "deliberate — the margin theorem is the formal core of the physical-"
        "unity premise, which is a separate necessary condition and not a node "
        "of the conditional chain. That chain is substrate-neutral by design; "
        "routing `not_physicallyEnforced_of_margin` into `chain` would make its "
        "edges exclude digital claimants on a premise they do not state. Its "
        "consumers are the physical-unity paper and the witnesses of "
        "`Examples/PhysicalUnity.lean`"
    ),
    "Phase10_AgreementResistance.lean": (
        "deliberate — the resistance bounds carry the physical-unity paper's "
        "typical-case agreement result, a second route beside the worst-case "
        "chaining of the conditional chain rather than a node of it. Routing "
        "them into `chain` would make its edges rest on the harmonic "
        "approximation that turns resistance into phase variance, which the "
        "chain does not state. Their consumers are the physical-unity paper "
        "and the witnesses of `Examples/AgreementResistance.lean`"
    ),
    "Phase10_RelativePhase.lean": (
        "deliberate — the relative-phase encoder answers the worst case of the "
        "chaining bound, a phase gradient or winding, by changing what the "
        "encoder reads rather than by bounding how far the gradient runs. The "
        "conditional chain's encoders read absolute phase, so routing "
        "`relContent_eq_of_wave` into `chain` would change the encoder the "
        "chain states. Its consumers are the physical-unity paper and the "
        "witnesses of `Examples/RelativePhase.lean`"
    ),
    "Phase10_UnityWindow.lean": (
        "deliberate — the unity window reads the causal-cone deadline forward "
        "and adds the relaxation edge for a declared contraction rate. It is a "
        "timing condition of the physical-unity premise, not a node of the "
        "substrate-neutral conditional chain, and identifying the rate with a "
        "spectral gap is made in the paper's text rather than proved. Its "
        "consumers are the physical-unity paper and the witnesses of "
        "`Examples/UnityWindow.lean`"
    ),
}

# A declaration head: optional attributes and modifiers, the keyword, the name.
# The name keeps its own dotted prefix — `Widget.ofThing` is a declaration in
# `Widget`'s namespace, and truncating it there would make every mention of the
# structure `Widget` look like a use of this constant.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:noncomputable|protected|private|scoped)\s+)*"
    r"(?:structure|class|inductive|theorem|lemma|def|abbrev|opaque)\s+"
    r"([^\W\d][\w.'₀-₉]*)"
)
NAMESPACE_RE = re.compile(r"^namespace\s+([\w.'₀-₉]+)")
END_RE = re.compile(r"^end\s+([\w.'₀-₉]+)\s*$")
IMPORT_RE = re.compile(r"^import\s+([\w.'₀-₉]+)", re.MULTILINE)
TOKEN_RE = re.compile(r"[^\W\d][\w.'₀-₉]*")

BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)


def is_witness(path: Path, lean_dir: Path) -> bool:
    """True for the witness index and for every per-phase file under it."""
    relative = path.relative_to(lean_dir)
    return relative.name == f"{WITNESS_DIR}.lean" or relative.parts[0] == WITNESS_DIR


def strip_comments(text: str) -> str:
    """Remove Lean block and line comments, so prose never counts as usage."""
    return LINE_COMMENT_RE.sub("", BLOCK_COMMENT_RE.sub("", text))


def suffixes(name: str) -> list[str]:
    """Every spelling that can reach *name*: the full name and its tails.

    `Pkg.Widget.ofThing` is reachable as itself, as `Widget.ofThing` from
    inside `Pkg`, and as `ofThing` from inside `Pkg.Widget` — which is also the
    segment dot notation on a `Widget` term contributes.
    """
    parts = name.split(".")
    return [".".join(parts[i:]) for i in range(len(parts))]


def declarations(code: str) -> set[str]:
    """Full names of the declarations in *code*, which must be comment-free."""
    names: set[str] = set()
    namespaces: list[str] = []
    for line in code.splitlines():
        opened = NAMESPACE_RE.match(line)
        if opened:
            namespaces.append(opened.group(1))
            continue
        closed = END_RE.match(line)
        if closed:
            if namespaces and namespaces[-1] == closed.group(1):
                namespaces.pop()
            continue
        declared = DECL_RE.match(line)
        if declared:
            names.add(".".join([*namespaces, declared.group(1)]))
    return names


class Library:
    """The Lean files under a package directory, with imports resolved.

    Everything the gate asks is a question about one file's view of the others:
    what it imports, what names that makes visible, and which of them it
    spells. Each is computed once per file and kept.
    """

    def __init__(self, lean_dir: Path) -> None:
        self.lean_dir = lean_dir
        self.files = sorted(path.resolve() for path in lean_dir.rglob("*.lean"))
        self.code = {path: strip_comments(path.read_text(encoding="utf-8")) for path in self.files}
        self.declared = {path: declarations(self.code[path]) for path in self.files}
        self.imports = {path: self._imports(self.code[path]) for path in self.files}
        self._reachable: dict[Path, frozenset[Path]] = {}
        self._resolution: dict[Path, dict[str, str | None]] = {}
        self._spellings: dict[Path, set[str]] = {}

    def _imports(self, code: str) -> list[Path]:
        """The files this one imports; anything outside the package is ignored."""
        known = set(self.files)
        candidates = (
            (self.lean_dir.parent / (module.replace(".", "/") + ".lean")).resolve()
            for module in IMPORT_RE.findall(code)
        )
        return [path for path in candidates if path in known]

    def reachable(self, path: Path) -> frozenset[Path]:
        """Every file *path* imports, directly or transitively."""
        cached = self._reachable.get(path)
        if cached is not None:
            return cached
        reached: set[Path] = set()
        frontier = list(self.imports[path])
        while frontier:
            found = frontier.pop()
            if found in reached:
                continue
            reached.add(found)
            frontier.extend(self.imports[found])
        self._reachable[path] = frozenset(reached)
        return self._reachable[path]

    def resolution(self, path: Path) -> dict[str, str | None]:
        """Each spelling visible in *path*, mapped to the constant it reaches.

        ``None`` where two visible constants share the spelling: a name that
        does not resolve uniquely reaches neither of them.
        """
        cached = self._resolution.get(path)
        if cached is not None:
            return cached
        table: dict[str, str | None] = {}
        visible = set(self.declared[path])
        for imported in self.reachable(path):
            visible |= self.declared[imported]
        for full in visible:
            for form in suffixes(full):
                table[form] = full if form not in table else None
        self._resolution[path] = table
        return table

    def spellings(self, path: Path) -> set[str]:
        """Every name *path*'s code spells, each with its trailing segments."""
        cached = self._spellings.get(path)
        if cached is not None:
            return cached
        spelled: set[str] = set()
        for token in TOKEN_RE.findall(self.code[path]):
            spelled.update(suffixes(token.strip(".")))
        self._spellings[path] = spelled
        return spelled


def consumes(lib: Library, consumer: Path, module: Path) -> bool:
    """True if *consumer*'s code spells a constant that *module* declares."""
    resolution = lib.resolution(consumer)
    declared = lib.declared[module]
    return any(resolution.get(form) in declared for form in lib.spellings(consumer))


def is_consumer(lib: Library, consumer: Path, module: Path) -> bool:
    """True if *consumer* is a file whose references to *module* would count."""
    return (
        consumer != module
        and consumer.name not in NOT_CONSUMERS
        and not is_witness(consumer, lib.lean_dir)
        and module in lib.reachable(consumer)
    )


def module_has_consumer(lib: Library, module: Path) -> bool:
    """True if at least one declaration of *module* is referenced in the code of
    a file that imports it and is not a witness or the root aggregator."""
    if not lib.declared[module]:
        return True  # no declarations to be a leaf
    return any(
        consumes(lib, consumer, module)
        for consumer in lib.files
        if is_consumer(lib, consumer, module)
    )


def find_leaves(lean_dir: Path = LEAN_DIR) -> list[Path]:
    """Every checked module with no code-level consumer, in path order."""
    lib = Library(lean_dir)
    return [
        module
        for module in lib.files
        if module.name not in NOT_CHECKED
        and not is_witness(module, lean_dir)
        and not module_has_consumer(lib, module)
    ]


def classify(
    leaves: list[Path], allowed: dict[str, str] = ALLOWED_LEAVES
) -> tuple[list[Path], list[str]]:
    """Split the leaf set against the recorded baseline.

    Returns the leaves nobody has recorded and the recorded names that have
    since acquired a consumer — the two ways the tree and `ALLOWED_LEAVES` can
    disagree, and both are failures.
    """
    leaf_names = {module.name for module in leaves}
    unrecorded = [module for module in leaves if module.name not in allowed]
    stale = sorted(name for name in allowed if name not in leaf_names)
    return unrecorded, stale


def report_unrecorded(unrecorded: list[Path]) -> None:
    print(
        f"check_leaves: {len(unrecorded)} module(s) have zero declarations "
        "consumed\n  outside themselves, the Examples/ witnesses, and the root "
        "aggregator.\n"
    )
    for module in unrecorded:
        print(f"  {module.relative_to(REPO)}")
    print(
        "\n"
        "A module whose declarations are referenced by nothing outside\n"
        "itself and the Examples/ witnesses is a leaf in the edge graph.\n"
        "Its types are imported; its theorems are not. That is how C1's\n"
        "defect arose in Phase8_SelfConsistency. Wire a consumer, or record\n"
        "the module in ALLOWED_LEAVES with the reason it stays dangling.\n"
    )


def report_stale(stale: list[str]) -> None:
    print(
        f"check_leaves: {len(stale)} recorded leaf(s) now have a consumer.\n"
        "  Delete them from ALLOWED_LEAVES — an exemption nobody removes is\n"
        "  how a gate stops meaning anything.\n"
    )
    for name in stale:
        print(f"  {name}")
    print()


def main() -> int:
    unrecorded, stale = classify(find_leaves())

    if not unrecorded and not stale:
        print(
            "check_leaves: no unrecorded leaf modules "
            f"({len(ALLOWED_LEAVES)} recorded, all still leaves)."
        )
        return 0

    if unrecorded:
        report_unrecorded(unrecorded)
    if stale:
        report_stale(stale)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
