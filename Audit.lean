import PhysicsOfConsciousness

/-!
# The axiom audit

`supplementary.tex` makes a claim about this development that no gate checked:

> The development declares **no axioms**: `#print axioms` on any result above
> reports only `propext`, `Classical.choice` and `Quot.sound`.

and, of `Phase8_CriticalExponent`, the stronger form — *every* declaration in
the file depends only on those three. `Axioms.lean` is the record of how that
state was reached: every `axiom` in it is commented out, three of them because
they were **refutable** (§5 of that file), and the design rule that replaced
them puts a physical postulate in a class field, where it is an obligation on
each instance rather than a global assertion.

That claim lived in prose. `lake build` does not check it, and cannot: `sorry`
is a *warning*, a fresh `axiom` is a legal declaration, and a class field
promoted back to a standalone postulate compiles exactly as well as the shape
the design rule forbids. The three removals in `Axioms.lean` §5 are the
evidence that this failure mode is not hypothetical in this repository.

This module closes that gap. It sweeps **every** declaration the library adds
to the environment — not a hand-kept list of headline results, because a list
is a thing that goes stale the next time a theorem is added — and fails the
build if any of them rests on anything but the three.

## What it catches

* A `sorry` anywhere in a real declaration: `sorryAx` is collected like any
  other axiom, so the build fails instead of printing a warning nobody reads.
* A new `axiom`, including one reintroduced into `Axioms.lean`.
* A postulate imported from outside Mathlib's own footprint.

## What it does not catch

`example ... := sorry` adds no constant to the environment, so the sweep never
sees it. The `no-lean-sorry` pre-commit hook covers that case textually.

The sweep is the published sentence, executable. It is deliberately stated
over the whole library rather than over `chain`: a theorem that depends on
nothing suspect tells you about that theorem, and the manuscript's claim is
about the development.
-/

open Lean Elab Command

namespace Audit

/-- Mathlib's own axiom footprint, and the whole of what this development is
permitted to rest on. `Quot.sound` and `propext` are Lean's; `Classical.choice`
is classical logic, which the analysis in Phases 3, 5 and 8 uses throughout.
Adding a fourth entry here is a change to what the manuscript claims, so it is
a change that belongs in `supplementary.tex` in the same commit. -/
def permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Is `m` a module of this development? The root aggregator carries the
library's own name and so is not caught by the prefix test. -/
def isOurs (m : Name) : Bool :=
  m == `PhysicsOfConsciousness || (`PhysicsOfConsciousness).isPrefixOf m

end Audit

/-! ## The sweep

Reports the footprint on a passing run — an audit whose output is silence gives
a reader no way to tell it from an audit that did not run — and throws on a
declaration resting on anything else. -/

run_cmd do
  let env ← getEnv
  let mods := env.allImportedModuleNames
  let mut checked : Nat := 0
  let mut offenders : Array (Name × Array Name) := #[]
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    unless Audit.isOurs mods[idx.toNat]! do continue
    checked := checked + 1
    let extra := (← liftCoreM <| collectAxioms c).filter
      fun a => !Audit.permitted.contains a
    unless extra.isEmpty do offenders := offenders.push (c, extra)
  -- An empty sweep passes vacuously, which is how a gate rots: rename the
  -- library, move a module out from under the prefix, and this file goes green
  -- while checking nothing. The library is 37 modules and about two thousand
  -- declarations, so zero is never the right answer.
  if checked == 0 then
    throwError "axiom audit swept no declarations. `Audit.isOurs` matched none \
      of the {mods.size} imported modules, so the gate is checking nothing. \
      Was the library renamed?"
  unless offenders.isEmpty do
    let lines := offenders.toList.map fun (c, ax) => s!"  {c} depends on {ax.toList}"
    throwError "axiom audit failed: {offenders.size} of {checked} declarations \
      rest on axioms outside the permitted three.\n\
      {String.intercalate "\n" lines}\n\
      `supplementary.tex` claims the development declares no axioms. Either the \
      declaration above is wrong, or that claim is."
  logInfo s!"axiom audit: {checked} declarations in {mods.filter Audit.isOurs |>.size} \
    modules, all resting only on {Audit.permitted.toList}."
