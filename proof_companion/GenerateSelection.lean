import Lean
import PhysicsOfConsciousness

/-!
Propose selection entries by enumerating the *elaborated environment*, never by
matching regular expressions against Lean source. Emits one TSV row per candidate
declaration: module, name, kind, source line, and whether it carries a docstring.

This tool only proposes candidates for `selection.json`; it is not the extractor.
Curating which candidates enter the companion stays a deliberate editorial act
(`README.md`, "Extending coverage"), and `Extract.lean` still re-elaborates every
selected declaration from source. The compiler-generated names filtered below are
therefore a convenience for the curator, not a correctness boundary.

Run from the repository root:
  lake env lean --run proof_companion/GenerateSelection.lean > candidates.tsv
-/

open Lean

namespace ProofCompanion

/-- Suffixes Lean attaches to equation lemmas, recursors, and structure plumbing.
These are generated alongside a declaration rather than written by an author. -/
def generatedSuffixes : List String :=
  [ "casesOn", "recOn", "rec", "brecOn", "below", "ibelow", "binductionOn"
  , "ndrec", "ndrecOn", "noConfusion", "noConfusionType", "injEq", "inj"
  , "sizeOf_spec", "toCtorIdx", "ofNat", "mk", "ctorIdx"
  , "eq_def", "eq_1", "eq_2", "eq_3", "eq_4", "induct", "fun_cases" ]

/-- A name is compiler-generated when any component is internal (`_@`, `match_1`,
`proof_1`, …) or when it ends in one of the generated suffixes above. -/
def isGenerated (name : Name) : Bool :=
  if name.isInternal || name.hasMacroScopes then true
  else
    let comps := name.components.map toString
    comps.any (fun c =>
      c.startsWith "_" || c.startsWith "match_" || c.startsWith "proof_"
        || c.startsWith "eq_" || c.startsWith "unsafe_") ||
    (match name.components.reverse with
     | last :: _ => generatedSuffixes.contains (toString last)
     | [] => true)

def kindOf (info : ConstantInfo) : String :=
  match info with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "recursor"

def run : CoreM Unit := do
  let env ← getEnv
  let mut rows : Array (String × String × String × Nat × Bool) := #[]
  -- Walk the project's own modules only. Iterating `env.constants` would drag the
  -- whole of Mathlib through this loop for no gain: Mathlib results are recorded
  -- as dependencies of a selected proof, never as companion content themselves.
  for idx in [0 : env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    unless (`PhysicsOfConsciousness).isPrefixOf modName do continue
    for name in env.header.moduleData[idx]!.constNames do
      if isGenerated name then continue
      if isPrivateName name then continue
      let some info := env.find? name | continue
      if info.isCtor then continue
      let line ←
        match ← findDeclarationRanges? name with
        | some r => pure r.range.pos.line
        | none => pure 0
      -- No source range means nothing an author wrote at a place we can cite.
      if line == 0 then continue
      let doc := (← findDocString? env name).isSome
      rows := rows.push (toString modName, toString name, kindOf info, line, doc)
  let sorted := rows.qsort (fun a b =>
    if a.1 != b.1 then a.1 < b.1 else a.2.2.2.1 < b.2.2.2.1)
  IO.println "module\tname\tkind\tline\tdocstring"
  for (m, n, k, l, d) in sorted do
    IO.println s!"{m}\t{n}\t{k}\t{l}\t{if d then "yes" else "no"}"
  IO.eprintln s!"{sorted.size} candidate declarations"

end ProofCompanion

unsafe def main : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `PhysicsOfConsciousness }] {} 0
  let ctx : Core.Context :=
    { fileName := "<GenerateSelection>", fileMap := default, options := {} }
  let _ ← (ProofCompanion.run.toIO ctx { env := env })
  return
