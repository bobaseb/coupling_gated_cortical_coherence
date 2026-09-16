import Lean

/-!
Extract selected declarations and their elaboration traces using the repository's
pinned Lean. No project source is edited, and no proof is reconstructed from text.
Run from the repository root with `lake env lean --run proof_companion/Extract.lean`.
-/

open Lean Elab

namespace ProofCompanion

structure Location where
  line : Nat
  column : Nat
  deriving ToJson

def location (p : Position) : Location := ⟨p.line, p.column⟩

structure TacticRecord where
  id : Nat
  parent : Option Nat
  declaration : Option String
  start : Location
  finish : Location
  source : String
  syntax_kind : String
  synthetic : Bool
  goals_before : Array String
  goals_after : Array String
  deriving ToJson

structure DeclarationRecord where
  name : String
  kind : String
  universe_parameters : Array String
  start : Location
  finish : Location
  statement : String
  source : String
  docstring : Option String
  type_dependencies : Array String
  proof_dependencies : Array String
  axioms : Array String
  tactics : Array TacticRecord
  deriving ToJson

structure FieldRecord where
  name : String
  statement : String
  deriving ToJson

structure StructureRecord where
  name : String
  fields : Array FieldRecord
  deriving ToJson

structure ExampleRecord where
  start : Location
  finish : Location
  source : String
  deriving ToJson

structure Snapshot where
  schema_version : Nat := 1
  lean_version : String := Lean.versionString
  source_file : String
  declarations : Array DeclarationRecord
  structures : Array StructureRecord
  anonymous_examples : Array ExampleRecord
  deriving ToJson

def sortedNames (names : Array Name) : Array String :=
  (names.map toString).qsort (· < ·)

def sourceSlice (input : String) (start finish : String.Pos.Raw) : String :=
  String.Pos.Raw.extract input start finish

def ppOptions : Options :=
  ({} : Options).set `pp.width (100 : Nat)

def runMeta (env : Environment) (inputCtx : Parser.InputContext) (action : MetaM α) : IO α :=
  Prod.fst <$> action.toIO
    { fileName := inputCtx.fileName
      fileMap := inputCtx.fileMap
      options := ppOptions } { env := env }

def ppType (env : Environment) (inputCtx : Parser.InputContext) (type : Expr) : IO String :=
  runMeta env inputCtx do return (← Meta.ppExpr type).pretty 100

def ppGoals (ctx : ContextInfo) (mctx : MetavarContext) (goals : List MVarId) :
    IO (Array String) :=
  { ctx with mctx, options := ctx.options.set `pp.width (100 : Nat) }.runMetaM {} do
    goals.toArray.mapM fun goal => return (← Meta.ppGoal goal).pretty 100

def within (p : Location) (a b : Position) : Bool :=
  (a.line < p.line || (a.line == p.line && a.column ≤ p.column)) &&
  (p.line < b.line || (p.line == b.line && p.column ≤ b.column))

def tacticRecord (ctx : ContextInfo) (info : TacticInfo) (input : String)
    (id : Nat) (parent : Option Nat) : IO TacticRecord := do
  let start := info.stx.getPos?.getD 0
  let finish := info.stx.getTailPos?.getD start
  return {
    id, parent, declaration := ctx.parentDecl?.map toString
    start := location (ctx.fileMap.toPosition start)
    finish := location (ctx.fileMap.toPosition finish)
    source := sourceSlice input start finish
    syntax_kind := toString info.stx.getKind
    synthetic := match info.stx.getHeadInfo with | .original .. => false | _ => true
    goals_before := ← ppGoals ctx info.mctxBefore info.goalsBefore
    goals_after := ← ppGoals ctx info.mctxAfter info.goalsAfter
  }

/-- Preserve nested tactic ancestry; flat before/after lists do not define proof-tree edges. -/
partial def collectTactics (input : String) (ranges : Array DeclarationRange) (tree : InfoTree)
    (ctx? : Option ContextInfo := none) (parent : Option Nat := none)
    (records : Array TacticRecord := #[]) : IO (Array TacticRecord) := do
  match tree with
  | .hole _ => return records
  | .context context child =>
    collectTactics input ranges child (context.mergeIntoOuter? ctx?) parent records
  | .node info children =>
    let mut records := records
    let mut parent := parent
    if let some ctx := ctx? then
      if let .ofTacticInfo tactic := info then
        let start := location (ctx.fileMap.toPosition (tactic.stx.getPos?.getD 0))
        if ranges.any (fun range => within start range.pos range.endPos) then
          let id := records.size
          records := records.push (← tacticRecord ctx tactic input id parent)
          parent := some id
    for child in children do
      records ← collectTactics input ranges child (info.updateContext? ctx?) parent records
    return records

partial def collectExamples (inputCtx : Parser.InputContext) (stx : Syntax) : Array ExampleRecord :=
  if stx.isOfKind ``Parser.Command.example then
    let start := stx.getPos?.getD 0
    let finish := stx.getTailPos?.getD start
    #[{ start := location (inputCtx.fileMap.toPosition start)
        finish := location (inputCtx.fileMap.toPosition finish)
        source := sourceSlice inputCtx.inputString start finish }]
  else
    stx.getArgs.foldl (fun found child => found ++ collectExamples inputCtx child) #[]

def declarationKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .inductInfo _ => "inductive"
  | _ => "other"

def extractDeclaration (env : Environment) (inputCtx : Parser.InputContext)
    (tactics : Array TacticRecord) (name : Name) : IO DeclarationRecord := do
  let some constant := env.find? name
    | throw <| IO.userError s!"Selected declaration not found: {name}"
  if (env.getModuleIdxFor? name).isSome then
    throw <| IO.userError s!"Selected declaration is imported, not in this source: {name}"
  let some ranges ← runMeta env inputCtx (findDeclarationRanges? name)
    | throw <| IO.userError s!"No declaration range for {name}"
  let range := ranges.range
  let sourceLines := inputCtx.inputString.splitOn "\n"
  let source := String.intercalate "\n"
    (sourceLines.drop (range.pos.line - 1) |>.take (range.endPos.line - range.pos.line + 1))
  let axioms ← runMeta env inputCtx (collectAxioms name)
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all permitted.contains do
    throw <| IO.userError s!"Unexpected axioms in {name}: {axioms}"
  return {
    name := toString name, kind := declarationKind constant
    universe_parameters := constant.levelParams.toArray.map toString
    start := location ranges.selectionRange.pos, finish := location range.endPos
    statement := ← ppType env inputCtx constant.type, source
    docstring := ← findDocString? env name
    type_dependencies := sortedNames constant.type.getUsedConstants
    proof_dependencies := sortedNames
      ((constant.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    axioms := sortedNames axioms
    tactics := tactics.filter fun t =>
      within t.start range.pos range.endPos && within t.finish range.pos range.endPos
  }

/-- Follow statement types and structure field types, retaining project-owned structures. -/
partial def collectStructures (env : Environment) (inputCtx : Parser.InputContext)
    (pending : List Name) (seen : NameSet := {}) (records : Array StructureRecord := #[]) :
    IO (Array StructureRecord) := do
  match pending with
  | [] => return records
  | name :: rest =>
    if seen.contains name then return ← collectStructures env inputCtx rest seen records
    let seen := seen.insert name
    let some constant := env.find? name
      | return ← collectStructures env inputCtx rest seen records
    let own := name.getRoot == `PhysicsOfConsciousness || name.getRoot == `CompanionFixture
    if !own then return ← collectStructures env inputCtx rest seen records
    let mut pending := constant.type.getUsedConstants.toList ++ rest
    let mut records := records
    if let some structureInfo := getStructureInfo? env name then
      let mut fields := #[]
      for info in structureInfo.fieldInfo do
        if let some field := env.find? info.projFn then
          let statement ← ppType env inputCtx field.type
          fields := fields.push ({ name := toString info.projFn, statement } : FieldRecord)
          pending := field.type.getUsedConstants.toList ++ pending
      records := records.push { name := toString name, fields }
    return ← collectStructures env inputCtx pending seen records

unsafe def extract (fileName : String) (names : Array Name) : IO Snapshot := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile fileName) fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let moduleName := ((fileName.dropEnd 5).toString.replace "/" ".").toName
  let (env, messages) ← processHeader header {} messages inputCtx
    (mainModule := moduleName)
  let state ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
  if state.commandState.messages.hasErrors then
    for message in state.commandState.messages.toList do
      IO.eprintln (← message.toString)
    throw <| IO.userError s!"Elaboration failed: {fileName}"
  let env := state.commandState.env
  let ranges ← names.mapM fun name => do
    let some ranges ← runMeta env inputCtx (findDeclarationRanges? name)
      | throw <| IO.userError s!"Selected declaration has no source range: {name}"
    return ranges.range
  let mut tactics := #[]
  for tree in state.commandState.infoState.trees do
    tactics ← collectTactics inputCtx.inputString ranges tree none none tactics
  let declarations ← names.mapM (extractDeclaration env inputCtx tactics)
  let structures ← collectStructures env inputCtx names.toList
  return {
    source_file := fileName, declarations, structures
    anonymous_examples := state.commands.foldl
      (fun examples stx => examples ++ collectExamples inputCtx stx) #[]
  }

end ProofCompanion

unsafe def main (args : List String) : IO Unit := do
  let fileName :: output :: names := args
    | throw <| IO.userError "Usage: Extract.lean SOURCE.lean OUTPUT.json DECLARATION..."
  if names.isEmpty then throw <| IO.userError "Select at least one declaration"
  let snapshot ← ProofCompanion.extract fileName (names.toArray.map String.toName)
  IO.FS.writeFile output ((toJson snapshot).pretty ++ "\n")
  IO.eprintln s!"Extracted {snapshot.declarations.size} declarations from {fileName}"
