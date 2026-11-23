import Lean

/-! Classify candidate byte positions using the pinned parser's source information. Only comment trivia and plain documentation bodies qualify. Other source text retains the usual token check. -/

open Lean Elab
namespace SourceCommentCheck

private def inSpan (x : Nat) (a b : String.Pos.Raw) : Bool :=
  a.byteIdx ≤ x && x < b.byteIdx

private def inTrivia (info : SourceInfo) (x : Nat) : Bool :=
  match info with
  | .original leading _ trailing _ =>
    inSpan x leading.startPos leading.stopPos || inSpan x trailing.startPos trailing.stopPos
  | _ => false

private partial def commentAt (x : Nat) : Syntax → Bool
  | .missing => false
  | .atom info _ | .ident info .. => inTrivia info x
  | .node _ kind args =>
    let plainDoc := kind == ``Parser.Command.moduleDoc || kind == ``Parser.Command.docComment ||
      kind == ``Parser.Command.plainDocComment
    let docBody := if plainDoc then
      match (args[1]? : Option Syntax) with
      | some (Syntax.atom (SourceInfo.original _ a _ b) _) => inSpan x a b
      | _ => false
    else false
    docBody || args.any (commentAt x)

private partial def inspectCommands (positions : List Nat) : Frontend.FrontendM (List Nat) := do
  if positions.isEmpty then return []
  let done ← Frontend.processCommand
  let state ← get
  if state.commandState.messages.hasErrors then
    throw <| IO.userError "Could not parse or elaborate the source for comment verification"
  let unchecked := positions.filter fun i => !commentAt i state.commands.back!
  if done || unchecked.any (· < state.parserState.pos.byteIdx) then return unchecked
  inspectCommands unchecked

private def check (env : Environment) (fileName moduleName : String) (positions : List Nat) : IO Unit := do
  let ctx := Parser.mkInputContext (← IO.FS.readFile fileName) fileName
  let (header, parserState, messages) ← Parser.parseHeader ctx
  if messages.hasErrors then throw <| IO.userError s!"Could not parse the header of {fileName}"
  let positions := positions.filter fun i => !commentAt i header.raw
  let (unchecked, _) ← (inspectCommands positions).run ⟨ctx⟩ |>.run {
    commandState := Command.mkState (env.setMainModule moduleName.toName) messages {}, parserState, cmdPos := parserState.pos }
  if let some i := unchecked.head? then
    let pos := ctx.fileMap.toPosition ⟨i⟩
    throw <| IO.userError s!"Forbidden proof/trust token in {fileName}:{pos.line}:{pos.column + 1}"

private structure Request where
  fileName : String
  moduleName : String
  positions : List Nat
  deriving FromJson

/-- The driver prepends the original header. Lean itself loads and initializes the imported syntax. -/
private def checkRequest : Command.CommandElabM Unit := do
  let some path ← IO.getEnv "CONTEXTUAL_SOURCE_COMMENT_REQUEST" | throwError "Missing source comment request"
  let request ← IO.ofExcept <| (Json.parse (← IO.FS.readFile path)).bind (fromJson? (α := Request))
  check (← getEnv) request.fileName request.moduleName request.positions

end SourceCommentCheck
