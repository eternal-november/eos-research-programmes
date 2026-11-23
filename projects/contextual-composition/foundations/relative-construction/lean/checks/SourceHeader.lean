import Lean

/-- Print the end of the actual import header in Lean's normalized UTF-8 coordinates. -/
def main (args : List String) : IO Unit := do
  let [fileName] := args | throw <| IO.userError "Expected one source path"
  let ctx := Lean.Parser.mkInputContext (← IO.FS.readFile fileName) fileName
  let (header, _, messages) ← Lean.Parser.parseHeader ctx
  if messages.hasErrors then throw <| IO.userError s!"Could not parse the header of {fileName}"
  IO.println (header.raw.getTailPos?.getD 0).byteIdx
