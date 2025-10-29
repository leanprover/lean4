import Lake.CLI.Main

/-!

Usage: `lean --run script/Modulize.lean [--meta] file1.lean file2.lean ...`

A simple script that inserts `module` and `public section` into un-modulized files and
bumps their imports to `public`.

When `--meta` is passed, `public meta section` and `public meta import` is used instead.
-/

open Lean Parser.Module

def main (args : List String) : IO Unit := do
  let mut args := args
  let mut doMeta := false
  while !args.isEmpty && args[0]!.startsWith "-" do
    match args[0]! with
    | "--meta" => doMeta := true
    | arg => throw <| .userError s!"unknown flag '{arg}'"
    args := args.tail

  for path in args do
    -- Parse the input file
    let mut text ← IO.FS.readFile path
    let inputCtx := Parser.mkInputContext text path
    let (header, parserState, msgs) ← Parser.parseHeader inputCtx
    if !msgs.toList.isEmpty then -- skip this file if there are parse errors
      msgs.forM fun msg => msg.toString >>= IO.println
      throw <| .userError "parse errors in file"
    let `(header| $[module%$moduleTk?]? $imps:import*) := header
      | throw <| .userError s!"unexpected header syntax of {path}"
    if moduleTk?.isSome then
      continue

    -- initial whitespace if empty header
    let startPos := header.raw.getPos? |>.getD parserState.pos

    let dummyEnv ← mkEmptyEnvironment
    let (initCmd, parserState', _) :=
      Parser.parseCommand inputCtx { env := dummyEnv, options := {} } parserState msgs

    -- insert section if any trailing command
    if !initCmd.isOfKind ``Parser.Command.eoi then
      let insertPos? :=
          -- put below initial module docstring if any
          guard (initCmd.isOfKind ``Parser.Command.moduleDoc) *> initCmd.getTailPos? <|>
          -- else below header
          header.raw.getTailPos?
      let insertPos := insertPos?.getD startPos  -- empty header
      let mut sec := if doMeta then
        "public meta section"
      else
        "@[expose] public section"
      if !imps.isEmpty then
        sec := "\n\n" ++ sec
      if insertPos?.isNone then
        sec := sec ++ "\n\n"
      text := text.extract 0 insertPos ++ sec ++ text.extract insertPos text.rawEndPos

    -- prepend each import with `public `
    for imp in imps.reverse do
      let insertPos := imp.raw.getPos?.get!
      let prfx := if doMeta then "public meta " else "public "
      text := text.extract 0 insertPos ++ prfx ++ text.extract insertPos text.rawEndPos

    -- insert `module` header
    let mut initText := text.extract 0 startPos
    if !initText.trim.isEmpty then
      -- If there is a header comment, preserve it and put `module` in the line after
      initText := initText.trimRight ++ "\n"
    text := initText ++ "module\n\n" ++ text.extract startPos text.rawEndPos

    IO.FS.writeFile path text
