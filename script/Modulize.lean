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
    let `(header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $imps:import*) := header
      | throw <| .userError s!"unexpected header syntax of {path}"
    if moduleTk?.isSome then
      continue

    -- initial whitespace if empty header
    let startPos := header.raw.getPos? |>.getD parserState.pos

    let dummyEnv ← mkEmptyEnvironment
    let (initCmd, parserState', msgs') :=
      Parser.parseCommand inputCtx { env := dummyEnv, options := {} } parserState msgs

    -- insert section if any trailing command (or error, which could be from an unknown command)
    if !initCmd.isOfKind ``Parser.Command.eoi || msgs'.hasErrors then
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
      let insertPos := text.pos! insertPos
      text := text.extract text.startPos insertPos ++ sec ++ text.extract insertPos text.endPos

    -- prepend each import with `public `
    for imp in imps.reverse do
      let insertPos := imp.raw.getPos?.get!
      let prfx := if doMeta then "public meta " else "public "
      let insertPos := text.pos! insertPos
      text := text.extract text.startPos insertPos ++ prfx ++ text.extract insertPos text.endPos

    -- insert `module` header
    let mut initText := text.extract text.startPos (text.pos! startPos)
    if !initText.trimAscii.isEmpty then
      -- If there is a header comment, preserve it and put `module` in the line after
      initText := initText.trimAsciiEnd.toString ++ "\n"
    text := initText ++ "module\n\n" ++ text.extract (text.pos! startPos) text.endPos

    IO.FS.writeFile path text
