import Lake.CLI.Main

/-!
A simple script that inserts `module` and `@[expose] public section` into un-modulized files and
bumps their imports to `public`.
-/

open Lean Parser.Module

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let mods := args.toArray.map (·.toName)

  -- Determine default module(s) to run shake on
  let defaultTargetModules : Array Name ← try
    let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
    let config ← Lake.MonadError.runEIO <| Lake.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
    let some workspace ← Lake.loadWorkspace config |>.toBaseIO
      | throw <| IO.userError "failed to load Lake workspace"
    let defaultTargetModules := workspace.root.defaultTargets.flatMap fun target =>
      if let some lib := workspace.root.findLeanLib? target then
        lib.roots
      else if let some exe := workspace.root.findLeanExe? target then
        #[exe.config.root]
      else
        #[]
    pure defaultTargetModules
  catch _ =>
    pure #[]

  -- the list of root modules
  let mods := if mods.isEmpty then defaultTargetModules else mods
  -- Only submodules of `pkg` will be edited or have info reported on them
  let pkg := mods[0]!.components.head!

  -- Load all the modules
  let imps := mods.map ({ module := · })
  let env ← importModules imps {}

  let srcSearchPath ← getSrcSearchPath

  for mod in env.header.moduleNames do
    if !pkg.isPrefixOf mod then
      continue

    -- Parse the input file
    let some path ← srcSearchPath.findModuleWithExt "lean" mod
      | throw <| .userError "error: failed to find source file for {mod}"
    let mut text ← IO.FS.readFile path
    let inputCtx := Parser.mkInputContext text path.toString
    let (header, parserState, msgs) ← Parser.parseHeader inputCtx
    if !msgs.toList.isEmpty then -- skip this file if there are parse errors
      msgs.forM fun msg => msg.toString >>= IO.println
      throw <| .userError "parse errors in file"
    let `(header| $[module%$moduleTk?]? $imps:import*) := header
      | throw <| .userError s!"unexpected header syntax of {path}"
    if moduleTk?.isSome then
      continue

    let looksMeta := mod.components.any (· ∈ [`Tactic, `Linter])

    -- initial whitespace if empty header
    let startPos := header.raw.getPos? |>.getD parserState.pos

    -- insert section if any trailing text
    if header.raw.getTrailingTailPos?.all (· < text.endPos) then
      let insertPos := header.raw.getTailPos? |>.getD startPos  -- empty header
      let mut sec := if looksMeta then
        "public meta section"
      else
        "@[expose] public section"
      if !imps.isEmpty then
        sec := "\n\n" ++ sec
      if header.raw.getTailPos?.isNone then
        sec := sec ++ "\n\n"
      text := text.extract 0 insertPos ++ sec ++ text.extract insertPos text.endPos

    -- prepend each import with `public `
    for imp in imps.reverse do
      let insertPos := imp.raw.getPos?.get!
      let prfx := if looksMeta then "public meta " else "public "
      text := text.extract 0 insertPos ++ prfx ++ text.extract insertPos text.endPos

    -- insert `module` header
    let mut initText := text.extract 0 startPos
    if !initText.trim.isEmpty then
      -- If there is a header comment, preserve it and put `module` in the line after
      initText := initText.trimRight ++ "\n"
    text := initText ++ "module\n\n" ++ text.extract startPos text.endPos

    IO.FS.writeFile path text
