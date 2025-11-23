/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich
-/
import Lake.CLI.Main
import Lean.ExtraModUses

/-! # `lake exe shake` command

This command will check the current project (or a specified target module) and all dependencies for
unused imports. This works by looking at generated `.olean` files to deduce required imports and
ensuring that every import is used to contribute some constant or other elaboration dependency
recorded by `recordExtraModUse`. Because recompilation is not needed this is quite fast (about 8
seconds to check `Mathlib` and all dependencies).
-/

/-- help string for the command line interface -/
def help : String := "Lean project tree shaking tool
Usage: lake exe shake [OPTIONS] <MODULE>..

Arguments:
  <MODULE>
    A module path like `Mathlib`. All files transitively reachable from the
    provided module(s) will be checked.

Options:
  --force
    Skips the `lake build --no-build` sanity check

  --fix
    Apply the suggested fixes directly. Make sure you have a clean checkout
    before running this, so you can review the changes.
"

open Lean

/-- We use `Nat` as a bitset for doing efficient set operations.
The bit indexes will usually be a module index. -/
structure Bitset where
  toNat : Nat
deriving Inhabited, DecidableEq, Repr

namespace Bitset

instance : EmptyCollection Bitset where
  emptyCollection := { toNat := 0 }

instance : Insert Nat Bitset where
  insert i s := { toNat := s.toNat ||| (1 <<< i) }

instance : Singleton Nat Bitset where
  singleton i := insert i ∅

instance : Inter Bitset where
  inter a b := { toNat := a.toNat &&& b.toNat }

instance : Union Bitset where
  union a b := { toNat := a.toNat ||| b.toNat }

instance : XorOp Bitset where
  xor a b := { toNat := a.toNat ^^^ b.toNat }

def has (s : Bitset) (i : Nat) : Bool := s ∩ {i} ≠ ∅

end Bitset

/-- The kind of a module dependency, corresponding to the homonymous `ExtraModUse` fields. -/
structure NeedsKind where
  isExported : Bool
  isMeta : Bool
deriving Inhabited, BEq, Repr, Hashable

namespace NeedsKind

@[match_pattern]  abbrev priv : NeedsKind := { isExported := false, isMeta := false }
@[match_pattern]  abbrev pub  : NeedsKind := { isExported := true,  isMeta := false }
@[match_pattern]  abbrev metaPriv : NeedsKind := { isExported := false, isMeta := true }
@[match_pattern]  abbrev metaPub  : NeedsKind := { isExported := true,  isMeta := true }

def all : Array NeedsKind := #[pub, priv, metaPub, metaPriv]

def ofImport : Lean.Import → NeedsKind
  | { isExported := true, isMeta := true, .. } => .metaPub
  | { isExported := true, isMeta := false, .. } => .pub
  | { isExported := false, isMeta := true, .. } => .metaPriv
  | { isExported := false, isMeta := false, .. } => .priv

end NeedsKind

/-- Logically, a map `NeedsKind → Bitset`. -/
structure Needs where
  pub : Bitset
  priv : Bitset
  metaPub : Bitset
  metaPriv : Bitset
deriving Inhabited, Repr

def Needs.empty : Needs := default

def Needs.get (needs : Needs) (k : NeedsKind) : Bitset :=
  match k with
  | .pub => needs.pub
  | .priv => needs.priv
  | .metaPub => needs.metaPub
  | .metaPriv => needs.metaPriv

def Needs.has (needs : Needs) (k : NeedsKind) (i : ModuleIdx) : Bool :=
  needs.get k |>.has i

def Needs.set (needs : Needs) (k : NeedsKind) (s : Bitset) : Needs :=
  match k with
  | .pub   => { needs with pub := s }
  | .priv  => { needs with priv := s }
  | .metaPub => { needs with metaPub := s }
  | .metaPriv => { needs with metaPriv := s }

def Needs.modify (needs : Needs) (k : NeedsKind) (f : Bitset → Bitset) : Needs :=
  needs.set k (f (needs.get k))

def Needs.union (needs : Needs) (k : NeedsKind) (s : Bitset) : Needs :=
  needs.modify k (· ∪ s)

def Needs.sub (needs : Needs) (k : NeedsKind) (s : Bitset) : Needs :=
  needs.modify k (fun s' => s' ^^^ (s' ∩ s))

/-- The main state of the checker, containing information on all loaded modules. -/
structure State where
  env  : Environment
  /--
  `transDeps[i]` is the (non-reflexive) transitive closure of `mods[i].imports`. More specifically,
  * `j ∈ transDeps[i].pub` if `i -(public import)->+ j`
  * `j ∈ transDeps[i].priv` if `i -(import ...)-> _ -(public import)->* j`
  * `j ∈ transDeps[i].priv` if `i -(import all)->+ i'` and `j ∈ transDeps[i'].pub/priv`
  * `j ∈ transDeps[i].metaPub` if `i -(public (meta)? import)->* _ -(public meta import)-> _ -(public (meta)? import)->* j`
  * `j ∈ transDeps[i].metaPriv` if `i -(meta import ...)-> _ -(public (meta)? import)->* j`
  * `j ∈ transDeps[i].metaPriv` if `i -(import ...)-> i'` and `j ∈ transDeps[i'].metaPub`
  * `j ∈ transDeps[i].metaPriv` if `i -(import all)->+ i'` and `j ∈ transDeps[i'].metaPub/metaPriv`
  -/
  transDeps : Array Needs := #[]
  /--
  `transDepsOrig` is the initial value of `transDeps` before changes potentially resulting from
  changes to upstream headers.
  -/
  transDepsOrig : Array Needs := #[]

def State.mods (s : State) := s.env.header.moduleData
def State.modNames (s : State) := s.env.header.moduleNames

/--
Given module `j`'s transitive dependencies, computes the union of `transImps` and the transitive
dependencies resulting from importing the module via `imp` according to the rules of
`State.transDeps`.
-/
def addTransitiveImps (transImps : Needs) (imp : Import) (j : Nat) (impTransImps : Needs) : Needs := Id.run do
  let mut transImps := transImps

  -- `j ∈ transDeps[i].pub` if `i -(public import)->+ j`
  if imp.isExported && !imp.isMeta then
    transImps := transImps.union .pub {j} |>.union .pub (impTransImps.get .pub)

  if !imp.isExported && !imp.isMeta then
    -- `j ∈ transDeps[i].priv` if `i -(import ...)-> _ -(public import)->* j`
    transImps := transImps.union .priv {j} |>.union .priv (impTransImps.get .pub)
    if imp.importAll then
      -- `j ∈ transDeps[i].priv` if `i -(import all)->+ i'` and `j ∈ transDeps[i'].pub/priv`
      transImps := transImps.union .priv (impTransImps.get .pub ∪ impTransImps.get .priv)

  -- `j ∈ transDeps[i].metaPub` if `i -(public (meta)? import)->* _ -(public meta import)-> _ -(public (meta)? import)->* j`
  if imp.isExported then
    transImps := transImps.union .metaPub (impTransImps.get .metaPub)
    if imp.isMeta then
      transImps := transImps.union .metaPub {j} |>.union .metaPub (impTransImps.get .pub ∪ impTransImps.get .metaPub)

  if !imp.isExported then
    if imp.isMeta then
      -- `j ∈ transDeps[i].metaPriv` if `i -(meta import ...)-> _ -(public (meta)? import)->* j`
      transImps := transImps.union .metaPriv {j} |>.union .metaPriv (impTransImps.get .pub ∪ impTransImps.get .metaPub)
    if imp.importAll then
      -- `j ∈ transDeps[i].metaPriv` if `i -(import all)->+ i'` and `j ∈ transDeps[i'].metaPub/metaPriv`
      transImps := transImps.union .metaPriv (impTransImps.get .metaPub ∪ impTransImps.get .metaPriv)
    else
      -- `j ∈ transDeps[i].metaPriv` if `i -(import ...)-> i'` and `j ∈ transDeps[i'].metaPub`
      transImps := transImps.union .metaPriv (impTransImps.get .metaPub)

  transImps

/-- Calculates the needs for a given module `mod` from constants and recorded extra uses. -/
def calcNeeds (env : Environment) (i : ModuleIdx) : Needs := Id.run do
  let mut needs := default
  for ci in env.header.moduleData[i]!.constants do
    -- Added guard for cases like `structure` that are still exported even if private
    let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
    let k := { isExported := pubCI?.isSome, isMeta := isMeta env ci.name }
    needs := visitExpr k ci.type needs
    if let some e := ci.value? (allowOpaque := true) then
      -- type and value has identical visibility under `meta`
      let k := if k.isMeta then k else
        if pubCI?.any (·.hasValue (allowOpaque := true)) then .pub else .priv
      needs := visitExpr k e needs

  for use in getExtraModUses env i do
    let j := env.getModuleIdx? use.module |>.get!
    needs := needs.union { use with } {j}

  return needs
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr (k : NeedsKind) e deps :=
    Lean.Expr.foldConsts e deps fun c deps => match env.getModuleIdxFor? c with
      | some j =>
        let k := { k with isMeta := k.isMeta && !isMeta env c }
        if j != i then deps.union k {j} else deps
      | _ => deps

/--
Calculates the same as `calcNeeds` but tracing each module to a use-def declaration pair or
`none` if merely a recorded extra use.
-/
def getExplanations (env : Environment) (i : ModuleIdx) :
    Std.HashMap (ModuleIdx × NeedsKind) (Option (Name × Name)) := Id.run do
  let mut deps := default
  for ci in env.header.moduleData[i]!.constants do
    -- Added guard for cases like `structure` that are still exported even if private
    let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
    let k := { isExported := pubCI?.isSome, isMeta := isMeta env ci.name }
    deps := visitExpr k ci.name ci.type deps
    if let some e := ci.value? (allowOpaque := true) then
      let k := if k.isMeta then k else
        if pubCI?.any (·.hasValue (allowOpaque := true)) then .pub else .priv
      deps := visitExpr k ci.name e deps

  for use in getExtraModUses env i do
    let j := env.getModuleIdx? use.module |>.get!
    if !deps.contains (j, { use with }) then
      deps := deps.insert (j, { use with }) none

  return deps
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr (k : NeedsKind) name e deps :=
    Lean.Expr.foldConsts e deps fun c deps => match env.getModuleIdxFor? c with
      | some i =>
        let k := { k with isMeta := k.isMeta && !isMeta env c }
        if
          if let some (some (name', _)) := deps[(i, k)]? then
            decide (name.toString.length < name'.toString.length)
          else true
        then
          deps.insert (i, k) (name, c)
        else
          deps
      | _ => deps

partial def initStateFromEnv (env : Environment) : State := Id.run do
  let mut s := { env }
  for i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]!
    let mut imps := #[]
    let mut transImps := Needs.empty
    for imp in mod.imports do
      let j := env.getModuleIdx? imp.module |>.get!
      imps := imps.push j
      transImps := addTransitiveImps transImps imp j s.transDeps[j]!
    s := { s with transDeps := s.transDeps.push transImps }
  s := { s with transDepsOrig := s.transDeps }
  return s

/-- The list of edits that will be applied in `--fix`. `edits[i] = (removed, added)` where:

* If `j ∈ removed` then we want to delete module named `j` from the imports of `i`
* If `j ∈ added` then we want to add module index `j` to the imports of `i`.
-/
abbrev Edits := Std.HashMap Name (Array Import × Array Import)

/-- Register that we want to remove `tgt` from the imports of `src`. -/
def Edits.remove (ed : Edits) (src : Name) (tgt : Import) : Edits :=
  match ed.get? src with
  | none => ed.insert src (#[tgt], #[])
  | some (a, b) => ed.insert src (a.push tgt, b)

/-- Register that we want to add `tgt` to the imports of `src`. -/
def Edits.add (ed : Edits) (src : Name) (tgt : Import) : Edits :=
  match ed.get? src with
  | none => ed.insert src (#[], #[tgt])
  | some (a, b) => ed.insert src (a, b.push tgt)

/-- Parse a source file to extract the location of the import lines, for edits and error messages.

Returns `(path, inputCtx, imports, endPos)` where `imports` is the `Lean.Parser.Module.import` list
and `endPos` is the position of the end of the header.
-/
def parseHeaderFromString (text path : String) :
    IO (System.FilePath × Parser.InputContext ×
      TSyntax ``Parser.Module.header × String.Pos.Raw) := do
  let inputCtx := Parser.mkInputContext text path
  let (header, parserState, msgs) ← Parser.parseHeader inputCtx
  if !msgs.toList.isEmpty then -- skip this file if there are parse errors
    msgs.forM fun msg => msg.toString >>= IO.println
    throw <| .userError "parse errors in file"
  -- the insertion point for `add` is the first newline after the imports
  let insertion := header.raw.getTailPos?.getD parserState.pos
  let insertion := text.findAux (· == '\n') text.endPos insertion + '\n'
  pure (path, inputCtx, header, insertion)

/-- Parse a source file to extract the location of the import lines, for edits and error messages.

Returns `(path, inputCtx, imports, endPos)` where `imports` is the `Lean.Parser.Module.import` list
and `endPos` is the position of the end of the header.
-/
def parseHeader (srcSearchPath : SearchPath) (mod : Name) :
    IO (System.FilePath × Parser.InputContext ×
      TSyntax ``Parser.Module.header × String.Pos.Raw) := do
  -- Parse the input file
  let some path ← srcSearchPath.findModuleWithExt "lean" mod
    | throw <| .userError s!"error: failed to find source file for {mod}"
  let text ← IO.FS.readFile path
  parseHeaderFromString text path.toString

def decodeHeader : TSyntax ``Parser.Module.header → Option (TSyntax `module) × Option (TSyntax `prelude) × TSyntaxArray ``Parser.Module.import
  | `(Parser.Module.header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $imports*) =>
    (moduleTk?.map .mk, preludeTk?.map .mk, imports)
  | _ => unreachable!

def decodeImport : TSyntax ``Parser.Module.import → Import
  | `(Parser.Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id) =>
    { module := id.getId, isExported := pubTk?.isSome, isMeta := metaTk?.isSome, importAll := allTk?.isSome }
  | stx => panic! s!"unexpected syntax {stx}"

/-- Analyze and report issues from module `i`. Arguments:

* `srcSearchPath`: Used to find the path for error reporting purposes
* `i`: the module index
* `needs`: the module's calculated needs
* `pinned`: dependencies that should be preserved even if unused
* `edits`: accumulates the list of edits to apply if `--fix` is true
* `addOnly`: if true, only add missing imports, do not remove unused ones
-/
def visitModule (srcSearchPath : SearchPath)
    (i : Nat) (needs : Needs) (preserve : Needs) (edits : Edits) (headerStx : TSyntax ``Parser.Module.header)
    (addOnly := false) (githubStyle := false) (explain := false) : StateT State IO Edits := do
  let s ← get
  -- Do transitive reduction of `needs` in `deps`.
  let mut deps := needs
  let (_, prelude?, imports) := decodeHeader headerStx
  if prelude?.isNone then
    deps := deps.union .pub {s.env.getModuleIdx? `Init |>.get!}
  for imp in imports do
    if addOnly || imp.raw.getTrailing?.any (·.toString.toSlice.contains "shake: keep") then
      let imp := decodeImport imp
      let j := s.env.getModuleIdx? imp.module |>.get!
      let k := NeedsKind.ofImport imp
      deps := deps.union k {j}
  for j in [0:s.mods.size] do
    let transDeps := s.transDeps[j]!
    for k in NeedsKind.all do
      if s.transDepsOrig[i]!.has k j && preserve.has k j then
        deps := deps.union k {j}
      if deps.has k j then
        let transDeps := addTransitiveImps .empty { k with module := .anonymous } j transDeps
        for k' in NeedsKind.all do
          deps := deps.sub k' (transDeps.sub k' {j} |>.get k')

  -- Any import which is not in `transDeps` was unused.
  -- Also accumulate `newDeps` which is the transitive closure of the remaining imports
  let mut toRemove : Array Import := #[]
  let mut newDeps := Needs.empty
  for imp in s.mods[i]!.imports do
    let j := s.env.getModuleIdx? imp.module |>.get!
    if
        -- skip folder-nested imports
        s.modNames[i]!.isPrefixOf imp.module ||
        imp.importAll then
      newDeps := addTransitiveImps newDeps imp j s.transDeps[j]!
    else
      let k := NeedsKind.ofImport imp
      -- A private import should also be removed if the public version is needed
      if !deps.has k j || !k.isExported && deps.has { k with isExported := true } j then
        toRemove := toRemove.push imp
      else
        newDeps := addTransitiveImps newDeps imp j s.transDeps[j]!

  -- If `newDeps` does not cover `deps`, then we have to add back some imports until it does.
  -- To minimize new imports we pick only new imports which are not transitively implied by
  -- another new import
  let mut toAdd : Array Import := #[]
  for j in [0:s.mods.size] do
    for k in NeedsKind.all do
      if deps.has k j && !newDeps.has k j && !newDeps.has { k with isExported := true } j then
        let imp := { k with module := s.modNames[j]! }
        toAdd := toAdd.push imp
        newDeps := addTransitiveImps newDeps imp j s.transDeps[j]!

  -- mark and report the removals
  let mut edits := toRemove.foldl (init := edits) fun edits imp =>
    edits.remove s.modNames[i]! imp

  if !toAdd.isEmpty || !toRemove.isEmpty || explain then
    if let some path ← srcSearchPath.findModuleWithExt "lean" s.modNames[i]! then
      println! "{path}:"
    else
      println! "{s.modNames[i]!}:"

  if !toRemove.isEmpty then
    println! "  remove {toRemove}"

  if githubStyle then
    try
      let (path, inputCtx, stx, endHeader) ← parseHeader srcSearchPath s.modNames[i]!
      let (_, _, imports) := decodeHeader stx
      for stx in imports do
        if toRemove.any fun imp => imp == decodeImport stx then
          let pos := inputCtx.fileMap.toPosition stx.raw.getPos?.get!
          println! "{path}:{pos.line}:{pos.column+1}: warning: unused import \
            (use `lake exe shake --fix` to fix this, or `lake exe shake --update` to ignore)"
      if !toAdd.isEmpty then
        -- we put the insert message on the beginning of the last import line
        let pos := inputCtx.fileMap.toPosition endHeader
        println! "{path}:{pos.line-1}:1: warning: \
          add {toAdd} instead"
    catch _ => pure ()

  -- mark and report the additions
  edits := toAdd.foldl (init := edits) fun edits imp =>
    edits.add s.modNames[i]! imp

  if !toAdd.isEmpty then
    println! "  add {toAdd}"

  -- recalculate transitive dependencies of downstream modules
  let mut newTransDepsI := Needs.empty
  for imp in s.mods[i]!.imports do
    if !toRemove.contains imp then
      let j := s.env.getModuleIdx? imp.module |>.get!
      newTransDepsI := addTransitiveImps newTransDepsI imp j s.transDeps[j]!
  for imp in toAdd do
    let j := s.env.getModuleIdx? imp.module |>.get!
    newTransDepsI := addTransitiveImps newTransDepsI imp j s.transDeps[j]!

  set { s with transDeps := s.transDeps.set! i newTransDepsI }

  if explain then
    let explanation := getExplanations s.env i
    let sanitize n := if n.hasMacroScopes then (sanitizeName n).run' { options := {} } else n
    let run (imp : Import) := do
      let j := s.env.getModuleIdx? imp.module |>.get!
      if let some exp? := explanation[(j, NeedsKind.ofImport imp)]? then
        println! "  note: `{imp}` required"
        if let some (n, c) := exp? then
          println! "    because `{sanitize n}` refers to `{sanitize c}`"
        else
          println! "    because of additional compile-time dependencies"
    for j in s.mods[i]!.imports do
      if !toRemove.contains j then
        run j
    for i in toAdd do run i

  return edits

/-- Convert a list of module names to a bitset of module indexes -/
def toBitset (s : State) (ns : List Name) : Bitset :=
  ns.foldl (init := ∅) fun c name =>
    match s.env.getModuleIdxFor? name with
    | some i => c ∪ {i}
    | none => c

/-- The parsed CLI arguments. See `help` for more information -/
structure Args where
  /-- `--help`: shows the help -/
  help : Bool := false
  /-- `--force`: skips the `lake build --no-build` sanity check -/
  force : Bool := false
  /-- `--gh-style`: output messages that can be parsed by `gh-problem-matcher-wrap` -/
  githubStyle : Bool := false
  /-- `--explain`: give constants explaining why each module is needed -/
  explain : Bool := false
  /-- `--fix`: apply the fixes directly -/
  fix : Bool := false
  /-- `<MODULE>..`: the list of root modules to check -/
  mods : Array Name := #[]

local instance : Ord Import where
  compare a b :=
    if a.isExported && !b.isExported then
      Ordering.lt
    else if !a.isExported && b.isExported then
      Ordering.gt
    else
      a.module.cmp b.module

/-- The main entry point. See `help` for more information on arguments. -/
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- Parse the arguments
  let rec parseArgs (args : Args) : List String → Args
    | [] => args
    | "--help" :: rest => parseArgs { args with help := true } rest
    | "--force" :: rest => parseArgs { args with force := true } rest
    | "--fix" :: rest => parseArgs { args with fix := true } rest
    | "--explain" :: rest => parseArgs { args with explain := true } rest
    | "--gh-style" :: rest => parseArgs { args with githubStyle := true } rest
    | "--" :: rest => { args with mods := args.mods ++ rest.map (·.toName) }
    | other :: rest => parseArgs { args with mods := args.mods.push other.toName } rest
  let args := parseArgs {} args

  -- Bail if `--help` is passed
  if args.help then
    IO.println help
    IO.Process.exit 0

  if !args.force then
    if (← IO.Process.output { cmd := "lake", args := #["build", "--no-build"] }).exitCode != 0 then
      IO.println "There are out of date oleans. Run `lake build` or `lake exe cache get` first"
      IO.Process.exit 1

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

  let srcSearchPath ← getSrcSearchPath
  -- the list of root modules
  let mods := if args.mods.isEmpty then defaultTargetModules else args.mods
  -- Only submodules of `pkg` will be edited or have info reported on them
  let pkg := mods[0]!.components.head!

  -- Load all the modules
  let imps := mods.map ({ module := · })
  let (_, s) ← importModulesCore imps (isExported := true) |>.run
  let s := s.markAllExported
  let env ← finalizeImport s (isModule := true) imps {} (leakEnv := false) (loadExts := false)

  StateT.run' (s := initStateFromEnv env) do

  let s ← get
  -- Parse the config file

  -- Run the calculation of the `needs` array in parallel
  let needs := s.mods.mapIdx fun i _ =>
    Task.spawn fun _ => calcNeeds s.env i

  -- Parse headers in parallel
  let headers ← s.mods.mapIdxM fun i _ =>
    BaseIO.asTask (parseHeader srcSearchPath s.modNames[i]! |>.toBaseIO)

  if args.fix then
    println! "The following changes will be made automatically:"

  -- Check all selected modules
  let mut edits : Edits := ∅
  let mut revNeeds : Needs := default
  for i in [0:s.mods.size], t in needs, header in headers do
    match header.get with
    | .ok (_, _, stx, _) =>
      edits ← visitModule (addOnly := !pkg.isPrefixOf s.modNames[i]!)
        srcSearchPath i t.get revNeeds edits stx args.githubStyle args.explain
      if isExtraRevModUse s.env i then
        revNeeds := revNeeds.union .priv {i}
    | .error e =>
      println! e.toString

  if !args.fix then
    -- return error if any issues were found
    return if edits.isEmpty then 0 else 1

  -- Apply the edits to existing files
  let mut count := 0
  for mod in s.modNames, header? in headers do
    let some (remove, add) := edits[mod]? | continue
    let add : Array Import := add.qsortOrd

    -- Parse the input file
    let .ok (path, inputCtx, stx, insertion) := header?.get | continue
    let (_, _, imports) := decodeHeader stx
    let text := inputCtx.fileMap.source

    -- Calculate the edit result
    let mut pos : String.Pos.Raw := 0
    let mut out : String := ""
    let mut seen : Std.HashSet Import := {}
    for stx in imports do
      let mod := decodeImport stx
      if remove.contains mod || seen.contains mod then
        out := out ++ text.extract pos stx.raw.getPos?.get!
        -- We use the end position of the syntax, but include whitespace up to the first newline
        pos := text.findAux (· == '\n') text.rawEndPos stx.raw.getTailPos?.get! + '\n'
      seen := seen.insert mod
    out := out ++ text.extract pos insertion
    for mod in add do
      if !seen.contains mod then
        seen := seen.insert mod
        out := out ++ s!"{mod}\n"
    out := out ++ text.extract insertion text.rawEndPos

    IO.FS.writeFile path out
    count := count + 1

  -- Since we throw an error upon encountering issues, we can be sure that everything worked
  -- if we reach this point of the script.
  if count > 0 then
    println! "Successfully applied {count} suggestions."
  else
    println! "No edits required."
  return 0
