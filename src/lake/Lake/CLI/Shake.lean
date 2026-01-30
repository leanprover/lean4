/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich
-/
module

prelude
public import Init.Prelude
public import Init.System.IO
public import Lean.Util.Path
import Lean.Environment
import Lean.ExtraModUses
import Lean.Parser.Module

/-! # Shake: A Lean import minimizer

This command will check the current project (or a specified target module) and all dependencies for
unused imports. This works by looking at generated `.olean` files to deduce required imports and
ensuring that every import is used to contribute some constant or other elaboration dependency
recorded by `recordExtraModUse` and friends.
-/

open Lean

namespace Lake.Shake

/-- The parsed CLI arguments for shake. -/
public structure Args where
  keepImplied : Bool := false
  keepPrefix : Bool := false
  keepPublic : Bool := false
  addPublic : Bool := false
  force : Bool := false
  githubStyle : Bool := false
  explain : Bool := false
  trace : Bool := false
  fix : Bool := false
  /-- `<MODULE>..`: the list of root modules to check -/
  mods : Array Name := #[]

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

def has (s : Bitset) (i : Nat) : Bool := s.toNat.testBit i

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

/-- Logically, a map `NeedsKind → Set ModuleIdx`, or `Set Import`. -/
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

instance : Union Needs where
  union a b := {
    pub := a.pub ∪ b.pub
    priv := a.priv ∪ b.priv
    metaPub := a.metaPub ∪ b.metaPub
    metaPriv := a.metaPriv ∪ b.metaPriv }

/-- The list of edits that will be applied in `--fix`. `edits[i] = (removed, added)` where:

* If `j ∈ removed` then we want to delete module named `j` from the imports of `i`
* If `j ∈ added` then we want to add module index `j` to the imports of `i`.
-/
abbrev Edits := Std.HashMap Name (Array Import × Array Import)

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
  /-- Modules that should always be preserved downstream. -/
  preserve : Needs := default
  /-- Edits to be applied to the module imports. -/
  edits : Edits := {}

  -- Memoizations
  reservedNames : Std.HashSet Name := Id.run do
    let mut m := {}
    for (c, _) in env.constants do
      if isReservedName env c then
        m := m.insert c
    return m
  indirectModUses : Std.HashMap Name (Array ModuleIdx) :=
    indirectModUseExt.getState env
  modNames : Array Name :=
    env.header.moduleNames

def State.mods (s : State) := s.env.header.moduleData

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

def isDeclMeta' (env : Environment) (declName : Name) : Bool :=
  -- Matchers are not compiled by themselves but inlined by the compiler, so there is no IR decl
  -- to be tagged as `meta`.
  -- TODO: It would be better to base the entire `meta` inference on the IR only and consider module
  -- references from any other context as compatible with both phases.
  let inferFor :=
    if declName.isStr && (declName.getString!.startsWith "match_" || declName.getString! == "_unsafe_rec") then declName.getPrefix else declName
  -- `isMarkedMeta` knows about non-defs such as `meta structure`, isDeclMeta knows about decls
  -- implicitly marked meta
  isMarkedMeta env inferFor || isDeclMeta env inferFor

/--
Given an `Expr` reference, returns the declaration name that should be considered the reference, if
any.
-/
def getDepConstName? (s : State) (ref : Name) : Option Name := do
  -- Ignore references to reserved names, they can be re-generated in-place
  guard <| !s.reservedNames.contains ref
  -- `_simp_...` constants are similar, use base decl instead
  return if ref.isStr && ref.getString!.startsWith "_simp_" then
    ref.getPrefix
  else
    ref

/-- Calculates the needs for a given module `mod` from constants and recorded extra uses. -/
def calcNeeds (s : State) (i : ModuleIdx) : Needs := Id.run do
  let env := s.env
  let mut needs := default
  for ci in env.header.moduleData[i]!.constants do
    -- Added guard for cases like `structure` that are still exported even if private
    let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
    let k := { isExported := pubCI?.isSome, isMeta := isDeclMeta' env ci.name }
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
  visitExpr (k : NeedsKind) (e : Expr) (deps : Needs) : Needs :=
    let env := s.env
    Lean.Expr.foldConsts e deps fun c deps => Id.run do
      let mut deps := deps
      if let some c := getDepConstName? s c then
        if let some j := env.getModuleIdxFor? c then
          let k := { k with isMeta := k.isMeta && !isDeclMeta' env c }
          if j != i then
            deps := deps.union k {j}
            for indMod in s.indirectModUses[c]?.getD #[] do
              if s.transDeps[i]!.has k indMod then
                deps := deps.union k {indMod}
      return deps

abbrev Explanations := Std.HashMap (ModuleIdx × NeedsKind) (Option (Name × Name))

/--
Calculates the same as `calcNeeds` but tracing each module to a use-def declaration pair or
`none` if merely a recorded extra use.
-/
def getExplanations (s : State) (i : ModuleIdx) : Explanations := Id.run do
  let env := s.env
  let mut deps := default
  for ci in env.header.moduleData[i]!.constants do
    -- Added guard for cases like `structure` that are still exported even if private
    let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
    let k := { isExported := pubCI?.isSome, isMeta := isDeclMeta' env ci.name }
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
    let env := s.env
    Lean.Expr.foldConsts e deps fun c deps => Id.run do
      let mut deps := deps
      if let some c := getDepConstName? s c then
        if let some j := env.getModuleIdxFor? c then
          let k := { k with isMeta := k.isMeta && !isDeclMeta' env c }
          deps := addExplanation j k name c deps
        for indMod in s.indirectModUses[c]?.getD #[] do
          if s.transDeps[i]!.has k indMod then
            deps := addExplanation indMod k name (`_indirect ++ c) deps
      return deps
  addExplanation (j : ModuleIdx) (k : NeedsKind) (use def_ : Name) (deps : Explanations) : Explanations :=
    if
      if let some (some (name', _)) := deps[(j, k)]? then
        decide (use.toString.length < name'.toString.length)
      else true
    then
      deps.insert (j, k) (use, def_)
    else deps

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
    IO (System.FilePath × (ictx : Parser.InputContext) ×
      TSyntax ``Parser.Module.header × String.Pos ictx.fileMap.source) := do
  let inputCtx := Parser.mkInputContext text path
  let (header, parserState, msgs) ← Parser.parseHeader inputCtx
  if !msgs.toList.isEmpty then -- skip this file if there are parse errors
    msgs.forM fun msg => msg.toString >>= IO.println
    throw <| .userError "parse errors in file"
  -- the insertion point for `add` is the first newline after the imports
  let insertion := header.raw.getTailPos?.getD parserState.pos
  let insertion := inputCtx.fileMap.source.pos! insertion |>.find (· == '\n') |>.next!
  pure ⟨path, inputCtx, header, insertion⟩

/-- Parse a source file to extract the location of the import lines, for edits and error messages.

Returns `(path, inputCtx, imports, endPos)` where `imports` is the `Lean.Parser.Module.import` list
and `endPos` is the position of the end of the header.
-/
def parseHeader (srcSearchPath : SearchPath) (mod : Name) :
    IO (System.FilePath × (ictx : Parser.InputContext) ×
      TSyntax ``Parser.Module.header × String.Pos ictx.fileMap.source) := do
  -- Parse the input file
  let some path ← srcSearchPath.findModuleWithExt "lean" mod
    | throw <| .userError s!"error: failed to find source file for {mod}"
  let text ← IO.FS.readFile path
  parseHeaderFromString text path.toString

def decodeHeader : TSyntax ``Parser.Module.header → Option (TSyntax `module) × Option (TSyntax `prelude) × TSyntaxArray ``Parser.Module.import
  | `(Parser.Module.header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $imports*) =>
    (moduleTk?.map .mk, preludeTk?.map .mk, imports)
  | stx => panic! s!"unexpected header syntax {stx}"

def decodeImport : TSyntax ``Parser.Module.import → Import
  | `(Parser.Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id) =>
    { module := id.getId, isExported := pubTk?.isSome, isMeta := metaTk?.isSome, importAll := allTk?.isSome }
  | stx => panic! s!"unexpected syntax {stx}"

/-- Analyze and report issues from module `i`. Arguments:

* `pkg`: the first component of the module name
* `srcSearchPath`: Used to find the path for error reporting purposes
* `i`: the module index
* `needs`: the module's calculated needs
* `addOnly`: if true, only add missing imports, do not remove unused ones
-/
def visitModule (pkg : Name) (srcSearchPath : SearchPath)
    (i : Nat) (needs : Needs) (headerStx : TSyntax ``Parser.Module.header) (args : Args)
    (addOnly := false) : StateT State IO Unit := do
  if isExtraRevModUse (← get).env i then
    modify fun s => { s with preserve := s.preserve.union (if args.addPublic then .pub else .priv) {i} }
    if args.trace then
      IO.eprintln s!"Preserving `{(← get).modNames[i]!}` because of recorded extra rev use"

  -- only process modules in the selected package
  -- TODO: should be after `keep-downstream` but core headers are not found yet?
  if !pkg.isPrefixOf (← get).modNames[i]! then
    return

  let (module?, prelude?, imports) := decodeHeader headerStx
  if module?.any (·.raw.getTrailing?.any (·.toString.contains "shake: keep-downstream")) then
    modify fun s => { s with preserve := s.preserve.union (if args.addPublic then .pub else .priv) {i} }

  let s ← get

  let addOnly := addOnly || module?.any (·.raw.getTrailing?.any (·.toString.contains "shake: keep-all"))
  let mut deps := needs

  -- Add additional preserved imports
  for impStx in imports do
    let imp := decodeImport impStx
    let j := s.env.getModuleIdx? imp.module |>.get!
    let k := NeedsKind.ofImport imp
    if addOnly ||
        args.keepPublic && imp.isExported ||
        impStx.raw.getTrailing?.any (·.toString.contains "shake: keep") then
      deps := deps.union k {j}
      if args.trace then
        IO.eprintln s!"Adding `{imp}` as additional dependency"
  for j in [0:s.mods.size] do
    for k in NeedsKind.all do
      -- Remove `meta` while preserving, no use-case for preserving `meta` so far.
      -- Downgrade to private unless `--add-public` is used.
      if s.transDepsOrig[i]!.has k j &&
          (s.preserve.has { k with isMeta := false, isExported := false } j ||
           s.preserve.has { k with isMeta := false, isExported := true } j) then
        deps := deps.union { k with isMeta := false, isExported := k.isExported && args.addPublic } {j}

  -- Do transitive reduction of `needs` in `deps`.
  if !addOnly then
    for j in [0:s.mods.size] do
      let transDeps := s.transDeps[j]!
      for k in NeedsKind.all do
        if deps.has k j then
          let transDeps := addTransitiveImps .empty { k with module := .anonymous } j transDeps
          for k' in NeedsKind.all do
            deps := deps.sub k' (transDeps.sub k' {j} |>.get k')

  if prelude?.isNone then
    deps := deps.union .pub {s.env.getModuleIdx? `Init |>.get!}

  -- Accumulate `transDeps` which is the non-reflexive transitive closure of the still-live imports
  let mut transDeps := Needs.empty
  let mut alwaysAdd : Array Import := #[]  -- to be added even if implied by other imports
  for imp in s.mods[i]!.imports do
    let j := s.env.getModuleIdx? imp.module |>.get!
    let k := NeedsKind.ofImport imp
    if deps.has k j || imp.importAll then
      transDeps := addTransitiveImps transDeps imp j s.transDeps[j]!
      deps := deps.union k {j}
    -- skip folder-nested `public (meta)? import`s but remove `meta`
    else if s.modNames[i]!.isPrefixOf imp.module then
      let imp := { imp with isMeta := false }
      let k := { k with isMeta := false }
      if args.trace then
        IO.eprintln s!"`{imp}` is preserved as folder-nested import"
      transDeps := addTransitiveImps transDeps imp j s.transDeps[j]!
      deps := deps.union k {j}
      if !s.mods[i]!.imports.contains imp then
        alwaysAdd := alwaysAdd.push imp

  -- If `transDeps` does not cover `deps`, then we have to add back some imports until it does.
  -- To minimize new imports we pick only new imports which are not transitively implied by
  -- another new import, so we visit module indices in descending order.
  let mut keptPrefix := false
  let mut newTransDeps := transDeps
  let mut toAdd : Array Import := #[]
  for j in (0...s.mods.size).toArray.reverse do
    for k in NeedsKind.all do
      if deps.has k j && !newTransDeps.has k j && !newTransDeps.has { k with isExported := true } j then
        -- `add-public/keep-prefix` may change the import and even module we're considering
        let mut k := k
        let mut imp : Import := { k with module := s.modNames[j]! }
        let mut j := j
        if args.trace then
          IO.eprintln s!"`{imp}` is needed{if needs.has k j then " (calculated)" else ""}"
        if args.addPublic && !k.isExported &&
            -- also add as public if previously `public meta`, which could be from automatic porting
            (s.transDepsOrig[i]!.has { k with isExported := true } j || s.transDepsOrig[i]!.has { k with isExported := true, isMeta := true } j) then
          k := { k with isExported := true }
          imp := { imp with isExported := true }
          if args.trace then
            IO.eprintln s!"* upgrading to `{imp}` because of `--add-public`"
        if args.keepPrefix then
          let rec tryPrefix : Name → Option ModuleIdx
            | .str p _ => tryPrefix p <|> (do
              let j' ← s.env.getModuleIdx? p
              -- `j'` must be reachable from `i` (allow downgrading from `meta`)
              guard <| s.transDepsOrig[i]!.has k j' || s.transDepsOrig[i]!.has { k with isMeta := true } j'
              let j'transDeps := addTransitiveImps .empty p j' s.transDeps[j']!
              -- `j` must be reachable from `j'` (now downgrading must be done in the other direction)
              guard <| j'transDeps.has k j || j'transDeps.has { k with isMeta := false } j
              return j')
            | _ => none
          if let some j' := tryPrefix imp.module then
            imp := { imp with module := s.modNames[j']! }
            j := j'
            keptPrefix := true
            if args.trace then
              IO.eprintln s!"* upgrading to `{imp}` because of `--keep-prefix`"
        if !s.mods[i]!.imports.contains imp then
          toAdd := toAdd.push imp
        deps := deps.union k {j}
        newTransDeps := addTransitiveImps newTransDeps imp j s.transDeps[j]!

  if keptPrefix then
    -- if an import was replaced by `--keep-prefix`, we did not necessarily visit the modules in
    -- dependency order anymore and so we have to redo the transitive closure checking
    newTransDeps := transDeps
    for j in (0...s.mods.size).toArray.reverse do
      for k in NeedsKind.all do
        if deps.has k j then
          let mut imp : Import := { k with module := s.modNames[j]! }
          if toAdd.contains imp && (newTransDeps.has k j || newTransDeps.has { k with isExported := true } j) then
            if args.trace then
              IO.eprintln s!"Removing `{imp}` from imports to be added because it is now implied"
            toAdd := toAdd.erase imp
            deps := deps.sub k {j}
          else
            newTransDeps := addTransitiveImps newTransDeps imp j s.transDeps[j]!

  -- now that `toAdd` filtering is done, add `alwaysAdd`
  toAdd := alwaysAdd ++ toAdd

  -- Any import which is still not in `deps` was unused
  let mut toRemove : Array Import := #[]
  for imp in s.mods[i]!.imports do
    let j := s.env.getModuleIdx? imp.module |>.get!
    let k := NeedsKind.ofImport imp
    if args.keepImplied && newTransDeps.has k j then
      if args.trace && !deps.has k j then
        IO.eprintln s!"`{imp}` is implied by other imports"
    else if !deps.has k j then
      if args.trace then
        IO.eprintln s!"`{imp}` is now unused"
      toRemove := toRemove.push imp
    -- A private import should also be removed if the public version has been added
    else if !k.isExported && !imp.importAll && newTransDeps.has { k with isExported := true } j then
      if args.trace then
        IO.eprintln s!"`{imp}` is already covered by `{ { imp with isExported := true } }`"
      toRemove := toRemove.push imp

  -- mark and report the removals
  modify fun s => { s with
    edits := toRemove.foldl (init := s.edits) fun edits imp =>
      edits.remove s.modNames[i]! imp }

  if !toAdd.isEmpty || !toRemove.isEmpty || args.explain then
    if let some path ← srcSearchPath.findModuleWithExt "lean" s.modNames[i]! then
      println! "{path}:"
    else
      println! "{s.modNames[i]!}:"

  if !toRemove.isEmpty then
    println! "  remove {toRemove}"

  if args.githubStyle then
    try
      let ⟨path, inputCtx, stx, endHeader⟩ ← parseHeader srcSearchPath s.modNames[i]!
      let (_, _, imports) := decodeHeader stx
      for stx in imports do
        if toRemove.any fun imp => imp == decodeImport stx then
          let pos := inputCtx.fileMap.toPosition stx.raw.getPos?.get!
          println! "{path}:{pos.line}:{pos.column+1}: warning: unused import \
            (use `lake shake --fix` to fix this, or `lake shake --update` to ignore)"
      if !toAdd.isEmpty then
        -- we put the insert message on the beginning of the last import line
        let pos := inputCtx.fileMap.toPosition endHeader.offset
        println! "{path}:{pos.line-1}:1: warning: \
          add {toAdd} instead"
    catch _ => pure ()

  -- mark and report the additions
  modify fun s => { s with
    edits := toAdd.foldl (init := s.edits) fun edits imp =>
      edits.add s.modNames[i]! imp }

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

  modify fun s => { s with transDeps := s.transDeps.set! i newTransDepsI }

  if args.explain then
    let explanation := getExplanations s i
    let sanitize n := if n.hasMacroScopes then (sanitizeName n).run' { options := {} } else n
    let run (imp : Import) := do
      let j := s.env.getModuleIdx? imp.module |>.get!
      let mut k := NeedsKind.ofImport imp
      if let some exp? := explanation[(j, k)]? <|> guard args.addPublic *> explanation[(j, { k with isExported := false})]? then
        println! "  note: `{imp}` required"
        if let some (n, c) := exp? then
          println! "    because `{sanitize n}` refers to `{sanitize c}`"
        else
          println! "    because of additional compile-time dependencies"
    for j in s.mods[i]!.imports do
      if !toRemove.contains j then
        run j
    for i in toAdd do run i

local instance : Ord Import where
  compare :=
    let _ := @lexOrd
    compareOn fun imp => (!imp.isExported, imp.module.toString)

/--
Run the shake analysis with the given arguments.

Assumes Lean's search path has already been properly configured.
-/
public def run (args : Args) (h : 0 < args.mods.size)
    (srcSearchPath : SearchPath := {}) : IO UInt32 := do

  -- the list of root modules
  let mods := args.mods
  -- Only submodules of `pkg` will be edited or have info reported on them
  let pkg := mods[0].getRoot

  -- Load all the modules
  let imps := mods.map ({ module := · })
  let (_, s) ← importModulesCore imps (isExported := true) |>.run
  let s := s.markAllExported
  let mut env ← finalizeImport s (isModule := true) imps {} (leakEnv := true) (loadExts := false)
  if env.header.moduleData.any (!·.isModule) then
    throw <| .userError "`lake shake` only works with `module`s currently"
  -- the one env ext we want to initialize
  let is := indirectModUseExt.toEnvExtension.getState env
  let newState ← indirectModUseExt.addImportedFn is.importedEntries { env := env, opts := {} }
  env := indirectModUseExt.toEnvExtension.setState (asyncMode := .sync) env { is with state := newState }

  StateT.run' (s := initStateFromEnv env) do

  let s ← get
  -- Run the calculation of the `needs` array in parallel
  let needs := s.mods.mapIdx fun i _ =>
    Task.spawn fun _ => calcNeeds s i

  -- Parse headers in parallel
  let headers ← s.mods.mapIdxM fun i _ =>
    if !pkg.isPrefixOf s.modNames[i]! then
      pure <| Task.pure <| .ok ⟨default, default, default, default⟩
    else
      BaseIO.asTask (parseHeader srcSearchPath s.modNames[i]! |>.toBaseIO)

  if args.fix then
    println! "The following changes will be made automatically:"

  -- Check all selected modules
  for i in [0:s.mods.size], t in needs, header in headers do
    match header.get with
    | .ok ⟨_, _, stx, _⟩ =>
      visitModule pkg srcSearchPath i t.get stx args
    | .error e =>
      println! e.toString

  if !args.fix then
    -- return error if any issues were found
    return if (← get).edits.isEmpty then 0 else 1

  -- Apply the edits to existing files
  let mut count := 0
  for mod in s.modNames, header? in headers do
    let some (remove, add) := (← get).edits[mod]? | continue
    let add : Array Import := add.qsortOrd

    -- Parse the input file
    let .ok ⟨path, inputCtx, stx, insertion⟩ := header?.get | continue
    let (_, _, imports) := decodeHeader stx
    let text := inputCtx.fileMap.source

    -- Calculate the edit result
    let mut pos : String.Pos text := text.startPos
    let mut out : String := ""
    let mut seen : Std.HashSet Import := {}
    for stx in imports do
      let mod := decodeImport stx
      if remove.contains mod || seen.contains mod then
        out := out ++ text.extract pos (text.pos! stx.raw.getPos?.get!)
        -- We use the end position of the syntax, but include whitespace up to the first newline
        pos := text.pos! stx.raw.getTailPos?.get! |>.find '\n' |>.next!
      seen := seen.insert mod
    out := out ++ text.extract pos insertion
    for mod in add do
      if !seen.contains mod then
        seen := seen.insert mod
        out := out ++ s!"{mod}\n"
    out := out ++ text.extract insertion text.endPos

    IO.FS.writeFile path out
    count := count + 1

  -- Since we throw an error upon encountering issues, we can be sure that everything worked
  -- if we reach this point of the script.
  if count > 0 then
    println! "Successfully applied {count} suggestions."
  else
    println! "No edits required."
  return 0
