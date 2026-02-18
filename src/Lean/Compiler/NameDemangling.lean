/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.While
import Init.Data.String.TakeDrop
import Init.Data.String.Search
public import Lean.Compiler.NameMangling

/-!
# Lean Name Demangling

Human-friendly demangling of Lean compiler symbol names. Extends the core
`Name.demangle` from `NameMangling.lean` with prefix handling, compiler suffix
folding, and backtrace line parsing.

This is the single source of truth for name demangling. The C runtime calls
these functions via `@[export]` for backtrace display.
-/

namespace Lean.Name.Demangle

-- ============================================================================
-- Raw position helpers (avoid dependent String.Pos proofs)
-- ============================================================================

private abbrev RawPos := String.Pos.Raw

private def rawGet (s : String) (i : RawPos) : Char :=
  String.Pos.Raw.get s i

private def rawNext (s : String) (i : RawPos) : RawPos :=
  String.Pos.Raw.next s i

private def rawAtEnd (s : String) (i : RawPos) : Bool :=
  i.byteIdx >= s.utf8ByteSize

private def rawExtract (s : String) (b e : RawPos) : String :=
  String.Pos.Raw.extract s b e

private def rawEnd (s : String) : RawPos := ⟨s.utf8ByteSize⟩

-- ============================================================================
-- Helpers
-- ============================================================================

private def isAllDigits (s : String) : Bool :=
  !s.isEmpty && s.all (·.isDigit)

private def isHexChar (c : Char) : Bool :=
  c.isDigit || (c.val >= 0x61 && c.val <= 0x66) || (c.val >= 0x41 && c.val <= 0x46)

-- ============================================================================
-- Component type and Name conversion
-- ============================================================================

private inductive Component where
  | str (s : String)
  | num (n : Nat)
  deriving BEq, Repr, Inhabited

/-- Convert a `Name` to a forward-ordered array of components. -/
private def nameToComponents (n : Name) : Array Component :=
  go n [] |>.toArray
where
  go : Name → List Component → List Component
    | .anonymous, acc => acc
    | .str pre s, acc => go pre (Component.str s :: acc)
    | .num pre n, acc => go pre (Component.num n :: acc)

private def formatComponents (comps : Array Component) : String :=
  comps.toList.map (fun
    | Component.str s => s
    | Component.num n => toString n)
  |> String.intercalate "."

-- ============================================================================
-- Compiler suffix matching
-- ============================================================================

/-- Match a component against known compiler-generated suffixes.
Returns the human-friendly flag label, or `none`. -/
private def matchSuffix (c : Component) : Option String :=
  match c with
  | Component.str s =>
    -- Exact matches
    if s == "_redArg" then some "arity↓"
    else if s == "_boxed" then some "boxed"
    else if s == "_impl" then some "impl"
    -- Exact or indexed
    else if s == "_lam" || s == "_lambda" || s == "_elam" then some "λ"
    else if s == "_jp" then some "jp"
    else if s == "_closed" then some "closed"
    -- Indexed: _lam_N, _lambda_N, _elam_N, _jp_N, _closed_N
    else if s.startsWith "_lam_" && isAllDigits (rawExtract s ⟨5⟩ (rawEnd s)) then some "λ"
    else if s.startsWith "_lambda_" && isAllDigits (rawExtract s ⟨8⟩ (rawEnd s)) then some "λ"
    else if s.startsWith "_elam_" && isAllDigits (rawExtract s ⟨6⟩ (rawEnd s)) then some "λ"
    else if s.startsWith "_jp_" && isAllDigits (rawExtract s ⟨4⟩ (rawEnd s)) then some "jp"
    else if s.startsWith "_closed_" && isAllDigits (rawExtract s ⟨8⟩ (rawEnd s)) then some "closed"
    else none
  | _ => none

private def isSpecIndex (c : Component) : Bool :=
  match c with
  | Component.str s =>
    s.startsWith "spec_" && s.length > 5 && isAllDigits (rawExtract s ⟨5⟩ (rawEnd s))
  | _ => false

-- ============================================================================
-- Postprocessing: components → human-friendly string
-- ============================================================================

private def stripPrivate (comps : Array Component) (start stop : Nat) :
    Nat × Bool :=
  if stop - start >= 3 && comps[start]? == some (Component.str "_private") then
    Id.run do
      for i in [start + 1 : stop] do
        if comps[i]? == some (Component.num 0) then
          if i + 1 < stop then return (i + 1, true)
          else return (start, false)
      return (start, false)
  else
    (start, false)

private structure SpecEntry where
  name : String
  flags : Array String

private def processSpecContext (comps : Array Component) : SpecEntry := Id.run do
  -- Strip private prefix within context
  let mut begin_ := 0
  if comps.size >= 3 && comps[0]? == some (Component.str "_private") then
    for i in [1:comps.size] do
      if comps[i]? == some (Component.num 0) && i + 1 < comps.size then
        begin_ := i + 1
        break
  let mut nameParts : Array String := #[]
  let mut flags : Array String := #[]
  for i in [begin_:comps.size] do
    let c := comps[i]!
    match matchSuffix c with
    | some flag =>
      if !flags.contains flag then
        flags := flags.push flag
    | none =>
      if isSpecIndex c then pure ()
      else match c with
        | Component.str s => nameParts := nameParts.push s
        | Component.num n => nameParts := nameParts.push (toString n)
  { name := String.intercalate "." nameParts.toList, flags }

/-- Main postprocessing: transform raw demangled components into a
human-friendly display string. -/
private def postprocessComponents (components : Array Component) : String := Id.run do
  if components.isEmpty then return ""

  -- 1. Strip _private prefix
  let (privStart, isPrivate) := stripPrivate components 0 components.size
  let mut parts := components.extract privStart components.size

  -- 2. Strip hygienic suffixes: everything from _@ onward
  for i in [:parts.size] do
    match parts[i]! with
    | Component.str s =>
      if s.startsWith "_@" then
        parts := parts.extract 0 i
        break
    | _ => pure ()

  -- 3. Handle specialization: _at_ ... _spec N
  let mut specEntries : Array SpecEntry := #[]
  let mut firstAt : Option Nat := none
  for i in [:parts.size] do
    if parts[i]! == Component.str "_at_" then
      firstAt := some i
      break

  if let some fa := firstAt then
    let base := parts.extract 0 fa
    let rest := parts.extract fa parts.size

    -- Parse _at_..._spec entries
    let mut entries : Array (Array Component) := #[]
    let mut currentCtx : Option (Array Component) := none
    let mut remaining : Array Component := #[]
    let mut skipNext := false

    for i in [:rest.size] do
      if skipNext then
        skipNext := false
        continue
      let p := rest[i]!
      if p == Component.str "_at_" then
        if let some ctx := currentCtx then
          entries := entries.push ctx
        currentCtx := some #[]
      else if p == Component.str "_spec" then
        if let some ctx := currentCtx then
          entries := entries.push ctx
          currentCtx := none
        skipNext := true
      else if match p with | Component.str s => s.startsWith "_spec" | _ => false then
        if let some ctx := currentCtx then
          entries := entries.push ctx
          currentCtx := none
      else
        match currentCtx with
        | some ctx => currentCtx := some (ctx.push p)
        | none => remaining := remaining.push p

    if let some ctx := currentCtx then
      if !ctx.isEmpty then
        entries := entries.push ctx

    for entry in entries do
      let se := processSpecContext entry
      if !se.name.isEmpty || !se.flags.isEmpty then
        specEntries := specEntries.push se

    parts := base ++ remaining

  -- 4. Collect suffix flags from the end
  let mut flags : Array String := #[]
  let mut cont := true
  while cont && !parts.isEmpty do
    let last := parts.back!
    match matchSuffix last with
    | some flag =>
      flags := flags.push flag
      parts := parts.pop
    | none =>
      match last with
      | Component.num _ =>
        if parts.size >= 2 then
          match matchSuffix parts[parts.size - 2]! with
          | some flag =>
            flags := flags.push flag
            parts := parts.pop.pop
          | none => cont := false
        else cont := false
      | _ => cont := false

  if isPrivate then
    flags := flags.push "private"

  -- 5. Format result
  let name := if parts.isEmpty then "?" else formatComponents parts
  let mut result := name

  if !flags.isEmpty then
    result := result ++ " [" ++ String.intercalate ", " flags.toList ++ "]"

  for entry in specEntries do
    let ctxStr := if entry.name.isEmpty then "?" else entry.name
    if !entry.flags.isEmpty then
      result := result ++ " spec at " ++ ctxStr ++ "["
        ++ String.intercalate ", " entry.flags.toList ++ "]"
    else
      result := result ++ " spec at " ++ ctxStr

  return result

-- ============================================================================
-- lp_ package/body splitting
-- ============================================================================

/-- Check if a mangled name body starts with an uppercase letter
(after skipping `00` disambiguation and leading underscores). -/
private partial def hasUpperStart (s : String) : Bool := Id.run do
  if s.isEmpty then return false
  let mut pos : RawPos := ⟨0⟩
  -- Skip 00 disambiguation
  if s.utf8ByteSize >= 2 && rawGet s ⟨0⟩ == '0' && rawGet s ⟨1⟩ == '0' then
    pos := ⟨2⟩
  -- Skip leading underscores
  while !rawAtEnd s pos && rawGet s pos == '_' do
    pos := rawNext s pos
  if rawAtEnd s pos then return false
  return (rawGet s pos).isUpper

/-- Given `s` = everything after `lp_`, find a valid split into (pkg, body).
Returns the raw mangled package and body strings, or `none`. -/
private partial def findLpSplit (s : String) : Option (String × String) := Id.run do
  let endPos := rawEnd s
  let mut validSplits : Array (String × String × Bool) := #[]
  let mut pos : RawPos := ⟨0⟩
  while !rawAtEnd s pos do
    if rawGet s pos == '_' && pos.byteIdx > 0 then
      let nextByte := rawNext s pos
      if !rawAtEnd s nextByte then
        let pkg := rawExtract s ⟨0⟩ pos
        let body := rawExtract s nextByte endPos
        if (Name.demangle? body).isSome then
          validSplits := validSplits.push (pkg, body, hasUpperStart body)
    pos := rawNext s pos
  if validSplits.isEmpty then return none
  -- Prefer: shortest valid package (first split point).
  -- Among splits where body starts uppercase, pick the first.
  -- If no uppercase, still pick the first.
  let upperSplits := validSplits.filter (·.2.2)
  if !upperSplits.isEmpty then
    return some (upperSplits[0]!.1, upperSplits[0]!.2.1)
  else
    return some (validSplits[0]!.1, validSplits[0]!.2.1)

/-- Unmangle a package name (single-component mangled name). -/
private def unmanglePkg (s : String) : String :=
  match Name.demangle s with
  | .str .anonymous s => s
  | _ => s

-- ============================================================================
-- Full symbol demangling
-- ============================================================================

/-- Strip `.cold.N` or `.cold` LLVM suffix from a symbol. -/
private partial def stripColdSuffix (s : String) : String × String := Id.run do
  let endPos := rawEnd s
  let mut pos : RawPos := ⟨0⟩
  while !rawAtEnd s pos do
    if rawGet s pos == '.' then
      let rest := rawExtract s pos endPos
      if rest.startsWith ".cold" then
        return (rawExtract s ⟨0⟩ pos, rest)
    pos := rawNext s pos
  return (s, "")

/-- Demangle a mangled body and postprocess to human-friendly string. -/
private def demangleBody (body : String) : String :=
  let name := Name.demangle body
  postprocessComponents (nameToComponents name)

/-- Try prefix-based demangling of a symbol (without .cold suffix). -/
private def demangleCore (s : String) : Option String := do
  -- _init_l_
  if s.startsWith "_init_l_" then
    let body := rawExtract s ⟨8⟩ (rawEnd s)
    if !body.isEmpty then return s!"[init] {demangleBody body}"

  -- _init_lp_
  if s.startsWith "_init_lp_" then
    let after := rawExtract s ⟨9⟩ (rawEnd s)
    if let some (pkg, body) := findLpSplit after then
      if !body.isEmpty then return s!"[init] {demangleBody body} ({unmanglePkg pkg})"

  -- initialize_l_
  if s.startsWith "initialize_l_" then
    let body := rawExtract s ⟨13⟩ (rawEnd s)
    if !body.isEmpty then return s!"[module_init] {demangleBody body}"

  -- initialize_lp_
  if s.startsWith "initialize_lp_" then
    let after := rawExtract s ⟨14⟩ (rawEnd s)
    if let some (pkg, body) := findLpSplit after then
      if !body.isEmpty then return s!"[module_init] {demangleBody body} ({unmanglePkg pkg})"

  -- initialize_ (bare module init)
  if s.startsWith "initialize_" then
    let body := rawExtract s ⟨11⟩ (rawEnd s)
    if !body.isEmpty then return s!"[module_init] {demangleBody body}"

  -- l_
  if s.startsWith "l_" then
    let body := rawExtract s ⟨2⟩ (rawEnd s)
    if !body.isEmpty then return demangleBody body

  -- lp_
  if s.startsWith "lp_" then
    let after := rawExtract s ⟨3⟩ (rawEnd s)
    if let some (pkg, body) := findLpSplit after then
      if !body.isEmpty then return s!"{demangleBody body} ({unmanglePkg pkg})"

  none

/-- Demangle a C symbol name produced by the Lean compiler.
Returns `none` if the symbol is not a recognized Lean name. -/
public def demangleSymbol (symbol : String) : Option String := do
  if symbol.isEmpty then none

  -- Strip .cold suffix first
  let (core, coldSuffix) := stripColdSuffix symbol

  -- Handle lean_apply_N
  if core.startsWith "lean_apply_" then
    let rest := rawExtract core ⟨11⟩ (rawEnd core)
    if isAllDigits rest then
      let r := s!"<apply/{rest}>"
      if coldSuffix.isEmpty then return r else return s!"{r} {coldSuffix}"

  -- Handle _lean_main
  if core == "_lean_main" then
    if coldSuffix.isEmpty then return "[lean] main"
    else return s!"[lean] main {coldSuffix}"

  -- Try prefix-based demangling
  let result ← demangleCore core
  if coldSuffix.isEmpty then return result
  else return s!"{result} {coldSuffix}"

-- ============================================================================
-- Backtrace line parsing
-- ============================================================================

/-- Extract the symbol name from a backtrace line.
Returns `(prefix, symbol, suffix)` where `prefix ++ symbol ++ suffix == line`.
Handles Linux glibc and macOS backtrace formats. -/
private partial def extractSymbol (line : String) :
    Option (String × String × String) := Id.run do
  let endPos := rawEnd line
  -- Try Linux glibc: ./lean(SYMBOL+0x2a) [0x555...]
  let mut pos : RawPos := ⟨0⟩
  while !rawAtEnd line pos do
    if rawGet line pos == '(' then
      let symStart := rawNext line pos
      let mut j := symStart
      while !rawAtEnd line j do
        let c := rawGet line j
        if c == '+' || c == ')' then
          if j.byteIdx > symStart.byteIdx then
            return some (rawExtract line ⟨0⟩ symStart,
                         rawExtract line symStart j,
                         rawExtract line j endPos)
          return none
        j := rawNext line j
      return none
    pos := rawNext line pos

  -- Try macOS: N   lib   0xADDR SYMBOL + offset
  pos := ⟨0⟩
  while !rawAtEnd line pos do
    if rawGet line pos == '0' then
      let pos1 := rawNext line pos
      if !rawAtEnd line pos1 && rawGet line pos1 == 'x' then
        -- Skip hex digits
        let mut j := rawNext line pos1
        while !rawAtEnd line j && isHexChar (rawGet line j) do
          j := rawNext line j
        -- Skip spaces
        while !rawAtEnd line j && rawGet line j == ' ' do
          j := rawNext line j
        if rawAtEnd line j then return none
        let symStart := j
        -- Find " + " or end
        while !rawAtEnd line j do
          if rawGet line j == ' ' then
            let j1 := rawNext line j
            if !rawAtEnd line j1 && rawGet line j1 == '+' then
              let j2 := rawNext line j1
              if !rawAtEnd line j2 && rawGet line j2 == ' ' then
                break
          j := rawNext line j
        if j.byteIdx > symStart.byteIdx then
          return some (rawExtract line ⟨0⟩ symStart,
                       rawExtract line symStart j,
                       rawExtract line j endPos)
        return none
    pos := rawNext line pos

  return none

/-- Demangle a backtrace line. Returns `none` if no Lean symbol was found. -/
public def demangleBtLine (line : String) : Option String := do
  let (pfx, sym, sfx) ← extractSymbol line
  let demangled ← demangleSymbol sym
  return pfx ++ demangled ++ sfx

-- ============================================================================
-- C exports for runtime backtrace handler
-- ============================================================================

/-- C export: demangle a backtrace line.
Returns the demangled line, or empty string if nothing was demangled. -/
@[export lean_demangle_bt_line_cstr]
def demangleBtLineCStr (line : @& String) : String :=
  (demangleBtLine line).getD ""

/-- C export: demangle a single symbol.
Returns the demangled name, or empty string if not a Lean symbol. -/
@[export lean_demangle_symbol_cstr]
def demangleSymbolCStr (symbol : @& String) : String :=
  (demangleSymbol symbol).getD ""

end Lean.Name.Demangle
