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
import Init.Data.String.Iterate
import Lean.Data.NameTrie
public import Lean.Compiler.NameMangling

/-! Human-friendly demangling of Lean compiler symbol names, extending
`Name.demangle` with prefix handling, compiler suffix folding, and backtrace
line parsing. Called from the C runtime via `@[export]` for backtrace display. -/

namespace Lean.Name.Demangle

/-- `String.dropPrefix?` returning a `String` instead of a `Slice`. -/
private def dropPrefix? (s : String) (pre : String) : Option String :=
  (s.dropPrefix? pre).map (·.toString)

private def isAllDigits (s : String) : Bool :=
  !s.isEmpty && s.all (·.isDigit)

private def nameToNameParts (n : Name) : Array NamePart :=
  go n [] |>.toArray
where
  go : Name → List NamePart → List NamePart
    | .anonymous, acc => acc
    | .str pre s, acc => go pre (NamePart.str s :: acc)
    | .num pre n, acc => go pre (NamePart.num n :: acc)

private def formatNameParts (comps : Array NamePart) : String :=
  comps.toList.map (fun
    | NamePart.str s => s
    | NamePart.num n => toString n)
  |> String.intercalate "."

private def matchSuffix (c : NamePart) : Option String :=
  match c with
  | NamePart.str s =>
    if s == "_redArg" then some "arity↓"
    else if s == "_boxed" then some "boxed"
    else if s == "_impl" then some "impl"
    else if s == "_lam" || s == "_lambda" || s == "_elam" then some "λ"
    else if s == "_jp" then some "jp"
    else if s == "_closed" then some "closed"
    else if (dropPrefix? s "_lam_").any isAllDigits then some "λ"
    else if (dropPrefix? s "_elam_").any isAllDigits then some "λ"
    else none
  | _ => none

private def isSpecIndex (c : NamePart) : Bool :=
  match c with
  | NamePart.str s => (dropPrefix? s "spec_").any isAllDigits
  | _ => false

private def stripPrivate (comps : Array NamePart) (start stop : Nat) :
    Nat × Bool :=
  if stop - start >= 3 && comps[start]? == some (NamePart.str "_private") then
    Id.run do
      for i in [start + 1 : stop] do
        if comps[i]? == some (NamePart.num 0) then
          if i + 1 < stop then return (i + 1, true)
          else return (start, false)
      return (start, false)
  else
    (start, false)

private structure SpecEntry where
  name : String
  flags : Array String

private def processSpecContext (comps : Array NamePart) : SpecEntry := Id.run do
  let mut begin_ := 0
  if comps.size >= 3 && comps[0]? == some (NamePart.str "_private") then
    for i in [1:comps.size] do
      if comps[i]? == some (NamePart.num 0) && i + 1 < comps.size then
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
        | NamePart.str s => nameParts := nameParts.push s
        | NamePart.num n => nameParts := nameParts.push (toString n)
  { name := String.intercalate "." nameParts.toList, flags }

private def postprocessNameParts (components : Array NamePart) : String := Id.run do
  if components.isEmpty then return ""

  let (privStart, isPrivate) := stripPrivate components 0 components.size
  let mut parts := components.extract privStart components.size

  -- Strip hygienic suffixes (_@ onward)
  for i in [:parts.size] do
    match parts[i]! with
    | NamePart.str s =>
      if s.startsWith "_@" then
        parts := parts.extract 0 i
        break
    | _ => pure ()

  -- Handle specialization contexts (_at_ ... _spec N)
  let mut specEntries : Array SpecEntry := #[]
  let mut firstAt : Option Nat := none
  for i in [:parts.size] do
    if parts[i]! == NamePart.str "_at_" then
      firstAt := some i
      break

  if let some fa := firstAt then
    let base := parts.extract 0 fa
    let rest := parts.extract fa parts.size

    let mut entries : Array (Array NamePart) := #[]
    let mut currentCtx : Option (Array NamePart) := none
    let mut remaining : Array NamePart := #[]
    let mut skipNext := false

    for i in [:rest.size] do
      if skipNext then
        skipNext := false
        continue
      let p := rest[i]!
      if p == NamePart.str "_at_" then
        if let some ctx := currentCtx then
          entries := entries.push ctx
        currentCtx := some #[]
      else if p == NamePart.str "_spec" then
        if let some ctx := currentCtx then
          entries := entries.push ctx
          currentCtx := none
        skipNext := true
      else if match p with | NamePart.str s => s.startsWith "_spec" | _ => false then
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

  -- Collect suffix flags from the end
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
      | NamePart.num _ =>
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

  let name := if parts.isEmpty then "?" else formatNameParts parts
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

private def hasUpperStart (s : String) : Bool :=
  let s := ((s.dropPrefix? "00").map (·.toString)).getD s
  go s s.startPos
where
  go (s : String) (pos : s.Pos) : Bool :=
    if h : pos = s.endPos then false
    else if pos.get h == '_' then go s (pos.next h)
    else (pos.get h).isUpper
  termination_by pos

private def findLpSplit (s : String) : Option (String × String) := Id.run do
  let mut validSplits : Array (String × String × Bool) := #[]
  for ⟨pos, h⟩ in s.positions do
    if pos.get h == '_' && pos ≠ s.startPos then
      let nextPos := pos.next h
      if nextPos == s.endPos then continue
      let pkg := s.extract s.startPos pos
      let body := s.extract nextPos s.endPos
      -- Package must be a valid single-component mangled name
      let validPkg := match Name.demangle? pkg with
        | some (.str .anonymous _) => true
        | _ => false
      if validPkg && (Name.demangle? body).isSome then
        validSplits := validSplits.push (pkg, body, hasUpperStart body)
  if validSplits.isEmpty then return none
  -- Prefer: shortest valid package (first split point).
  -- Among splits where body starts uppercase, pick the first.
  -- If no uppercase, still pick the first.
  let upperSplits := validSplits.filter (·.2.2)
  if !upperSplits.isEmpty then
    return some (upperSplits[0]!.1, upperSplits[0]!.2.1)
  else
    return some (validSplits[0]!.1, validSplits[0]!.2.1)

private def unmanglePkg (s : String) : String :=
  match Name.demangle s with
  | .str .anonymous s => s
  | _ => s

private def stripColdSuffix (s : String) : String × String :=
  match s.find? ".cold" with
  | some pos => (s.extract s.startPos pos, s.extract pos s.endPos)
  | none => (s, "")

private def demangleBody (body : String) : String :=
  let name := Name.demangle body
  postprocessNameParts (nameToNameParts name)

private def demangleCore (s : String) : Option String := do
  -- _init_l_
  if let some body := dropPrefix? s "_init_l_" then
    if !body.isEmpty then return s!"[init] {demangleBody body}"

  -- _init_lp_
  if let some after := dropPrefix? s "_init_lp_" then
    if let some (pkg, body) := findLpSplit after then
      if !body.isEmpty then return s!"[init] {demangleBody body} ({unmanglePkg pkg})"

  -- initialize_l_
  if let some body := dropPrefix? s "initialize_l_" then
    if !body.isEmpty then return s!"[module_init] {demangleBody body}"

  -- initialize_lp_
  if let some after := dropPrefix? s "initialize_lp_" then
    if let some (pkg, body) := findLpSplit after then
      if !body.isEmpty then return s!"[module_init] {demangleBody body} ({unmanglePkg pkg})"

  -- initialize_ (bare module init)
  if let some body := dropPrefix? s "initialize_" then
    if !body.isEmpty then return s!"[module_init] {demangleBody body}"

  -- l_
  if let some body := dropPrefix? s "l_" then
    if !body.isEmpty then return demangleBody body

  -- lp_
  if let some after := dropPrefix? s "lp_" then
    if let some (pkg, body) := findLpSplit after then
      if !body.isEmpty then return s!"{demangleBody body} ({unmanglePkg pkg})"

  none

public def demangleSymbol (symbol : String) : Option String := do
  if symbol.isEmpty then none

  -- Strip .cold suffix first
  let (core, coldSuffix) := stripColdSuffix symbol

  -- Handle lean_apply_N
  if let some rest := dropPrefix? core "lean_apply_" then
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

private def skipWhile (s : String) (pos : s.Pos) (pred : Char → Bool) : s.Pos :=
  if h : pos = s.endPos then pos
  else if pred (pos.get h) then skipWhile s (pos.next h) pred
  else pos
termination_by pos

private def splitAt₂ (s : String) (p₁ p₂ : s.Pos) : String × String × String :=
  (s.extract s.startPos p₁, s.extract p₁ p₂, s.extract p₂ s.endPos)

/-- Extract the symbol from a backtrace line (Linux glibc or macOS format). -/
private def extractSymbol (line : String) :
    Option (String × String × String) :=
  tryLinux line |>.orElse (fun _ => tryMacOS line)
where
  -- Linux glibc: ./lean(SYMBOL+0x2a) [0x555...]
  tryLinux (line : String) : Option (String × String × String) := do
    let parenPos ← line.find? '('
    if h : parenPos = line.endPos then none else
    let symStart := parenPos.next h
    let delimPos ← symStart.find? (fun c => c == '+' || c == ')')
    if delimPos == symStart then none else
    some (splitAt₂ line symStart delimPos)
  -- macOS: N   lib   0xADDR SYMBOL + offset
  tryMacOS (line : String) : Option (String × String × String) := do
    let zxPos ← line.find? "0x"
    if h : zxPos = line.endPos then none else
    let afterZero := zxPos.next h
    if h2 : afterZero = line.endPos then none else
    let afterX := afterZero.next h2
    let afterHex := skipWhile line afterX (·.isHexDigit)
    let symStart := skipWhile line afterHex (· == ' ')
    if symStart == line.endPos then none else
    let symEnd := (symStart.find? " + ").getD line.endPos
    if symEnd == symStart then none else
    some (splitAt₂ line symStart symEnd)

public def demangleBtLine (line : String) : Option String := do
  let (pfx, sym, sfx) ← extractSymbol line
  let demangled ← demangleSymbol sym
  return pfx ++ demangled ++ sfx

@[export lean_demangle_bt_line_cstr]
def demangleBtLineCStr (line : @& String) : String :=
  (demangleBtLine line).getD ""

@[export lean_demangle_symbol_cstr]
def demangleSymbolCStr (symbol : @& String) : String :=
  (demangleSymbol symbol).getD ""

end Lean.Name.Demangle
