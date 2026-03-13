/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Arnez
-/
module

prelude
import Init.While
import Init.Data.String.TakeDrop
import Init.Data.String.Search
import Init.Data.String.Iterate
import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Slice.Array
import Lean.Data.NameTrie
public import Lean.Compiler.NameMangling

/-! Human-friendly demangling of Lean compiler symbol names, extending
`Name.demangle` with prefix handling, compiler suffix folding, and backtrace
line parsing. Called from the C runtime via `@[export]` for backtrace display. -/

namespace Lean.Name.Demangle

def isAllDigits (s : String.Slice) : Bool :=
  !s.isEmpty && s.all (·.isDigit)

def nameToNameParts (n : Name) : Array NamePart :=
  go n [] |>.toArray
where
  go : Name → List NamePart → List NamePart
    | .anonymous, acc => acc
    | .str pre s, acc => go pre (NamePart.str s :: acc)
    | .num pre n, acc => go pre (NamePart.num n :: acc)

def namePartsToName (parts : Subarray NamePart) : Name :=
  parts.foldl (fun acc p =>
    match p with
    | .str s => acc.mkStr s
    | .num n => acc.mkNum n) .anonymous

def matchSuffix (c : NamePart) : Option String :=
  match c with
  | NamePart.str s =>
    if s == "_redArg" then some "arity↓"
    else if s == "_impl" then some "impl"
    else if s == "_override" then some "override"
    else if (s.dropPrefix? "_lam_").any isAllDigits then some "λ"
    else if (s.dropPrefix? "_elam_").any isAllDigits then some "λ"
    else if (s.dropPrefix? "_closed_").any isAllDigits then some "closed"
    else none
  | _ => none

def isSpecIndex (c : NamePart) : Bool :=
  match c with
  | NamePart.str s => (s.dropPrefix? "spec_").any isAllDigits
  | _ => false

/-- Returns the length of the private prefix, if existing. -/
def findPrivate? (parts : Subarray NamePart) : Option Nat := do
  guard <| parts.size >= 3 && parts[0]? matches some (NamePart.str "_private")
  for h : i in *...parts.size do
    if parts[i] matches .num 0 then
      return i + 1
  none

/-- Returns the start position of the macro scope suffix, if existing. -/
def findMacroScopes? (parts : Subarray NamePart) : Option Nat := do
  guard <| parts.size >= 3 && parts[parts.size - 2]? matches some (.str "_hyg") &&
    parts[parts.size - 1]? matches some (.num _)
  let mut i := parts.size - 2
  while i ≠ 0 do
    i := i - 1
    if parts[i]! matches .str "_@" then
      return i
  none

/--
Returns the index of the `_at_` token corresponding to a `spec_N`.
This process can be compared to finding the opening parenthesis corresponding to a
closing parenthesis (`_at_` being the opening parenthesis and `spec_N` the closing one).
-/
def findAtToken? (parts : Subarray NamePart) : Option Nat := do
  let mut i := parts.size
  let mut specCount := 1
  while i ≠ 0 do
    i := i - 1
    if parts[i]! matches .str "_at_" then
      specCount := specCount - 1
      if specCount = 0 then
        return i
    if isSpecIndex parts[i]! then
      specCount := specCount + 1
  none

partial def postprocessNameParts (parts : Subarray NamePart) (inSpec : Bool := false) :
    String := Id.run do
  let mut parts := parts
  let mut flags := #[]
  -- Handle suffixes
  -- Note: the_boxed suffix is independent from macro scopes and can only occur at the top level
  if !inSpec && parts[parts.size - 1]? matches some (.str "_boxed") then
    flags := flags.push "boxed"
    parts := parts[*...parts.size - 1]
  if let some i := findMacroScopes? parts then
    parts := parts[*...i]
  repeat
    let some part := parts[parts.size - 1]? | break
    let some suffix := matchSuffix part | break
    parts := parts[*...parts.size - 1]
    unless flags.contains suffix do
      flags := flags.push suffix
  if parts[parts.size - 1]?.any isSpecIndex then
    if let some idx := findAtToken? parts[*...parts.size - 1] then
      let before := parts[*...idx]
      let after := parts[(idx + 1)...parts.size - 1]
      let beforeRes := postprocessNameParts before (inSpec := true)
      let afterRes := postprocessNameParts after (inSpec := true)
      let res := s!"{beforeRes} spec at {afterRes}"
      -- we add flags from the back to the front so reverse for a reasonable order
      return if flags.isEmpty then res else s!"{res} [{String.intercalate ", " flags.toListRev}]"
  -- Handle the private prefix
  -- We need to handle prefixes after specializations to make sure that the `_private`s in
  -- `_private.X.0.foo._at_.bar.spec_0` gets attributed to `foo` and not to the whole thing
  if let some i := findPrivate? parts then
    flags := flags.push "private"
    parts := parts[i...*]
  let res := (namePartsToName parts).toString
    -- we add flags from the back to the front so reverse for a reasonable order
  return if flags.isEmpty then res else s!"{res} [{String.intercalate ", " flags.toListRev}]"

/-- Split off the first name component (package names are encoded as string prefix components). -/
def splitPrefix (nm : Name) : Option (String × Name) := do
  match nm with
  | .str .anonymous s => some (s, .anonymous)
  | .str nm s =>
    let (pfx, nm) ← splitPrefix nm
    return (pfx, .str nm s)
  | .num nm i =>
    let (pfx, nm) ← splitPrefix nm
    return (pfx, .num nm i)
  | .anonymous => none

def demangleWithPkg (s : String) (normalPrefix packagePrefix : String) (postprocess : Bool) :
    Option String := do
  if let some s := s.dropPrefix? normalPrefix then
    let name ← Name.demangle? s.copy
    return if postprocess then
      postprocessNameParts (nameToNameParts name).toSubarray
    else name.toString
  else if let some s := s.dropPrefix? packagePrefix then
    let name ← Name.demangle? s.copy
    let (pkg, name) ← splitPrefix name
    return if postprocess then
      postprocessNameParts (nameToNameParts name).toSubarray ++ s!" ({pkg})"
    else s!"{name} ({pkg})"
  else
    none

def consumeModuleInitializationPrefix (s : String) : IRPhases × String :=
  if let some s := s.dropPrefix? "meta_" then
    (.comptime, s.copy)
  else if let some s := s.dropPrefix? "runtime_" then
    (.runtime, s.copy)
  else
    (.all, s)

def demangleCore (s : String) : Option String := do
  if let some rest := s.dropPrefix? "lean_apply_" then
    if isAllDigits rest then
      return s!"<apply/{rest}>"
  if s == "_lean_main" then
    return "[lean] main"
  if let some res := demangleWithPkg s "l_" "lp_" (postprocess := true) then
    return res
  if let some res := demangleWithPkg s "_init_l_" "_init_lp_" (postprocess := true) then
    return s!"[init] {res}"
  if let some res := s.dropPrefix? "_init_" then
    -- exported name
    return s!"[init] {res}"
  let (phases, s) := consumeModuleInitializationPrefix s
  -- module names don't require post-processing
  if let some res := demangleWithPkg s "initialize_" "initializep_" (postprocess := false) then
    match phases with
    | .runtime => return s!"[runtime_module_init] {res}"
    | .comptime => return s!"[meta_module_init] {res}"
    | .all => return s!"[module_init] {res}"
  none

def stripColdSuffix (s : String) : String × String :=
  match s.find? ".cold" with
  | some pos => (s.extract s.startPos pos, s.extract pos s.endPos)
  | none => (s, "")

public def demangleSymbol (symbol : String) : Option String := do
  if symbol.isEmpty then none
  let (core, coldSuffix) := stripColdSuffix symbol
  let result ← demangleCore core
  if coldSuffix.isEmpty then return result
  else return s!"{result} {coldSuffix}"

def skipWhile (s : String) (pos : s.Pos) (pred : Char → Bool) : s.Pos :=
  if h : pos = s.endPos then pos
  else if pred (pos.get h) then skipWhile s (pos.next h) pred
  else pos
termination_by pos

def splitAt₂ (s : String) (p₁ p₂ : s.Pos) : String × String × String :=
  (s.extract s.startPos p₁, s.extract p₁ p₂, s.extract p₂ s.endPos)

/-- Extract the symbol from a backtrace line (Linux glibc or macOS format). -/
def extractSymbol (line : String) :
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
