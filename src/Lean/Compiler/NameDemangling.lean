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
import Init.Data.Range.Polymorphic.Iterators
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

def namePartsToName (parts : Array NamePart) : Name :=
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

def findPrivate? (comps : Array NamePart) : Option Nat := do
  guard <| comps.size >= 3 && comps[0]? == some (.str "_private")
  comps.idxOf? (.num 0) |>.map (· + 1)

def findMacroScopes? (comps : Array NamePart) : Option Nat := do
  guard <| comps.size >= 3 && comps[comps.size - 2]? == some (.str "_hyg") &&
    comps.back? matches some (.num _)
  comps.idxOf? (.str "_@")

partial def postprocessNameParts (parts : Array NamePart) (fullName : Bool := true) :
    String := Id.run do
  let mut parts := parts
  let mut flags := #[]
  -- _boxed suffix is independent from macro scopes and can only occur at the top level
  if fullName && parts.back? == some (.str "_boxed") then
    flags := flags.push "boxed"
    parts := parts.pop
  if parts.back?.any isSpecIndex then
    if let some idx := parts.idxOf? (.str "_at_") then
      let before := parts.take idx
      let after := parts.extract (idx + 1) (parts.size - 1)
      let res := postprocessNameParts before ++ " spec at " ++ postprocessNameParts after
      if flags.isEmpty then
        return res
      else
        return s!"{res} [{String.intercalate ", " flags.toList}]"
  if let some i := findPrivate? parts then
    flags := flags.push "private"
    parts := parts.drop i
  if let some i := findMacroScopes? parts then
    parts := parts.take i
  repeat
    let some part := parts.back? | break
    let some suffix := matchSuffix part | break
    parts := parts.pop
    unless flags.contains suffix do
      flags := flags.push suffix
  let nameStr := (namePartsToName parts).toString
  if flags.isEmpty then
    return nameStr
  else
    return s!"{nameStr} [{String.intercalate ", " flags.toList}]"

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

def demangleWithPkg (s : String) (normalPrefix packagePrefix : String) : Option String := do
  if let some s := s.dropPrefix? normalPrefix then
    let name ← Name.demangle? s.copy
    return postprocessNameParts (nameToNameParts name)
  else if let some s := s.dropPrefix? packagePrefix then
    let name ← Name.demangle? s.copy
    let (pkg, name) ← splitPrefix name
    return postprocessNameParts (nameToNameParts name) ++ s!" ({pkg})"
  else
    none

def consumeModuleInitializationPrefix (s : String) : IRPhases × String :=
  if let some s := s.dropPrefix? "meta_" then
    (.comptime, s.copy)
  else if let some s := s.dropPrefix? "runtime_" then
    (.runtime, s.copy)
  else
    (.all, s)

def stripColdSuffix (s : String) : String × String :=
  match s.find? ".cold" with
  | some pos => (s.extract s.startPos pos, s.extract pos s.endPos)
  | none => (s, "")

def demangleCore (s : String) : Option String := do
  if let some rest := s.dropPrefix? "lean_apply_" then
    if isAllDigits rest then
      return s!"<apply/{rest}>"
  if s == "_lean_main" then
    return "[lean] main"
  if let some res := demangleWithPkg s "l_" "lp_" then
    return res
  if let some res := demangleWithPkg s "_init_l_" "_init_lp_" then
    return s!"[init] {res}"
  if let some res := s.dropPrefix? "_init_" then
    -- exported name
    return s!"[init] {res}"
  let (phases, s) := consumeModuleInitializationPrefix s
  if let some res := demangleWithPkg s "initialize_" "initializep_" then
    match phases with
    | .runtime => return s!"[runtime_module_init] {res}"
    | .comptime => return s!"[meta_module_init] {res}"
    | .all => return s!"[module_init] {res}"
  none

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
