/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich, Mac Malone
-/
module

prelude
public import Lean.Parser.Module

public section

namespace Lean
namespace ParseImports

structure State where
  imports       : Array Import := #[]
  pos           : String.Pos.Raw := 0
  badModifier   : Bool := false
  error?        : Option String := none
  isModule      : Bool := false
  -- per-import fields to be consumed by `moduleIdent`
  isMeta        : Bool := false
  isExported    : Bool := false
  importAll     : Bool := false
  deriving Inhabited

@[expose] def Parser := String → State → State

@[inline] def skip : Parser := fun _ s => s

instance : Inhabited Parser := ⟨skip⟩

@[inline] def State.setPos (s : State) (pos : String.Pos.Raw) : State :=
  { s with pos := pos }

@[inline] def State.mkError (s : State) (msg : String) : State :=
  { s with error? := some msg }

def State.mkEOIError (s : State) : State :=
  s.mkError "unexpected end of input"

@[inline] def State.clearError (s : State) : State :=
  { s with error? := none, badModifier := false  }

@[inline] def State.next (s : State) (input : String) (pos : String.Pos.Raw) : State :=
  { s with pos := pos.next input }

@[inline] def State.next' (s : State) (input : String) (pos : String.Pos.Raw) (h : ¬ pos.atEnd input) : State :=
  { s with pos := pos.next' input h }

partial def finishCommentBlock (nesting : Nat) : Parser := fun input s =>
  let input := input
  let i     := s.pos
  if h : i.atEnd input then eoi s
  else
    let curr := i.get' input h
    let i    := i.next' input h
    if curr == '-' then
      if h : i.atEnd input then eoi s
      else
        let curr := i.get' input h
        if curr == '/' then -- "-/" end of comment
          if nesting == 1 then s.next input i
          else finishCommentBlock (nesting-1) input (s.next' input i h)
        else
          finishCommentBlock nesting input (s.next' input i h)
    else if curr == '/' then
      if h : i.atEnd input then eoi s
      else
        let curr := i.get' input h
        if curr == '-' then finishCommentBlock (nesting+1) input (s.next' input i h)
        else finishCommentBlock nesting input (s.setPos i)
    else finishCommentBlock nesting input (s.setPos i)
where
  eoi s := s.mkError "unterminated comment"

@[specialize] partial def takeUntil (p : Char → Bool) : Parser := fun input s =>
  let i := s.pos
  if h : i.atEnd input then s
  else if p (i.get' input h) then s
  else takeUntil p input (s.next' input i h)

@[inline] def takeWhile (p : Char → Bool) : Parser :=
  takeUntil (fun c => !p c)

@[inline] def andthen (p q : Parser) : Parser := fun input s =>
  let s := p input s
  if s.error? matches some .. then s else q input s

instance : AndThen Parser where
  andThen p q := andthen p (q ())

partial def whitespace : Parser := fun input s =>
  let i := s.pos
  if h : i.atEnd input then s
  else
    let curr := i.get' input h
    if curr == '\t' then
      s.mkError "tabs are not allowed; please configure your editor to expand them"
    else if curr.isWhitespace then whitespace input (s.next input i)
    else if curr == '-' then
      let i    := i.next' input h
      let curr := i.get input
      if curr == '-' then andthen (takeUntil (fun c => c = '\n')) whitespace input (s.next input i)
      else s
    else if curr == '/' then
      let i        := i.next' input h
      let curr     := i.get input
      if curr == '-' then
        let i    := i.next input
        let curr := i.get input
        if curr == '-' || curr == '!' then s -- "/--" and "/-!" doc comment are actual tokens
        else andthen (finishCommentBlock 1) whitespace input (s.next input i)
      else s
    else s

@[inline] partial def keywordCore (k : String) (failure : Parser) (success : Parser) : Parser := fun input s =>
  let rec @[specialize] go (i j : String.Pos.Raw) : State :=
    if h₁ : i.atEnd k then
      success input <| whitespace input (s.setPos j)
    else if h₂ : j.atEnd input then
      failure input s
    else
      let curr₁ := i.get' k h₁
      let curr₂ := j.get' input h₂
      if curr₁ != curr₂ then
        failure input s
      else
        go (i.next' k h₁) (j.next' input h₂)
  go 0 s.pos

@[inline] def keyword (k : String) : Parser :=
  keywordCore k (fun _ s => s.mkError s!"`{k}` expected") skip

@[inline] def isIdCont : String → State → Bool := fun input s =>
  let i := s.pos
  let curr := i.get input
  if curr == '.' then
    let i := i.next input
    if h : i.atEnd input then
      false
    else
      let curr := i.get' input h
      isIdFirst curr || isIdBeginEscape curr
  else
    false

def State.pushImport (i : Import) (s : State) : State :=
  { s with imports := s.imports.push i }

@[inline] def isIdRestCold (c : Char) : Bool :=
  c = '_' || c = '\'' || c == '!' || c == '?' || isLetterLike c || isSubScriptAlnum c

@[inline] def isIdRestFast (c : Char) : Bool :=
  c.isAlphanum || (c != '.' && c != '\n' && c != ' ' && isIdRestCold c)

partial def moduleIdent : Parser := fun input s =>
  let finalize (module : Name) : Parser := fun input s =>
    let imp := { module, isMeta := s.isMeta, importAll := s.importAll, isExported := s.isExported }
    let s := whitespace input (s.pushImport imp)
    {s with isMeta := false, importAll := false, isExported := !s.isModule}
  let rec parse (module : Name) (s : State) :=
    let i := s.pos
    if h : i.atEnd input then
      s.mkEOIError
    else
      let curr := i.get' input h
      if isIdBeginEscape curr then
        let startPart := i.next' input h
        let s         := takeUntil isIdEndEscape input (s.setPos startPart)
        if h : s.pos.atEnd input then
          s.mkError "unterminated identifier escape"
        else
          let stopPart  := s.pos
          let s         := s.next' input s.pos h
          let module    := .str module (String.Pos.Raw.extract input startPart stopPart)
          if isIdCont input s then
            let s := s.next input s.pos
            parse module s
          else
            finalize module input s
      else if isIdFirst curr then
        let startPart := i
        let s         := takeWhile isIdRestFast input (s.next' input i h)
        let stopPart  := s.pos
        let module    := .str module (String.Pos.Raw.extract input startPart stopPart)
        if isIdCont input s then
          let s := s.next input s.pos
          parse module s
        else
          finalize module input s
      else
        s.mkError "expected identifier"
  parse .anonymous s

@[inline] def atomic (p : Parser) : Parser := fun input s =>
  let pos := s.pos
  let s := p input s
  if s.error? matches some .. then {s with pos} else s

@[specialize] partial def manyImports (p : Parser) : Parser := fun input s =>
  let pos := s.pos
  let s := p input s
  if s.error? matches some .. then
    if s.pos == pos then s.clearError else s
  else if s.badModifier then
    let err := "cannot use 'public', 'meta', or 'all' without 'module'"
    {s with pos, badModifier := false, error? := some err}
  else
    manyImports p input s

def setIsModule (isModule : Bool) : Parser := fun _ s =>
  { s with isModule, isExported := !isModule }

def setMeta : Parser := fun _ s =>
  if s.isModule then
    { s with isMeta := true }
  else
    { s with badModifier := true }

def setExported : Parser := fun _ s =>
  if s.isModule then
    { s with isExported := true }
  else
    { s with badModifier := true }

def setImportAll : Parser := fun _ s =>
  if s.isModule then
    { s with importAll := true }
  else
    { s with badModifier := true }

def main : Parser :=
  keywordCore "module" (setIsModule false) (setIsModule true) >>
  keywordCore "prelude" (fun _ s => s.pushImport `Init) skip >>
  manyImports (atomic (keywordCore "public" skip setExported >>
    keywordCore "meta" skip setMeta >>
    keyword "import") >>
    keywordCore "all" skip setImportAll >>
    moduleIdent)

end ParseImports

/--
Simpler and faster version of `parseImports`. We use it to implement Lake.
-/
def parseImports' (input : String) (fileName : String) : IO ModuleHeader := do
  let s := ParseImports.main input (ParseImports.whitespace input {})
  let some err := s.error?
    | return { s with }
  let fileMap := input.toFileMap
  let pos := fileMap.toPosition s.pos
  throw <| .userError s!"{fileName}:{pos.line}:{pos.column}: {err}"

structure PrintImportResult where
  result?  : Option ModuleHeader := none
  errors   : Array String := #[]
  deriving ToJson

structure PrintImportsResult where
  imports : Array PrintImportResult
  deriving ToJson

def printImportsJson (fileNames : Array String) : IO Unit := do
  let rs ← fileNames.mapM fun fn => do
    try
      let res ← parseImports' (← IO.FS.readFile ⟨fn⟩) fn
      return { result? := some res }
    catch e => return { errors := #[e.toString] }
  IO.println (toJson { imports := rs : PrintImportsResult } |>.compress)

end Lean
