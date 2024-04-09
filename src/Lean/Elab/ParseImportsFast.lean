/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Parser.Module

namespace Lean
namespace ParseImports

structure State where
  imports : Array Import := #[]
  pos     : String.Pos := 0
  error?  : Option String := none
  deriving Inhabited

def Parser := String → State → State

instance : Inhabited Parser where
  default := fun _ s => s

@[inline] def State.setPos (s : State) (pos : String.Pos) : State :=
  { s with pos := pos }

@[inline] def State.mkError (s : State) (msg : String) : State :=
  { s with error? := some msg }

def State.mkEOIError (s : State) : State :=
  s.mkError "unexpected end of input"

@[inline] def State.next (s : State) (input : String) (pos : String.Pos) : State :=
  { s with pos := input.next pos }

@[inline] def State.next' (s : State) (input : String) (pos : String.Pos) (h : ¬ input.atEnd pos): State :=
  { s with pos := input.next' pos h }

partial def finishCommentBlock (nesting : Nat) : Parser := fun input s =>
  let input := input
  let i     := s.pos
  if h : input.atEnd i then eoi s
  else
    let curr := input.get' i h
    let i    := input.next' i h
    if curr == '-' then
      if h : input.atEnd i then eoi s
      else
        let curr := input.get' i h
        if curr == '/' then -- "-/" end of comment
          if nesting == 1 then s.next input i
          else finishCommentBlock (nesting-1) input (s.next' input i h)
        else
          finishCommentBlock nesting input (s.next' input i h)
    else if curr == '/' then
      if h : input.atEnd i then eoi s
      else
        let curr := input.get' i h
        if curr == '-' then finishCommentBlock (nesting+1) input (s.next' input i h)
        else finishCommentBlock nesting input (s.setPos i)
    else finishCommentBlock nesting input (s.setPos i)
where
  eoi s := s.mkError "unterminated comment"

@[specialize] partial def takeUntil (p : Char → Bool) : Parser := fun input s =>
  let i := s.pos
  if h : input.atEnd i then s
  else if p (input.get' i h) then s
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
  if h : input.atEnd i then s
  else
    let curr := input.get' i h
    if curr == '\t' then
      s.mkError "tabs are not allowed; please configure your editor to expand them"
    else if curr.isWhitespace then whitespace input (s.next input i)
    else if curr == '-' then
      let i    := input.next' i h
      let curr := input.get i
      if curr == '-' then andthen (takeUntil (fun c => c = '\n')) whitespace input (s.next input i)
      else s
    else if curr == '/' then
      let i        := input.next' i h
      let curr     := input.get i
      if curr == '-' then
        let i    := input.next i
        let curr := input.get i
        if curr == '-' || curr == '!' then s -- "/--" and "/-!" doc comment are actual tokens
        else andthen (finishCommentBlock 1) whitespace input (s.next input i)
      else s
    else s

@[inline] partial def keywordCore (k : String) (failure : Parser) (success : Parser) : Parser := fun input s =>
  let rec @[specialize] go (i j : String.Pos) : State :=
    if h₁ : k.atEnd i then
      success input <| whitespace input (s.setPos j)
    else if h₂ : input.atEnd j then
      failure input s
    else
      let curr₁ := k.get' i h₁
      let curr₂ := input.get' j h₂
      if curr₁ != curr₂ then
        failure input s
      else
        go (k.next' i h₁) (input.next' j h₂)
  go 0 s.pos

@[inline] partial def keyword (k : String) : Parser :=
  keywordCore k (fun _ s => s.mkError s!"`{k}` expected") (fun _ s => s)

@[inline] def isIdCont : String → State → Bool := fun input s =>
  let i := s.pos
  let curr := input.get i
  if curr == '.' then
    let i := input.next i
    if h : input.atEnd i then
      false
    else
      let curr := input.get' i h
      isIdFirst curr || isIdBeginEscape curr
  else
    false

def State.pushModule (module : Name) (runtimeOnly : Bool) (s : State) : State :=
  { s with imports := s.imports.push { module, runtimeOnly } }

@[inline] def isIdRestCold (c : Char) : Bool :=
  c = '_' || c = '\'' || c == '!' || c == '?' || isLetterLike c || isSubScriptAlnum c

@[inline] def isIdRestFast (c : Char) : Bool :=
  c.isAlphanum || (c != '.' && c != '\n' && c != ' ' && isIdRestCold c)

partial def moduleIdent (runtimeOnly : Bool) : Parser := fun input s =>
  let rec parse (module : Name) (s : State) :=
    let i := s.pos
    if h : input.atEnd i then
      s.mkEOIError
    else
      let curr := input.get' i h
      if isIdBeginEscape curr then
        let startPart := input.next' i h
        let s         := takeUntil isIdEndEscape input (s.setPos startPart)
        if h : input.atEnd s.pos then
          s.mkError "unterminated identifier escape"
        else
          let stopPart  := s.pos
          let s         := s.next' input s.pos h
          let module    := .str module (input.extract startPart stopPart)
          if isIdCont input s then
            let s := s.next input s.pos
            parse module s
          else
            whitespace input (s.pushModule module runtimeOnly)
      else if isIdFirst curr then
        let startPart := i
        let s         := takeWhile isIdRestFast input (s.next' input i h)
        let stopPart  := s.pos
        let module    := .str module (input.extract startPart stopPart)
        if isIdCont input s then
          let s := s.next input s.pos
          parse module s
        else
          whitespace input (s.pushModule module runtimeOnly)
      else
        s.mkError "expected identifier"
  parse .anonymous s

@[specialize] partial def many (p : Parser) : Parser := fun input s =>
  let pos := s.pos
  let size := s.imports.size
  let s := p input s
  match s.error? with
  | none => many p input s
  | some _ => { pos, error? := none, imports := s.imports.shrink size }

@[inline] partial def preludeOpt (k : String) : Parser :=
  keywordCore k (fun _ s => s.pushModule `Init false) (fun _ s => s)

def main : Parser :=
  preludeOpt "prelude" >>
  many (keyword "import" >> keywordCore "runtime" (moduleIdent false) (moduleIdent true))

end ParseImports

/--
Simpler and faster version of `parseImports`. We use it to implement Lake.
-/
def parseImports' (input : String) (fileName : String) : IO (Array Lean.Import) := do
  let s := ParseImports.main input (ParseImports.whitespace input {})
  match s.error? with
  | none => return s.imports
  | some err => throw <| IO.userError s!"{fileName}: {err}"

deriving instance ToJson for Import

structure PrintImportResult where
  imports? : Option (Array Import) := none
  errors   : Array String := #[]
  deriving ToJson

structure PrintImportsResult where
  imports : Array PrintImportResult
  deriving ToJson

@[export lean_print_imports_json]
def printImportsJson (fileNames : Array String) : IO Unit := do
  let rs ← fileNames.mapM fun fn => do
    try
      let deps ← parseImports' (← IO.FS.readFile ⟨fn⟩) fn
      return { imports? := some deps }
    catch e => return { errors := #[e.toString] }
  IO.println (toJson { imports := rs : PrintImportsResult } |>.compress)

end Lean
