/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.Config
import Lake.Util.Binder
import Lake.Util.Name
import Lean.Parser.Command
import Lean.Elab.Command

namespace Lake.DSL
open Lean Parser Command

abbrev DocComment := TSyntax ``docComment
abbrev Attributes := TSyntax ``Term.attributes
abbrev AttrInstance := TSyntax ``Term.attrInstance
abbrev WhereDecls := TSyntax ``Term.whereDecls

---

def expandAttrs (attrs? : Option Attributes) : Array AttrInstance :=
  if let some attrs := attrs? then
    match attrs with
    | `(Term.attributes| @[$attrs,*]) => attrs
    | _ => #[]
  else
    #[]

syntax identOrStr :=
  ident <|> str

abbrev IdentOrStr := TSyntax ``identOrStr

def expandIdentOrStrAsIdent (stx : IdentOrStr) : Ident :=
  match stx with
  | `(identOrStr|$x:ident) => x
  | `(identOrStr|$x:str) => mkIdentFrom x (Name.mkSimple x.getString)
  | _ => ⟨.missing⟩

/-- A field assignment in a declarative configuration. -/
syntax declField :=
  ident " := " term

@[inherit_doc declField] abbrev DeclField := TSyntax ``declField

syntax structVal :=
  "{" manyIndent(group(declField ", "?)) "}"

syntax declValDo :=
  ppSpace Term.do (Term.whereDecls)?

syntax declValStruct :=
  ppSpace structVal (Term.whereDecls)?

syntax declValWhere :=
  " where " sepByIndentSemicolon(declField) (Term.whereDecls)?

syntax simpleDeclSig :=
  ident Term.typeSpec declValSimple

syntax structDeclSig :=
  ((identOrStr)? (declValWhere <|> declValStruct)?) <|> identOrStr

syntax bracketedSimpleBinder :=
  "(" ident (" : " term)? ")"

syntax simpleBinder :=
  ident <|> bracketedSimpleBinder

abbrev SimpleBinder := TSyntax ``simpleBinder
open Lean.Parser.Term in
def expandOptSimpleBinder (stx? : Option SimpleBinder) : MacroM FunBinder := do
  match stx? with
  | some stx =>
    match stx with
    | `(simpleBinder| $id:ident) =>
      `(funBinder| $id)
    | `(simpleBinder| ($id $[: $ty?]?)) =>
      let ty := ty?.getD (← `(_))
      `(funBinder| ($id : $ty))
    | _ => `(funBinder| _)
  | none => `(funBinder| _)

structure Field where
  ref : Syntax
  val : Term

open Lean Elab Command

def elabConfigDecl
  (tyName : Name)
  (sig : TSyntax ``structDeclSig)
  (doc? : Option DocComment) (attrs : Array AttrInstance)
  (name? : Option Name := none)
: CommandElabM PUnit := do
  let mkCmd (bodyRef : Syntax) (nameStx? : Option IdentOrStr) (fs : TSyntaxArray ``declField) wds? := do
    let mut m := mkNameMap Field
    let nameId? := nameStx?.map expandIdentOrStrAsIdent
    if let some id := nameId? then
      m := m.insert `name {ref := id, val := Name.quoteFrom id id.getId}
    for x in fs do
      let `(declField| $id := $val) := x
        | throwErrorAt x "ill-formed field declaration syntax"
      let fieldName := id.getId
      addCompletionInfo <| .fieldId x fieldName {} tyName
      if findField? (← getEnv) tyName fieldName |>.isSome then
        m := m.insert fieldName {ref := id, val}
      else
        logWarningAt id m!"unknown '{.ofConstName tyName}' field '{fieldName}'"
    let fs ← m.foldM (init := #[]) fun a k {ref, val} => withRef ref do
      return a.push <| ← `(Term.structInstField| $(← mkIdentFromRef k true):ident := $val)
    let ty := mkCIdentFrom (← getRef) tyName
    let declId ← id do
      if let some id := nameId? then
        if let some name := name? then
          return mkIdentFrom id name
        else
          return id
      else
        if let some name := name? then
          mkIdentFromRef name
        else
          Elab.Term.mkFreshIdent (← getRef)
    let defn ← withRef bodyRef `({$[$fs:structInstField],*})
    let cmd ← `($[$doc?]? @[$attrs,*] abbrev $declId : $ty := $defn $[$wds?:whereDecls]?)
    withMacroExpansion sig cmd <| elabCommand cmd
  match sig with
  | `(structDeclSig| $nameStx:identOrStr) =>
    mkCmd (← getRef) nameStx #[] none
  | `(structDeclSig| $[$nameStx?]? where%$tk $fs;* $[$wds?:whereDecls]?) =>
    mkCmd tk nameStx? fs.getElems wds?
  | `(structDeclSig| $[$nameStx?]? { $[$fs $[,]?]* }%$tk $[$wds?:whereDecls]?) =>
    mkCmd tk nameStx? fs wds?
  | stx => throwErrorAt stx "ill-formed configuration syntax"
