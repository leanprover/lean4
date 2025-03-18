/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
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
  "{" structInstFields(sepByIndentSemicolon(declField)) "}"

syntax declValDo :=
  ppSpace Term.do (Term.whereDecls)?

syntax declValStruct :=
  ppSpace structVal (Term.whereDecls)?

syntax declValWhere :=
  " where " structInstFields(sepByIndentSemicolon(declField)) (Term.whereDecls)?

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

open Lean Syntax Elab Command

def elabConfigDecl
  (tyName : Name)
  (sig : TSyntax ``structDeclSig)
  (doc? : Option DocComment) (attrs : Array AttrInstance)
  (name? : Option Name := none)
: CommandElabM PUnit := do
  let mkCmd (whereInfo : SourceInfo) (nameStx? : Option IdentOrStr) (fs : TSyntaxArray ``declField) wds? := do
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
    let fs ← m.foldM (init := #[]) fun a k {ref, val} => do
      let id := mkIdentFrom ref k true
      -- An unhygienic quotation is used to avoid introducing source info
      -- which will break field auto-completion.
      let fieldStx := Unhygienic.run `(Term.structInstField| $id:ident := $val)
      return a.push fieldStx
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
    /-
    Quotation syntax produces synthetic source information.
    However, field auto-completion requires the trailing position of this token,
    which can only be obtained from the original source info. Thus, we must
    construct this token manually to preserve its original source info.
    -/
    let whereTk := atom whereInfo "where"
    let fields := mkNode ``Term.structInstFields #[mkSep fs mkNullNode]
    let whereStx := mkNode ``whereStructInst #[whereTk, fields, mkOptionalNode wds?]
    let cmd ← `($[$doc?]? @[$attrs,*] abbrev $declId : $ty $whereStx:whereStructInst)
    withMacroExpansion sig cmd <| elabCommand cmd
  match sig with
  | `(structDeclSig| $nameStx:identOrStr) =>
    mkCmd .none nameStx #[] none
  | `(structDeclSig| $[$nameStx?]? where%$tk $fs;* $[$wds?:whereDecls]?) =>
    mkCmd tk.getHeadInfo nameStx? fs.getElems wds?
  | `(structDeclSig| $[$nameStx?]? {%$tk $fs;* } $[$wds?:whereDecls]?) =>
    mkCmd tk.getHeadInfo nameStx? fs wds?
  | stx => throwErrorAt stx "ill-formed configuration syntax"
