/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Binder
import Lake.Util.Name
import Lake.Config.Meta
import Lean.Parser.Command
import Lean.Elab.Command

open Lean Parser Command

namespace Lake.DSL

/-- The name given to the definition created by the `package` syntax. -/
def packageDeclName := `_package

---

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

-- syntax structDeclSig :=
--   ((identOrStr)? (declValWhere <|> declValStruct)?) <|> identOrStr

syntax optConfig :=
  (declValWhere <|> declValStruct)?

abbrev OptConfig := TSyntax ``optConfig

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

open Syntax Elab Command

def mkConfigFields
  (tyName : Name) (infos : NameMap ConfigFieldInfo) (fs : Array DeclField)
: CommandElabM (TSyntax ``Term.structInstFields) := do
  let mut m := mkNameMap Field
  for x in fs do
    let `(declField| $id := $val) := x
      | throwErrorAt x "ill-formed field declaration syntax"
    let fieldName := id.getId
    addCompletionInfo <| .fieldId x fieldName {} tyName
    if let some info := infos.find? fieldName then
      let c := info.realName
      if !info.canonical && m.contains c then
        logWarningAt id m!"redefined field '{c}' ('{fieldName}' is an alias of '{c}')"
      m := m.insert c {ref := id, val}
    else
      logWarningAt id m!"unknown '{.ofConstName tyName}' field '{fieldName}'"
  let fs ← m.foldM (init := #[]) fun a k {ref, val} => do
    let id := mkIdentFrom ref k true
    -- An unhygienic quotation is used to avoid introducing source info
    -- which will break field auto-completion.
    let fieldStx := Unhygienic.run `(Term.structInstField| $id:ident := $val)
    return a.push fieldStx
  return mkNode ``Term.structInstFields #[mkSep fs mkNullNode]

def mkConfigDeclIdent (stx? : Option IdentOrStr) : CommandElabM Ident := do
  match stx? with
  | some stx => return expandIdentOrStrAsIdent stx
  | none => Elab.Term.mkFreshIdent (← getRef)

def elabConfig
  (tyName : Name) [info : ConfigInfo tyName]
  (id : Ident) (ty : Term) (config : TSyntax ``optConfig)
: CommandElabM PUnit := do
  let mkCmd (whereInfo : SourceInfo) (fs : TSyntaxArray ``declField) wds? := do
    /-
    Quotation syntax produces synthetic source information.
    However, field auto-completion requires the trailing position of this token,
    which can only be obtained from the original source info. Thus, we must
    construct this token manually to preserve its original source info.
    -/
    let whereTk := atom whereInfo "where"
    let fields ← mkConfigFields tyName info.fieldMap fs
    let whereStx := mkNode ``whereStructInst #[whereTk, fields, mkOptionalNode wds?]
    let cmd ← `(def $id : $ty $whereStx:whereStructInst)
    withMacroExpansion config cmd <| elabCommand cmd
  match config with
  | `(optConfig| ) =>
    mkCmd .none #[] none
  | `(optConfig| where%$tk $fs;* $[$wds?:whereDecls]?) =>
    mkCmd tk.getHeadInfo fs.getElems wds?
  | `(optConfig| {%$tk $fs;* } $[$wds?:whereDecls]?) =>
    mkCmd tk.getHeadInfo fs wds?
  | stx => throwErrorAt stx "ill-formed configuration syntax"
