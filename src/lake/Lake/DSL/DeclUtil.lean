/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.Config
import Lake.Util.Name
import Lake.Util.Binder
import Lean.Parser.Command

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

def expandIdentOrStrAsString (stx : IdentOrStr) : MacroM String :=
  match stx with
  | `(identOrStr|$x:ident) => return x.getId.toString (escape := false)
  | `(identOrStr|$x:str) => return x.getString
  | _ => Macro.throwErrorAt stx "ill-formed syntax; expected identifier or string literal"

def expandIdentOrStrAsName (stx : IdentOrStr) : MacroM Name :=
  match stx with
  | `(identOrStr|$x:ident) => return x.getId
  | `(identOrStr|$x:str) => return Name.mkSimple x.getString
  | _ => Macro.throwErrorAt stx "ill-formed syntax; expected identifier or string literal"

def expandIdentOrStrAsIdent (stx : IdentOrStr) : MacroM Ident :=
  match stx with
  | `(identOrStr|$x:ident) => return x
  | `(identOrStr|$x:str) => return mkIdentFrom x (Name.mkSimple x.getString)
  | _ => Macro.throwErrorAt stx "ill-formed syntax; expected identifier or string literal"

def mkStrLitFrom (ref : Syntax) (val : String) : StrLit :=
  Syntax.mkStrLit val <| SourceInfo.fromRef ref

def mkSimpleNameFrom (ref : Syntax) (name : String) : Term :=
  Syntax.mkApp (mkCIdentFrom ref ``SimpleName.mk) #[mkStrLitFrom ref name]

def expandIdentOrStr (stx : TSyntax ``identOrStr) : MacroM Term :=
  return mkSimpleNameFrom stx <| ← expandIdentOrStrAsString stx

syntax declField :=
  ident ":=" term

syntax structVal :=
  "{" manyIndent(group(declField ", "?)) "}"

syntax declValDo :=
  ppSpace Term.do (Term.whereDecls)?

syntax declValStruct :=
  ppSpace structVal (Term.whereDecls)?

syntax declValWhere :=
  " where " sepByIndentSemicolon(declField) (Term.whereDecls)?

syntax declValTyped :=
  Term.typeSpec declValSimple

syntax declValOptTyped :=
  (Term.typeSpec)? declValSimple

syntax structDeclSig :=
  identOrStr (declValWhere <|> declValOptTyped <|> declValStruct)?

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

def expandDeclField : TSyntax ``declField → MacroM (TSyntax ``Term.structInstField)
| `(declField| $id :=%$tk $val) => `(Term.structInstField| $id:ident :=%$tk $val)
| x => Macro.throwErrorAt x "ill-formed field declaration"

def mkConfigDecl
(declName? : Option Name) (doc? : Option DocComment)
(attrs : Array AttrInstance) (ty : Term) (spec : Syntax)
: MacroM Syntax.Command := do
  match spec with
  | `(structDeclSig| $nameStx:identOrStr) =>
    let declName ← expandIdentOrStrAsName nameStx
    let declId := mkIdentFrom nameStx <| declName?.getD declName
    let rawName := Name.quoteFrom nameStx declName
    `($[$doc?]? @[$attrs,*] abbrev $declId : $ty :=
      {name := $(← expandIdentOrStr nameStx), rawName := $rawName})
  | `(structDeclSig| $nameStx where $fs;* $[$wds?:whereDecls]?) => do
    let declName ← expandIdentOrStrAsName nameStx
    let declId := mkIdentFrom nameStx <| declName?.getD declName
    let rawName := Name.quoteFrom nameStx declName
    let fields ← fs.getElems.mapM expandDeclField
    let defn ← `({ name := $(← expandIdentOrStr nameStx), rawName := $rawName, $fields,* })
    `($[$doc?]? @[$attrs,*] abbrev $declId : $ty := $defn $[$wds?:whereDecls]?)
  | `(structDeclSig| $nameStx $[: $ty?]? :=%$defTk $defn $[$wds?]?) => do
    let declName ← expandIdentOrStrAsName nameStx
    let declId := mkIdentFrom nameStx <| declName?.getD declName
    let notice ← withRef defTk `(#eval IO.eprintln s!" warning: {__dir__}: `:=` syntax for configurations has been deprecated")
    `($notice $[$doc?]? @[$attrs,*] abbrev $declId : $ty := $defn $[$wds?]?)
  | `(structDeclSig| $nameStx { $[$fs $[,]?]* } $[$wds?:whereDecls]?) => do
    let declName ← expandIdentOrStrAsName nameStx
    let declId := mkIdentFrom nameStx <| declName?.getD declName
    let rawName := Name.quoteFrom nameStx declName
    let fields ← fs.mapM expandDeclField
    let defn ← `({ name := $(← expandIdentOrStr nameStx), rawName := $rawName, $fields,* })
    `($[$doc?]? @[$attrs,*] abbrev $declId : $ty := $defn $[$wds?:whereDecls]?)
  | stx => Macro.throwErrorAt stx "ill-formed configuration syntax"
