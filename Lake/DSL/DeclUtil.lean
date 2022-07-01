/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Command

namespace Lake.DSL
open Lean Parser Command

abbrev DocComment := TSyntax ``docComment
abbrev Attributes := TSyntax ``Term.attributes
abbrev AttrInstance := TSyntax ``Term.attrInstance
abbrev WhereDecls := TSyntax ``Term.whereDecls

abbrev Hole := TSyntax ``Term.hole
abbrev BinderIdent := TSyntax ``Term.binderIdent
abbrev SimpleBinder := TSyntax ``Term.simpleBinder
abbrev FunBinder := TSyntax ``Term.funBinder

instance : Coe Hole BinderIdent where
  coe s := ⟨s.raw⟩

instance : Coe Ident BinderIdent where
  coe s := ⟨s.raw⟩

instance : Coe BinderIdent SimpleBinder where
  coe s := ⟨s.raw⟩

instance : Coe SimpleBinder FunBinder where
  coe s := ⟨s.raw⟩

---

syntax structVal :=
  "{" manyIndent(group(Term.structInstField ", "?)) "}"

syntax declValDo :=
  ppSpace Term.do (Term.whereDecls)?

syntax declValStruct :=
  ppSpace structVal (Term.whereDecls)?

syntax declValTyped :=
  Term.typeSpec declValSimple

syntax declValOptTyped :=
  (Term.typeSpec)? declValSimple

syntax simpleDeclSig :=
  ident Term.typeSpec declValSimple

def expandAttrs (attrs? : Option Attributes) : Array AttrInstance :=
  if let some attrs := attrs? then
    match attrs with
    | `(Term.attributes| @[$attrs,*]) => attrs
    | _ => #[]
  else
    #[]
