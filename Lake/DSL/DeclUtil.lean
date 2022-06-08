/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Command

namespace Lake.DSL
open Lean Parser Command

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

def expandAttrs (attrs? : Option Syntax) : Array Syntax :=
  if let some attrs := attrs? then
    match attrs with
    | `(Term.attributes| @[$attrs,*]) => attrs
    | _ => #[]
  else
    #[]
