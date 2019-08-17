/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment
import init.lean.attributes

namespace Lean

private def getIOTypeArg : Expr → Option Expr
| Expr.app (Expr.const `IO _) arg   => some arg
| _ => none

private def isUnitType : Expr → Bool
| Expr.const `Unit _   => true
| _ => false

private def isIOUnit (type : Expr) : Bool :=
match getIOTypeArg type with
| some type => isUnitType type
| _ => false

def mkInitAttr : IO (ParametricAttribute Name) :=
registerParametricAttribute `init "initialization procedure for global references" $ fun env declName stx =>
  match env.find declName with
  | none => Except.error "unknown declaration"
  | some decl =>
    match attrParamSyntaxToIdentifier stx with
    | some initFnName =>
      match env.find initFnName with
      | none => Except.error ("unknown initialization function '" ++ toString initFnName ++ "'")
      | some initDecl =>
        match getIOTypeArg initDecl.type with
        | none => Except.error ("initialization function '" ++ toString initFnName ++ "' must have type of the form `IO <type>`")
        | some initTypeArg =>
          if decl.type == initTypeArg then Except.ok initFnName
          else Except.error ("initialization function '" ++ toString initFnName ++ "' type mismatch")
    | _ => match stx with
      | Syntax.missing =>
        if isIOUnit decl.type then Except.ok Name.anonymous
        else Except.error "initialization function must have type `IO Unit`"
      | _ => Except.error "unexpected kind of argument"

@[init mkInitAttr]
constant initAttr : ParametricAttribute Name := default _

def isIOUnitInitFn (env : Environment) (fn : Name) : Bool :=
match initAttr.getParam env fn with
| some Name.anonymous => true
| _ => false

@[export lean_get_init_fn_name_for]
def getInitFnNameFor (env : Environment) (fn : Name) : Option Name :=
match initAttr.getParam env fn with
| some Name.anonymous => none
| some n => some n
| _ => none

def hasInitAttr (env : Environment) (fn : Name) : Bool :=
(getInitFnNameFor env fn).isSome

def setInitAttr (env : Environment) (declName : Name) (initFnName : Name := Name.anonymous) : Except String Environment :=
initAttr.setParam env declName initFnName

end Lean
