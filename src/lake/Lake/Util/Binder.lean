/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Parser.Term
import Lean.Elab.Term
import Lean.Expr

namespace Lake
open Lean Parser

abbrev Ellipsis := TSyntax ``Term.ellipsis
abbrev NamedArgument := TSyntax ``Term.namedArgument
abbrev Argument := TSyntax ``Term.argument

instance : Coe Term Argument where
  coe s := ⟨s.raw⟩

instance : Coe Ellipsis Argument where
  coe s := ⟨s.raw⟩

instance : Coe NamedArgument Argument where
  coe s := ⟨s.raw⟩

abbrev Hole := TSyntax ``Term.hole
abbrev BinderIdent := TSyntax ``Term.binderIdent
abbrev TypeSpec := TSyntax ``Term.typeSpec

def mkHoleFrom (ref : Syntax) : Hole :=
  mkNode ``Term.hole #[mkAtomFrom ref "_"]

instance : Coe Hole Term where
  coe s := ⟨s.raw⟩

instance : Coe Hole BinderIdent where
  coe s := ⟨s.raw⟩

instance : Coe Ident BinderIdent where
  coe s := ⟨s.raw⟩

abbrev BracketedBinder := TSyntax ``Term.bracketedBinder
abbrev FunBinder := TSyntax ``Term.funBinder

instance : Coe BinderIdent FunBinder where
  coe s := ⟨s.raw⟩

@[run_parser_attribute_hooks]
def binder := Term.binderIdent <|> Term.bracketedBinder

abbrev Binder := TSyntax ``binder
instance : Coe Binder (TSyntax [identKind, ``Term.hole, ``Term.bracketedBinder]) where
  coe stx := ⟨stx.raw⟩

abbrev BinderModifier := TSyntax [``Term.binderTactic, ``Term.binderDefault]

--------------------------------------------------------------------------------
-- Adapted from the private utilities in `Lean.Elab.Binders`

structure BinderSyntaxView where
  id : Ident
  type : Term
  info : BinderInfo
  modifier? : Option BinderModifier := none

def expandOptType (ref : Syntax) (optType : Syntax) : Term :=
  if optType.isNone then
    mkHoleFrom ref
  else
    ⟨optType[0][1]⟩

def getBinderIds (ids : Syntax) : MacroM (Array BinderIdent) :=
  ids.getArgs.mapM fun id =>
    let k := id.getKind
    if k == identKind || k == `Lean.Parser.Term.hole then
      return ⟨id⟩
    else
      Macro.throwErrorAt id "identifier or `_` expected"

def expandBinderIdent (stx : Syntax) : MacroM Ident :=
  match stx with
  | `(_) => (⟨·⟩) <$> Elab.Term.mkFreshIdent stx
  | _    => pure ⟨stx⟩

def expandOptIdent (stx : Syntax) : BinderIdent :=
  if stx.isNone then mkHoleFrom stx else ⟨stx[0]⟩

def expandBinderType (ref : Syntax) (stx : Syntax) : Term :=
  if stx.getNumArgs == 0 then mkHoleFrom ref else ⟨stx[1]⟩

def expandBinderModifier (optBinderModifier : Syntax) : Option BinderModifier :=
  if optBinderModifier.isNone then
    none
  else
    some ⟨optBinderModifier[0]⟩

def matchBinder (stx : Syntax) : MacroM (Array BinderSyntaxView) := do
  let k := stx.getKind
  if stx.isIdent || k == ``Term.hole then
    -- binderIdent
    return #[{ id := (← expandBinderIdent stx), type := mkHoleFrom stx, info := .default }]
  else if k == ``Lean.Parser.Term.explicitBinder then
    -- `(` binderIdent+ binderType (binderDefault <|> binderTactic)? `)`
    let ids ← getBinderIds stx[1]
    let type := stx[2]
    let modifier? := expandBinderModifier stx[3]
    ids.mapM fun id => return {
      id := ← expandBinderIdent id,
      type := expandBinderType id type,
      info := .default,
      modifier?
    }
  else if k == ``Lean.Parser.Term.implicitBinder then
    -- `{` binderIdent+ binderType `}`
    let ids ← getBinderIds stx[1]
    let type := stx[2]
    ids.mapM fun id => return {
      id := ← expandBinderIdent id,
      type := expandBinderType id type,
      info := .implicit
    }
  else if k == ``Lean.Parser.Term.strictImplicitBinder then
    -- `⦃` binderIdent+ binderType `⦄`
    let ids ← getBinderIds stx[1]
    let type := stx[2]
    ids.mapM fun id => do pure {
      id := ← expandBinderIdent id,
      type := expandBinderType id type,
      info := .strictImplicit
    }
  else if k == ``Lean.Parser.Term.instBinder then
    -- `[` optIdent type `]`
    let id := expandOptIdent stx[1]
    let type := stx[2]
    return #[{id := ← expandBinderIdent id, type := ⟨type⟩, info := .instImplicit}]
  else
    Macro.throwUnsupported

--------------------------------------------------------------------------------

def BinderSyntaxView.mkBinder : BinderSyntaxView → MacroM Binder
| {id, type, info, modifier?} => do
  match info with
  | .default        => `(binder| ($id : $type $[$modifier?]?))
  | .implicit       => `(binder| {$id : $type})
  | .strictImplicit => `(binder| ⦃$id : $type⦄)
  | .instImplicit   => `(binder| [$id : $type])

def BinderSyntaxView.mkArgument : BinderSyntaxView → MacroM NamedArgument
| {id, ..} => `(Term.namedArgument| ($id := $id))

def expandBinders (dbs : Array Binder) : MacroM (Array Binder × Array Term) := do
  let mut bs := #[]
  let mut args : Array Term := #[]
  for db in dbs do
    let views ← matchBinder db.raw
    for view in views do
      bs := bs.push (← view.mkBinder)
      args := args.push ⟨(← view.mkArgument).raw⟩
  return (bs, args)
