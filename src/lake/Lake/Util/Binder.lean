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

/-- Same as `mkHole` but returns `TSyntax`. -/
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

abbrev DeclBinder := TSyntax [identKind, ``Term.hole, ``Term.bracketedBinder]

@[run_parser_attribute_hooks]
def binder := Term.binderIdent <|> Term.bracketedBinder
abbrev Binder := TSyntax ``binder

instance : Coe BinderIdent Binder where
  coe stx := ⟨stx.raw⟩

instance : Coe BracketedBinder Binder where
  coe stx := ⟨stx.raw⟩

instance : Coe Binder DeclBinder where
  coe stx := ⟨stx.raw⟩

abbrev BinderModifier := TSyntax [``Term.binderTactic, ``Term.binderDefault]

abbrev DepArrow := TSyntax ``Term.depArrow

instance : Coe DepArrow Term where
  coe stx := ⟨stx.raw⟩

--------------------------------------------------------------------------------
-- Adapted from the private utilities in `Lean.Elab.Binders`

structure BinderSyntaxView where
  ref : Syntax
  id : Ident
  type : Term
  info : BinderInfo
  modifier? : Option BinderModifier := none
  deriving Inhabited, Repr

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
  optBinderModifier.getOptional?.map (⟨·⟩)

def expandBinderCore (binders : Array BinderSyntaxView) (stx : Syntax) : MacroM (Array BinderSyntaxView) := do
  let k := stx.getKind
  if stx.isIdent || k == ``Term.hole then
    -- binderIdent
    return binders.push {
      ref := stx
      id := ← expandBinderIdent stx,
      type := mkHoleFrom stx,
      info := .default
    }
  else if k == ``Lean.Parser.Term.explicitBinder then
    -- `(` binderIdent+ binderType (binderDefault <|> binderTactic)? `)`
    let ids ← getBinderIds stx[1]
    let type := stx[2]
    let modifier? := expandBinderModifier stx[3]
    ids.foldlM (init := binders) fun binders id => return binders.push {
      ref := stx
      id := ← expandBinderIdent id,
      type := expandBinderType id type,
      info := .default,
      modifier?
    }
  else if k == ``Lean.Parser.Term.implicitBinder then
    -- `{` binderIdent+ binderType `}`
    let ids ← getBinderIds stx[1]
    let type := stx[2]
    ids.foldlM (init := binders) fun binders id => return binders.push {
      ref := stx
      id := ← expandBinderIdent id
      type := expandBinderType id type
      info := .implicit
    }
  else if k == ``Lean.Parser.Term.strictImplicitBinder then
    -- `⦃` binderIdent+ binderType `⦄`
    let ids ← getBinderIds stx[1]
    let type := stx[2]
    ids.foldlM (init := binders) fun binders id => return binders.push {
      ref := stx
      id := ← expandBinderIdent id
      type := expandBinderType id type
      info := .strictImplicit
    }
  else if k == ``Lean.Parser.Term.instBinder then
    -- `[` optIdent type `]`
    let id := expandOptIdent stx[1]
    let type := stx[2]
    return binders.push {
      ref := stx
      id := ← expandBinderIdent id
      type := ⟨type⟩
      info := .instImplicit
    }
  else
    Macro.throwUnsupported

@[inline] def expandBinder (stx : Syntax) : MacroM (Array BinderSyntaxView) :=
  expandBinderCore #[] stx

def expandBinders (stxs : Array Syntax) : MacroM (Array BinderSyntaxView) :=
  stxs.foldlM expandBinderCore #[]

--------------------------------------------------------------------------------

def BinderSyntaxView.mkBinder : BinderSyntaxView → BracketedBinder
| {ref, id, type, info, modifier?} => Unhygienic.run <| MonadRef.withRef ref do
  match info with
  | .default        => `(bracketedBinder| ($id : $type $[$modifier?]?))
  | .implicit       => `(bracketedBinder| {$id : $type})
  | .strictImplicit => `(bracketedBinder| ⦃$id : $type⦄)
  | .instImplicit   => `(bracketedBinder| [$id : $type])

def BinderSyntaxView.mkDepArrow (res : Term) (self : BinderSyntaxView) : DepArrow :=
  Unhygienic.run <| MonadRef.withRef self.ref do
    `(Term.depArrow| $(self.mkBinder) → $res)

def mkDepArrow (binders : Array BinderSyntaxView) (res : Term) : Term :=
  binders.foldl (fun r v => v.mkDepArrow r) res

def BinderSyntaxView.mkFunBinder : BinderSyntaxView → FunBinder
| {ref, id, type, info, ..} => Unhygienic.run <| withRef ref do
  match info with
  | .default        => `(Term.funBinder| ($id : $type))
  | .implicit       => `(Term.funBinder| {$id : $type})
  | .strictImplicit => `(Term.funBinder| ⦃$id : $type⦄)
  | .instImplicit   => `(Term.funBinder| [$id : $type])

def BinderSyntaxView.mkArgument : BinderSyntaxView → NamedArgument
| {ref, id, ..} => Unhygienic.run <| withRef ref `(Term.namedArgument| ($id := $id))
