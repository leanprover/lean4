/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Parser.Term
meta import Lean.Parser.Term

namespace Lake
open Lean Parser

public abbrev Ellipsis := TSyntax ``Term.ellipsis
public abbrev NamedArgument := TSyntax ``Term.namedArgument
public abbrev Argument := TSyntax ``Term.argument

public instance : Coe Term Argument where
  coe s := ⟨s.raw⟩

public instance : Coe Ellipsis Argument where
  coe s := ⟨s.raw⟩

public instance : Coe NamedArgument Argument where
  coe s := ⟨s.raw⟩

public abbrev Hole := TSyntax ``Term.hole
public abbrev BinderIdent := TSyntax ``Term.binderIdent
public abbrev TypeSpec := TSyntax ``Term.typeSpec

/-- Same as `mkHole` but returns `TSyntax`. -/
public def mkHoleFrom (ref : Syntax) : Hole :=
  mkNode ``Term.hole #[mkAtomFrom ref "_"]

public instance : Coe Hole Term where
  coe s := ⟨s.raw⟩

public instance : Coe Hole BinderIdent where
  coe s := ⟨s.raw⟩

public instance : Coe Ident BinderIdent where
  coe s := ⟨s.raw⟩

public abbrev BracketedBinder := TSyntax ``Term.bracketedBinder
public abbrev FunBinder := TSyntax ``Term.funBinder

public instance : Coe BinderIdent FunBinder where
  coe s := ⟨s.raw⟩

public abbrev DeclBinder := TSyntax [identKind, ``Term.hole, ``Term.bracketedBinder]

@[run_parser_attribute_hooks]
public def binder := Term.binderIdent <|> Term.bracketedBinder
public abbrev Binder := TSyntax ``binder

public instance : Coe BinderIdent Binder where
  coe stx := ⟨stx.raw⟩

public instance : Coe BracketedBinder Binder where
  coe stx := ⟨stx.raw⟩

public instance : Coe Binder DeclBinder where
  coe stx := ⟨stx.raw⟩

public abbrev BinderModifier := TSyntax [``Term.binderTactic, ``Term.binderDefault]

public abbrev DepArrow := TSyntax ``Term.depArrow

public instance : Coe DepArrow Term where
  coe stx := ⟨stx.raw⟩

--------------------------------------------------------------------------------
-- Adapted from the private utilities in `Lean.Elab.Binders`

public structure BinderSyntaxView where
  ref : Syntax
  id : Ident
  type : Term
  info : BinderInfo
  modifier? : Option BinderModifier := none
  deriving Inhabited, Repr

public def expandOptType (ref : Syntax) (optType : Syntax) : Term :=
  if optType.isNone then
    mkHoleFrom ref
  else
    ⟨optType[0][1]⟩

public def getBinderIds (ids : Syntax) : MacroM (Array BinderIdent) :=
  ids.getArgs.mapM fun id =>
    let k := id.getKind
    if k == identKind || k == `Lean.Parser.Term.hole then
      return ⟨id⟩
    else
      Macro.throwErrorAt id "identifier or `_` expected"

public def expandBinderIdent (stx : Syntax) : MacroM Ident :=
  match stx with
  | `(_) => (⟨·⟩) <$> `(x)
  | _    => pure ⟨stx⟩

public def expandOptIdent (stx : Syntax) : BinderIdent :=
  if stx.isNone then mkHoleFrom stx else ⟨stx[0]⟩

public def expandBinderType (ref : Syntax) (stx : Syntax) : Term :=
  if stx.getNumArgs == 0 then mkHoleFrom ref else ⟨stx[1]⟩

public def expandBinderModifier (optBinderModifier : Syntax) : Option BinderModifier :=
  optBinderModifier.getOptional?.map (⟨·⟩)

public def expandBinderCore
  (binders : Array BinderSyntaxView) (stx : Syntax)
: MacroM (Array BinderSyntaxView) := do
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

@[inline] public def expandBinder (stx : Syntax) : MacroM (Array BinderSyntaxView) :=
  expandBinderCore #[] stx

public def expandBinders (stxs : Array Syntax) : MacroM (Array BinderSyntaxView) :=
  stxs.foldlM expandBinderCore #[]

--------------------------------------------------------------------------------

public def BinderSyntaxView.mkBinder : BinderSyntaxView → BracketedBinder
| {ref, id, type, info, modifier?} => Unhygienic.run <| MonadRef.withRef ref do
  match info with
  | .default        => `(bracketedBinder| ($id : $type $[$modifier?]?))
  | .implicit       => `(bracketedBinder| {$id : $type})
  | .strictImplicit => `(bracketedBinder| ⦃$id : $type⦄)
  | .instImplicit   => `(bracketedBinder| [$id : $type])

public def BinderSyntaxView.mkDepArrow (res : Term) (self : BinderSyntaxView) : DepArrow :=
  Unhygienic.run <| MonadRef.withRef self.ref do
    `(Term.depArrow| $(self.mkBinder) → $res)

public def mkDepArrow (binders : Array BinderSyntaxView) (res : Term) : Term :=
  binders.foldl (fun r v => v.mkDepArrow r) res

public def BinderSyntaxView.mkFunBinder : BinderSyntaxView → FunBinder
| {ref, id, type, info, ..} => Unhygienic.run <| withRef ref do
  match info with
  | .default        => `(Term.funBinder| ($id : $type))
  | .implicit       => `(Term.funBinder| {$id : $type})
  | .strictImplicit => `(Term.funBinder| ⦃$id : $type⦄)
  | .instImplicit   => `(Term.funBinder| [$id : $type])

public def BinderSyntaxView.mkArgument : BinderSyntaxView → NamedArgument
| {ref, id, ..} => Unhygienic.run <| withRef ref `(Term.namedArgument| ($id := $id))
