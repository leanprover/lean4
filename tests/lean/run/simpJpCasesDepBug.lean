/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Command
import Lean.Meta.Closure
import Lean.Meta.SizeOf
import Lean.Meta.Injective
import Lean.Meta.Structure
import Lean.Meta.AppBuilder
import Lean.Elab.Command
import Lean.Elab.DeclModifiers
import Lean.Elab.DeclUtil
import Lean.Elab.Inductive
import Lean.Elab.DeclarationRange
import Lean.Elab.Binders

namespace Lean.Elab.Command
open Meta

inductive StructFieldKind where
  | newField | copiedField | fromParent | subobject
  deriving Inhabited, DecidableEq, Repr

structure StructFieldInfo where
  name     : Name
  declName : Name -- Remark: for `fromParent` fields, `declName` is only relevant in the generation of auxiliary "default value" functions.
  fvar     : Expr
  kind     : StructFieldKind
  value?   : Option Expr := none
  deriving Inhabited, Repr

private def addCtorFields (fieldInfos : Array StructFieldInfo) : Nat → Expr → TermElabM Expr
  | 0,   type => pure type
  | i+1, type => do
    let info := fieldInfos[i]!
    let decl ← Term.getFVarLocalDecl! info.fvar
    let type ← instantiateMVars type
    let type := type.abstract #[info.fvar]
    match info.kind with
    | StructFieldKind.fromParent =>
      let val := decl.value
      addCtorFields fieldInfos i (type.instantiate1 val)
    | _  =>
      addCtorFields fieldInfos i (mkForall decl.userName decl.binderInfo decl.type type)
