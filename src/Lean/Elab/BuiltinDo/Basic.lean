/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

def elabDoIdDecl (x : Ident) (xType? : Option Term) (rhs : TSyntax `doElem) (contRef : Syntax) (k : DoElabM Expr)
    (kind : DoElemContKind := .nonDuplicable) (declKind : LocalDeclKind := .default) : DoElabM Expr := do
  let xType ← Term.elabType (xType?.getD (mkHole x))
  let lctx ← getLCtx
  let ctx ← read
  elabDoElem rhs <| .mk (kind := kind) (declKind := declKind) (ref := contRef) x.getId xType do
    withLCtxKeepingMutVarDefs lctx ctx x.getId do
      Term.addLocalVarInfo x (← getFVarFromUserName x.getId)
      k
