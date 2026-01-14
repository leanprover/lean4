/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Util.ReplaceExpr

public section

namespace Lean.Meta

/-- A mapping from MVarId to MVarId -/
structure MVarRenaming where
  map : MVarIdMap MVarId := {}

def MVarRenaming.isEmpty (s : MVarRenaming) : Bool :=
  s.map.isEmpty

def MVarRenaming.find? (s : MVarRenaming) (mvarId : MVarId) : Option MVarId :=
  s.map.get? mvarId

def MVarRenaming.find! (s : MVarRenaming) (mvarId : MVarId) : MVarId :=
  (s.find? mvarId).get!

def MVarRenaming.insert (s : MVarRenaming) (mvarId mvarId' : MVarId) : MVarRenaming :=
  { s with map := s.map.insert mvarId mvarId' }

def MVarRenaming.apply (s : MVarRenaming) (e : Expr) : Expr :=
  if !e.hasMVar then e
  else if s.map.isEmpty then e
  else e.replace fun e => match e with
    | Expr.mvar mvarId => match s.map.get? mvarId with
      | none           => e
      | some newMVarId => mkMVar newMVarId
    | _ => none

end Lean.Meta
