/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.FunIndInfo

/-!
This module is very similar to Lean.Meta.Tactic.Try.Collect, and maybe some common aspects
ough to be abstracted.
-/

namespace Lean.Meta.FunInd

namespace Collector

structure FunIndCandidate where
  expr : Expr
  deriving Hashable, BEq

/-- `Set` with insertion order preserved. -/
structure OrdSet (α : Type) [Hashable α] [BEq α] where
  elems : Array α := #[]
  set : Std.HashSet α := {}
  deriving Inhabited

def OrdSet.insert {_ : Hashable α} {_ : BEq α} (s : OrdSet α) (a : α) : OrdSet α :=
  if s.set.contains a then
    s
  else
    let { elems, set } := s
    { elems := elems.push a, set := set.insert a }

def OrdSet.isEmpty {_ : Hashable α} {_ : BEq α} (s : OrdSet α) : Bool :=
  s.elems.isEmpty

structure Result where
  /-- Function induction candidates. -/
  funIndCandidates : OrdSet FunIndCandidate := {}

abbrev M := StateRefT Result MetaM

def saveFunInd (e : Expr) (declName : Name) (args : Array Expr) : M Unit := do
  let some funIndInfo ← getFunIndInfo? (cases := false) declName | return
  if funIndInfo.params.size != args.size then return ()
  for arg in args, kind in funIndInfo.params do
    if kind matches .target then
      if !arg.isFVar then return
  modify fun s => { s with funIndCandidates := s.funIndCandidates.insert { expr := e } }

def visitApp (e : Expr) (declName : Name) (args : Array Expr) : M Unit := do
  saveFunInd e declName args

unsafe abbrev Cache := PtrSet Expr

unsafe def visit (e : Expr) : StateRefT Cache M Unit := do
  unless (← get).contains e do
    modify fun s => s.insert e
    match e with
      | .const _ _        => pure ()
      | .forallE _ d b _  => visit d; visit b
      | .lam _ d b _      => visit d; visit b
      | .mdata _ b        => visit b
      | .letE _ t v b _   => visit t; visit v; visit b
      | .app ..           => e.withApp fun f args => do
        if let .const declName _ := f then
          unless e.hasLooseBVars do
            visitApp e declName args
        else
          visit f
        args.forM visit
      | .proj _ _ b       => visit b
      | _                 => return ()

unsafe def main (mvarId : MVarId) : MetaM Result := mvarId.withContext do
  let (_, s) ← go |>.run mkPtrSet |>.run {}
  return s
where
  go : StateRefT Cache M Unit := do
    for localDecl in (← getLCtx) do
      unless localDecl.isAuxDecl do
        if let some val := localDecl.value? then
          visit val
        else
          visit localDecl.type
    visit (← mvarId.getType)

end Collector

def collect (mvarId : MVarId) : MetaM Collector.Result := do
  unsafe Collector.main mvarId

end Lean.Meta.FunInd
