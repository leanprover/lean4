/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Meta.Tactic.Cases

/-!
This module contains the implementation of the pre processing pass for automatically splitting up
structures containing information about supported types into individual parts recursively.

The implementation runs cases recursively on all "interesting" types where a type is interesting if
it is a non recursive structure and at least one of the following conditions hold:
- it contains something of type `BitVec`/`UIntX`/`Bool`
- it is parametrized by an interesting type
- it contains another interesting type
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

/--
Contains a cache for interesting and uninteresting types such that we don't duplicate work in the
structures pass.
-/
structure InterestingStructures where
  interesting : Std.HashMap Name Bool := {}

private abbrev M := StateRefT InterestingStructures MetaM

namespace M

@[inline]
def lookup (n : Name) : M (Option Bool) := do
  let s ← get
  return s.interesting.get? n

@[inline]
def markInteresting (n : Name) : M Unit := do
  modify (fun s => {s with interesting := s.interesting.insert n true})

@[inline]
def markUninteresting (n : Name) : M Unit := do
  modify (fun s => {s with interesting := s.interesting.insert n false})

end M

partial def structuresPass : Pass where
  name := `structures
  run' goal := do
    let (_, { interesting, .. }) ← checkContext goal |>.run {}

    let goals ← goal.casesRec fun decl => do
      if decl.isLet || decl.isImplementationDetail then
        return false
      else
        let some const := decl.type.getAppFn.constName? | return false
        return interesting.getD const false
    match goals with
    | [goal] => return goal
    | _ => throwError "structures preprocessor generated more than 1 goal"
where
  checkContext (goal : MVarId) : M Unit := do
    goal.withContext do
      for decl in ← getLCtx do
        if !decl.isLet && !decl.isImplementationDetail then
          discard <| typeRelevant decl.type

  constInterestingCached (n : Name) : M Bool := do
    if let some cached ← M.lookup n then
      return cached

    let interesting ← constInteresting n
    if interesting then
      M.markInteresting n
      return true
    else
      M.markUninteresting n
      return false

  constInteresting (n : Name) : M Bool := do
    let env ← getEnv
    if !isStructure env n then
      return false
    let constInfo := (← getConstInfoInduct n)
    if constInfo.isRec then
      return false

    let ctorTyp := (← getConstInfoCtor constInfo.ctors.head!).type
    let analyzer state arg := do
      return state || (← typeRelevant (← arg.fvarId!.getType))
    forallTelescope ctorTyp (fun args _ => args.foldlM (init := false) analyzer)

  typeRelevant (expr : Expr) : M Bool := do
    match_expr expr with
    | BitVec n => return (← getNatValue? n).isSome
    | UInt8 => return true
    | UInt16 => return true
    | UInt32 => return true
    | UInt64 => return true
    | USize => return true
    | Bool => return true
    | _ =>
      let some const := expr.getAppFn.constName? | return false
      constInterestingCached const


end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
