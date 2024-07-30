/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Environment

namespace Lean
namespace Expr
namespace FoldConstsImpl

unsafe structure State where
 visited       : PtrSet Expr := mkPtrSet
 visitedConsts : NameHashSet := {}

unsafe abbrev FoldM := StateM State

unsafe def fold {α : Type} (f : Name → α → α) (e : Expr) (acc : α) : FoldM α :=
  let rec visit (e : Expr) (acc : α) : FoldM α := do
    if (← get).visited.contains e then
      return acc
    modify fun s => { s with visited := s.visited.insert e }
    match e with
    | .forallE _ d b _   => visit b (← visit d acc)
    | .lam _ d b _       => visit b (← visit d acc)
    | .mdata _ b         => visit b acc
    | .letE _ t v b _    => visit b (← visit v (← visit t acc))
    | .app f a           => visit a (← visit f acc)
    | .proj _ _ b        => visit b acc
    | .const c _         =>
      if (← get).visitedConsts.contains c then
        return acc
      else
        modify fun s => { s with visitedConsts := s.visitedConsts.insert c };
        return f c acc
    | _ => return acc
  visit e acc

@[inline] unsafe def foldUnsafe {α : Type} (e : Expr) (init : α) (f : Name → α → α) : α :=
  (fold f e init).run' {}

end FoldConstsImpl

/-- Apply `f` to every constant occurring in `e` once. -/
@[implemented_by FoldConstsImpl.foldUnsafe]
opaque foldConsts {α : Type} (e : Expr) (init : α) (f : Name → α → α) : α := init

def getUsedConstants (e : Expr) : Array Name :=
  e.foldConsts #[] fun c cs => cs.push c

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def getUsedConstantsAsSet (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

end Expr

namespace ConstantInfo

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def getUsedConstantsAsSet (c : ConstantInfo) : NameSet :=
  c.type.getUsedConstantsAsSet ++ match c.value? with
  | some v => v.getUsedConstantsAsSet
  | none => match c with
    | .inductInfo val => .ofList val.ctors
    | .opaqueInfo val => val.value.getUsedConstantsAsSet
    | .ctorInfo val => ({} : NameSet).insert val.name
    | .recInfo val => .ofList val.all
    | _ => {}

end ConstantInfo

def getMaxHeight (env : Environment) (e : Expr) : UInt32 :=
  e.foldConsts 0 fun constName max =>
    match env.find? constName with
    | ConstantInfo.defnInfo val =>
      match val.hints with
      | ReducibilityHints.regular h => if h > max then h else max
      | _                           => max
    | _ => max

end Lean
