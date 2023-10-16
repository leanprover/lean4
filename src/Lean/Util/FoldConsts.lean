/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Environment

namespace Lean
namespace Expr
namespace FoldConstsImpl

abbrev cacheSize : USize := 8192 - 1

structure State where
  visitedTerms  : Array Expr  -- Remark: cache based on pointer address. Our "unsafe" implementation relies on the fact that `()` is not a valid Expr
  visitedConsts : NameHashSet -- cache based on structural equality

abbrev FoldM := StateM State

unsafe def visited (e : Expr) (size : USize) : FoldM Bool := do
  let s ← get
  let h := ptrAddrUnsafe e
  let i := h % size
  let k := s.visitedTerms.uget i lcProof
  if ptrAddrUnsafe k == h then pure true
  else do
    modify fun s => { s with visitedTerms := s.visitedTerms.uset i e lcProof }
    pure false

unsafe def fold {α : Type} (f : Name → α → α) (size : USize) (e : Expr) (acc : α) : FoldM α :=
  let rec visit (e : Expr) (acc : α) : FoldM α := do
    if (← visited e size) then
      pure acc
    else
      match e with
      | Expr.forallE _ d b _   => visit b (← visit d acc)
      | Expr.lam _ d b _       => visit b (← visit d acc)
      | Expr.mdata _ b         => visit b acc
      | Expr.letE _ t v b _    => visit b (← visit v (← visit t acc))
      | Expr.app f a           => visit a (← visit f acc)
      | Expr.proj _ _ b        => visit b acc
      | Expr.const c _         =>
        let s ← get
        if s.visitedConsts.contains c then
          pure acc
        else do
          modify fun s => { s with visitedConsts := s.visitedConsts.insert c };
          pure $ f c acc
      | _                      => pure acc
  visit e acc

unsafe def initCache : State :=
  { visitedTerms  := mkArray cacheSize.toNat (cast lcProof ()),
    visitedConsts := {} }

@[inline] unsafe def foldUnsafe {α : Type} (e : Expr) (init : α) (f : Name → α → α) : α :=
  (fold f cacheSize e init).run' initCache

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
