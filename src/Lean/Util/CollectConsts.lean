/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Declaration

namespace Lean.CollectConsts

structure State where
  visitedExprPtr  : HashSet USize := {}
  constSet        : HashSet Name := {}
  consts          : Array Name := #[]
  deriving Inhabited

def State.add (s : State) (declName : Name) : State :=
  if s.constSet.contains declName then
    s
  else
    { s with constSet := s.constSet.insert declName, consts := s.consts.push declName }

abbrev Visitor := State → State

mutual
  unsafe def visit (e : Expr) : Visitor := fun s =>
    let addr := ptrAddrUnsafe e
    if s.visitedExprPtr.contains addr then s
    else main e { s with visitedExprPtr := s.visitedExprPtr.insert addr }

  unsafe def main : Expr → Visitor
    | .proj _ _ e      => visit e
    | .forallE _ d b _ => visit b ∘ visit d
    | .lam _ d b _     => visit b ∘ visit d
    | .letE _ t v b _  => visit b ∘ visit v ∘ visit t
    | .app f a         => visit a ∘ visit f
    | .mdata _ b       => visit b
    | .const n _       => fun s => s.add n
    | _                => id
end

end CollectConsts

def collectConsts (s : CollectConsts.State) (e : Expr) : CollectConsts.State :=
  unsafe CollectConsts.main e s

def Declaration.collectConsts (d : Declaration) : Array Name :=
  let s := Id.run <| d.foldExprM Lean.collectConsts {}
  s.consts

end Lean
