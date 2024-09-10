/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Util.PtrSet

namespace Lean.Expr
namespace NumObjs

unsafe structure State where
 visited : PtrSet Expr := mkPtrSet
 counter : Nat := 0

unsafe abbrev M := StateM State

unsafe def visit (e : Expr) : M Unit :=
  unless (← get).visited.contains e do
    modify fun { visited, counter } => { visited := visited.insert e, counter := counter + 1 }
    match e with
      | .forallE _ d b _ => visit d; visit b
      | .lam _ d b _     => visit d; visit b
      | .mdata _ b       => visit b
      | .letE _ t v b _  => visit t; visit v; visit b
      | .app f a         => visit f; visit a
      | .proj _ _ b      => visit b
      | _                => return ()

unsafe def main (e : Expr) : Nat :=
  let (_, s) := NumObjs.visit e |>.run {}
  s.counter

end NumObjs

/--
Returns the number of allocated `Expr` objects in the given expression `e`.

This operation is performed in `IO` because the result depends on the memory representation of the object.

Note: Use this function primarily for diagnosing performance issues.
-/
def numObjs (e : Expr) : IO Nat :=
  return unsafe NumObjs.main e

end Lean.Expr
