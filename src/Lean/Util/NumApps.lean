/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Util.PtrSet

namespace Lean.Expr
namespace NumApps

unsafe structure State where
 visited  : PtrSet Expr := mkPtrSet
 counters : NameMap Nat := {}

unsafe abbrev M := StateM State

unsafe def visit (e : Expr) : M Unit :=
  unless (← get).visited.contains e do
    modify fun s => { s with visited := s.visited.insert e }
    match e with
      | .forallE _ d b _ => visit d; visit b
      | .lam _ d b _     => visit d; visit b
      | .mdata _ b       => visit b
      | .letE _ t v b _  => visit t; visit v; visit b
      | .app ..          => e.withApp fun f args => do
        if let .const declName _ := f then
          let c := (← get).counters.find? declName |>.getD 0
          modify fun s => { s with counters := s.counters.insert declName (c+1) }
        visit f
        args.forM visit
      | .proj _ _ b      => visit b
      | _                => return ()

unsafe def main (e : Expr) : NameMap Nat :=
  let (_, s) := NumApps.visit e |>.run {}
  s.counters

end NumApps

/--
Returns the number of applications for each declaration used in `e`.

This operation is performed in `IO` because the result depends on the memory representation of the object.

Note: Use this function primarily for diagnosing performance issues.
-/
def numApps (e : Expr) (threshold : Nat := 0) : IO (Array (Name × Nat)) := do
  let counters := unsafe NumApps.main e
  let mut result := #[]
  for (declName, num) in counters do
    if num > threshold then
      result := result.push (declName, num)
  return result.qsort fun a b => a.2 > b.2

end Lean.Expr
