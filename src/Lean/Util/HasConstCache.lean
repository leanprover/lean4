/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean

structure HasConstCache (declName : Name) where
  cache : HashMapImp Expr Bool := mkHashMapImp

unsafe def HasConstCache.containsUnsafe (e : Expr) : StateM (HasConstCache declName) Bool := do
  if let some r := (← get).cache.find? (beq := ⟨ptrEq⟩) e then
    return r
  else
    match e with
    | .const n ..        => return n == declName
    | .app f a           => cache e (← containsUnsafe f <||> containsUnsafe a)
    | .lam _ d b _       => cache e (← containsUnsafe d <||> containsUnsafe b)
    | .forallE _ d b _   => cache e (← containsUnsafe d <||> containsUnsafe b)
    | .letE _ t v b _    => cache e (← containsUnsafe t <||> containsUnsafe v <||> containsUnsafe b)
    | .mdata _ b         => cache e (← containsUnsafe b)
    | .proj _ _ b        => cache e (← containsUnsafe b)
    | _                  => return false
where
  cache (e : Expr) (r : Bool) : StateM (HasConstCache declName) Bool := do
    modify fun ⟨cache⟩ => ⟨cache.insert (beq := ⟨ptrEq⟩) e r |>.1⟩
    return r

/--
  Return true iff `e` contains the constant `declName`.
  Remark: the results for visited expressions are stored in the state cache. -/
@[implemented_by HasConstCache.containsUnsafe]
opaque HasConstCache.contains (e : Expr) : StateM (HasConstCache declName) Bool

end Lean
