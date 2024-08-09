/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Std.Data.HashMap.Raw

namespace Lean

structure HasConstCache (declNames : Array Name) where
  cache : Std.HashMap.Raw Expr Bool := Std.HashMap.Raw.empty

unsafe def HasConstCache.containsUnsafe (e : Expr) : StateM (HasConstCache declNames) Bool := do
  if let some r := (← get).cache.get? (beq := ⟨ptrEq⟩) e then
    return r
  else
    match e with
    | .const n ..        => return declNames.contains n
    | .app f a           => cache e (← containsUnsafe f <||> containsUnsafe a)
    | .lam _ d b _       => cache e (← containsUnsafe d <||> containsUnsafe b)
    | .forallE _ d b _   => cache e (← containsUnsafe d <||> containsUnsafe b)
    | .letE _ t v b _    => cache e (← containsUnsafe t <||> containsUnsafe v <||> containsUnsafe b)
    | .mdata _ b         => cache e (← containsUnsafe b)
    | .proj _ _ b        => cache e (← containsUnsafe b)
    | _                  => return false
where
  cache (e : Expr) (r : Bool) : StateM (HasConstCache declNames) Bool := do
    modify fun ⟨cache⟩ => ⟨cache.insert (beq := ⟨ptrEq⟩) e r⟩
    return r

/--
  Return true iff `e` contains the constant `declName`.
  Remark: the results for visited expressions are stored in the state cache. -/
@[implemented_by HasConstCache.containsUnsafe]
opaque HasConstCache.contains (e : Expr) : StateM (HasConstCache declNames) Bool

end Lean
