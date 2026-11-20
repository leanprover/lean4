import Lean

/-!
Tests the `LocalContext` iterators `iter`, `iterFromIdx` and `revIter`, which skip the holes left
by erased declarations.
-/

open Lean Meta

def names (it : List LocalDecl) : List Name := it.map (·.userName)

/--
info: [a, b, c, d]
---
info: [c, d]
---
info: [d, c, b, a]
---
info: [a, c, d]
---
info: [d, c, a]
-/
#guard_msgs in
#eval show MetaM Unit from do
  withLocalDeclD `a (mkConst ``Nat) fun a =>
  withLocalDeclD `b (mkConst ``Nat) fun b =>
  withLocalDeclD `c (mkConst ``Nat) fun _ =>
  withLocalDeclD `d (mkConst ``Nat) fun _ => do
    let lctx ← getLCtx
    logInfo m!"{names lctx.iter.toList}"
    let some decl := lctx.find? a.fvarId! | unreachable!
    logInfo m!"{names (lctx.iterFromIdx (decl.index + 2)).toList}"
    logInfo m!"{names lctx.revIter.toList}"
    let lctx := lctx.erase b.fvarId!
    logInfo m!"{names lctx.iter.toList}"
    logInfo m!"{names lctx.revIter.toList}"
