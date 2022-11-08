/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Instances
import Lean.Compiler.InlineAttrs
import Lean.Compiler.Specialize
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF
namespace Simp

/--
Similar to `findFunDecl?`, but follows aliases (i.e., `let _x.i := _x.j`).
Consider the following example
```
fun _f.1 ... := ...
let _x.2 := _f.1
```
`findFunDecl? _x.2` returns `none`, but `findFunDecl'? _x.2` returns the declaration for `_f.1`.
-/
partial def findFunDecl'? (fvarId : FVarId) : CompilerM (Option FunDecl) := do
  if let some decl ← findFunDecl? fvarId then
    return decl
  else if let some (.fvar fvarId' #[]) ← findLetValue? fvarId then
    findFunDecl'? fvarId'
  else
    return none

/-
-- TODO: cleanup
partial def findExpr (e : LetValue) : CompilerM LetValue := do
  match e with
  | .fvar fvarId args =>
    if args.isEmpty then
      let some decl ← findLetDecl? fvarId | return e
      findExpr decl.value
    else
      return e
  | _ => return e
-/
end Simp
end Lean.Compiler.LCNF
