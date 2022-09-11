/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.Types

namespace Lean.Compiler.LCNF

private abbrev Visitor := NameMap (Array Bool) → NameMap (Array Bool)

private partial def updateMap (decls : Array Decl) (code : Code) : Visitor :=
  go code
where
  goLetDecl (letDecl : LetDecl) : Visitor := fun s => Id.run do
    let .const declName _ := letDecl.value.getAppFn | return s
    let some mask := s.find? declName | return s
    for decl in decls do
      if decl.name == declName then
        -- Recall that mask.size == decl.params.size
        let mut mask := mask
        let args := letDecl.value.getAppArgs
        let sz := Nat.min args.size decl.params.size
        for i in [:sz] do
          let arg := args[i]!
          let param := decl.params[i]!
          unless arg.isFVarOf param.fvarId || (arg.isErased && param.type.isErased) do
            mask := mask.set! i false
        -- If the declaration is partially applied, we assume the missing arguments are not fixed
        for i in [args.size:decl.params.size] do
          mask := mask.set! i false
        return s.insert decl.name mask
    return s

  go (code : Code) : Visitor :=
    match code with
    | .let decl k => go k ∘ goLetDecl decl
    | .fun decl k | .jp decl k => go k ∘ go decl.value
    | .cases c => fun s => c.alts.foldl (init := s) fun s alt => go alt.getCode s
    | .unreach .. | .jmp .. | .return .. => id

/--
Given the (potentially mutually) recursive declarations `decls`,
return a map from declaration name `decl.name` to a bit-mask `m` where `m[i]` is true
iff the `decl.params[i]` is a fixed argument. That is, it does not change in recursive
applications.
The function assumes that if a function `f` was declared in a mutual block, then `decls`
contains all (computationally relevant) functions in the mutual block.
-/
def mkFixedArgMap (decls : Array Decl) : NameMap (Array Bool) := Id.run do
  let mut m := {}
  for decl in decls do
    m := m.insert decl.name (mkArray decl.params.size true)
  for decl in decls do
    m := updateMap decls decl.value m
  return m

end Lean.Compiler.LCNF
