/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.InferType

namespace Lean.Compiler.LCNF

/--
Return code that is equivalent to `c >>= f`. That is, executes `c`, and then `f x`, where
`x` is a variable that contains the result of `c`'s computation.

If `c` contains a jump to a join point `jp_i` not declared in `c`, we throw an exception because
an invalid block would be generated. It would be invalid because `f` would not
be applied to `jp_i`. Note that, we could have decided to create a copy of `jp_i` where we apply `f` to it,
by we decided to not do it to avoid code duplication.
-/
partial def Code.bind (c : Code) (f : FVarId → CompilerM Code) : CompilerM Code := do
  go c |>.run {}
where
  go (c : Code) : ReaderT FVarIdSet CompilerM Code := do
    match c with
    | .let decl k => return .let decl (← go k)
    | .fun decl k => return .fun decl (← go k)
    | .jp decl k =>
      let value ← go decl.value
      let type ← value.inferParamType decl.params
      let decl := { decl with value, type }
      withReader (fun s => s.insert decl.fvarId) do
        return .jp decl (← go k)
    | .cases c =>
      let alts ← c.alts.mapM fun
        | .alt ctorName params k => return .alt ctorName params (← go k)
        | .default k => return .default (← go k)
      if alts.isEmpty then
        throwError "`Code.bind` failed, empty `cases` found"
      let mut resultType ← alts[0]!.inferType
      for alt in alts[1:] do
        resultType := joinTypes resultType (← alt.inferType)
      return .cases { c with alts, resultType }
    | .return fvarId => f fvarId
    | .jmp fvarId .. =>
      unless (← read).contains fvarId do
        throwError "`Code.bind` failed, it contains a out of scope join point"
      return c
    | .unreach .. => return c

end Lean.Compiler.LCNF