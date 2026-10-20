/-
Copyright (c) 2026 Moritz Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Roos
-/
module

prelude
public import Lean.Meta.Basic

public section

namespace Lean

/--
Pretty-prints a local declaration and its type as a binder,
using the appropriate brackets given its `BinderInfo`. Example output: `{α : Type}`.

Returns `none` for let decls.
-/
protected def LocalDecl.ppAsBinder : LocalDecl → Option MessageData
  | .ldecl .. => none
  | .cdecl _ fvarId _ type binderInfo _ =>
    let (lBracket, rBracket) : String × String := match binderInfo with
      | .implicit       => ("{", "}")
      | .strictImplicit => ("⦃", "⦄")
      | .instImplicit   => ("[", "]")
      | .default        => ("(", ")")
    some <| .bracket lBracket m!"{mkFVar fvarId} : {type}" rBracket

/--
Pretty-prints a free variable and its type as a binder,
using the appropriate brackets given its `BinderInfo`. Example output: `{α : Type}`.

Returns `none` for let decls.
-/
@[inline]
protected def FVarId.ppAsBinder (fvarId : FVarId) : MetaM (Option MessageData) :=
  return (← fvarId.getDecl).ppAsBinder

end Lean
