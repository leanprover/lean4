/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.Format
import Lean.Compiler.IR.Basic

namespace Lean.IR.UnboxResult

/--
Tags types that the compiler should unbox if they occur in result values.

This attribute currently has no effect.
-/
@[builtin_doc]
builtin_initialize unboxAttr : TagAttribute ←
  registerTagAttribute `unbox "compiler tries to unbox result values if their types are tagged with `[unbox]`" fun declName => do
    let cinfo ← getConstInfo declName;
    match cinfo with
    | ConstantInfo.inductInfo v =>
      if v.isRec then throwError "recursive inductive datatypes are not supported"
      else pure ()
    | _ => throwError "constant must be an inductive type"

def hasUnboxAttr (env : Environment) (n : Name) : Bool :=
  unboxAttr.hasTag env n

end Lean.IR.UnboxResult
