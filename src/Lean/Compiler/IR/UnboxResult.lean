/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.Format
import Lean.Compiler.IR.Basic

namespace Lean
namespace IR
namespace UnboxResult

def mkUnboxAttr : IO TagAttribute :=
registerTagAttribute `unbox "compiler tries to unbox result values if their types are tagged with `[unbox]`" $ fun declName => do
  cinfo ← Core.getConstInfo declName;
  match cinfo with
  | ConstantInfo.inductInfo v =>
    if v.isRec then Core.throwError "recursive inductive datatypes are not supported"
    else pure ()
  | _ => Core.throwError "constant must be an inductive type"

@[init mkUnboxAttr]
constant unboxAttr : TagAttribute := arbitrary _

def hasUnboxAttr (env : Environment) (n : Name) : Bool :=
unboxAttr.hasTag env n

end UnboxResult
end IR
end Lean
