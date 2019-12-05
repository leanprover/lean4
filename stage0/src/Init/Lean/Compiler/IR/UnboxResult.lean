/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Data.Format
import Init.Lean.Compiler.IR.Basic
import Init.Lean.Compiler.IR.CtorLayout

namespace Lean
namespace IR
namespace UnboxResult

def mkUnboxAttr : IO TagAttribute :=
registerTagAttribute `unbox "compiler tries to unbox result values if their types are tagged with `[unbox]`" $ fun env declName =>
  match env.find declName with
  | none => Except.error "unknown declaration"
  | some cinfo => match cinfo with
    | ConstantInfo.inductInfo v =>
      if v.isRec then Except.error "recursive inductive datatypes are not supported"
      else Except.ok ()
    | _ => Except.error "constant must be an inductive type"

@[init mkUnboxAttr]
constant unboxAttr : TagAttribute := arbitrary _

def hasUnboxAttr (env : Environment) (n : Name) : Bool :=
unboxAttr.hasTag env n

end UnboxResult
end IR
end Lean
