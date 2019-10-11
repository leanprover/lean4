/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment
import Init.Lean.Compiler.IR.Basic

namespace Lean
namespace IR

inductive CtorFieldInfo
| irrelevant
| object (i : Nat)
| usize  (i : Nat)
| scalar (sz : Nat) (offset : Nat) (type : IRType)

structure CtorLayout :=
(cidx       : Nat)
(fieldInfo  : List CtorFieldInfo)
(numObjs    : Nat)
(numUSize   : Nat)
(scalarSize : Nat)

@[extern "lean_ir_get_ctor_layout"]
constant getCtorLayout (env : Environment) (ctorName : Name) : Except String CtorLayout := default _

end IR
end Lean
