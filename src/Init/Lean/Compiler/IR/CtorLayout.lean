/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment
import Init.Lean.Compiler.IR.Format

namespace Lean
namespace IR

inductive CtorFieldInfo
| irrelevant
| object (i : Nat)
| usize  (i : Nat)
| scalar (sz : Nat) (offset : Nat) (type : IRType)

namespace CtorFieldInfo

def format : CtorFieldInfo → Format
| irrelevant => "◾"
| object i   => "obj@" ++ fmt i
| usize i    => "usize@" ++ fmt i
| scalar sz offset type => "scalar#" ++ fmt sz ++ "@" ++ fmt offset ++ ":" ++ fmt type

instance : HasFormat CtorFieldInfo := ⟨format⟩

end CtorFieldInfo

structure CtorLayout :=
(cidx       : Nat)
(fieldInfo  : List CtorFieldInfo)
(numObjs    : Nat)
(numUSize   : Nat)
(scalarSize : Nat)

@[extern "lean_ir_get_ctor_layout"]
constant getCtorLayout (env : @& Environment) (ctorName : @& Name) : Except String CtorLayout := arbitrary _

end IR
end Lean
