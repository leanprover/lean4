/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment
import Lean.Compiler.IR.Format

namespace Lean
namespace IR

inductive CtorFieldInfo where
  | irrelevant
  | object (i : Nat)
  | usize  (i : Nat)
  | scalar (sz : Nat) (offset : Nat) (type : IRType)
  deriving Inhabited

namespace CtorFieldInfo

def format : CtorFieldInfo → Format
  | irrelevant => "◾"
  | object i   => f!"obj@{i}"
  | usize i    => f!"usize@{i}"
  | scalar sz offset type => f!"scalar#{sz}@{offset}:{type}"

instance : ToFormat CtorFieldInfo := ⟨format⟩

end CtorFieldInfo

structure CtorLayout where
  cidx       : Nat
  fieldInfo  : List CtorFieldInfo
  numObjs    : Nat
  numUSize   : Nat
  scalarSize : Nat

@[extern "lean_ir_get_ctor_layout"]
opaque getCtorLayout (env : @& Environment) (ctorName : @& Name) : Except String CtorLayout

end IR
end Lean
