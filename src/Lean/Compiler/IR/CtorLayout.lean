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

opaque getCtorLayout (env : @& Environment) (ctorName : @& Name) : Except String CtorLayout

end IR

-- Expose `getCtorLayout` in the `Lean` namespace to make it available for the benefit of
-- the test `lean/ctor_layout.lean`
-- Can be removed once we no longer have to limit the number of exported symbols and
-- can use `Lean.IR` from the interpreter.
@[extern "lean_ir_get_ctor_layout"]
def getCtorLayout := IR.getCtorLayout

end Lean
