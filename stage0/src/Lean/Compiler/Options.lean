/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.Trace
import Lean.Data.Options

namespace Lean.Compiler

register_builtin_option compiler.check : Bool := {
  defValue := true
  group    := "compiler"
  descr    := "type check code after each compiler step (this is useful for debugging purses)"
}

end Lean.Compiler
