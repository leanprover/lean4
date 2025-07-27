/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Util.Trace
public import Lean.Data.Options

public section

namespace Lean.Compiler

register_builtin_option compiler.check : Bool := {
  defValue := false
  group    := "compiler"
  descr    := "type check code after each compiler step (this is useful for debugging purses)"
}

end Lean.Compiler
