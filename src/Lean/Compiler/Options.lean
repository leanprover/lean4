/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Util.Trace

public section

namespace Lean.Compiler

register_builtin_option compiler.check : Bool := {
  defValue := false
  descr    := "type check code after each compiler step (this is useful for debugging purses)"
}

register_builtin_option compiler.checkMeta : Bool := {
  defValue := true
  descr := "Check that `meta` declarations only refer to other `meta` declarations and ditto for \
    non-`meta` declarations. Disabling this option may lead to delayed compiler errors and is
    intended only for debugging purposes."
}

end Lean.Compiler
