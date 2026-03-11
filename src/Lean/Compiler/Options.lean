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

register_builtin_option compiler.traceUnnormalized : Bool := {
  defValue := false
  descr    := "don't normalize declarations before tracing them at each pipeline step (this is \
    useful for debugging purposes)"
}

register_builtin_option compiler.checkMeta : Bool := {
  defValue := true
  descr := "Check that `meta` declarations only refer to other `meta` declarations and ditto for \
    non-`meta` declarations. Disabling this option may lead to delayed compiler errors and is
    intended only for debugging purposes."
}

register_builtin_option compiler.relaxedMetaCheck : Bool := {
  defValue := false
  descr := "Allow mixed `meta`/non-`meta` references in the same module. References to imports are unaffected."
}

register_builtin_option compiler.ignoreBorrowAnnotation : Bool := {
  defValue := false
  descr := "Ignore user defined borrow inference annotations. This is useful for export/extern \
    forward declarations"
}

end Lean.Compiler
