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

register_builtin_option compiler.postponeCompile : Bool := {
  defValue := false
  descr := "Internal. Toggle experimental `leanir` separate compilation."
}

register_builtin_option compiler.inLeanIR : Bool := {
  defValue := false
  descr := "Internal. Indicates whether the compiler is currently running in `leanir`."
}

register_builtin_option compiler.disable : Bool := {
  defValue := false
  descr := "Disable code generation for all declarations of the module, so that none of its code \
    can be run during elaboration or by importing modules. Only has an effect when given on the \
    command line or in the module setup, in which case it cannot be reset using `set_option`."
}

private builtin_initialize disabledRef : IO.Ref Bool ← IO.mkRef false

/-- Disables code generation for the remainder of the process if `compiler.disable` is set in `opts`. -/
def disableIfRequested (opts : Options) : BaseIO Unit := do
  if compiler.disable.get opts then
    disabledRef.set true

/-- Returns whether code generation was disabled for this process using `compiler.disable`. -/
@[export lean_compiler_is_disabled]
def isDisabled : BaseIO Bool :=
  disabledRef.get

end Lean.Compiler
