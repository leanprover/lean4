/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.Options

namespace Lean.Compiler.LCNF

/--
User controlled configuration options for the code generator.
-/
structure ConfigOptions where
  /--
  Any function declaration or join point with size `≤ smallThresold` is inlined
  even if there are multiple occurrences.
  -/
  smallThreshold : Nat := 1
  /--
  Maximum number of times a recursive definition tagged with `[inline]` can be recursively inlined before generating an
  error during compilation.
  -/
  maxRecInline : Nat := 1
  /--
  Maximum number of times a recursive definition tagged with `[inline_if_reduce]` can be recursively inlined
  before generating an error during compilation.
  -/
  maxRecInlineIfReduce : Nat := 16
  /--
  Perform type compatibility checking after each compiler pass.
  -/
  checkTypes : Bool := false
  deriving Inhabited

register_builtin_option compiler.small : Nat := {
  defValue := 1
  group    := "compiler"
  descr    := "(compiler) function declarations with size `≤ small` is inlined even if there are multiple occurrences."
}

register_builtin_option compiler.maxRecInline : Nat := {
  defValue := 1
  group    := "compiler"
  descr    := "(compiler) maximum number of times a recursive definition tagged with `[inline]` can be recursively inlined before generating an error during compilation."
}

register_builtin_option compiler.maxRecInlineIfReduce : Nat := {
  defValue := 16
  group    := "compiler"
  descr    := "(compiler) maximum number of times a recursive definition tagged with `[inline_if_reduce]` can be recursively inlined before generating an error during compilation."
}

register_builtin_option compiler.checkTypes : Bool := {
  defValue := false
  group    := "compiler"
  descr    := "(compiler) perform type compatibility checking after each compiler pass. Note this is not a complete check, and it is used only for debugging purposes. It fails in code that makes heavy use of dependent types."
}

def toConfigOptions (opts : Options) : ConfigOptions := {
  smallThreshold := compiler.small.get opts
  maxRecInline   := compiler.maxRecInline.get opts
  maxRecInlineIfReduce := compiler.maxRecInlineIfReduce.get opts
  checkTypes := compiler.checkTypes.get opts
}

end Lean.Compiler.LCNF
