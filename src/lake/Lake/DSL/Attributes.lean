/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.DSL.AttributesCore

open Lean

namespace Lake

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `test_runner
    descr           := testDriverAttr.attr.descr
    add             := fun decl stx attrKind => do
      logWarningAt stx "@[test_runner] has been deprecated, use @[test_driver] instead"
      testDriverAttr.attr.add decl stx attrKind
    applicationTime := testDriverAttr.attr.applicationTime
    erase           := fun decl => testDriverAttr.attr.erase decl
 }
