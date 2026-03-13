/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF

builtin_initialize
  Lean.registerTraceClass `Compiler
  Lean.registerTraceClass `Compiler.stat
