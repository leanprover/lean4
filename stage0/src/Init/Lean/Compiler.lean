/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Compiler.InlineAttrs
import Init.Lean.Compiler.Specialize
import Init.Lean.Compiler.ConstFolding
import Init.Lean.Compiler.ClosedTermCache
import Init.Lean.Compiler.ExternAttr
import Init.Lean.Compiler.ImplementedByAttr
import Init.Lean.Compiler.NeverExtractAttr
import Init.Lean.Compiler.IR
