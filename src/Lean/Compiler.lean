/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.InlineAttrs
import Lean.Compiler.Specialize
import Lean.Compiler.ConstFolding
import Lean.Compiler.ClosedTermCache
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.NeverExtractAttr
import Lean.Compiler.IR
import Lean.Compiler.CSimpAttr
import Lean.Compiler.FFI
import Lean.Compiler.NoncomputableAttr
import Lean.Compiler.Main
import Lean.Compiler.AtMostOnce -- TODO: delete after we port code generator to Lean
import Lean.Compiler.Old -- TODO: delete after we port code generator to Lean
