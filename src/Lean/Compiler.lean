/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.InlineAttrs
public import Lean.Compiler.Specialize
public import Lean.Compiler.ClosedTermCache
public import Lean.Compiler.ExternAttr
public import Lean.Compiler.ImplementedByAttr
public import Lean.Compiler.NeverExtractAttr
public import Lean.Compiler.IR
public import Lean.Compiler.CSimpAttr
public import Lean.Compiler.FFI
public import Lean.Compiler.MetaAttr
public import Lean.Compiler.NoncomputableAttr
public import Lean.Compiler.Main
public import Lean.Compiler.NameDemangling
public import Lean.Compiler.Old -- TODO: delete after we port code generator to Lean
