/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Compiler.ExternAttr

public section

namespace Lean.Compiler.Bytecode

private opaque SymbolCacheImpl : NonemptyType.{0}

def SymbolCache : Type := SymbolCacheImpl.type

instance : Nonempty SymbolCache := by exact SymbolCacheImpl.property

structure Symbol where
  arity : Nat
  declName : Name

structure BytecodeDecl where
  code : ByteArray
  symbols : Array Symbol
  cache : SymbolCache
