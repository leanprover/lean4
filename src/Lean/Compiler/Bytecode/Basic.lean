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

structure Symbol where
  arity : Nat
  declName : Name

private opaque SymbolCacheImpl (symbols : Array Symbol) : NonemptyType.{0}

def SymbolCache (symbols : Array Symbol) : Type := (SymbolCacheImpl symbols).type

instance : Nonempty (SymbolCache symbols) := by exact (SymbolCacheImpl symbols).property

@[extern "lean_bytecode_mk_initial_cache"]
opaque SymbolCache.mkEmpty (symbols : @& Array Symbol) : SymbolCache symbols

structure BytecodeDecl where
  code : ByteArray
  symbols : Array Name

structure RuntimeBytecodeDecl where
  code : ByteArray
  symbols : Array Symbol
  cache : SymbolCache symbols
  value : NonScalar
