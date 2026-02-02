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
  name : Name
  code : ByteArray
  stackReserved : Nat -- stackSpace + additional space for arguments
  stackSpace : Nat
  symbols : Array Symbol

structure RuntimeBytecodeDecl where
  name : Name
  code : ByteArray
  stackReserved : Nat -- stackSpace + additional space for arguments
  stackSpace : Nat
  symbols : Array Symbol
  cache : SymbolCache symbols

@[extern "lean_eval_bytecode_decl"]
unsafe opaque RuntimeBytecodeDecl.eval (α)
  (env : Environment) (decl : RuntimeBytecodeDecl) : Except String α

builtin_initialize declExt :
    SimplePersistentEnvExtension BytecodeDecl (PHashMap Name RuntimeBytecodeDecl) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn    := fun s d => s.insert d.name { d with cache := .mkEmpty _ }
    -- Store `meta` closure only in `.olean`, turn all other decls into opaque externs.
    -- Leave storing the remainder for `meta import` and server `#eval` to `exportIREntries` below.
    exportEntriesFnEx? := some fun env s entries _ =>
      let decls := entries.foldl (init := #[]) fun decls decl => decls.push decl
      let entries := decls.qsort fun a b => a.name.quickLt b.name
      entries
    -- Written to on codegen environment branch but accessed from other elaboration branches when
    -- calling into the interpreter. We cannot use `async` as the IR declarations added may not
    -- share a name prefix with the top-level Lean declaration being compiled, e.g. from
    -- specialization.
    asyncMode     := .sync
    replay?       := some <| SimplePersistentEnvExtension.replayOfFilter
      (!·.contains ·.name) (fun s d => s.insert d.name { d with cache := .mkEmpty _ })
  }

@[export lean_find_bytecode_decl]
def findBytecodeDecl (env : Environment) (nm : Name) : Option RuntimeBytecodeDecl :=
  (declExt.getState env).find? nm
