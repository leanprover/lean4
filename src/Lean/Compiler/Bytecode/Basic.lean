/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
import Lean.Compiler.ExportAttr
import Lean.Compiler.InitAttr
import all Lean.Compiler.ModPkgExt
public import Lean.Compiler.LCNF.PhaseExt

public section

namespace Lean.Compiler.Bytecode

private opaque SymbolCacheImpl (symbols : Array Name) : NonemptyType.{0}

def DeclCache (symbols : Array Name) : Type := (SymbolCacheImpl symbols).type

instance : Nonempty (DeclCache symbols) := by exact (SymbolCacheImpl symbols).property

@[extern "lean_bytecode_mk_initial_cache"]
opaque DeclCache.mkEmpty (symbols : @& Array Name) : DeclCache symbols

structure BytecodeDecl where
  name : Name
  code : ByteArray
  stackReserved : Nat -- stackSpace + additional space for arguments
  stackSpace : Nat
  symbols : Array Name
  arity : Nat
deriving Inhabited

structure RuntimeBytecodeDecl where
  name : Name
  code : ByteArray
  stackReserved : Nat -- stackSpace + additional space for arguments
  stackSpace : Nat
  symbols : Array Name
  cache : DeclCache symbols
  arity : Nat

@[extern "lean_eval_bytecode_decl"]
unsafe axiom RuntimeBytecodeDecl.eval (α) (env : @& Environment) (decl : @& RuntimeBytecodeDecl) : α

builtin_initialize declMapExt :
    SimplePersistentEnvExtension BytecodeDecl (PHashMap Name RuntimeBytecodeDecl) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun decls => decls.foldl (init := {}) fun acc arr =>
      arr.foldl (init := acc) (fun s d => s.insert d.name { d with cache := .mkEmpty _ })
    addEntryFn    := fun s d => s.insert d.name { d with cache := .mkEmpty _ }
    -- Store `meta` closure only in `.olean`, turn all other decls into opaque externs.
    -- Leave storing the remainder for `meta import` and server `#eval` to `exportIREntries` below.
    exportEntriesFnEx? := some fun env _ entries =>
      let entries := entries.toArray
      -- Do not save all IR even in .olean.private as it will be in .ir anyway
      .uniform <| if env.header.isModule then
        entries.filterMap fun d => do
          if isDeclMeta env d.name then
            return d
          guard <| Compiler.LCNF.isDeclPublic env d.name
          -- TODO: boxed `[extern]`s are created eagerly by lean but we need to see their IR in
          -- leanir. It would be nicer to make them part of standard `compileDecls` so they can be
          -- postponed like anyone else.
          if Compiler.LCNF.isBoxedName d.name && isExtern env d.name.getPrefix then
            return d
          -- Bodies of imported IR decls are not relevant for codegen, only interpretation
          none
      else entries
    -- Written to on codegen environment branch but accessed from other elaboration branches when
    -- calling into the interpreter. We cannot use `async` as the IR declarations added may not
    -- share a name prefix with the top-level Lean declaration being compiled, e.g. from
    -- specialization.
    asyncMode     := .sync
    replay?       := some <| SimplePersistentEnvExtension.replayOfFilter (!·.contains ·.name)
      (fun s d => s.insert d.name { d with cache := .mkEmpty _ })
  }

@[export lean_bytecode_export_entries]
private def exportBytecodeEntries (env : Environment) : Array (Name × Array EnvExtensionEntry) :=
  let irDecls := declMapExt.getEntries env |>.foldl (init := #[]) fun decls decl => decls.push decl
  -- safety: cast to erased type
  let irEntries : Array EnvExtensionEntry := unsafe unsafeCast <|
    irDecls.qsort fun a b : BytecodeDecl => a.name.quickLt b.name

  -- save all initializers independent of meta/private. Non-meta initializers will only be used when
  -- .ir is actually loaded, and private ones iff visible.
  let initDecls : Array (Name × Name) :=
    (regularInitAttr.ext.exportEntriesFn env (regularInitAttr.ext.getState env)).private
  -- safety: cast to erased type
  let initDecls : Array EnvExtensionEntry := unsafe unsafeCast initDecls

  -- needed during initialization via interpreter
  let modPkg : Array (Option PkgId) := (modPkgExt.exportEntriesFn env (modPkgExt.getState env)).private
  -- safety: cast to erased type
  let modPkg : Array EnvExtensionEntry := unsafe unsafeCast modPkg

  #[(declMapExt.name, irEntries),
    (Lean.regularInitAttr.ext.name, initDecls),
    (modPkgExt.name, modPkg)]

@[export lean_find_bytecode_decl]
def findBytecodeDecl (env : Environment) (nm : Name) : Option RuntimeBytecodeDecl :=
  (declMapExt.getState env).find? nm

@[export lean_ir_decl_arity]
def declArity (env : Environment) (nm : Name) : USize :=
  (LCNF.getSigCore? env LCNF.impureSigExt nm).map (·.params.usize) |>.getD 0
