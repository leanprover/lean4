/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
import Lean.Compiler.ExportAttr
public import Lean.Compiler.LCNF.PhaseExt

public section

namespace Lean.Compiler.Bytecode

register_builtin_option interpreter.prefer_native : Bool := {
  defValue := true
}

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
  cache : DeclCache symbols
  /-- We only really care about this number for partial applications -/
  arity : Nat
  constants : Array NonScalar
  sorryDep? : Option Name := none

@[extern "lean_eval_bytecode_decl"]
unsafe axiom BytecodeDecl.eval (α) (env : @& Environment) (decl : @& BytecodeDecl) : α

@[extern "lean_bytecode_store_init_value"]
unsafe opaque BytecodeDecl.setInitValue {α} (decl : @& BytecodeDecl) (x : α) : BaseIO Unit

private abbrev declLt (a b : BytecodeDecl) :=
  Name.quickLt a.name b.name

private abbrev sortDecls (decls : Array BytecodeDecl) : Array BytecodeDecl :=
  decls.qsort declLt

builtin_initialize declMapExt :
    SimplePersistentEnvExtension BytecodeDecl (PHashMap Name BytecodeDecl) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun decls => {}
    addEntryFn    := fun s d => s.insert d.name d
    -- Store `meta` closure only in `.olean`, turn all other decls into opaque externs.
    -- Leave storing the remainder for `meta import` and server `#eval` to `exportIREntries` below.
    exportEntriesFnEx? := some fun env _ entries =>
      let decls := entries.foldl (init := #[]) fun decls decl => decls.push decl
      let entries := sortDecls decls
      .uniform entries
      /- -- Do not save all IR even in .olean.private as it will be in .ir anyway
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
      else entries -/
    -- Written to on codegen environment branch but accessed from other elaboration branches when
    -- calling into the interpreter. We cannot use `async` as the IR declarations added may not
    -- share a name prefix with the top-level Lean declaration being compiled, e.g. from
    -- specialization.
    asyncMode     := .sync
    replay?       := some <| SimplePersistentEnvExtension.replayOfFilter (!·.contains ·.name)
      (fun s d => s.insert d.name d)
  }

@[export lean_find_bytecode_decl]
partial def findBytecodeDecl (env : Environment) (nm : Name) : Option BytecodeDecl :=
  match env.getModuleIdxFor? nm with
  | none => (declMapExt.getState env).find? nm
  | some idx =>
    findIn (declMapExt.getModuleIREntries env idx) <|>
      findIn (declMapExt.getModuleEntries env idx)
where
  findIn (xs : Array BytecodeDecl) (start : Nat := 0) (stop := xs.size) : Option BytecodeDecl := do
    if stop = start then
      none
    else if stop = start + 1 then
      xs[start]?
    else
      let mid := (start + stop) / 2
      let midVal ← xs[mid]?
      match nm.quickCmp midVal.name with
      | .eq => return midVal
      | .lt => findIn xs start mid
      | .gt => findIn xs (mid + 1) stop

@[export lean_ir_decl_arity]
def declArity (env : Environment) (nm : Name) : USize :=
  (LCNF.getSigCore? env LCNF.impureSigExt nm).map (·.params.usize) |>.getD 0x1_0000_0000

@[export lean_decl_get_sorry_dep]
def getSorryDep (env : Environment) (declName : Name) : Option Name :=
  match findBytecodeDecl env declName with
  | some decl => decl.sorryDep?
  | _ => none

/-- Returns additional names that compiler env exts may want to call `getModuleIdxFor?` on. -/
@[export lean_get_ir_extra_const_names]
private def getIRExtraConstNames (env : Environment) (level : OLeanLevel) (includeDecls := false) : Array Name :=
  let env := env.setExporting (level == .exported)
  LCNF.impureSigExt.getState env |>.iter.map (·.1)
    |>.filter (fun n => (includeDecls || !env.contains n) &&
      (level == .private || Compiler.LCNF.isDeclPublic env n || isDeclMeta env n))
    |>.toArray

@[export lean_has_compile_error]
private def hasCompileError (env : Environment) (constName : Name) : Bool :=
  match env.getModuleIdxFor? constName with
  | some _ => false  -- Compile errors in imports would have stopped the build before this point
  -- TODO: do we need to store failures as a separate state? Not if we make sure to only ever
  -- evaluate constants previously called `compileDecl` on.
  | none => !(LCNF.impureSigExt.getState env |>.contains constName)
