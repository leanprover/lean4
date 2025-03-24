/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.Format

namespace Lean.IR

inductive LogEntry where
  | step (cls : Name) (decls : Array Decl)
  | message (msg : Format)

namespace LogEntry
protected def fmt : LogEntry → Format
  | step cls decls => Format.bracket "[" (format cls) "]" ++ decls.foldl (fun fmt decl => fmt ++ Format.line ++ format decl) Format.nil
  | message msg    => msg

instance : ToFormat LogEntry := ⟨LogEntry.fmt⟩
end LogEntry

abbrev Log := Array LogEntry

def Log.format (log : Log) : Format :=
  log.foldl (init := Format.nil) fun fmt entry =>
    f!"{fmt}{Format.line}{entry}"

@[export lean_ir_log_to_string]
def Log.toString (log : Log) : String :=
  log.format.pretty

structure CompilerState where
  env : Environment
  log : Log := #[]

abbrev CompilerM := ReaderT Options (EStateM String CompilerState)

def log (entry : LogEntry) : CompilerM Unit :=
  modify fun s => { s with log := s.log.push entry }

def tracePrefixOptionName := `trace.compiler.ir

private def isLogEnabledFor (opts : Options) (optName : Name) : Bool :=
  match opts.find optName with
  | some (DataValue.ofBool v) => v
  | _     => opts.getBool tracePrefixOptionName

private def logDeclsAux (optName : Name) (cls : Name) (decls : Array Decl) : CompilerM Unit := do
  let opts ← read
  if isLogEnabledFor opts optName then
    log (LogEntry.step cls decls)

@[inline] def logDecls (cls : Name) (decl : Array Decl) : CompilerM Unit :=
  logDeclsAux (tracePrefixOptionName ++ cls) cls decl

private def logMessageIfAux {α : Type} [ToFormat α] (optName : Name) (a : α) : CompilerM Unit := do
  let opts ← read
  if isLogEnabledFor opts optName then
    log (LogEntry.message (format a))

@[inline] def logMessageIf {α : Type} [ToFormat α] (cls : Name) (a : α) : CompilerM Unit :=
  logMessageIfAux (tracePrefixOptionName ++ cls) a

@[inline] def logMessage {α : Type} [ToFormat α] (a : α) : CompilerM Unit :=
  logMessageIfAux tracePrefixOptionName a

@[inline] def modifyEnv (f : Environment → Environment) : CompilerM Unit :=
  modify fun s => { s with env := f s.env }

abbrev DeclMap := PHashMap Name Decl

private abbrev declLt (a b : Decl) :=
  Name.quickLt a.name b.name

private abbrev sortDecls (decls : Array Decl) : Array Decl :=
  decls.qsort declLt

private abbrev findAtSorted? (decls : Array Decl) (declName : Name) : Option Decl :=
  let tmpDecl := Decl.extern declName #[] default default
  decls.binSearch tmpDecl declLt

builtin_initialize declMapExt : SimplePersistentEnvExtension Decl DeclMap ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn    := fun s d => s.insert d.name d
    toArrayFn     := fun s =>
      let decls := s.foldl (init := #[]) fun decls decl => decls.push decl
      sortDecls decls
    -- Written to on codegen environment branch but accessed from other elaboration branches when
    -- calling into the interpreter. We cannot use `async` as the IR declarations added may not
    -- share a name prefix with the top-level Lean declaration being compiled, e.g. from
    -- specialization.
    asyncMode     := .sync
    replay?       := some <| SimplePersistentEnvExtension.replayOfFilter (!·.contains ·.name) (fun s d => s.insert d.name d)
  }

@[export lean_ir_find_env_decl]
def findEnvDecl (env : Environment) (declName : Name) : Option Decl :=
  match env.getModuleIdxFor? declName with
  | some modIdx => findAtSorted? (declMapExt.getModuleEntries env modIdx) declName
  | none        => declMapExt.getState env |>.find? declName

def findDecl (n : Name) : CompilerM (Option Decl) :=
  return findEnvDecl (← get).env n

def containsDecl (n : Name) : CompilerM Bool :=
  return (← findDecl n).isSome

def getDecl (n : Name) : CompilerM Decl := do
  let (some decl) ← findDecl n | throw s!"unknown declaration '{n}'"
  return decl

@[export lean_ir_add_decl]
def addDeclAux (env : Environment) (decl : Decl) : Environment :=
  declMapExt.addEntry (env.addExtraName decl.name) decl

def getDecls (env : Environment) : List Decl :=
  declMapExt.getEntries env

def getEnv : CompilerM Environment := do
  let s ← get; pure s.env

def addDecl (decl : Decl) : CompilerM Unit :=
  modifyEnv fun env => declMapExt.addEntry (env.addExtraName decl.name) decl

def addDecls (decls : Array Decl) : CompilerM Unit :=
  decls.forM addDecl

def findEnvDecl' (env : Environment) (n : Name) (decls : Array Decl) : Option Decl :=
  match decls.find? (fun decl => decl.name == n) with
  | some decl => some decl
  | none      => findEnvDecl env n

def findDecl' (n : Name) (decls : Array Decl) : CompilerM (Option Decl) :=
  return findEnvDecl' (← get).env n decls

def containsDecl' (n : Name) (decls : Array Decl) : CompilerM Bool := do
  if decls.any fun decl => decl.name == n then
    return true
  else
    containsDecl n

def getDecl' (n : Name) (decls : Array Decl) : CompilerM Decl := do
  let (some decl) ← findDecl' n decls | throw s!"unknown declaration '{n}'"
  return decl

@[export lean_decl_get_sorry_dep]
def getSorryDep (env : Environment) (declName : Name) : Option Name :=
  match findEnvDecl env declName with
  | some (.fdecl (info := { sorryDep? := dep?, .. }) ..) => dep?
  | _ => none

end IR
end Lean
