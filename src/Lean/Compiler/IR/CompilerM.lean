/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
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
  | other => opts.getBool tracePrefixOptionName

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

@[inline] def logMessage {α : Type} [ToFormat α] (cls : Name) (a : α) : CompilerM Unit :=
  logMessageIfAux tracePrefixOptionName a

@[inline] def modifyEnv (f : Environment → Environment) : CompilerM Unit :=
  modify fun s => { s with env := f s.env }

open Std (HashMap)

abbrev DeclMap := SMap Name Decl

/- Create an array of decls to be saved on .olean file.
   `decls` may contain duplicate entries, but we assume the one that occurs last is the most recent one. -/
private def mkEntryArray (decls : List Decl) : Array Decl :=
  /- Remove duplicates by adding decls into a map -/
  let map : HashMap Name Decl := {}
  let map := decls.foldl (init := map) fun map decl => map.insert decl.name decl
  map.fold (fun a k v => a.push v) #[]

builtin_initialize declMapExt : SimplePersistentEnvExtension Decl DeclMap ←
  registerSimplePersistentEnvExtension {
    name       := `IRDecls,
    addImportedFn := fun as =>
       let m : DeclMap := mkStateFromImportedEntries (fun s (d : Decl) => s.insert d.name d) {} as
       m.switch,
    addEntryFn := fun s d => s.insert d.name d,
    toArrayFn  := mkEntryArray
  }

@[export lean_ir_find_env_decl]
def findEnvDecl (env : Environment) (n : Name) : Option Decl :=
  (declMapExt.getState env).find? n

def findDecl (n : Name) : CompilerM (Option Decl) := do
  let s ← get
  pure $ findEnvDecl s.env n

def containsDecl (n : Name) : CompilerM Bool := do
  let s ← get
  pure $ (declMapExt.getState s.env).contains n

def getDecl (n : Name) : CompilerM Decl := do
  let (some decl) ← findDecl n | throw s!"unknown declaration '{n}'"
  pure decl

@[export lean_ir_add_decl]
def addDeclAux (env : Environment) (decl : Decl) : Environment :=
  declMapExt.addEntry env decl

def getDecls (env : Environment) : List Decl :=
  declMapExt.getEntries env

def getEnv : CompilerM Environment := do
  let s ← get; pure s.env

def addDecl (decl : Decl) : CompilerM Unit :=
  modifyEnv fun env => declMapExt.addEntry env decl

def addDecls (decls : Array Decl) : CompilerM Unit :=
  decls.forM addDecl

def findEnvDecl' (env : Environment) (n : Name) (decls : Array Decl) : Option Decl :=
  match decls.find? (fun decl => decl.name == n) with
  | some decl => some decl
  | none      => (declMapExt.getState env).find? n

def findDecl' (n : Name) (decls : Array Decl) : CompilerM (Option Decl) := do
  let s ← get; pure $ findEnvDecl' s.env n decls

def containsDecl' (n : Name) (decls : Array Decl) : CompilerM Bool := do
  if decls.any fun decl => decl.name == n then
    pure true
  else
    let s ← get
    pure $ (declMapExt.getState s.env).contains n

def getDecl' (n : Name) (decls : Array Decl) : CompilerM Decl := do
  let (some decl) ← findDecl' n decls | throw s!"unknown declaration '{n}'"
  pure decl

@[export lean_decl_get_sorry_dep]
def getSorryDep (env : Environment) (declName : Name) : Option Name :=
  match (declMapExt.getState env).find? declName with
  | some (Decl.fdecl (info := { sorryDep? := dep?, .. }) ..) => dep?
  | _ => none

end IR
end Lean
