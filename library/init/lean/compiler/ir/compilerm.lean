/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.reader
import init.lean.environment
import init.lean.compiler.ir.basic
import init.lean.compiler.ir.format

namespace Lean
namespace IR

inductive LogEntry
| step (cls : Name) (decls : Array Decl)
| message (msg : Format)

namespace LogEntry
protected def fmt : LogEntry → Format
| step cls decls => Format.bracket "[" (format cls) "]" ++ decls.foldl (fun fmt decl => fmt ++ Format.line ++ format decl) Format.nil
| message msg    => msg

instance : HasFormat LogEntry := ⟨LogEntry.fmt⟩
end LogEntry

abbrev Log := Array LogEntry

def Log.format (log : Log) : Format :=
log.foldl (fun fmt entry => fmt ++ Format.line ++ format entry) Format.nil

@[export lean_ir_log_to_string]
def Log.toString (log : Log) : String :=
log.format.pretty

structure CompilerState :=
(env : Environment) (log : Log := Array.empty)

abbrev CompilerM := ReaderT Options (EState String CompilerState)

def log (entry : LogEntry) : CompilerM Unit :=
modify $ fun s => { log := s.log.push entry, .. s }

def tracePrefixOptionName := `trace.compiler.ir

private def isLogEnabledFor (opts : Options) (optName : Name) : Bool :=
match opts.find optName with
| some (DataValue.ofBool v) => v
| other => opts.getBool tracePrefixOptionName

private def logDeclsAux (optName : Name) (cls : Name) (decls : Array Decl) : CompilerM Unit :=
do opts ← read;
   when (isLogEnabledFor opts optName) $ log (LogEntry.step cls decls)

@[inline] def logDecls (cls : Name) (decl : Array Decl) : CompilerM Unit :=
logDeclsAux (tracePrefixOptionName ++ cls) cls decl

private def logMessageIfAux {α : Type} [HasFormat α] (optName : Name) (a : α) : CompilerM Unit :=
do opts ← read;
   when (isLogEnabledFor opts optName) $ log (LogEntry.message (format a))

@[inline] def logMessageIf {α : Type} [HasFormat α] (cls : Name) (a : α) : CompilerM Unit :=
logMessageIfAux (tracePrefixOptionName ++ cls) a

@[inline] def logMessage {α : Type} [HasFormat α] (cls : Name) (a : α) : CompilerM Unit :=
logMessageIfAux tracePrefixOptionName a

@[inline] def modifyEnv (f : Environment → Environment) : CompilerM Unit :=
modify $ fun s => { env := f s.env, .. s }

abbrev DeclMap := SMap Name Decl Name.quickLt

/- Create an array of decls to be saved on .olean file.
   `decls` may contain duplicate entries, but we assume the one that occurs last is the most recent one. -/
private def mkEntryArray (decls : List Decl) : Array Decl :=
/- Remove duplicates by adding decls into a map -/
let map : HashMap Name Decl := {};
let map := decls.foldl (fun (map : HashMap Name Decl) decl => map.insert decl.name decl) map;
map.fold (fun a k v => a.push v) Array.empty

def mkDeclMapExtension : IO (SimplePersistentEnvExtension Decl DeclMap) :=
registerSimplePersistentEnvExtension {
  name       := `IRDecls,
  addImportedFn := fun as =>
     let m : DeclMap := mkStateFromImportedEntries (fun s (d : Decl) => s.insert d.name d) {} as;
     m.switch,
  addEntryFn := fun s d => s.insert d.name d,
  toArrayFn  := mkEntryArray
}

@[init mkDeclMapExtension]
constant declMapExt : SimplePersistentEnvExtension Decl DeclMap := default _

@[export lean_ir_find_env_decl]
def findEnvDecl (env : Environment) (n : Name) : Option Decl :=
(declMapExt.getState env).find n

def findDecl (n : Name) : CompilerM (Option Decl) :=
do s ← get;
   pure $ findEnvDecl s.env n

def containsDecl (n : Name) : CompilerM Bool :=
do s ← get;
   pure $ (declMapExt.getState s.env).contains n

def getDecl (n : Name) : CompilerM Decl :=
do (some decl) ← findDecl n | throw ("unknown declaration '" ++ toString n ++ "'");
   pure decl

@[export lean_ir_add_decl]
def addDeclAux (env : Environment) (decl : Decl) : Environment :=
declMapExt.addEntry env decl

def getDecls (env : Environment) : List Decl :=
declMapExt.getEntries env

def getEnv : CompilerM Environment :=
do s ← get; pure s.env

def addDecl (decl : Decl) : CompilerM Unit :=
modifyEnv (fun env => declMapExt.addEntry env decl)

def addDecls (decls : Array Decl) : CompilerM Unit :=
decls.mfor addDecl

def findEnvDecl' (env : Environment) (n : Name) (decls : Array Decl) : Option Decl :=
match decls.find (fun decl => if decl.name == n then some decl else none) with
| some decl => some decl
| none      => (declMapExt.getState env).find n

def findDecl' (n : Name) (decls : Array Decl) : CompilerM (Option Decl) :=
do s ← get; pure $ findEnvDecl' s.env n decls

def containsDecl' (n : Name) (decls : Array Decl) : CompilerM Bool :=
if decls.any (fun decl => decl.name == n) then pure true
else do
  s ← get;
  pure $ (declMapExt.getState s.env).contains n

def getDecl' (n : Name) (decls : Array Decl) : CompilerM Decl :=
do (some decl) ← findDecl' n decls | throw ("unknown declaration '" ++ toString n ++ "'");
   pure decl

end IR
end Lean
