/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.Format
import Lean.Compiler.MetaAttr

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

namespace CollectUsedDecls'

abbrev M := StateM NameSet

@[inline] def collect (f : FunId) : M Unit :=
  modify fun s => s.insert f

partial def collectFnBody : FnBody → M Unit
  | .vdecl _ _ v b   =>
    match v with
    | .fap f _ => collect f *> collectFnBody b
    | .pap f _ => collect f *> collectFnBody b
    | _        => collectFnBody b
  | .jdecl _ _ v b   => collectFnBody v *> collectFnBody b
  | .case _ _ _ alts => alts.forM fun alt => collectFnBody alt.body
  | e => unless e.isTerminal do collectFnBody e.body

def collectDecl : Decl → M NameSet
  | .fdecl (body := b) .. => collectFnBody b *> get
  | .extern .. => get

end CollectUsedDecls'

def collectUsedDecls' (decl : Decl) (used : NameSet := {}) : NameSet :=
  (CollectUsedDecls'.collectDecl decl).run' used

def getMetaClosure (m : DeclMap) (decls : Array Decl) : NameSet := Id.run do
  let mut toVisit := decls.map (·.name) |>.toList
  let mut res : NameSet := .ofList toVisit
  while !toVisit.isEmpty do
    let n :: toVisit' := toVisit | continue
    toVisit := toVisit'
    let some d := m.find? n | continue
    for d' in collectUsedDecls' d do
      if !res.contains d' then
        res := res.insert d'
        toVisit := d' :: toVisit
  return res

builtin_initialize declMapExt : SimplePersistentEnvExtension Decl DeclMap ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn    := fun s d => s.insert d.name d
    exportEntriesFnEx? := some fun env s entries level => Id.run do
      let decls := entries.foldl (init := #[]) fun decls decl => decls.push decl
      let mut entries := sortDecls decls
      if level == .exported then
        let closure := getMetaClosure s (decls.filter (isMeta env ·.name))
        entries := entries.filter fun
          | d@(.fdecl f xs ty b info) =>
            let n := match f with
              | .str n "_boxed" => n
              | n => n
            closure.contains n
          | _ => true
      return entries
    -- Written to on codegen environment branch but accessed from other elaboration branches when
    -- calling into the interpreter. We cannot use `async` as the IR declarations added may not
    -- share a name prefix with the top-level Lean declaration being compiled, e.g. from
    -- specialization.
    asyncMode     := .sync
    replay?       := some <| SimplePersistentEnvExtension.replayOfFilter (!·.contains ·.name) (fun s d => s.insert d.name d)
  }

@[export lean_ir_decl_map_ext_idx]
private def getDeclMapExtIdx : Unit → Nat :=
  fun _ => declMapExt.toEnvExtension.idx

def findEnvDecl (env : Environment) (declName : Name) (level := OLeanLevel.ir) : Option Decl :=
  match env.getModuleIdxFor? declName with
  | some modIdx => findAtSorted? (declMapExt.getModuleEntries (level := level) env modIdx) declName
  | none        => declMapExt.getState env |>.find? declName

@[export lean_ir_find_env_decl]
private def findInterpreterDecl (env : Environment) (declName : Name) : Option Decl :=
  findEnvDecl env declName .exported

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
