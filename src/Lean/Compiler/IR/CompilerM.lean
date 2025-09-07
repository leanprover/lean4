/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.CoreM
public import Lean.Environment
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.IR.Format
public import Lean.Compiler.MetaAttr
public import Lean.Compiler.ExportAttr
public import Lean.Compiler.LCNF.PhaseExt

public section

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

def Log.toString (log : Log) : String :=
  log.format.pretty

abbrev CompilerM := CoreM

def log (entry : LogEntry) : CompilerM Unit :=
  addTrace `Compiler.IR m!"{entry}"

def tracePrefixOptionName := `trace.compiler.ir

private def isLogEnabledFor (opts : Options) (optName : Name) : Bool :=
  match opts.find optName with
  | some (DataValue.ofBool v) => v
  | _     => opts.getBool tracePrefixOptionName

private def logDeclsAux (optName : Name) (cls : Name) (decls : Array Decl) : CompilerM Unit := do
  if isLogEnabledFor (← getOptions) optName then
    log (LogEntry.step cls decls)

@[inline] def logDecls (cls : Name) (decl : Array Decl) : CompilerM Unit :=
  logDeclsAux (tracePrefixOptionName ++ cls) cls decl

private def logMessageIfAux {α : Type} [ToFormat α] (optName : Name) (a : α) : CompilerM Unit := do
  if isLogEnabledFor (← getOptions) optName then
    log (LogEntry.message (format a))

@[inline] def logMessageIf {α : Type} [ToFormat α] (cls : Name) (a : α) : CompilerM Unit :=
  logMessageIfAux (tracePrefixOptionName ++ cls) a

@[inline] def logMessage {α : Type} [ToFormat α] (a : α) : CompilerM Unit :=
  logMessageIfAux tracePrefixOptionName a

abbrev DeclMap := PHashMap Name Decl

private abbrev declLt (a b : Decl) :=
  Name.quickLt a.name b.name

private abbrev sortDecls (decls : Array Decl) : Array Decl :=
  decls.qsort declLt

private abbrev findAtSorted? (decls : Array Decl) (declName : Name) : Option Decl :=
  let tmpDecl := Decl.extern declName #[] default default
  decls.binSearch tmpDecl declLt

/-- Meta status of local declarations, not persisted. -/
private builtin_initialize declMetaExt : EnvExtension (List Name × NameSet) ←
  registerEnvExtension
    (mkInitial := pure ([], {}))
    (asyncMode := .sync)
    (replay? := some <| fun oldState newState _ s =>
      let newEntries := newState.1.take (newState.1.length - oldState.1.length)
      newEntries.foldl (init := s) fun s n =>
        if s.1.contains n then
          s
        else
          (n :: s.1, s.2.insert n))

/-- Whether a declaration should be exported for interpretation. -/
def isDeclMeta (env : Environment) (declName : Name) : Bool :=
  if !env.header.isModule then
    true
  else
    -- The interpreter may call the boxed variant even if the IR does not directly reference it, so
    -- use same visibility as base decl.
    -- Note that boxed decls are created after the `inferVisibility` pass.
    let inferFor := match declName with
      | .str n "_boxed" => n
      | n               => n
    declMetaExt.getState env |>.2.contains inferFor

/-- Marks a declaration to be exported for interpretation. -/
def setDeclMeta (env : Environment) (declName : Name) : Environment :=
  if isDeclMeta env declName then
    env
  else
    declMetaExt.modifyState env fun s =>
      (declName :: s.1, s.2.insert declName)

builtin_initialize declMapExt : SimplePersistentEnvExtension Decl DeclMap ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn    := fun s d => s.insert d.name d
    -- Store `meta` closure only in `.olean`, turn all other decls into opaque externs.
    -- Leave storing the remainder for `meta import` and server `#eval` to `exportIREntries` below.
    exportEntriesFnEx? := some fun env s entries _ =>
      let decls := entries.foldl (init := #[]) fun decls decl => decls.push decl
      let entries := sortDecls decls
      -- Do not save all IR even in .olean.private as it will be in .ir anyway
      if env.header.isModule then
        entries.filterMap fun d => do
          if isDeclMeta env d.name then
            return d
          guard <| Compiler.LCNF.isDeclPublic env d.name
          -- Bodies of imported IR decls are not relevant for codegen, only interpretation
          match d with
          | .fdecl f xs ty b info =>
            if let some (.str _ s) := getExportNameFor? env f then
              return .extern f xs ty { entries := [.standard `all s] }
            else
              return .extern f xs ty { entries := [.opaque f] }
          | d => some d
      else entries
    -- Written to on codegen environment branch but accessed from other elaboration branches when
    -- calling into the interpreter. We cannot use `async` as the IR declarations added may not
    -- share a name prefix with the top-level Lean declaration being compiled, e.g. from
    -- specialization.
    asyncMode     := .sync
    replay?       := some <| SimplePersistentEnvExtension.replayOfFilter (!·.contains ·.name) (fun s d => s.insert d.name d)
  }

@[export lean_ir_export_entries]
private def exportIREntries (env : Environment) : Array (Name × Array EnvExtensionEntry) :=
  let decls := declMapExt.getEntries env |>.foldl (init := #[]) fun decls decl => decls.push decl
  -- safety: cast to erased type
  let entries : Array EnvExtensionEntry := unsafe unsafeCast <| sortDecls decls
  #[(``declMapExt, entries)]

@[export lean_ir_find_env_decl]
def findEnvDecl (env : Environment) (declName : Name) : Option Decl :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    -- `meta import/import all` and server `#eval`
    -- This case is important even for codegen because it needs to see IR via `import all` (because
    -- it can also see the LCNF)
    findAtSorted? (declMapExt.getModuleIREntries env modIdx) declName <|>
    -- (closure of) `meta def`; will report `.extern`s for other `def`s so needs to come second
    findAtSorted? (declMapExt.getModuleEntries env modIdx) declName
  | none => declMapExt.getState env |>.find? declName

def findDecl (n : Name) : CompilerM (Option Decl) :=
  return findEnvDecl (← getEnv) n

def containsDecl (n : Name) : CompilerM Bool :=
  return (← findDecl n).isSome

def getDecl (n : Name) : CompilerM Decl := do
  let (some decl) ← findDecl n | throwError s!"unknown declaration `{n}`"
  return decl

def findLocalDecl (n : Name) : CompilerM (Option Decl) :=
  return declMapExt.getState (← getEnv) |>.find? n

/-- Returns the list of IR declarations in declaration order. -/
def getDecls (env : Environment) : List Decl :=
  declMapExt.getEntries env

def addDecl (decl : Decl) : CompilerM Unit := do
  modifyEnv (declMapExt.addEntry · decl)

def addDecls (decls : Array Decl) : CompilerM Unit :=
  decls.forM addDecl

def findEnvDecl' (env : Environment) (n : Name) (decls : Array Decl) : Option Decl :=
  match decls.find? (fun decl => decl.name == n) with
  | some decl => some decl
  | none      => findEnvDecl env n

def findDecl' (n : Name) (decls : Array Decl) : CompilerM (Option Decl) :=
  return findEnvDecl' (← getEnv) n decls

def containsDecl' (n : Name) (decls : Array Decl) : CompilerM Bool := do
  if decls.any fun decl => decl.name == n then
    return true
  else
    containsDecl n

def getDecl' (n : Name) (decls : Array Decl) : CompilerM Decl := do
  let (some decl) ← findDecl' n decls | throwError s!"unknown declaration `{n}`"
  return decl

@[export lean_decl_get_sorry_dep]
def getSorryDep (env : Environment) (declName : Name) : Option Name :=
  match findEnvDecl env declName with
  | some (.fdecl (info := { sorryDep? := dep?, .. }) ..) => dep?
  | _ => none

/-- Returns additional names that compiler env exts may want to call `getModuleIdxFor?` on. -/
@[export lean_get_ir_extra_const_names]
private def getIRExtraConstNames (env : Environment) (level : OLeanLevel) : Array Name :=
  declMapExt.getEntries env |>.toArray.map (·.name)
    |>.filter fun n => !env.contains n &&
      (level == .private || Compiler.LCNF.isDeclPublic env n || isDeclMeta env n)

end IR
end Lean
