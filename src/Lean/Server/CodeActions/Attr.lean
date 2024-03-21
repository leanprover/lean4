/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Lean.Server.CodeActions.Basic

/-!
# Initial setup for code action attributes

* Attribute `@[hole_code_action]` collects code actions which will be called
  on each occurrence of a hole (`_`, `?_` or `sorry`).

* Attribute `@[tactic_code_action]` collects code actions which will be called
  on each occurrence of a tactic.

* Attribute `@[command_code_action]` collects code actions which will be called
  on each occurrence of a command.
-/
namespace Lean.CodeAction

open Lean Elab Server Lsp RequestM Snapshots

/-- A hole code action extension. -/
abbrev HoleCodeAction :=
  CodeActionParams → Snapshot →
  (ctx : ContextInfo) → (hole : TermInfo) → RequestM (Array LazyCodeAction)

/-- Read a hole code action from a declaration of the right type. -/
def mkHoleCodeAction (n : Name) : ImportM HoleCodeAction := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck HoleCodeAction opts ``HoleCodeAction n

/-- An extension which collects all the hole code actions. -/
builtin_initialize holeCodeActionExt :
    PersistentEnvExtension Name (Name × HoleCodeAction) (Array Name × Array HoleCodeAction) ←
  registerPersistentEnvExtension {
    mkInitial := pure (#[], #[])
    addImportedFn := fun as => return (#[], ← as.foldlM (init := #[]) fun m as =>
      as.foldlM (init := m) fun m a => return m.push (← mkHoleCodeAction a))
    addEntryFn := fun (s₁, s₂) (n₁, n₂) => (s₁.push n₁, s₂.push n₂)
    exportEntriesFn := (·.1)
  }

builtin_initialize
  registerBuiltinAttribute {
    name := `hole_code_action
    descr := "Declare a new hole code action, to appear in the code actions on ?_ and _"
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'hole_code_action', must be global"
      if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
      modifyEnv (holeCodeActionExt.addEntry · (decl, ← mkHoleCodeAction decl))
  }

/-- A command code action extension. -/
abbrev CommandCodeAction :=
  CodeActionParams → Snapshot → (ctx : ContextInfo) → (node : InfoTree) →
  RequestM (Array LazyCodeAction)

/-- Read a command code action from a declaration of the right type. -/
def mkCommandCodeAction (n : Name) : ImportM CommandCodeAction := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck CommandCodeAction opts ``CommandCodeAction n

/-- An entry in the command code actions extension, containing the attribute arguments. -/
structure CommandCodeActionEntry where
  /-- The declaration to tag -/
  declName : Name
  /-- The command kinds that this extension supports.
  If empty it is called on all command kinds. -/
  cmdKinds : Array Name
  deriving Inhabited

/-- The state of the command code actions extension. -/
structure CommandCodeActions where
  /-- The list of command code actions to apply on any command. -/
  onAnyCmd : Array CommandCodeAction := {}
  /-- The list of command code actions to apply when a particular command kind is highlighted. -/
  onCmd : NameMap (Array CommandCodeAction) := {}
  deriving Inhabited

/-- Insert a command code action entry into the `CommandCodeActions` structure. -/
def CommandCodeActions.insert (self : CommandCodeActions)
    (tacticKinds : Array Name) (action : CommandCodeAction) : CommandCodeActions :=
  if tacticKinds.isEmpty then
    { self with onAnyCmd := self.onAnyCmd.push action }
  else
    { self with onCmd := tacticKinds.foldl (init := self.onCmd) fun m a =>
        m.insert a ((m.findD a #[]).push action) }

builtin_initialize builtinCmdCodeActions : IO.Ref CommandCodeActions ← IO.mkRef {}

def insertBuiltin (args : Array Name) (proc : CommandCodeAction) : IO Unit := do
  builtinCmdCodeActions.modify fun self => self.insert args proc

/-- An extension which collects all the command code actions. -/
builtin_initialize cmdCodeActionExt :
    PersistentEnvExtension CommandCodeActionEntry (CommandCodeActionEntry × CommandCodeAction)
      (Array CommandCodeActionEntry × CommandCodeActions) ←
  registerPersistentEnvExtension {
    mkInitial := return (#[], ← builtinCmdCodeActions.get)
    addImportedFn := fun as => do
      let init ← builtinCmdCodeActions.get
      return (#[], ← as.foldlM (init := init) fun m as =>
      as.foldlM (init := m) fun m ⟨name, kinds⟩ =>
        return m.insert kinds (← mkCommandCodeAction name))
    addEntryFn := fun (s₁, s₂) (e, n₂) => (s₁.push e, s₂.insert e.cmdKinds n₂)
    exportEntriesFn := (·.1)
  }

builtin_initialize
  registerBuiltinAttribute {
    name := `command_code_action
    descr := "Declare a new command code action, to appear in the code actions on commands"
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'command_code_action', must be global"
      let `(attr| command_code_action $args*) := stx | return
      let args ← args.mapM realizeGlobalConstNoOverloadWithInfo
      if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
      modifyEnv (cmdCodeActionExt.addEntry · (⟨decl, args⟩, ← mkCommandCodeAction decl))
  }

private def addBuiltin (declName : Name) (args : Array Name) : AttrM Unit := do
  let go : MetaM Unit := do
    let val := mkAppN (mkConst ``insertBuiltin) #[toExpr args, mkConst declName]
    let initDeclName ← mkFreshUserName (declName ++ `declare)
    declareBuiltin initDeclName val
  go.run' {}

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `builtin_command_code_action
    descr           := "Declare a new builtin command code action, to appear in the code actions on commands"
    applicationTime := .afterCompilation
    add             := fun decl stx kind => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'command_code_action', must be global"
      let `(attr| builtin_command_code_action $args*) := stx |
        throwError "unexpected 'command_code_action' attribute syntax"
      let args ← args.mapM realizeGlobalConstNoOverloadWithInfo
      if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
      addBuiltin decl args
  }
