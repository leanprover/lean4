/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context

/-!
The `@[frameproc]` attribute registers `FrameProc`s for `vcgen`.
-/

open Lean Meta Elab Sym
open Lean.Elab.Tactic.Do.Internal

public section

namespace Lean.Elab.Tactic.Do.Internal.VCGen

unsafe def getFrameProcFromDeclImpl (declName : Name) : ImportM FrameProc := do
  let ctx ← read
  match ctx.env.find? declName with
  | none => throw <| .userError s!"unknown constant '{declName}'"
  | some info =>
    unless info.type.isConstOf ``FrameProc do
      throw <| .userError s!"`{declName}` is not a `FrameProc`"
    IO.ofExcept <| ctx.env.evalConst FrameProc ctx.opts declName

/-- Recover the compiled `FrameProc` value of a `@[frameproc]`-annotated declaration. -/
@[implemented_by getFrameProcFromDeclImpl]
opaque getFrameProcFromDecl (declName : Name) : ImportM FrameProc

abbrev FrameProcExtension := ScopedEnvExtension Name (Name × FrameProc) FrameProcs

def toFrameProcEntry (declName : Name) : ImportM (Name × FrameProc) := do
  return (declName, ← getFrameProcFromDecl declName)

builtin_initialize frameProcExt : FrameProcExtension ←
  registerScopedEnvExtension {
    name         := by exact decl_name%
    mkInitial    := return {}
    ofOLeanEntry := fun _ declName => toFrameProcEntry declName
    toOLeanEntry := fun (declName, _) => declName
    addEntry     := fun s (_declName, fp) => s.insert fp
  }

/-- The frame inference procedures in scope. -/
def getFrameProcs {m : Type → Type} [Monad m] [MonadEnv m] : m FrameProcs :=
  return frameProcExt.getState (← getEnv)

def addFrameProcAttr (declName : Name) (kind : AttributeKind) : AttrM Unit := do
  ensureAttrDeclIsMeta `frameproc declName kind
  let fp ← getFrameProcFromDecl declName
  frameProcExt.add (declName, fp) kind

builtin_initialize registerBuiltinAttribute {
  ref             := by exact decl_name%
  name            := `frameproc
  descr           := "register a frame inference procedure for `vcgen`"
  applicationTime := .afterCompilation
  add             := fun declName _stx kind => addFrameProcAttr declName kind
}

end Lean.Elab.Tactic.Do.Internal.VCGen
