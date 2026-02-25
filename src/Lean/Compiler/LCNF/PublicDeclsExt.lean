/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Environment

namespace Lean.Compiler.LCNF

/-- Creates a replayable local environment extension holding a name set. -/
public def mkDeclSetExt : IO (EnvExtension (List Name × NameSet)) :=
  registerEnvExtension
    (mkInitial := pure ([], {}))
    (asyncMode := .sync)
    (replay? := some <| fun oldState newState _ s =>
      let newEntries := newState.1.take (newState.1.length - oldState.1.length)
      newEntries.foldl (init := s) fun s n =>
        if s.1.contains n then
          s
        else
          (n :: s.1, if newState.2.contains n then s.2.insert n else s.2))

/--
Set of declarations to be exported to other modules; visibility shared by base/mono/IR phases.
-/
private builtin_initialize publicDeclsExt : EnvExtension (List Name × NameSet) ← mkDeclSetExt

public def isDeclPublic (env : Environment) (declName : Name) : Bool := Id.run do
  if !env.header.isModule then
    return true
  -- The IR compiler may call the boxed variant it introduces after we do visibility inference, so
  -- use same visibility as base decl.
  let inferFor := match declName with
    | .str n "_boxed" => n
    | n               => n
  let (_, map) := publicDeclsExt.getState env
  map.contains inferFor

public def setDeclPublic (env : Environment) (declName : Name) : Environment :=
  if isDeclPublic env declName then
    env
  else
    publicDeclsExt.modifyState env fun s =>
      (declName :: s.1, s.2.insert declName)

end Lean.Compiler.LCNF
