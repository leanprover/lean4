
/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Data.Json.FromToJson

namespace Lean.Elab.Deriving.FromToJson
open Lean.Elab.Command
open Lean.Json

def mkJsonField (n : Name) : Syntax :=
  let s := n.toString
  let s := s.dropRightWhile (· == '?')
  Syntax.mkStrLit s

def mkToJsonInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 && (← isStructure (← getEnv) declNames[0]) then
    let cmds ← liftTermElabM none <| do
      let ctx ← mkContext "toJson" declNames[0]
      let header ← mkHeader ctx ``ToJson 1 ctx.typeInfos[0]
      let fields := getStructureFieldsFlattened (← getEnv) declNames[0]
      let fields ← fields.mapM fun field => `(($(mkJsonField field), toJson $(mkIdent <| header.targetNames[0] ++ field)))
      let cmd ← `(private def $(mkIdent ctx.auxFunNames[0]):ident $header.binders:explicitBinder* :=
        mkObj [$fields,*])
      return #[cmd] ++ (← mkInstanceCmds ctx ``ToJson declNames)
    cmds.forM elabCommand
    return true
  else
    return false

def mkFromJsonInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 && (← isStructure (← getEnv) declNames[0]) then
    let cmds ← liftTermElabM none <| do
      let ctx ← mkContext "fromJson" declNames[0]
      let header ← mkHeader ctx ``FromJson 0 ctx.typeInfos[0]
      let fields := getStructureFieldsFlattened (← getEnv) declNames[0]
      let jsonFields := fields.map mkJsonField
      let fields := fields.map mkIdent
      let cmd ← `(private def $(mkIdent ctx.auxFunNames[0]):ident $header.binders:explicitBinder* (o : Json) : Option $(← mkInductiveApp ctx.typeInfos[0] header.argNames) := do
        $[let $fields:ident ← getObjValAs? o _ $jsonFields]*
        return { $[$fields:ident := $(id fields)]* })
      return #[cmd] ++ (← mkInstanceCmds ctx ``FromJson declNames)
    cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerBuiltinDerivingHandler ``ToJson mkToJsonInstanceHandler
  registerBuiltinDerivingHandler ``FromJson mkFromJsonInstanceHandler

end Lean.Elab.Deriving.FromToJson
