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

def mkJsonField (n : Name) : Bool × Syntax :=
  let s  := n.toString
  let s₁ := s.dropRightWhile (· == '?')
  (s != s₁, Syntax.mkStrLit s₁)

def mkToJsonInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 && (← isStructure (← getEnv) declNames[0]) then
    let cmds ← liftTermElabM none <| do
      let ctx ← mkContext "toJson" declNames[0]
      let header ← mkHeader ctx ``ToJson 1 ctx.typeInfos[0]
      let fields := getStructureFieldsFlattened (← getEnv) declNames[0] (includeSubobjectFields := false)
      let fields : Array Syntax ← fields.mapM fun field => do
        let (isOptField, nm) ← mkJsonField field
        if isOptField then `(opt $nm $(mkIdent <| header.targetNames[0] ++ field))
        else `([($nm, toJson $(mkIdent <| header.targetNames[0] ++ field))])
      let cmd ← `(private def $(mkIdent ctx.auxFunNames[0]):ident $header.binders:explicitBinder* :=
        mkObj <| List.join [$fields,*])
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
      let fields := getStructureFieldsFlattened (← getEnv) declNames[0] (includeSubobjectFields := false)
      let jsonFields := fields.map (Prod.snd ∘ mkJsonField)
      let fields := fields.map mkIdent
      let cmd ← `(private def $(mkIdent ctx.auxFunNames[0]):ident $header.binders:explicitBinder* (j : Json)
        : Option $(← mkInductiveApp ctx.typeInfos[0] header.argNames) := OptionM.run do
        $[let $fields:ident ← getObjValAs? j _ $jsonFields]*
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
