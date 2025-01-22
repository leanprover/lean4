
/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

import Lean.Elab.Command
import Lean.Elab.DefView
import Lean.Elab.Binders
import Lean.Meta.Tactic.Rewrite
import Lean.Parser.Command

set_option autoImplicit false

namespace Transform

open Lean Elab Command Term Meta

#check Lean.TSyntax

-- def toStr : Lean.Syntax → String
-- | .missing => "missing"
-- | .node info kind args => info.getRange?
-- | other => "other"

def start : Lean.Syntax → String.Pos :=
  fun s => s |>.getPos? |>.getD ⟨0⟩

def endPos : Lean.Syntax → String.Pos :=
  fun s => s |>.getTailPos? |>.getD ⟨0⟩

def modifyTheorem : Lean.TSyntax [`command] → CommandElabM (Lean.Syntax)
| `(command| theorem $id : $t := $d) => `(command| theorem $id : $t := sorry)
| _ => panic ""

def stringify (s : Lean.Syntax) : CommandElabM String := do
  let x := s.getRange?
  if let some r := x then
    let map ← Lean.MonadFileMap.getFileMap
    pure (map.source.toSubstring.extract r.start r.stop).toString
  else
    pure "ho"

elab "transform" cmd:command : command => do
  liftCoreM $ do
    pure ()
  let cmd2 ← modifyTheorem cmd
  -- let map ← Lean.MonadFileMap.getFileMap
  -- let str := map.source.toSubstring.extract (start cmd2) (endPos cmd2)
  -- Lean.logInfo s!"{Lean.Syntax.getHeadInfo cmd2 |>.getPos?}"
  -- Lean.logInfo s!"info {start cmd2} {endPos cmd2} {str} {cmd.getKind}"
  -- Lean.logInfo s!"{(←stringify cmd)}"
  Lean.logInfo s!"{(←liftCoreM $ Lean.PrettyPrinter.formatTerm cmd2)}"

transform theorem f : 1 - 2 := 111111111111

elab "#findCElab " c:command : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  match macroRes with
  | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match elabs with
    | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
    | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"

#findCElab theorem a : Unit := sorry

example : 1 = 1 := by
  simp []

end Transform
