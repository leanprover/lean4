/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Attr
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta.Grind
open Simp

builtin_initialize grindNormExt : SimpExtension ←
  registerSimpAttr `grind_norm "simplification/normalization theorems for `grind`"

builtin_initialize grindNormSimprocExt : SimprocExtension ←
  registerSimprocAttr `grind_norm_proc "simplification/normalization procedured for `grind`" none


#check simpAttrNameToSimprocAttrName

/-
  let str := id.getId.toString
  let idParser := mkIdentFrom id (`Parser.Attr ++ id.getId)
  let descr := quote ((doc.map (·.getDocString) |>.getD s!"simp set for {id.getId.toString}").removeLeadingSpaces)
  let procId := mkIdentFrom id (simpAttrNameToSimprocAttrName id.getId)
  let procStr := procId.getId.toString
  let procIdParser := mkIdentFrom procId (`Parser.Attr ++ procId.getId)
  let procDescr := quote s!"simproc set for {procId.getId.toString}"
  -- TODO: better docDomment for simprocs
  `($[$doc:docComment]? initialize ext : SimpExtension ← registerSimpAttr $(quote id.getId) $descr $(quote id.getId)
    $[$doc:docComment]? syntax (name := $idParser:ident) $(quote str):str (Parser.Tactic.simpPre <|> Parser.Tactic.simpPost)? (prio)? : attr
    /-- Simplification procedure -/
    initialize extProc : SimprocExtension ← registerSimprocAttr $(quote procId.getId) $procDescr none $(quote procId.getId)
    /-- Simplification procedure -/
    syntax (name := $procIdParser:ident) $(quote procStr):str (Parser.Tactic.simpPre <|> Parser.Tactic.simpPost)? : attr)

-/

end Lean.Meta.Grind
