/-
Copyright (c) 2024 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Matthew Robert Ballard
-/
prelude
import Init.Tactics
import Lean.Elab.Command
import Lean.Meta.Tactic.Simp.SimpTheorems

namespace Lean.Elab.Tactic.DiscrTreeKey

open Lean.Meta DiscrTree
open Lean.Elab.Tactic
open Lean.Elab.Command

private def mkKey (e : Expr) (simp : Bool) : MetaM (Array Key) := do
  let (_, _, type) ← withReducible <| forallMetaTelescopeReducing e
  let type ← whnfR type
  if simp then
    withSimpGlobalConfig do
      if let some (_, lhs, _) := type.eq? then
        mkPath lhs
      else if let some (lhs, _) := type.iff? then
        mkPath lhs
      else if let some (_, lhs, rhs) := type.ne? then
        mkPath (← mkEq lhs rhs)
      else if let some p := type.not? then
        mkPath p
      else
        mkPath type
  else
    mkPath type

private def getType (t : TSyntax `term) : TermElabM Expr := do
  if let `($id:ident) := t then
    if let some ldecl := (← getLCtx).findFromUserName? id.getId then
      return ldecl.type
    else
      let info ← getConstInfo (← realizeGlobalConstNoOverloadWithInfo id)
      return info.type
  else
    Term.elabTerm t none

@[builtin_command_elab Lean.Parser.discrTreeKeyCmd]
def evalDiscrTreeKeyCmd : CommandElab := fun stx => do
  Command.liftTermElabM <| do
    match stx with
    | `(command| #discr_tree_key $t:term) => do
      let type ← getType t
      logInfo (← keysAsPattern <| ← mkKey type false)
    | _                        => Elab.throwUnsupportedSyntax

@[builtin_command_elab Lean.Parser.discrTreeSimpKeyCmd]
def evalDiscrTreeSimpKeyCmd : CommandElab := fun stx => do
  Command.liftTermElabM <| do
    match stx with
    | `(command| #discr_tree_simp_key $t:term) => do
      let type ← getType t
      logInfo (← keysAsPattern <| ← mkKey type true)
    | _                        => Elab.throwUnsupportedSyntax

end Lean.Elab.Tactic.DiscrTreeKey
