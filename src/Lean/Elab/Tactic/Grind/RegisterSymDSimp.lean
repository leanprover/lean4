/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Init.Sym.DSimp.DSimprocDSL
import Lean.Meta.Sym.DSimp.Variant
import Lean.Elab.Tactic.Grind.DSimprocDSL
import Lean.Elab.Tactic.Grind.WithGrindTacticM
namespace Lean.Elab.Command
open Meta Sym.DSimp

def validateOptionDSimprocSyntax (proc? : Option Syntax) : CommandElabM Unit := do
  let some proc := proc? | return ()
  discard <| withGrindTacticM <| Tactic.Grind.elabSymDSimproc proc

@[builtin_command_elab Lean.Parser.Command.registerSymDSimp]
def elabRegisterSymDSimp : CommandElab := fun stx => do
  let id := stx[1]
  let name := id.getId
  -- Check for duplicate variant
  if (getSymDSimpVariant? (← getEnv) name).isSome then
    throwErrorAt id "Sym.dsimp variant `{name}` is already registered"
  let fields := stx[3].getArgs
  let mut pre? : Option Syntax := none
  let mut post? : Option Syntax := none
  let mut maxSteps? : Option Nat := none
  for field in fields do
    match field with
    | `(sym_dsimp_field| maxSteps := $val:num) =>
      unless maxSteps?.isNone do throwErrorAt field "duplicate `maxSteps` field"
      maxSteps? := some val.getNat
    | `(sym_dsimp_field| pre := $proc) =>
      unless pre?.isNone do throwErrorAt field "duplicate `pre` field"
      pre? := some proc
    | `(sym_dsimp_field| post := $proc) =>
      unless post?.isNone do throwErrorAt field "duplicate `post` field"
      post? := some proc
    | _ => throwErrorAt field "unexpected field"
  -- Validate pre/post by elaborating them
  validateOptionDSimprocSyntax pre?
  validateOptionDSimprocSyntax post?
  let config := { maxSteps := maxSteps?.getD 100_000 }
  let variant : SymDSimpVariant := { pre?, post?, config }
  modifyEnv fun env => symDSimpVariantExtension.addEntry env { name, variant }

end Lean.Elab.Command
