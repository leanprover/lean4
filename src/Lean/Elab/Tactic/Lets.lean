/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.Tactic.Lets
import Lean.Elab.Tactic.Location

/-!
# Tactics to manipulate `let` expressions
-/

open Lean Meta

namespace Lean.Elab.Tactic

declare_config_elab elabExtractLetsConfig ExtractLetsConfig

@[builtin_tactic extractLets] elab_rules : tactic
  | `(tactic| extract_lets $cfg:optConfig $ids* $[$ellipsis?:ellipsis]? $[$loc?:location]?) => do
    let mut config ← elabExtractLetsConfig cfg
    if ellipsis?.isSome || ids.isEmpty then
      config := { config with onlyGivenNames := false }
    let givenNames := (ids.map getNameOfIdent').toList
    withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
      (atLocal := fun h => do
        let fvars ← liftMetaTacticAux fun mvarId => do
          let (fvars, mvarId) ← mvarId.extractLetsLocalDecl h givenNames config
          return (fvars, [mvarId])
        withMainContext do
          for stx in ids, fvar in fvars do
            Term.addLocalVarInfo stx (.fvar fvar))
      (atTarget := do
        let fvars ← liftMetaTacticAux fun mvarId => do
          let (fvars, mvarId) ← mvarId.extractLets givenNames config
          return (fvars, [mvarId])
        withMainContext do
          for stx in ids, fvar in fvars do
            Term.addLocalVarInfo stx (.fvar fvar))
      (failed := fun _ => throwError "'extract_lets' tactic failed")

declare_config_elab elabLiftLetsConfig LiftLetsConfig

@[builtin_tactic liftLets] elab_rules : tactic
  | `(tactic| lift_lets $cfg:optConfig $[$loc?:location]?) => do
    let mut config ← elabLiftLetsConfig cfg
    withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
      (atLocal := fun h => liftMetaTactic1 fun mvarId => mvarId.liftLetsLocalDecl h config)
      (atTarget := liftMetaTactic1 fun mvarId => mvarId.liftLets config)
      (failed := fun _ => throwError "'lift_lets' tactic failed")

end Lean.Elab.Tactic
