/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
prelude
import Lean.Elab.Tactic.Basic

/-! # `classical` tactic -/

namespace Lean.Elab.Tactic
open Lean Meta Elab.Tactic

/--
`classical t` runs `t` in a scope where `Classical.propDecidable` is a low priority
local instance.
-/
def classical [Monad m] [MonadEnv m] [MonadFinally m] [MonadLiftT MetaM m] (t : m α) :
    m α := do
  modifyEnv Meta.instanceExtension.pushScope
  Meta.addInstance ``Classical.propDecidable .local 10
  try
    t
  finally
    modifyEnv Meta.instanceExtension.popScope

@[builtin_tactic Lean.Parser.Tactic.classical]
def evalClassical : Tactic := fun stx => do
  match stx with
  | `(tactic| classical $tacs:tacticSeq) =>
     classical <| Elab.Tactic.evalTactic tacs
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
