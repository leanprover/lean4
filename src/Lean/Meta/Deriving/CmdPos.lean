module
prelude
public import Lean.Elab.Deriving
public import Lean.Meta.Tactic.TryThis

public section

open Lean Meta Tactic Elab Command

builtin_initialize
  Lean.Elab.registerDerivingHandler ``Add fun _names => do
    let pos := (← read).cmdPos
    let stx : Syntax := Syntax.ofRange ⟨pos, pos⟩
    liftCoreM do
      TryThis.addSuggestion (← getRef) { suggestion := "deriving instance BEq for Nat\n\n" } stx
    return true
