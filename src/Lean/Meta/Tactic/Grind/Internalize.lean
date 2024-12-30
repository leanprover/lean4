/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Lean.Meta.LitValues
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

/-- Adds `e` to congruence table. -/
def addCongrTable (e : Expr) : GoalM Unit := do
  if let some { e := e' } := (← get).congrTable.find? { e } then
    -- `f` and `g` must have the same type.
    -- See paper: Congruence Closure in Intensional Type Theory
    let f := e.getAppFn
    let g := e'.getAppFn
    unless isSameExpr f g do
      unless (← hasSameType f g) do
        trace[grind.issues] "found congruence between{indentExpr e}\nand{indentExpr e'}\nbut functions have different types"
        return ()
    trace[grind.congr] "{e} = {e'}"
    pushEqHEq e e' congrPlaceholderProof
    let node ← getENode e
    setENode e { node with cgRoot := e' }
  else
    modify fun s => { s with congrTable := s.congrTable.insert { e } }

private def updateAppMap (e : Expr) : GoalM Unit := do
  let key := e.toHeadIndex
  modify fun s => { s with
    appMap := if let some es := s.appMap.find? key then
      s.appMap.insert key (e :: es)
    else
      s.appMap.insert key [e]
  }

private def activateTheoremPatterns (fName : Name) : GoalM Unit := do
  if let some thms := (← get).thmMap.find? fName then
    modify fun s => { s with thmMap := s.thmMap.erase fName }
    let appMap := (← get).appMap
    for thm in thms do
      let symbols := thm.symbols.filter fun sym => !appMap.contains sym
      let thm := { thm with symbols }
      match symbols with
      | [] =>
        trace[grind.pattern] "activated `{thm.origin.key}`"
        modify fun s => { s with newThms := s.newThms.push thm }
      | _ =>
        trace[grind.pattern] "reinsert `{thm.origin.key}`"
        modify fun s => { s with thmMap := s.thmMap.insert thm }

partial def internalize (e : Expr) (generation : Nat) : GoalM Unit := do
  if (← alreadyInternalized e) then return ()
  match e with
  | .bvar .. => unreachable!
  | .sort .. => return ()
  | .fvar .. | .letE .. | .lam .. | .forallE .. =>
    mkENodeCore e (ctor := false) (interpreted := false) (generation := generation)
  | .lit .. | .const .. =>
    mkENode e generation
  | .mvar ..
  | .mdata ..
  | .proj .. =>
    trace[grind.issues] "unexpected term during internalization{indentExpr e}"
    mkENodeCore e (ctor := false) (interpreted := false) (generation := generation)
  | .app .. =>
    if (← isLitValue e) then
      -- We do not want to internalize the components of a literal value.
      mkENode e generation
    else e.withApp fun f args => do
      if f.isConstOf ``Lean.Grind.nestedProof && args.size == 2 then
        -- We only internalize the proposition. We can skip the proof because of
        -- proof irrelevance
        let c := args[0]!
        internalize c generation
        registerParent e c
      else
        if let .const fName _ := f then
          activateTheoremPatterns fName
        else
          internalize f generation
          registerParent e f
        for h : i in [: args.size] do
          let arg := args[i]
          internalize arg generation
          registerParent e arg
      mkENode e generation
      addCongrTable e
      updateAppMap e
      propagateUp e

end Lean.Meta.Grind
