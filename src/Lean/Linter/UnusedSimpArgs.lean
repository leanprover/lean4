/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Simp
public import Lean.Linter.Util

public section

namespace Lean.Linter

open Lean Elab Command
open Lean.Linter (logLint)

private def warnUnused (stx : Syntax) (i : Nat) : CoreM Unit := do
  let stx : TSyntax `tactic := ⟨stx⟩
  let simpArgs := Tactic.getSimpParams stx
  unless i < simpArgs.size do
    throwError "Index {i} out of bounds for simp arguments of {stx}"
  let argStx := simpArgs[i]!
  let msg := m!"This simp argument is unused:{indentD argStx}"
  let mut otherArgs : Array Syntax := #[]
  for h : j in *...simpArgs.size do if j != i then
    otherArgs := otherArgs.push simpArgs[j]
  let stx' := Tactic.setSimpParams stx otherArgs
  let suggestion : Meta.Hint.Suggestion := stx'
  let suggestion := { suggestion with span? := stx }
  let mut hint ← MessageData.hint "Omit it from the simp argument list." #[ suggestion ]
  -- Add hint about `←`
  let isInv := argStx.getKind == ``Lean.Parser.Tactic.simpLemma && !argStx[1].isNone
  if isInv then
    hint := hint ++ .note m!"Simp arguments with `←` have the additional effect of removing \
      the other direction from the simp set, even if the simp argument itself is unused. \
      If the hint above does not work, try replacing `←` with `-` to only get that effect \
      and silence this warning."
  logLintIf Tactic.linter.unusedSimpArgs argStx (msg ++ hint)

def unusedSimpArgs : Linter where
  run cmdStx := do
    if !getLinterValue Tactic.linter.unusedSimpArgs (← getLinterOptions) then return
    let some cmdStxRange := cmdStx.getRange?  | return

    let infoTrees := (← get).infoState.trees.toArray
    let masksMap : IO.Ref (Std.HashMap Lean.Syntax.Range (Syntax × Array Bool)) ← IO.mkRef {}

    for tree in infoTrees do
      tree.visitM' (postNode := fun ci info _ => do
        match info with
        | .ofCustomInfo ci =>
          if let some {mask} := ci.value.get? Tactic.UnusedSimpArgsInfo then
            -- Only look at info with a range. This also happens to prevent the linter from
            -- reporting about unused simp arguments inside macro, which we do not want to do
            -- (we likely cannot see all uses of the macro, so the warning would be incomplete)
            let some range := info.range? | return
            let stx := ci.stx
            -- Check that we have the expected syntax
            unless stx.isOfKind ``Parser.Tactic.simpAll ||
                   stx.isOfKind ``Parser.Tactic.simp do return

            let maskAcc ←
              if let some (_, maskAcc) := (← masksMap.get)[range]? then
                unless mask.size = maskAcc.size do
                  throwErrorAt info.stx "Simp argument mask size mismatch}: {maskAcc.size} vs. {mask.size}"
                pure <| Array.zipWith (· || ·) mask maskAcc
              else
                pure mask
            masksMap.modify fun m => m.insert range (stx, maskAcc)
        | _ => pure ())

    -- Sort the outputs by position
    for (_range, tacticStx, mask) in (← masksMap.get).toArray.qsort (·.1.start < ·.1.start) do
      for i in *...mask.size do
        unless mask[i]! do
          liftCoreM <| warnUnused tacticStx i

builtin_initialize addLinter unusedSimpArgs
