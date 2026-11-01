/-
Copyright (c) 2026 Nicholas Sielicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.InferType

public section

namespace Lean.Compiler.LCNF

/--
Recognize a tail-recursive list loop whose `Option` accumulator is only
returned at the end or replaced by `some head` before the recursive call.
The original declaration handles the empty list and calls a worker for a
nonempty list. The worker carries the last element directly and constructs
`some` only when the loop ends.
-/
private def optionAccumulatorWorker? (decl : Decl .pure) :
    CompilerM (Option (Array (Decl .pure))) := do
  unless decl.recursive do return none
  let #[list, acc] := decl.params | return none
  let .app (.const ``List _) payloadType := list.type | return none
  let optionType := mkApp (mkConst ``Option) payloadType
  unless acc.type == optionType do
    return none
  let .code (.cases cases) := decl.value | return none
  unless cases.typeName == ``List && cases.discr == list.fvarId &&
      cases.resultType == optionType do return none
  let #[nilAlt, consAlt] := cases.alts | return none
  let .alt nilName nilParams nilCode := nilAlt | return none
  let .return nilResult := nilCode | return none
  unless nilName == ``List.nil && nilParams.isEmpty && nilResult == acc.fvarId do return none
  let .alt consName consParams consCode := consAlt | return none
  unless consName == ``List.cons do return none
  let #[head, tail] := consParams | return none
  unless head.type == payloadType && tail.type == list.type do return none
  let .let someDecl (.let recDecl (.return result)) := consCode | return none
  let .const ``Option.some someLevels someArgs := someDecl.value | return none
  let #[someTypeArg, .fvar somePayload] := someArgs | return none
  unless someLevels.isEmpty && somePayload == head.fvarId &&
      someDecl.type == optionType do return none
  let .const recName recLevels recArgs := recDecl.value | return none
  let #[.fvar recList, .fvar recAcc] := recArgs | return none
  unless recName == decl.name && recLevels.isEmpty &&
      recList == tail.fvarId && recAcc == someDecl.fvarId &&
      result == recDecl.fvarId && recDecl.type == optionType do return none

  let workerName := decl.name ++ `_optionAccumulatorWorker
  -- A user declaration may already have the generated name.
  if (← getEnv).contains workerName || (← getDecl? workerName).isSome then
    return none
  let payload ← mkParam `payload payloadType false
  let workerParams := #[list, payload]
  let workerType ← mkForallParams workerParams optionType
  let finalSome ← mkLetDecl `finalSome optionType
    (.const ``Option.some [] #[someTypeArg, .fvar payload.fvarId])
  let recWork ← mkLetDecl `recResult optionType
    (.const workerName [] #[.fvar tail.fvarId, .fvar head.fvarId])
  let workerCode : Code .pure := .cases ⟨``List, optionType, list.fvarId, #[
    .alt ``List.nil #[] (.let finalSome (.return finalSome.fvarId)),
    .alt ``List.cons consParams (.let recWork (.return recWork.fvarId))
  ]⟩
  let worker : Decl .pure := {
    decl with
    name := workerName
    type := workerType
    params := workerParams
    value := .code workerCode
    inlineAttr? := none
  }

  let wrapperResult ← mkLetDecl `result optionType
    (.const workerName [] #[.fvar tail.fvarId, .fvar head.fvarId])
  let wrapperCode : Code .pure := .cases ⟨``List, optionType, list.fvarId, #[
    .alt ``List.nil #[] (.return acc.fvarId),
    .alt ``List.cons consParams (.let wrapperResult (.return wrapperResult.fvarId))
  ]⟩
  let wrapper := { decl with value := .code wrapperCode, recursive := false }
  worker.saveMono
  wrapper.saveMono
  return some #[worker, wrapper]

private def runOptionAccumulatorWorker (decls : Array (Decl .pure)) :
    CompilerM (Array (Decl .pure)) := do
  decls.foldlM (init := #[]) fun result decl => do
    let replacement ← optionAccumulatorWorker? decl
    match replacement with
    | some workerAndWrapper => return result ++ workerAndWrapper
    | none => return result.push decl

/-- Remove intermediate `Option.some` values from a simple tail-recursive list loop. -/
def optionAccumulatorWorker : Pass where
  name := `optionAccumulatorWorker
  phase := .mono
  phaseOut := .mono
  run := runOptionAccumulatorWorker

end Lean.Compiler.LCNF
