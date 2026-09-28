module

import all Lean.LibrarySuggestions.SymbolFrequency
import all Init.Data.Array.Basic

open Lean LibrarySuggestions

/-- info: [List, Eq, HAppend.hAppend] -/
#guard_msgs in
run_meta do
  let ci ← getConstInfo `List.append_assoc
  let consts ← ci.type.foldRelevantConstants (init := #[]) (fun n ns => return ns.push n)
  logInfo m!"{consts}"

/-- info: [List, Ne, HAppend.hAppend, List.nil, Eq, List.head] -/
#guard_msgs in
run_meta do
  let ci ← getConstInfo `List.head_append_right
  let consts ← ci.type.foldRelevantConstants (init := #[]) (fun n ns => return ns.push n)
  logInfo m!"{consts}"

/-- info: [Array, Nat, LT.lt, HAdd.hAdd, OfNat.ofNat, Array.swap, Not] -/
#guard_msgs in
run_meta do
  let ci ← getConstInfo `Array.eraseIdx.induct
  let consts ← ci.type.foldRelevantConstants (init := #[]) (fun n ns => return ns.push n)
  logInfo m!"{consts}"

/-!
Cases for the application spine traversal: heads whose type exposes fewer binders than the
application has arguments, heads whose type unfolds to a function type, and local heads with
instance-implicit binders.
-/

@[expose] public def F : Bool → Type
  | true => Nat → Nat
  | false => Nat

@[expose] public def k : (b : Bool) → F b
  | true => fun n => n + 1
  | false => (0 : Nat)

public theorem k_true : k true 0 = 1 := rfl

@[expose] public def MyFun := Nat → Nat

@[expose] public def g : MyFun := id

public theorem g_zero : g 0 = 0 := rfl

public theorem local_inst (f : {α : Type} → [Inhabited α] → α → α) : @f Nat ⟨0⟩ 1 = @f Nat ⟨0⟩ 1 := rfl

public theorem sub_pos (n : Nat) (h : 0 < n) : n - 1 < n := by omega

/-- info: [Eq, Nat, k, Bool.true, OfNat.ofNat] -/
#guard_msgs in
run_meta do
  logInfo m!"{← (← getConstInfo ``k_true).type.relevantConstants}"

/-- info: [Eq, Nat, g, OfNat.ofNat] -/
#guard_msgs in
run_meta do
  logInfo m!"{← (← getConstInfo ``g_zero).type.relevantConstants}"

/-- info: [Inhabited, Eq, Nat, OfNat.ofNat] -/
#guard_msgs in
run_meta do
  logInfo m!"{← (← getConstInfo ``local_inst).type.relevantConstants}"

/-- info: [Nat, LT.lt, OfNat.ofNat, HSub.hSub] -/
#guard_msgs in
run_meta do
  logInfo m!"{← (← getConstInfo ``sub_pos).type.relevantConstants}"

/-- info: true -/
#guard_msgs in
run_meta do
  -- `relevantConstantsOfEach` shares the per-head parameter cache across the batch and must agree
  -- with `relevantConstants` on each statement.
  let env ← getEnv
  let some idx := env.getModuleIdx? `Init.Data.Array.Basic | throwError "module not found"
  let names := env.header.moduleData[idx.toNat]!.constNames.filter (wasOriginallyTheorem env)
  let types ← names.mapM fun n => return (← getConstInfo n).type
  let batch ← Expr.relevantConstantsOfEach types
  let single ← types.mapM (·.relevantConstants)
  logInfo m!"{names.size > 100 && batch == single}"
