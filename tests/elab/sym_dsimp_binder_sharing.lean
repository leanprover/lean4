import Lean
open Lean Meta Elab Tactic Sym

/-!
`Sym.dsimp` must keep terms maximally shared when it descends into binders whose
bound variable occurs in the body (or in later binder types). The free variables
introduced for the binders have to be registered in the share set before they are
substituted into the body, otherwise `sym.debug` reports a sharing violation.
-/

set_option sym.debug true
set_option warn.sorry false

elab "sym_dsimp" : tactic => withMainContext do
  let e ← instantiateMVars (← getMainTarget)
  SymM.run do
    let e ← shareCommon e
    let r ← DSimp.DSimpM.run' (DSimp.dsimp e)
    logInfo m!"result: {DSimp.Result.getResultExpr e r}"

/-- info: result: (g fun a => a = 0) = 1 -/
#guard_msgs in
example (g : (Nat → Prop) → Nat) : g (fun a => a = 0) = 1 := by sym_dsimp; sorry

/-- info: result: (g fun a b => a + b = 0) = 1 -/
#guard_msgs in
example (g : (Nat → Nat → Prop) → Nat) : g (fun a b => a + b = 0) = 1 := by sym_dsimp; sorry

/-- info: result: (∀ (a : Nat), a = 0) = True -/
#guard_msgs in
example : (∀ a : Nat, a = 0) = True := by sym_dsimp; sorry

/-- info: result: (∀ (a : Nat), a < 2 → a = 0) = True -/
#guard_msgs in
example : (∀ a : Nat, a < 2 → a = 0) = True := by sym_dsimp; sorry

/-- info: result: (g fun a => ∀ (b : Nat), b < a → b = 0) = 1 -/
#guard_msgs in
example (g : (Nat → Prop) → Nat) : g (fun a => ∀ b : Nat, b < a → b = 0) = 1 := by sym_dsimp; sorry

/--
info: result: g
    (let a := 2;
    a + a) =
  1
-/
#guard_msgs in
example (g : Nat → Nat) : g (let a := 2; a + a) = 1 := by sym_dsimp; sorry
