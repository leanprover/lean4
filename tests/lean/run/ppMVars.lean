import Lean.Elab.BuiltinNotation
import Lean.Meta.Basic
/-!
# Testing `pp.mvars`
-/

open Lean Meta

/-!
Default values
-/

/-- info: ?a : Nat -/
#guard_msgs in #check (?a : Nat)

/-- info: ⊢ Sort ?u.1 -/
#guard_msgs (info, drop all) in
example : (by_elab do return .sort (.mvar (.mk (.num `_uniq 1)))) := by
  trace_state
  sorry

/-!
Turning off `pp.mvars`
-/
section
set_option pp.mvars false

/-- info: ?_ : Nat -/
#guard_msgs in #check (?a : Nat)

/-- info: ?_ : Nat -/
#guard_msgs in #check (_ : Nat)

/-- info: ⊢ Sort _ -/
#guard_msgs (info, drop all) in
example : (by_elab do return .sort (.mvar (.mk (.num `_uniq 1)))) := by
  trace_state
  sorry

/-- info: ⊢ Type _ -/
#guard_msgs (info, drop all) in
example : Type _ := by
  trace_state
  sorry

end

/-!
Turning off `pp.mvars.levels`
-/
section
set_option pp.mvars.levels false

/-- info: ?a : Nat -/
#guard_msgs in #check (?a : Nat)

/-- info: ?m.222222222 : Nat -/
#guard_msgs in #check by_elab do
  -- Control the mvarId with something that's too big to happen naturally:
  let mvarId : MVarId := .mk (.num `_uniq 222222222)
  let lctx ← getLCtx
  let type := mkConst ``Nat
  Lean.MonadMCtx.modifyMCtx fun mctx => mctx.addExprMVarDecl mvarId .anonymous lctx {} type .natural 0
  return .mvar mvarId

/-- info: ⊢ Sort _ -/
#guard_msgs (info, drop all) in
example : (by_elab do return .sort (.mvar (.mk (.num `_uniq 1)))) := by
  trace_state
  sorry

/-- info: ⊢ Type _ -/
#guard_msgs (info, drop all) in
example : Type _ := by
  trace_state
  sorry

end

/-!
Turning off `pp.mvars.anonymous`
-/
section
set_option pp.mvars.anonymous false

/-- info: ?a : Nat -/
#guard_msgs in #check (?a : Nat)

/-- info: ?_ : Nat -/
#guard_msgs in #check by_elab do
  -- Control the mvarId with something that's too big to happen naturally:
  let mvarId : MVarId := .mk (.num `_uniq 222222222)
  let lctx ← getLCtx
  let type := mkConst ``Nat
  Lean.MonadMCtx.modifyMCtx fun mctx => mctx.addExprMVarDecl mvarId .anonymous lctx {} type .natural 0
  return .mvar mvarId

/-- info: ⊢ Sort _ -/
#guard_msgs (info, drop all) in
example : (by_elab do return .sort (.mvar (.mk (.num `_uniq 1)))) := by
  trace_state
  sorry

/-- info: ⊢ Type _ -/
#guard_msgs (info, drop all) in
example : Type _ := by
  trace_state
  sorry

end

/-!
Turning off `pp.mvars` and turning on `pp.mvars.withType`.
-/
section
set_option pp.mvars false
set_option pp.mvars.withType true

/-- info: (?_ : Nat) : Nat -/
#guard_msgs in #check (?a : Nat)

/-- info: (?_ : Nat) : Nat -/
#guard_msgs in #check (_ : Nat)

end

/-!
Turning on `pp.mvars.withType`.
-/
section
set_option pp.mvars.withType true

/-- info: (?a : Nat) : Nat -/
#guard_msgs in #check (?a : Nat)

end


/-!
Delayed assignment metavariables respecting `pp.mvars.anonymous`
-/

section
set_option pp.mvars.anonymous false

/-- info: fun x => ?a : (x : Nat) → ?_ x -/
#guard_msgs in #check fun _ : Nat => ?a

set_option pp.mvars.delayed true

/-- info: fun x => ?_ x : (x : Nat) → ?_ x -/
#guard_msgs in #check fun _ : Nat => ?a

end
