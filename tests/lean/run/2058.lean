/-!
# Localized error messages with unassigned metavariables
-/

set_option pp.mvars false


/-!
Test: now reports "don't know how to synthesize implicit argument" rather than an error on the `example` command.
-/

/--
error: don't know how to synthesize implicit argument 'α'
  @none ?_
context:
⊢ Type _
---
error: failed to infer 'let' declaration type
-/
#guard_msgs in
example : IO Unit := do
  let x := none
  pure ()


/-!
Test: now reports that the universe levels are not assigned at the 'let' rather than an error on the `example` command.
-/

/--
error: failed to infer universe levels in 'let' declaration type
  PUnit.{_}
-/
#guard_msgs in
def foo : IO Unit := do
  let x : PUnit := PUnit.unit
  pure ()

-- specializes to 0 on error
/--
info: def foo : IO Unit :=
let x := PUnit.unit.{0};
pure.{0, 0} Unit.unit
-/
#guard_msgs in set_option pp.universes true in #print foo


/-!
Test: Works for `have` too.
-/

/--
error: failed to infer universe levels in 'have' declaration type
  PUnit.{_}
-/
#guard_msgs in
def foo' : IO Unit := do
  have x : PUnit := PUnit.unit
  pure ()


/-!
Test: Works for `fun` binders.
-/

/--
error: failed to infer universe levels in binder type
  PUnit.{_}
-/
#guard_msgs in
example : Nat := (fun x : PUnit => 2) PUnit.unit


/-!
Test: A failure not in a binder, right now reports an error on `example`.
A change is that before the error was about level parameters rather than metavariables since
the def elaborator would turn all metavariables into parameters before this analysis.
-/

/--
error: declaration '_example' contains universe level metavariables at the expression
  Function.const ({α : Sort _} → α → α) 2 @id.{_}
in the declaration body
  Function.const ({α : Sort _} → α → α) 2 @id.{_}
-/
#guard_msgs in
example : Nat := Function.const _ 2 @id
