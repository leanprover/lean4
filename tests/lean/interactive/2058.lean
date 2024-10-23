/-!
# Localized error messages with unassigned metavariables
-/

set_option pp.mvars false


/-!
Test: now reports that the universe levels are not assigned at the 'let' rather than an error on the `example` command.
-/

def foo : IO Unit := do
  let x : PUnit := PUnit.unit
        --^ collectDiagnostics
  pure ()


/-!
Test: Works for `fun` binders too.
-/

example : Nat := (fun x : PUnit => 2) PUnit.unit
                        --^ collectDiagnostics


/-!
Test: A failure not in a binder, right now reports an error on `example` since there's no other location information.
-/

example : Nat := Function.const _ 2 @id
--^ collectDiagnostics
