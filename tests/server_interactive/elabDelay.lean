/-!
Regression test for the delay before elaborating commands after the first changed command
(`server.elabDelayMs`): a request in a later command must still see the edited state.

The `change` edits the first command, then `$/lean/plainGoal` is requested in the second command
without an intervening `sync`, so the request has to wait for the delayed elaboration.
-/

-- RESET
def f : Nat :=
  1
--^ sync
--^ change: "1" "2"

example : f = 2 := by
  unfold f
  rfl
--^ $/lean/plainGoal
