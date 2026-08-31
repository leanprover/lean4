import Std.Data.ExtTreeMap

/-!
# Test for extensional tree maps (#8721)
-/

open Std

/-!
The `ForIn` instance elaborates correctly for lawful monads.

Note: We require the `Monad` instance to be synthesized for the `ForIn` instance to make sure that
`LawfulMonad` is available. `forIn` still provides another monad instance which we ignore. This
results in one redundant instance synthesis (which should be cached though).
-/

def test (x : ExtTreeMap Nat Nat) : StateM Nat Nat := do
  let mut acc := 0
  for val in x do
    acc := acc + val.1
    modify fun a => a + val.2
  return acc

/--
info: (11, 5)
-/
#guard_msgs in
#eval (test {⟨4, 3⟩, ⟨7, 2⟩}).run 0
