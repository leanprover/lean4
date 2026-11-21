module

/-!
Regression test for #13647: with `Elab.async false`, private theorems were not exported under
`backward.privateInPublic`.
-/

set_option Elab.async false
set_option backward.privateInPublic true

public class U : Type where
  a : Nat
  h : a = a

private theorem A : 0 = 0 := rfl

/--
warning: Private declaration `A` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. ⏎

Disable `backward.privateInPublic.warn` to silence this warning.
-/
#guard_msgs in
public instance : U := ⟨0, A⟩
