module

/-!
Under `backward.privateInPublic`, a private declaration is exported together with its body. Check
that it does not refer to private declarations that are not exported (see
leanprover-community/mathlib4#45411).
-/

set_option backward.privateInPublic.warn false

private def helper : Nat := 1

/--
error: Private declaration `user` is exported because `backward.privateInPublic` is enabled, but it refers to the private declaration `helper`, which is not exported.

Hint: Enable `backward.privateInPublic` for `helper` as well.
-/
#guard_msgs in
set_option backward.privateInPublic true in
private def user : Nat := helper + 1

/--
error: Private declaration `userThm` is exported because `backward.privateInPublic` is enabled, but it refers to the private declaration `helper`, which is not exported.

Hint: Enable `backward.privateInPublic` for `helper` as well.
-/
#guard_msgs in
set_option backward.privateInPublic true in
private theorem userThm : helper = 1 := rfl

set_option backward.privateInPublic true in
private def helper2 : Nat := 1

-- Fine: `helper2` is exported as well.
set_option backward.privateInPublic true in
private def user2 : Nat := helper2 + 1

set_option backward.privateInPublic true in
private theorem userThm2 : helper2 = 1 := by simp [helper2]

-- Fine: only the statement of a theorem is exported, and the proof may use `helper`.
set_option backward.privateInPublic true in
private theorem userThm3 : 1 = 1 := by simp [helper]

-- Fine: auxiliary definitions such as matchers are exported along with the definition.
set_option backward.privateInPublic true in
private def user3 (n : Nat) : Nat := match n with | 0 => helper2 | _ + 1 => 2

-- Fine: the body of a non-private definition is not affected.
public def pub : Nat := helper + user2
