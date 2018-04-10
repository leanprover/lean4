open nat

namespace foo

definition tst1 (a b : nat) : nat :=
match a with
| 0     := 1
| (n+1) := foo
end


end foo
