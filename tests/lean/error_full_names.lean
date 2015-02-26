namespace foo
open nat
inductive nat : Type := zero | foosucc : nat → nat
check 0 + nat.zero --error
end foo

namespace foo
check nat.succ nat.zero --error
end foo
