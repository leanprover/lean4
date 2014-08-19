

variable nat : Type.{1}
variable f : nat → nat

namespace foo
  variable int : Type.{1}
  variable f   : int → int
  variable a   : nat
  variable i   : int
  check _root_.f a
  check f i
end foo

using foo
variables a : nat
variables i : int
check f a
check f i
