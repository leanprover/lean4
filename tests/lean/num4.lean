import data.num
set_option pp.notation false
set_option pp.implicit true

namespace foo
  variable N : Type.{1}
  variable z : N
  variable o : N
  variable a : N
  notation 0 := z
  notation 1 := o

  check a = 0
end foo

check 2 = 1
check #foo foo.a = 1

open foo
check a = 1
