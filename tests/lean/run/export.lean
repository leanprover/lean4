import data.nat

variables a b : nat.nat

namespace boo
  export nat
  check a + b
  check nat.add
  check boo.add
  check add
end boo

check boo.nat_rec

open boo
check a + b
check boo.nat_rec
check nat_rec
