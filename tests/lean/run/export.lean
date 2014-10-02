import data.nat

constants a b : nat

namespace boo
  export nat (rec add)
  check a + b
  check nat.add
  check boo.add
  check add
end boo

check boo.rec

open boo
check a + b
check boo.rec
check nat.rec
