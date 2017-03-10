constants a b : nat

namespace boo
  export nat (rec add)
  #check a + b
  #check nat.add
end boo

open boo
#check a + b
#check nat.rec
