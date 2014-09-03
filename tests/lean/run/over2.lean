import data.nat
open nat

namespace N1
  definition foo (a : nat) := a
end N1

namespace N2
  definition foo (a : nat) := a
end N2

open N1 N2

definition boo := foo
