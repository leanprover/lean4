import data.nat
using nat

namespace N1
  definition foo (a : nat) := a
end N1

namespace N2
  definition foo (a : nat) := a
end N2

using N1 N2

definition boo := foo