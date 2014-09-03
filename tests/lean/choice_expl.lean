namespace N1
  definition pr {A : Type} (a b : A) := a
end N1

namespace N2
  definition pr {A : Type} (a b : A) := b
end N2

open N1 N2
variable N : Type.{1}
variables a b : N
check @pr
check @pr N a b
check pr a b
