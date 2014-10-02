namespace N1
  definition pr {A : Type} (a b : A) := a
end N1

namespace N2
  definition pr {A : Type} (a b : A) := b
end N2

open N1 N2
constant N : Type.{1}
constants a b : N
check @pr
check @pr N a b
check pr a b
