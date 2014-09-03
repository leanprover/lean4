import logic

namespace N1
  variable num : Type.{1}
  variable foo : num → num → num
end N1

namespace N2
  variable val : Type.{1}
  variable foo : val → val → val
end N2

open N1
open N2
variables a b : num
variable f : num → val
coercion f

definition aux2 := foo a b
check aux2
theorem T3 : aux2 = N1.foo a b
:= refl _
