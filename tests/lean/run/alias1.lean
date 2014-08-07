import logic

namespace N1
  variable num : Type.{1}
  variable foo : num → num → num
end N1

namespace N2
  variable val : Type.{1}
  variable foo : val → val → val
end N2

using N1
using N2
variables a b : num
variables x y : val


check foo a b
check foo x y

variable f : num → val
coercion f

check foo a x
check foo x y
check foo x a

check foo a b
theorem T1 : foo a b = N1.foo a b
:= refl _

definition aux1 := foo a b  -- System elaborated it to N2.foo (f a) (f b)
theorem T2 : aux1 = N2.foo (f a) (f b)
:= refl _

using N1
definition aux2 := foo a b  -- Now N1 is in the beginning of the queue again, and this is elaborated to N1.foo a b
check aux2

theorem T3 : aux2 = N1.foo a b
:= refl aux2


check foo a b
theorem T4 : foo a b = N1.foo a b
:= refl _
