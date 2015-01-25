import logic

namespace N1
  constant num : Type.{1}
  constant foo : num → num → num
end N1

namespace N2
  constant val : Type.{1}
  constant foo : val → val → val
end N2

open N1
open N2
constants a b : num
constants x y : val


check foo a b
check foo x y

constant f : num → val
attribute f [coercion]

check foo a x
check foo x y
check foo x a

check foo a b
theorem T1 : foo a b = N1.foo a b
:= eq.refl _

definition aux1 := foo a b  -- System elaborated it to N1.foo a b
#erase_cache T2
theorem T2 : aux1 = N1.foo a b
:= eq.refl _

open N1
definition aux2 := foo a b  -- Now N1 is in the end of the queue, this is elaborated to N2.foo (f a) (f b)
check aux2

theorem T3 : aux2 = N2.foo (f a) (f b)
:= eq.refl aux2


check foo a b
theorem T4 : foo a b = N2.foo a b
:= eq.refl _
