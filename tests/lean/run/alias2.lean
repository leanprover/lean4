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
constant f : num → val
attribute f [coercion]

definition aux2 := foo a b
check aux2
theorem T3 : aux2 = N1.foo a b
:= eq.refl _
