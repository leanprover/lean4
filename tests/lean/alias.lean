import logic

namespace N1
  variable num : Type.{1}
  variable foo : num → num → num
end N1

namespace N2
  variable val : Type.{1}
  variable foo : val → val → val
end N2

open N2
open N1
variables a b : num
print raw foo a b
open N2
print raw foo a b
open N1
print raw foo a b
open N1
print raw foo a b
open N2
print raw foo a b
