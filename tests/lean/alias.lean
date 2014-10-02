import logic

namespace N1
  constant num : Type.{1}
  constant foo : num → num → num
end N1

namespace N2
  constant val : Type.{1}
  constant foo : val → val → val
end N2

open N2
open N1
constants a b : num
print raw foo a b
open N2
print raw foo a b
open N1
print raw foo a b
open N1
print raw foo a b
open N2
print raw foo a b
