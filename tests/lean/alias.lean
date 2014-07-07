import logic

namespace N1
  variable num : Type.{1}
  variable foo : num → num → num
end

namespace N2
  variable val : Type.{1}
  variable foo : val → val → val
end

using N2
using N1
variables a b : num
print raw foo a b
using N2
print raw foo a b
using N1
print raw foo a b
using N1
print raw foo a b
using N2
print raw foo a b

