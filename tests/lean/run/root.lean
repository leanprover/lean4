import standard
using num

variable foo : Bool

namespace N1
  variable foo : Bool
  check N1.foo
  check _root_.foo
  namespace N2
    variable foo : Bool
    check N1.foo
    check N1.N2.foo
    print raw foo
    print raw _root_.foo
  end
end



