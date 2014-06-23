variable N : Type.{1}
precedence `+`:65

namespace foo
  variable a : N
  variable f : N → N → N
  infix + := f
end

namespace bla
  variable b : N
  variable f : N → N → N
  infix + := f
end

variable g : N → N → N

using foo
using bla
print raw a + b -- + is overloaded, it creates a choice
print raw #foo a + b   -- + is not overloaded, we are parsing inside #foo
print raw g (#foo a + b) (#bla a + b) -- mixing both


