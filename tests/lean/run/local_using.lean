constant N : Type.{1}
precedence `+`:65

namespace foo
  constant a : N
  constant f : N → N → N
  infix + := f
end foo

namespace bla
  constant b : N
  constant f : N → N → N
  infix + := f
end bla

constant g : N → N → N

open foo
open bla
print raw a + b -- + is overloaded, it creates a choice
print raw #foo a + b   -- + is not overloaded, we are parsing inside #foo
print raw g (#foo a + b) (#bla a + b) -- mixing both
