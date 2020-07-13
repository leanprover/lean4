new_frontend

namespace Foo

protected def x := 10

end Foo

open Foo
#check x -- error unknown identifier `x`

#check Foo.x

namespace Bla.Foo
protected def y := 20
def z := 30
end Bla.Foo

open Bla
#check Foo.y
open Bla.Foo
#check y -- error unknown identifier `y`
#check z
