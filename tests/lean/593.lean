namespace Foo

def Bar.bar : Nat := 1

export Bar (bar)

def boo := 2

end Foo

namespace Baz

#check Foo.bar

open Foo in
#check bar

section Ex1
open Foo (bar)
#check bar
#check boo -- should fail
end Ex1

section Ex2
open Foo hiding bar
#check bar -- should fail
#check boo
end Ex2

section Ex2
open Foo renaming bar → bah
#check bah
end Ex2

export Foo (bar)
export Foo.Bar (bar)
#check bar

end Baz
