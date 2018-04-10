/- Thunk gadget works with overloaded functions -/
namespace foo

def f (a : nat) (b : thunk nat) : nat :=
a + b ()

end foo

namespace boo

def f (a : bool) (b : bool) : bool :=
a && b

end boo

namespace bla

def f (a : bool) (b : thunk nat) : nat :=
if a then b() else 42

end bla

open foo boo bla

example : f 10 10 = 20 :=
rfl

example : f 10 10 = foo.f 10 10 :=
rfl

example : f tt tt = tt :=
rfl

example : f tt tt = boo.f tt tt :=
rfl

example : f tt 10 = 10 :=
rfl

example : f tt 10 = bla.f tt 10 :=
rfl
