inductive SomeType
| x : SomeType

namespace SomeType

def a : SomeType := SomeType.x

end SomeType

#eval SomeType.b

def f (x : Nat) :=
  x.z
