

namespace Foo

def f (x : Nat) : Nat := x + 1

@[implementedBy f] constant g : Nat → Nat

end Foo
