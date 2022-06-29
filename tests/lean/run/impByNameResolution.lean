--

namespace Foo

def f (x : Nat) : Nat := x + 1

@[implementedBy f] opaque g : Nat → Nat

end Foo
