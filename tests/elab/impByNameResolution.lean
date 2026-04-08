--

namespace Foo

def f (x : Nat) : Nat := x + 1

@[implemented_by f] opaque g : Nat → Nat

end Foo
