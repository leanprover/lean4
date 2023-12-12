/-!
Test that PackMutual isn't confused when a recursive call has more arguments than is packed
into the unary argument, which can happen if the retturn type is a function type.
-/

namespace Ex1
mutual
def foo : Nat → Nat
  | .zero => 0
  | .succ n => (id bar) n
def bar : Nat → Nat
  | .zero => 0
  | .succ n => foo n
end
termination_by foo n => n; bar n => n
decreasing_by sorry

end Ex1

-- Same for n-ary functions

opaque id' : ∀ {α}, α → α := id

namespace Ex2

mutual
def foo : Nat → Nat → Nat
  | .zero, _m => 0
  | .succ n, .zero => (id' (bar n)) .zero
  | .succ n, m => (id' bar) n m
def bar : Nat → Nat → Nat
  | .zero, _m => 0
  | .succ n, m => foo n m
end
termination_by foo n m => (n,m); bar n m => (n,m)
decreasing_by sorry

end Ex2

-- With extra arguments

namespace Ex3
mutual
def foo : Nat → Nat → Nat
  | .zero => fun _ => 0
  | .succ n => fun m => (id bar) n m
def bar : Nat → Nat → Nat
  | .zero => fun _ => 0
  | .succ n => fun m => foo n m
end
termination_by foo n => n; bar n => n
decreasing_by sorry

end Ex3

-- n-ary and with extra arguments

namespace Ex4

mutual
def foo : Nat → Nat → Nat → Nat
  | .zero, _m => fun _ => 0
  | .succ n, .zero => fun k => (id' (bar n)) .zero k
  | .succ n, m => fun k => (id' bar) n m k
def bar : Nat → Nat → Nat → Nat
  | .zero, _m => fun _ => 0
  | .succ n, m => fun k => foo n m k
end
termination_by foo n m => (n,m); bar n m => (n,m)
decreasing_by sorry

end Ex4

-- Check that eta-expansion works even if the function does not
-- have a function type
namespace Ex5
def FunType := Nat → Nat

mutual
def foo : FunType
  | .zero => 0
  | .succ n => (id bar) n
def bar : Nat → Nat
  | .zero => 0
  | .succ n => foo n
end
termination_by foo n => n; bar n => n
decreasing_by sorry

end Ex5


namespace Ex6
def Fun3Type := Nat → Nat → Nat

mutual
def foo : Nat → Nat → Nat → Nat
  | .zero, _m => fun _ => 0
  | .succ n, .zero => fun k => (id' (bar n)) .zero k
  | .succ n, m => fun k => (id' bar) n m k
def bar : Nat → Fun3Type
  | .zero, _m => fun _ => 0
  | .succ n, m => fun k => foo n m k
end
termination_by foo n m => (n,m); bar n m => (n,m)
decreasing_by sorry

end Ex6
