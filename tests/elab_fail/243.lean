def f : (α : Type) × α → Nat
 | ⟨Bool, true⟩ => 1
 | _ => 2

namespace Foo

inductive A where
  | a | b

open A (a b)

def g : (α : Type) × α → Nat
 | ⟨A, a⟩ => 1
 | _ => 2

end Foo
