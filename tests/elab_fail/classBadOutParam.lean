
class C1 (x : outParam Nat) (y : { n : Nat // n > x }) (α : Type) := -- should fail
(val : α)

class C2 (x : outParam Nat) (y : outParam { n : Nat // n > x }) (α : Type) := -- should work
(val : α)
