
class C1 (x : outParam Nat) (y : { n : Nat // n > x }) (α : Type) where -- should fail
(val : α)

class C2 (x : outParam Nat) (y : outParam { n : Nat // n > x }) (α : Type) where -- should work
(val : α)
