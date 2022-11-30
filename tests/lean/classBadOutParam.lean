
class C1 (x : OutParam Nat) (y : { n : Nat // n > x }) (α : Type) := -- should fail
(val : α)

class C2 (x : OutParam Nat) (y : OutParam { n : Nat // n > x }) (α : Type) := -- should work
(val : α)
