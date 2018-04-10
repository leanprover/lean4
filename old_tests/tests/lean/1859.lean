prelude
class T1 (α : Type) := (O : Type)
class T2 (α : Type) extends T1 α
class T3 (α : Type) extends T1 α
class A (α : Type) [T1 α] := (x : T1.O α)
class B (α : Type) [T3 α] extends A α
def X {α : Type} [T2 α] : A α := sorry
example {α : Type} [T3 α] : B α := { X with }
