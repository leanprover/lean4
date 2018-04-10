open nat

class A := (n : ℕ)

definition f [A] := A.n

structure B extends A :=
(Hf : f = 0)

example : B := ⟨⟨0⟩, rfl⟩

example : B := (| (| 0 |), rfl |)
