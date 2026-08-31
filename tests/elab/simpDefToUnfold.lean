@[simp] def f (x : Nat) := x + 1

@[simp] def g (x : Nat) := id x

def h (x : Nat) := g (g x)

namespace Extra
  attribute [scoped simp] h
end Extra

theorem ex1 : f (g (h x)) = x + 1 := by
  simp -- did not unfold h
  simp [h]

theorem ex2 : f (g (h x)) = x + 1 := by
  open Extra in simp -- unfold f,g,h

theorem ex3 : f (g x) = x + 1 := by
  simp [-f] -- did not unfold f
  simp
