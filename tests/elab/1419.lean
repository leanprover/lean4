def Foo := Nat
def Foo.pow (x : Nat) (k : Nat) : Foo :=
  match k with
  | 0 => x
  | k+1 => pow x k

instance : Pow Foo Nat := ⟨Foo.pow⟩

example (x : Foo) : x ^ 2048 = x := by
  show Foo.pow x 2048 = x
  sorry
