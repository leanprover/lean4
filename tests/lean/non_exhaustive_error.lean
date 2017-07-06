
def g : ℕ × ℕ → ℕ
| (0, n) := n
| (m+2, 0) := m

definition f : string → nat → bool
| "hello world" 1 := tt
| "bye"         _ := tt

def foo (y : ℕ) : ℕ → ℕ → ℕ
| 0     a     := a
| (x+1) 0     := 3 + foo x 10
| (x+1) (n+2) := 42

namespace other

mutual def f, g
with f : nat → nat → nat
| 0 0 := 1
with g : nat → nat → nat
| 0 0 := 1

end other