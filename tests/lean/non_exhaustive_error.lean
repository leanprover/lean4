
def g : ℕ × ℕ → ℕ
| (0, n) := n
| (m+2, 0) := m

definition f : string → nat → bool
| "hello world" 1 := tt
| "bye"         _ := tt
