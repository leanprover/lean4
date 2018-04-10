--
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

inductive term | mk : ℕ → list term → term

def const_name : term → ℕ
| (term.mk n []) := n

namespace other2
def f : nat → nat
| 1000 := 1

def g : string → nat
| "hello" := 0

meta def h : name → nat
| `eq := 0

def r : int → nat
| -1000 := 0
end other2
