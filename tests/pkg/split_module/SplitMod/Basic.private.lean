module

-- An import that only the implementation needs.
import SplitMod.Impl

-- Full header.
def f (n : Nat) : Nat := n + implOffset

-- Typeless forms take the declared type.
theorem f_pos := by
  intro n
  unfold f implOffset
  omega

theorem f_succ (n : Nat) := by
  simp only [f]
  omega

def h := fun {α} [Inhabited α] (xs : List α) => xs.headD default

section
variable (k : Nat)
def addK (n : Fin k) : Nat := n + k + privHelper
end

private theorem implOnly : f 0 = 1 := rfl
