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

section
variable {β : Type _} (q : β → Prop) (hq : ∀ b, q b)
include hq

theorem allQ (b : β) : q b := hq b
end

theorem addZero : (n : Nat) → n + 0 = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (addZero n)
termination_by n => n

-- Not exported, unlike in a single-file module.
structure Impl where
  x : Nat
deriving Repr
