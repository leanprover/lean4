attribute [-simp] Nat.self_eq_add_right -- This was later added to the simp set and interfere with the test.

def foo : Nat := 0
def bar : Nat := 0

@[simp] theorem foo_eq_bar : foo = bar := rfl

example : foo = bar := by simp [← foo_eq_bar]
example : foo = bar + 1 := by
  simp [← foo_eq_bar]
  guard_target =ₛ foo = foo + 1
  sorry

def a : Nat := 0
def b : Nat := 0
def c : Nat := 0

@[simp] theorem abc : a = b ∧ a = c := And.intro rfl rfl

example : a = b := by simp [← abc]
example : a = c := by simp [← abc]
example : a = c + 1 := by
  simp [← abc]
  guard_target =ₛ a = a + 1
  sorry

opaque d : Nat
opaque e : Nat
@[simp↓] theorem de : d = e := sorry

example : d = e := by simp [← de]
example : d = e := by simp [↓←de]
example : d = e + 1 := by
  simp [↓←de]
  guard_target =ₛ d = d + 1
  sorry
