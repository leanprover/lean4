set_option debug.byAsSorry true in
/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem ex1 (h : b = a) : a = b := by
  rw [h]

/--
-/
#guard_msgs in
theorem ex2 (h : b = a) : a = b := by
  rw [h]

set_option debug.byAsSorry true in
/-- -/
#guard_msgs in
def f (x : Nat) : Nat := by
  exact x + 1 -- must not become a sorry since expected type is data

set_option debug.byAsSorry true in
/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
def g (x : Nat) : { x : Nat // x > 0 } :=
  ⟨by exact x + 1, by omega⟩

example : (g x).1 = x + 1 := by
  rfl
