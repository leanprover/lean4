@[simp] theorem Array.size_singleton : #[a].size = 1 := rfl
@[simp] theorem USize.not_size_le_one : ¬ USize.size ≤ 1 := by cases usize_size_eq <;> simp [*]

def f := #[true].any id 0 USize.size

-- `native_decide` used to prove `false` here, due to a bug in `Array.anyMUnsafe`.
example : f = true := by native_decide

example : f = true := by simp [f, Array.any, Array.anyM]
