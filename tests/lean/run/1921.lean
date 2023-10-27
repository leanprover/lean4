@[simp] theorem Array.size_singleton : #[a].size = 1 := rfl
@[simp] theorem USize.not_size_le_one : ¬ USize.size ≤ 1 := by cases usize_size_eq <;> simp [*]

def f := #[true].any id 0 USize.size

-- `native_decide` used to prove `false` here, due to a bug in `Array.anyMUnsafe`.
example : f = true := by native_decide

-- (config := { zeta := true }) solves everything here, but I wouldn't expect "application type mismatch"
-- here, so I am worried something isn't right. on master this instead gives "unsolved goals".
example : f = true := by simp [f, Array.any, Array.anyM]
