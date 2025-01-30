prelude
import Init.Data.List.Basic

@[tree_tac]
theorem a : [1, 2] ++ [3] = [1, 2, 3] := rfl

@[tree_tac]
theorem b : [1, 2, 3].length = 3 := sorry

example : ([1, 2] ++ [3]).length = 3 := by simp only [tree_tac]
