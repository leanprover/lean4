open tactic

example : 0 < 1 := by comp_val
example : 0 < 2 := by comp_val
example : 0 < 3 := by comp_val
example : 0 < 4 := by comp_val
example : 0 < 5 := by comp_val
example : 0 < 6 := by comp_val
example : 0 < 1293821 := by comp_val
example : 0 < 1293822 := by comp_val

example : 1 < 2 := by comp_val
example : 1 < 3 := by comp_val
example : 1 < 4 := by comp_val
example : 1 < 5 := by comp_val
example : 1 < 6 := by comp_val
example : 1 < 1293821 := by comp_val
example : 1 < 1293822 := by comp_val

example : 2 < 3 := by comp_val
example : 2 < 4 := by comp_val
example : 2 < 5 := by comp_val
example : 2 < 6 := by comp_val
example : 2 < 1293821 := by comp_val
example : 2 < 1293822 := by comp_val

example : 3 < 4 := by comp_val
example : 3 < 5 := by comp_val
example : 3 < 6 := by comp_val
example : 3 < 1293821 := by comp_val
example : 3 < 1293822 := by comp_val

example : 4 < 5 := by comp_val
example : 4 < 6 := by comp_val
example : 4 < 1293821 := by comp_val
example : 4 < 1293822 := by comp_val

example : 103093 < 1293821 := by comp_val
example : 3121 < 1293822 := by comp_val
example : 312110028381818 < 1181171711293822 := by comp_val
example : 312110028381819 < 1181171711293822 := by comp_val
example : 312110028381819 < 1181171711293821 := by comp_val

example (h : false) : 0 < 0 := by (try comp_val >> contradiction)
example (h : false) : 1 < 1 := by (try comp_val >> contradiction)
example (h : false) : 120201 < 1 := by (try comp_val >> contradiction)
example (h : false) : 120201 < 32019 := by (try comp_val >> contradiction)
example (h : false) : 120202 < 1 := by (try comp_val >> contradiction)
example (h : false) : 120202 < 32019 := by (try comp_val >> contradiction)
example (h : false) : 120202 < 2 := by (try comp_val >> contradiction)
example (h : false) : 120202 < 3192 := by (try comp_val >> contradiction)


example : 0 ≤ 0 := by comp_val
example : 0 ≤ 1 := by comp_val
example : 0 ≤ 2 := by comp_val
example : 0 ≤ 3 := by comp_val
example : 0 ≤ 4 := by comp_val
example : 0 ≤ 5 := by comp_val
example : 0 ≤ 6 := by comp_val
example : 0 ≤ 1293821 := by comp_val
example : 0 ≤ 1293822 := by comp_val

example : 1 ≤ 1 := by comp_val
example : 1 ≤ 2 := by comp_val
example : 1 ≤ 3 := by comp_val
example : 1 ≤ 4 := by comp_val
example : 1 ≤ 5 := by comp_val
example : 1 ≤ 6 := by comp_val
example : 1 ≤ 1293821 := by comp_val
example : 1 ≤ 1293822 := by comp_val

example : 2 ≤ 2 := by comp_val
example : 2 ≤ 3 := by comp_val
example : 2 ≤ 4 := by comp_val
example : 2 ≤ 5 := by comp_val
example : 2 ≤ 6 := by comp_val
example : 2 ≤ 1293821 := by comp_val
example : 2 ≤ 1293822 := by comp_val

example : 3 ≤ 3 := by comp_val
example : 3 ≤ 4 := by comp_val
example : 3 ≤ 5 := by comp_val
example : 3 ≤ 6 := by comp_val
example : 3 ≤ 1293821 := by comp_val
example : 3 ≤ 1293822 := by comp_val

example : 4 ≤ 4 := by comp_val
example : 4 ≤ 5 := by comp_val
example : 4 ≤ 6 := by comp_val
example : 4 ≤ 1293821 := by comp_val
example : 4 ≤ 1293822 := by comp_val

example : 103093 ≤ 103093 := by comp_val
example : 103093 ≤ 1293821 := by comp_val
example : 3121 ≤ 1293822 := by comp_val
example : 312110028381818 ≤ 1181171711293822 := by comp_val
example : 312110028381819 ≤ 1181171711293822 := by comp_val
example : 312110028381819 ≤ 1181171711293821 := by comp_val

example : 1 ≤ 5 := by comp_val
example : 3 ≤ 5 := by comp_val

example (h : false) : 1 ≤ 0 := by (try comp_val >> contradiction)
example (h : false) : 2 ≤ 1 := by (try comp_val >> contradiction)
example (h : false) : 120201 ≤ 1 := by (try comp_val >> contradiction)
example (h : false) : 120201 ≤ 32019 := by (try comp_val >> contradiction)
example (h : false) : 120202 ≤ 1 := by (try comp_val >> contradiction)
example (h : false) : 120202 ≤ 32019 := by (try comp_val >> contradiction)
example (h : false) : 120202 ≤ 2 := by (try comp_val >> contradiction)
example (h : false) : 120202 ≤ 3192 := by (try comp_val >> contradiction)

example : 0 ≠ 1 := by comp_val
example : 0 ≠ 2 := by comp_val
example : 0 ≠ 3 := by comp_val
example : 0 ≠ 4 := by comp_val
example : 0 ≠ 5 := by comp_val
example : 0 ≠ 6 := by comp_val
example : 0 ≠ 1293821 := by comp_val
example : 0 ≠ 1293822 := by comp_val

example : 1 ≠ 0 := by comp_val
example : 1 ≠ 2 := by comp_val
example : 1 ≠ 3 := by comp_val
example : 1 ≠ 4 := by comp_val
example : 1 ≠ 5 := by comp_val
example : 1 ≠ 6 := by comp_val
example : 1 ≠ 1293821 := by comp_val
example : 1 ≠ 1293822 := by comp_val

example : 2 ≠ 0 := by comp_val
example : 2 ≠ 1 := by comp_val
example : 2 ≠ 3 := by comp_val
example : 2 ≠ 4 := by comp_val
example : 2 ≠ 5 := by comp_val
example : 2 ≠ 6 := by comp_val
example : 2 ≠ 1293821 := by comp_val
example : 2 ≠ 1293822 := by comp_val

example : 3 ≠ 0 := by comp_val
example : 3 ≠ 2 := by comp_val
example : 3 ≠ 1 := by comp_val
example : 3 ≠ 4 := by comp_val
example : 3 ≠ 5 := by comp_val
example : 3 ≠ 6 := by comp_val
example : 3 ≠ 1293821 := by comp_val
example : 3 ≠ 1293822 := by comp_val

example : 4 ≠ 0 := by comp_val
example : 4 ≠ 2 := by comp_val
example : 4 ≠ 3 := by comp_val
example : 4 ≠ 1 := by comp_val
example : 4 ≠ 5 := by comp_val
example : 4 ≠ 6 := by comp_val
example : 4 ≠ 1293821 := by comp_val
example : 4 ≠ 1293822 := by comp_val

example : 5 ≠ 0 := by comp_val
example : 5 ≠ 2 := by comp_val
example : 5 ≠ 3 := by comp_val
example : 5 ≠ 4 := by comp_val
example : 5 ≠ 1 := by comp_val
example : 5 ≠ 6 := by comp_val
example : 5 ≠ 1293821 := by comp_val
example : 5 ≠ 1293822 := by comp_val

example : 103093 ≠ 103095 := by comp_val
example : 103093 ≠ 1293821 := by comp_val
example : 3121 ≠ 1293822 := by comp_val
example : 312110028381818 ≠ 1181171711293822 := by comp_val
example : 312110028381819 ≠ 1181171711293822 := by comp_val
example : 312110028381819 ≠ 1181171711293821 := by comp_val

example (h : false) : 1 ≠ 1 := by (try comp_val >> contradiction)
example (h : false) : 2 ≠ 2 := by (try comp_val >> contradiction)
example (h : false) : 120201 ≠ 120201 := by (try comp_val >> contradiction)
example (h : false) : 32019  ≠ 32019 := by (try comp_val >> contradiction)
example (h : false) : 120202 ≠ 120202 := by (try comp_val >> contradiction)
