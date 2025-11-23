
example : True := by dsimp? [trivial,]
example : True := by dsimp? only [trivial,]
example : True := by simp? [trivial,]
example : True := by simp? only [trivial,]
example : True := by simpa [trivial,]
example : True := by simpa only [trivial,]
example : True := by simpa [trivial,] using trivial
example : True := by simpa only [trivial,] using trivial
