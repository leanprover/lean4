-- works
example : 3 < 5 :=
  calc
    _ < 4 := by decide
    _ < _ := by decide

-- fails
example : 3 < 5 := by
  calc
    _ < 4 := by decide
    _ < _ := by decide
