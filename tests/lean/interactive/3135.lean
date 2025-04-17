/-!
# Loose docstrings
-/

/-!
Basic test
-/

section
/-- This is a loose docstring -/
--^ collectDiagnostics
end

section
/-- This is a loose docstring before an 'in' command. -/
--^ collectDiagnostics
set_option pp.all true in
def x := 0

-- Still elaborates the `def`
#check x
     --^ textDocument/hover
end

section
set_option pp.all true in
/-- This is a docstring in its correct position. -/
def y := 0
end
