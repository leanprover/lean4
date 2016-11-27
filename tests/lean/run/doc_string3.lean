/-!
Documentation header for test module
-/

/-- Documentation for x -/
def x := 10

namespace foo
/-!
  Another block of documentation
  for this example.
-/

/-- Documentation for y -/
def y := 20

end foo

/-!
  Documentation footer
  testing
-/

open tactic
run_command module_doc_strings >>= trace
