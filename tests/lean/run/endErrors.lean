/-! # `end` command errors

This file assesses the error messages produced by the `end` command.
-/

/--
error: Invalid `end`: There is no current scope to end

Note: Scopes are introduced using `namespace` and `section`
-/
#guard_msgs in
end

namespace A.B.C
/--
error: Missing name after `end`: The current scope is named 'C', but a name was not provided

Hint: To end the current scope 'C', specify its name:
  end ̲C̲
-/
#guard_msgs in
end

/--
error: Name 'A.B' does not match the current scope(s) 'A.B.C': Expected 'B.C' or some other suffix of the current scope(s)

Hint: If you meant to end the outer scope(s) 'A.B', you must end all the intervening scopes 'A.B.C':
  end A.B.̲C̲
-/
#guard_msgs in
end A.B

-- Ensure that we don't suggest including `«»` to get to an enclosing scope
section
namespace D

/-- error: Name 'A.B' does not match the current scope(s) 'D': Expected 'D' -/
#guard_msgs in
end A.B

end D
end

/--
error: Name 'Irrelevant' does not match the current scope(s) 'A.B.C': Expected 'C' or some other suffix of the current scope(s)
-/
#guard_msgs in
end Irrelevant

section

/--
error: Unexpected name 'C' after `end`: The current section is unnamed`

Hint: Delete the name 'C' to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵C̵
-/
#guard_msgs in
end C

end

/--
error: Invalid name after `end`: The provided name 'D.E.F.G' contains too many components; expected 'A.B.C' or some suffix thereof
-/
#guard_msgs in
end D.E.F.G
