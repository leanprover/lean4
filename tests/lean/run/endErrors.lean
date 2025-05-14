/-! # `end` command errors

This file assesses the error messages produced by the `end` command.
-/

/--
error: Invalid `end`: There is no current scope to end

Note: scopes are introduced using `namespace` and `section`
-/
#guard_msgs in
end

namespace A.B.C
/--
error: Missing name at `end`: The current scope is named 'C', but a name was not provided

Hint: To close the innermost scope 'C', specify its name:
  end ̲C̲
-/
#guard_msgs in
end

/--
error: Name mismatch at `end`: Expected the current scope name
  B.C
or some final part thereof, but found
  A.B

Hint: If you meant to end the outer scope(s) 'A.B', you must end the full intervening scopes 'A.B.C':
  end A.B.̲C̲
-/
#guard_msgs in
end A.B

/--
error: Name mismatch at `end`: Expected the current scope name
  C
but found
  Irrelevant
-/
#guard_msgs in
end Irrelevant

section

/--
error: Unexpected name after `end`: The current section is unnamed, but found the name
  C

Hint: Delete the name 'C' to end the current unnamed scope, then close any named scopes using an additional `end` command:
  end ̵C̵
-/
#guard_msgs in
end C
