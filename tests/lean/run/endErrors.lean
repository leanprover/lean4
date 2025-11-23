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
error: Missing name after `end`: Expected the current scope name `C`

Hint: To end the current scope `C`, specify its name:
  end ̲C̲
-/
#guard_msgs in
end

/--
error: Invalid name after `end`: Expected `B.C`, but found `A.B`

Hint: If you meant to end the outer scope(s) `A.B`, you must end all the intervening scopes `A.B.C`:
  end A.B.̲C̲
-/
#guard_msgs in
end A.B

-- Ensure that we don't suggest including `«»` to get to an enclosing scope
section
namespace D

/-- error: Invalid name after `end`: Expected `D`, but found `A.B` -/
#guard_msgs in
end A.B

end D
end

/--
error: Invalid name after `end`: Expected `C`, but found `Irrelevant`

Note: The current scopes are `A.B.C`
-/
#guard_msgs in
end Irrelevant

section

/--
error: Unexpected name `C` after `end`: The current section is unnamed

Hint: Delete the name `C` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵C̵
-/
#guard_msgs in
end C

end

/--
error: Invalid name after `end`: `D.E.F.G` contains too many components

Hint: The name after `end` must be `A.B.C` or some suffix thereof
-/
#guard_msgs in
end D.E.F.G

end B.C

/--
error: Invalid name after `end`: Expected `A`, but found `Z`

Hint: Use current scope name `A`:
  end Z̵A̲
-/
#guard_msgs in
end Z

/--
error: Invalid name after `end`: `X.Y.Z` contains too many components

Hint: Use current scope name `A`:
  end X̵.̵Y̵.̵Z̵A̲
-/
#guard_msgs in
end X.Y.Z
