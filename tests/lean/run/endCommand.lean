/-!
# Tests for the `end` command

These all rely on the fact that `end` always drops scopes even when validation fails.
-/

/-!
Ending a section
-/
section A
end A

/-!
Ending an anonymous section
-/
section
end

/-!
Error: ending an named section anonymously
-/
section A
/-- error: invalid 'end', name is missing (expected A) -/
#guard_msgs in
end

/-!
Error: ending an named section with the wrong name
-/
section A
/-- error: invalid 'end', name mismatch (expected A) -/
#guard_msgs in
end B

/-!
Error: ending an anonymous section with a name
-/
section
/-- error: invalid 'end', name mismatch (expected nothing) -/
#guard_msgs in
end A

/-!
Ending a namespace
-/
namespace A
end A

/-!
Error: ending a namespace anonymously
-/
namespace A
/-- error: invalid 'end', name is missing (expected A) -/
#guard_msgs in
end

/-!
Error: ending a namespace with the wrong name
-/
namespace A
/-- error: invalid 'end', name mismatch (expected A) -/
#guard_msgs in
end B

/-!
Error: ending outside a scope
-/
/-- error: invalid 'end', insufficient scopes -/
#guard_msgs in
end

/-!
Error: ending too many scopes
-/
namespace A.B
/-- error: invalid 'end', insufficient scopes -/
#guard_msgs in
end X.A.B

/-!
Ending two sections at once
-/
section A.B
end A.B

/-!
Ending sections separately
-/
section A.B
end B
end A

/-!
Ending two namespaces at once
-/
namespace A.B
end A.B

/-!
Ending namespaces separately
-/
namespace A.B
end B
end A

/-!
Error: ending mixed section/namespace at once
-/
section A.B
namespace C.D
/-- error: invalid 'end', mixed ending of namespace C.D and section B -/
#guard_msgs in
end A.B.C.D

/-!
Error: ending mixed namespace/section at once
-/
namespace A.B
section C.D
/-- error: invalid 'end', mixed ending of section C.D and namespace B -/
#guard_msgs in
end A.B.C.D
