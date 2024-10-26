/-!
# Tests for recursive structures
-/

/-- error: Recursive structures are not yet supported. -/
#guard_msgs in
structure A1 where
  xs : List A1
