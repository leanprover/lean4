/-!
Tests for the `DecidableEq Float` and `BEq Float` instances
-/

/-- info: false -/
#guard_msgs in
#eval 0.1 == 0.2

/-- info: true -/
#guard_msgs in
#eval 0.1 == 0.1

/-- info: true -/
#guard_msgs in
#eval 0.1 == 0.100000000000000001

/-- info: true -/
#guard_msgs in
#eval 0.0 == -0.0

/-- info: false -/
#guard_msgs in
#eval (0.0 / 0.0) == (0.0 / 0.0)

/-- info: false -/
#guard_msgs in
#eval 0.1 = 0.2

/-- info: true -/
#guard_msgs in
#eval 0.1 = 0.1

/-- info: true -/
#guard_msgs in
#eval 0.1 = 0.100000000000000001

/-- info: false -/
#guard_msgs in
#eval 0.0 = -0.0

/-- info: true -/
#guard_msgs in
#eval (0.0 / 0.0) = (0.0 / 0.0)
