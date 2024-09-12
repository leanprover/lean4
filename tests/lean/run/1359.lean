
/-- info: 42 = Nat.zero : Prop -/
#guard_msgs in
#check (by exact 42) = Nat.zero -- invalid 'by' tactic, expected type has not been provided

/-- info: 42 + 1 : Nat -/
#guard_msgs in
#check (by exact 42) + 1 -- invalid 'by' tactic, expected type has not been provided
