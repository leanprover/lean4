module

/-! test native equality on ByteArray  -/

def mk (xs : Array UInt8) : ByteArray := ⟨xs⟩


/-- info: true -/
#guard_msgs in
#eval mk #[] == mk #[]
/-- info: true -/
#guard_msgs in
#eval mk #[1, 2, 3, 4, 5] == mk #[1, 2, 3, 4, 5]

/-- info: true -/
#guard_msgs in
#eval mk #[1] != mk #[]
/-- info: true -/
#guard_msgs in
#eval mk #[] != mk #[1]
/-- info: true -/
#guard_msgs in
#eval mk #[1, 2, 3, 4, 5] != mk #[0, 2, 3, 4, 5]
/-- info: true -/
#guard_msgs in
#eval mk #[0, 2, 3, 4, 5] != mk #[1, 2, 3, 4, 5]
/-- info: true -/
#guard_msgs in
#eval mk #[1, 2, 3, 4, 5] != mk #[1, 2, 3, 0, 5]
/-- info: true -/
#guard_msgs in
#eval mk #[1, 2, 3, 0, 5] != mk #[1, 2, 3, 4, 5]


/-- info: true -/
#guard_msgs in
#eval mk #[] = mk #[]
/-- info: true -/
#guard_msgs in
#eval mk #[1, 2, 3, 4, 5] = mk #[1, 2, 3, 4, 5]

/-- info: true -/
#guard_msgs in
#eval mk #[1] ≠ mk #[]
/-- info: true -/
#guard_msgs in
#eval mk #[] ≠ mk #[1]
/-- info: true -/
#guard_msgs in
#eval mk #[1, 2, 3, 4, 5] ≠ mk #[0, 2, 3, 4, 5]
/-- info: true -/
#guard_msgs in
#eval mk #[0, 2, 3, 4, 5] ≠ mk #[1, 2, 3, 4, 5]
/-- info: true -/
#guard_msgs in
#eval mk #[1, 2, 3, 4, 5] ≠ mk #[1, 2, 3, 0, 5]
/-- info: true -/
#guard_msgs in
#eval mk #[1, 2, 3, 0, 5] ≠ mk #[1, 2, 3, 4, 5]
