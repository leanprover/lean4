def thunk1 : Thunk String := "foo"

/-- info: "foo" -/
#guard_msgs in
#eval let ⟨fn⟩ := thunk1; fn ()

/-- info: "foo" -/
#guard_msgs in
#eval (thunk1.casesOn id () : String)

def thunk2 : Thunk String := "bar"

/-- info: "bar" -/
#guard_msgs in
#eval (thunk2.casesOn id () : String)

/-- info: "bar" -/
#guard_msgs in
#eval let ⟨fn⟩ := thunk2; fn ()

def task1 : Task String := Task.pure "foo"

/-- info: "foo" -/
#guard_msgs in
#eval let ⟨v⟩ := task1; v

/-- info: "foo" -/
#guard_msgs in
#eval (task1.casesOn id : String)

def task2 : Task String := Task.pure "bar"

/-- info: "bar" -/
#guard_msgs in
#eval (task2.casesOn id : String)

/-- info: "bar" -/
#guard_msgs in
#eval let ⟨v⟩ := task2; v
