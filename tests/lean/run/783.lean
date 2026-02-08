structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

/-- info: { α := Nat, β := Bool, a := 10, b := true } : MyStruct -/
#guard_msgs in
#check { a := 10, b := true : MyStruct }
