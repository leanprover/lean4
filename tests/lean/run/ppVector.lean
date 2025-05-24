/-- info: #v[] : Vector Nat 0 -/
#guard_msgs in
#check (#v[] : Vector Nat 0)

/-- info: #v[1, 2, 3] : Vector Nat 3 -/
#guard_msgs in
#check #v[1, 2, 3]

variable (a : Nat) (h : 3 = a)

-- do we want to keep this
/-- info: #v[1, 2, 3] : Vector Nat a -/
#guard_msgs in
#check (⟨#[1, 2, 3], h⟩ : Vector Nat a)
