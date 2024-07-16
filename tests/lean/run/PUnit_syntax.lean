/-- info: Bool ×ₚ Nat ×ₚ List Unit : Type -/
#guard_msgs in
#check Bool ×ₚ Nat ×ₚ List Unit

/-- info: Bool ×ₚ Nat ×ₚ List Unit : Type -/
#guard_msgs in
#check PProd Bool (PProd Nat (List Unit))

/-- info: (Bool ×ₚ Nat) ×ₚ List Unit : Type -/
#guard_msgs in
#check PProd (PProd Bool Nat) (List Unit)

/-- info: Bool ×ₘ Nat ×ₘ List Unit : Type -/
#guard_msgs in
#check Bool ×ₘ Nat ×ₘ List Unit

/-- info: Bool ×ₘ Nat ×ₘ List Unit : Type -/
#guard_msgs in
#check MProd Bool (MProd Nat (List Unit))

/-- info: (Bool ×ₘ Nat) ×ₘ List Unit : Type -/
#guard_msgs in
#check MProd (MProd Bool Nat) (List Unit)

/-- info: PUnit.unit : PUnit -/
#guard_msgs in
#check ()ₚ

/-- info: (true, 5, [()])ₚ : Bool ×ₚ Nat ×ₚ List Unit -/
#guard_msgs in
#check (true, 5, [()])ₚ

/-- info: (true, 5, [()])ₘ : Bool ×ₘ Nat ×ₘ List Unit -/
#guard_msgs in
#check (true, 5, [()])ₘ

/-- info: (true, 5, [()])ₚ : Bool ×ₚ Nat ×ₚ List Unit -/
#guard_msgs in
#check PProd.mk true (PProd.mk 5 [()])

/-- info: (true, 5, [()])ₘ : Bool ×ₘ Nat ×ₘ List Unit -/
#guard_msgs in
#check MProd.mk true (MProd.mk 5 [()])

/-- info: PUnit.unit.{u} : PUnit -/
#guard_msgs in
#check PUnit.unit
