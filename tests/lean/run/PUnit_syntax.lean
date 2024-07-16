/-- info: Bool ×' Nat ×' List Unit : Type -/
#guard_msgs in
#check Bool ×' Nat ×' List Unit

/-- info: Bool ×' Nat ×' List Unit : Type -/
#guard_msgs in
#check PProd Bool (PProd Nat (List Unit))

/-- info: (Bool ×' Nat) ×' List Unit : Type -/
#guard_msgs in
#check PProd (PProd Bool Nat) (List Unit)

/-- info: PUnit.{u} : Sort u -/
#guard_msgs in
#check PUnit

/-- info: ⟨true, ⟨5, [()]⟩⟩ : Bool ×' Nat ×' List Unit -/
#guard_msgs in
#check (⟨true, 5, [()]⟩ : Bool ×' Nat ×' List Unit)

/-- info: ⟨true, ⟨5, [()]⟩⟩ : MProd Bool (Nat ×' List Unit) -/
#guard_msgs in
#check (⟨true, 5, [()]⟩ : MProd Bool (PProd Nat (List Unit)))

/-- info: ⟨true, ⟨5, [()]⟩⟩ : Bool ×' Nat ×' List Unit -/
#guard_msgs in
#check PProd.mk true (PProd.mk 5 [()])

/-- info: ⟨true, ⟨5, [()]⟩⟩ : MProd Bool (MProd Nat (List Unit)) -/
#guard_msgs in
#check MProd.mk true (MProd.mk 5 [()])

/-- info: PUnit.unit.{u} : PUnit -/
#guard_msgs in
#check PUnit.unit
