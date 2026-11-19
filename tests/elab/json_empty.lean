import Lean

/-!
# Validation of `Json Empty` instance

This test serves a similar purpose to the `Repr Empty` test in `repr_empty.lean`.
-/

structure Foo (α : Type) where
  y : Option α
deriving Lean.ToJson, Lean.FromJson, Repr

/-! First, two basic examples with α not-Empty -/
/-- info: {"y": 1} -/
#guard_msgs in
#eval Lean.toJson (⟨some 1⟩ : Foo Nat)

/-! Ensure we can parse the type back -/
/-- info: Except.ok { y := some 1 } -/
#guard_msgs in
#eval Lean.fromJson? (α := Foo Nat) <| json% {"y": 1}

/-- info: {"y": null} -/
#guard_msgs in
#eval Lean.toJson (⟨none⟩ : Foo Nat)

/-- info: Except.ok { y := none } -/
#guard_msgs in
#eval Lean.fromJson? (α := Foo Nat) <| json% {"y": null}

/-! Examples with the `Empty` type -/
/-- info: {"y": null} -/
#guard_msgs in
#eval Lean.toJson (⟨none⟩ : Foo Empty)

/-! Show that we can round-trip from string  -/
/-- info: Except.ok { y := none } -/
#guard_msgs in
#eval Lean.fromJson? (α := Foo Empty) <| json% {"y": null}

/-! Show that parsing fails -/
/-- info: Except.error "type Empty has no constructor to match JSON value '\"Yo!\"'.
This occurs when deserializing a value for type Empty, e.g. at type Option Empty with code
for the 'some' constructor." -/
#guard_msgs in
#eval Lean.fromJson? (α := Empty) <| json% "Yo!"

/-! Show that parsing fails if we supply anything else but `null` -/
/-- info: Except.error "Foo.y: type Empty has no constructor to match JSON value '1'.
This occurs when deserializing a value for type Empty, e.g. at type Option Empty with code
for the 'some' constructor." -/
#guard_msgs in
#eval Lean.fromJson? (α := Foo Empty) <| json% {"y": 1}
