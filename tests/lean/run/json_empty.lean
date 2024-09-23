import Lean

/-!
# Validation of `Json Empty` instance

This test serves a similar purpose to the `Repr Empty` test in `repr_empty.lean`.
-/

structure Foo (α : Type) where
  y : Option α
deriving Lean.ToJson, Lean.FromJson, Repr

def fromStrHelper (res : Type) [Lean.FromJson res] (s : String) : Except String res :=
  (Lean.Json.parse s) >>= Lean.fromJson?

/-! First, two basic examples with α not-Empty -/
/-- info: {"y": 1} -/
#guard_msgs in
#eval Lean.toJson (⟨some 1⟩ : Foo Nat)

/-! Ensure we can parse the type back -/
/-- info: Except.ok { y := some 1 } -/
#guard_msgs in
#eval fromStrHelper (Foo Nat) "{\"y\": 1}"

/-- info: {"y": null} -/
#guard_msgs in
#eval Lean.toJson (⟨none⟩ : Foo Nat)

/-- info: Except.ok { y := none } -/
#guard_msgs in
#eval fromStrHelper (Foo Nat) "{\"y\": null}"

/-! Examples with the `Empty` type -/
/-- info: {"y": null} -/
#guard_msgs in
#eval Lean.toJson (⟨none⟩ : Foo Empty)

/-! Show that we can round-trip from string  -/
/-- info: Except.ok { y := none } -/
#guard_msgs in
#eval fromStrHelper (Foo Empty) "{\"y\": null}"

/-! Show that parsing fails -/
/-- info: Except.error "no constructor matched JSON value '\"Yo!\"'" -/
#guard_msgs in
#eval fromStrHelper (Empty) "\"Yo!\""

/-! Show that parsing fails if we supply anything else but `null` -/
/-- info: Except.error "Foo.y: no constructor matched JSON value '1'" -/
#guard_msgs in
#eval fromStrHelper (Foo Empty) "{\"y\": 1}"
