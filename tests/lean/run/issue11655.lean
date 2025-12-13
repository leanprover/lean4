
inductive T : Bool → Type
| mkTrue  : T true
| mkFalse : T false

/--
error: Type mismatch in pattern: Pattern
  Nat.zero
has type
  Nat
but is expected to have type
  bif x✝² then Nat else List Nat
-/
#guard_msgs in
def test1 : (b : Bool) → (bif b then Nat else List Nat) → T b → Nat
  | .(true), Nat.zero, T.mkTrue  => 1
  | _, _, _ => 0

-- set_option trace.Meta.Match.match true
-- set_option trace.Meta.Match.debug true

/--
error: Failed to compile pattern matching: Expected an inductive type, but found
  match x✝¹ with
  | true => Nat
  | false => List Nat
-/
#guard_msgs in
def test2 : (b : Bool) → T b → (bif b then Nat else List Nat) → Nat
  | .(true), T.mkTrue, Nat.zero  => 1
  | _, _, _ => 0
