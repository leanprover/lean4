import Std.Data.HashMap

/-! Test some basic behavior related to `inline` discovered in #12334 -/

#guard_msgs in
def foo {n : Nat} (m : Std.HashMap Nat (Fin n)) : Std.HashMap Nat (Fin (n + 1)) :=
  m.map <| inline fun _ ↦ Fin.castSucc

/-- error: `inline` applied to parameters is invalid -/
#guard_msgs in
def params (n : Nat) : Nat := inline n

#guard_msgs in
def inlineLocal {n : Nat} (m : Std.HashMap Nat (Fin n)) : Std.HashMap Nat (Fin (n + 1)) :=
  inline <| foo m

/-- error: `inline` applied to constructor 'List.cons' is invalid -/
#guard_msgs in
def inlineCtor (x : Nat) (xs : List Nat) := inline <| List.cons x xs

/-- error: `inline` applied to non-local declaration 'Lean.Name.mkStr3' is invalid -/
#guard_msgs in
def inlineNonLocal (s1 s2 s3 : String) :=
  inline <| Lean.Name.mkStr3 s1 s2 s3
