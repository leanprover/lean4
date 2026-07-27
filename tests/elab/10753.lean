/-!
# Structure instance notation should not use defaults in patterns

https://github.com/leanprover/lean4/issues/10753
-/

/-!
In the following, it used to be that the `{ b := bv }` pattern was matching
`{ b := bv, a := 0 }`, which was confusing.
-/

structure Test where
  a : Nat := 0
  b : Nat

/-- error: Fields missing: `a` -/
#guard_msgs in
def test1 (t : Test) : Nat :=
  match t with
  | { b := bv } => bv

def test2 (t : Test) : Nat :=
  match t with
  | { b := bv, .. } => bv

/-- info: 2 -/
#guard_msgs in #eval test2 { a := 1, b := 2 }

/-!
Check pretty printing: in a pattern, we can't assume we can omit default values.
We can of course omit them outside of patterns.
-/

def test3 (t : Test) : Test :=
  match t with
  | { b := bv, a := 0 } => { b := bv }
  | _ => t

/--
info: def test3 : Test → Test :=
fun t =>
  match t with
  | { a := 0, b := bv } => { b := bv }
  | x => t
-/
#guard_msgs in #print test3
