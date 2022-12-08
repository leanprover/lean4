def f (x : Nat) : IO Unit := do
  match x with
  | 0 | 1 => IO.println "0 or 1"
  | _ => IO.println "greater than 1"

#eval f 0
#eval f 1
#eval f 2

def g (x : Nat) : IO Unit :=
  match x with
  | 0 | 1 => IO.println "0 or 1"
  | _ => IO.println "greater than 1"

#eval g 0
#eval g 1
#eval g 2

def h (x : Nat) : Nat :=
  match x with
  | 0 | 1 => 1
  | x + 2 => x + 1

example : h x > 0 := by
  match x with
  | 0 | 1 => decide
  | x + 2 => simp [h, Nat.add_succ]; simp_arith

inductive StrOrNum where
  | S (s : String)
  | I (i : Int)

def StrOrNum.asString (x : StrOrNum) :=
  match x with
  | I a | S a => toString a
