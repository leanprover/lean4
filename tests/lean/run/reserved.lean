-- `g.eq_def` is not reserved yet
theorem g.eq_def : 1 + x = x + 1 := Nat.add_comm ..

/--
error: failed to declare `g` because `g.eq_def` has already been declared
-/
#guard_msgs (error) in
def g (x : Nat) := x + 1

def f (x : Nat) := x + 1

/--
error: 'f.eq_def' is a reserved name
-/
#guard_msgs (error) in
theorem f.eq_def : f x = x + 1 := rfl

/--
error: 'f.eq_1' is a reserved name
-/
#guard_msgs (error) in
theorem f.eq_1 : f x = x + 1 := rfl

def f.eq_2_ := 10 -- Should be ok

/-- info: f.eq_1 (x : Nat) : f x = x + 1 -/
#guard_msgs in
#check f.eq_1

/-- error: unknown identifier 'f.eq_2' -/
#guard_msgs (error) in
#check f.eq_2

/-- info: f.eq_def (x : Nat) : f x = x + 1 -/
#guard_msgs in
#check f.eq_def

def nonrecfun : Bool → Nat
  | false => 0
  | true => 0

/--
info: nonrecfun.eq_def (x✝ : Bool) :
  nonrecfun x✝ =
    match x✝ with
    | false => 0
    | true => 0
-/
#guard_msgs in
#check nonrecfun.eq_def

/-- info: nonrecfun.eq_1 : nonrecfun false = 0 -/
#guard_msgs in
#check nonrecfun.eq_1

/-- info: nonrecfun.eq_2 : nonrecfun true = 0 -/
#guard_msgs in
#check nonrecfun.eq_2

def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

/--
info: fact.eq_def (x✝ : Nat) :
  fact x✝ =
    match x✝ with
    | 0 => 1
    | n.succ => (n + 1) * fact n
-/
#guard_msgs in
#check fact.eq_def

/-- info: fact.eq_1 : fact 0 = 1 -/
#guard_msgs in
#check fact.eq_1

/-- info: fact.eq_2 (n : Nat) : fact n.succ = (n + 1) * fact n -/
#guard_msgs in
#check fact.eq_2

/-- error: unknown identifier 'fact.eq_3' -/
#guard_msgs (error) in
#check fact.eq_3

def fact' : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact' n

example : fact' 0 + fact' 0 = 2 := by
  simp [fact'.eq_1]

example : fact' 0 + fact' 1 = 2 := by
  rw [fact'.eq_1]
  guard_target =ₛ 1 + fact' 1 = 2
  rw [fact'.eq_2]
  guard_target =ₛ 1 + (0+1) * fact' 0 = 2
  rw [fact'.eq_1]

example : fact' 0 + fact' 1 = 2 := by
  rw [fact'.eq_def, fact'.eq_def]; simp
  guard_target =ₛ 1 + fact' 0 = 2
  rw [fact'.eq_def]
  guard_target =
    (1 + fact.match_1 (fun _ => Nat) 0 (fun _ => 1) fun n => (n + 1) * fact' n) = 2
  simp

theorem bla : 0 = 0 := rfl

def bla.def := 1 -- should work since `bla` is a theorem
def bla.eq_1 := 2 -- should work since `bla` is a theorem

def find (as : Array Int) (i : Nat) (v : Int) : Nat :=
  if _ : i < as.size then
    if as[i] = v then
      i
    else
      find as (i+1) v
  else
    i

/--
info: find.eq_def (as : Array Int) (i : Nat) (v : Int) :
  find as i v = if x : i < as.size then if as[i] = v then i else find as (i + 1) v else i
-/
#guard_msgs in
#check find.eq_def

/--
info: find.eq_1 (as : Array Int) (i : Nat) (v : Int) :
  find as i v = if x : i < as.size then if as[i] = v then i else find as (i + 1) v else i
-/
#guard_msgs in
#check find.eq_1
