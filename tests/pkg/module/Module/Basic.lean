module

/-! Module docstring -/

/-- A definition. -/
def f := 1

#guard_msgs(drop warning) in
/-- A theorem. -/
theorem t : f = 1 := sorry

theorem trfl : f = 1 := rfl

@[expose] def fexp := 1

private def priv := 2

/-! Private decls should not be accessible in exported contexts. -/

/-- error: unknown identifier 'priv' -/
#guard_msgs in
abbrev h := priv


/-! Equational theorems tests. -/

def f_struct : Nat → Nat
| 0 => 0
| n + 1 => f_struct n
termination_by structural n => n

def f_wfrec : Nat → Nat → Nat
| 0, acc => acc
| n + 1, acc => f_wfrec n (acc + 1)
termination_by n => n

@[expose] def f_exp_wfrec : Nat → Nat → Nat
| 0, acc => acc
| n + 1, acc => f_exp_wfrec n (acc + 1)
termination_by n => n

@[inline] protected def Test.Option.map (f : α → β) : Option α → Option β
  | some x => some (f x)
  | none   => none


/-- error: 'f.eq_def' is a reserved name -/
#guard_msgs in
def f.eq_def := 1

/-- error: 'fexp.eq_def' is a reserved name -/
#guard_msgs in
def fexp.eq_def := 1

/-- info: f.eq_def : f = 1 -/
#guard_msgs in
#check f.eq_def

/-- info: f.eq_unfold : f = 1 -/
#guard_msgs in
#check f.eq_unfold

/-- info: fexp.eq_def : fexp = 1 -/
#guard_msgs in
#check fexp.eq_def

/-- info: fexp.eq_unfold : fexp = 1 -/
#guard_msgs in
#check fexp.eq_unfold

/-- info: f_struct.eq_1 : f_struct 0 = 0 -/
#guard_msgs in
#check f_struct.eq_1

/--
info: f_struct.eq_def (x✝ : Nat) :
  f_struct x✝ =
    match x✝ with
    | 0 => 0
    | n.succ => f_struct n
-/
#guard_msgs in
#check f_struct.eq_def

/--
info: f_struct.eq_unfold :
  f_struct = fun x =>
    match x with
    | 0 => 0
    | n.succ => f_struct n
-/
#guard_msgs(pass trace, all) in
#check f_struct.eq_unfold

/-- info: f_wfrec.eq_1 (x✝ : Nat) : f_wfrec 0 x✝ = x✝ -/
#guard_msgs(pass trace, all) in
#check f_wfrec.eq_1

/--
info: f_wfrec.eq_def (x✝ x✝¹ : Nat) :
  f_wfrec x✝ x✝¹ =
    match x✝, x✝¹ with
    | 0, acc => acc
    | n.succ, acc => f_wfrec n (acc + 1)
-/
#guard_msgs in
#check f_wfrec.eq_def

/--
info: f_wfrec.eq_unfold :
  f_wfrec = fun x x_1 =>
    match x, x_1 with
    | 0, acc => acc
    | n.succ, acc => f_wfrec n (acc + 1)
-/
#guard_msgs in
#check f_wfrec.eq_unfold

/-- info: f_exp_wfrec.eq_1 (x✝ : Nat) : f_exp_wfrec 0 x✝ = x✝ -/
#guard_msgs in
#check f_exp_wfrec.eq_1

/--
info: f_exp_wfrec.eq_def (x✝ x✝¹ : Nat) :
  f_exp_wfrec x✝ x✝¹ =
    match x✝, x✝¹ with
    | 0, acc => acc
    | n.succ, acc => f_exp_wfrec n (acc + 1)
-/
#guard_msgs in
#check f_exp_wfrec.eq_def

/--
info: f_exp_wfrec.eq_unfold :
  f_exp_wfrec = fun x x_1 =>
    match x, x_1 with
    | 0, acc => acc
    | n.succ, acc => f_exp_wfrec n (acc + 1)
-/
#guard_msgs in
#check f_exp_wfrec.eq_unfold
