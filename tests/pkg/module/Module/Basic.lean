module

axiom testSorry : α

/-! Module docstring -/

/-- A definition (not exposed). -/
def f := 1
/-- An definition (exposed) -/
@[expose] def fexp := 1

#guard_msgs(drop warning) in
/-- A theorem. -/
theorem t : f = 1 := testSorry

-- Check that the theorem types are checked in exported context, where `f` is not defeq to `1`
-- (but `fexp` is)

/--
error: type mismatch
  y
has type
  Vector Unit 1 : Type
but is expected to have type
  Vector Unit f : Type
-/
#guard_msgs in
theorem v (x : Vector Unit f) (y : Vector Unit 1) : x = y := testSorry

private theorem v' (x : Vector Unit f) (y : Vector Unit 1) : x = y := testSorry

private theorem v'' (x : Vector Unit fexp) (y : Vector Unit 1) : x = y := testSorry

-- Check that rfl theorems are complained about if they aren't rfl in the context of their type

/--
error: Not a definitional equality: the left-hand side
  f
is not definitionally equal to the right-hand side
  1

Note: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.
-/
#guard_msgs in
theorem trfl : f = 1 := rfl
/--
error: Not a definitional equality: the left-hand side
  f
is not definitionally equal to the right-hand side
  1

Note: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.
-/
#guard_msgs in
@[defeq] theorem trfl' : f = 1 := (rfl)

private theorem trflprivate : f = 1 := rfl
private def trflprivate' : f = 1 := rfl
@[defeq] private def trflprivate''' : f = 1 := rfl
private theorem trflprivate'''' : f = 1 := (rfl)

theorem fexp_trfl : fexp = 1 := rfl
@[defeq] theorem fexp_trfl' : fexp = 1 := rfl

opaque P : Nat → Prop
axiom hP1 : P 1

/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [t]; exact hP1
example : P f := by simp only [t]; exact hP1

/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl]; exact hP1
/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl']; exact hP1
example : P f := by dsimp only [trflprivate]; exact hP1
example : P f := by dsimp only [trflprivate']; exact hP1


example : P fexp := by dsimp only [fexp_trfl]; exact hP1
example : P fexp := by dsimp only [fexp_trfl]; exact hP1


-- Check that the error message does not mention the export issue if
-- it wouldn’t be a rfl otherwise either

/--
error: Not a definitional equality: the left-hand side
  f
is not definitionally equal to the right-hand side
  2
-/
#guard_msgs in
@[defeq] theorem not_rfl : f = 2 := testSorry

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

/-- info: @[defeq] private theorem f.eq_def : f = 1 -/
#guard_msgs in #print sig f.eq_def

/-- info: @[defeq] private theorem f.eq_unfold : f = 1 -/
#guard_msgs in #print sig f.eq_unfold

/-- info: @[defeq] theorem fexp.eq_def : fexp = 1 -/
#guard_msgs in #print sig fexp.eq_def

/-- info: @[defeq] theorem fexp.eq_unfold : fexp = 1 -/
#guard_msgs in #print sig fexp.eq_unfold

/-- info: @[defeq] private theorem f_struct.eq_1 : f_struct 0 = 0 -/
#guard_msgs in #print sig f_struct.eq_1

/--
info: private theorem f_struct.eq_def : ∀ (x : Nat),
  f_struct x =
    match x with
    | 0 => 0
    | n.succ => f_struct n
-/
#guard_msgs in #print sig f_struct.eq_def

/--
info: private theorem f_struct.eq_unfold : f_struct = fun x =>
  match x with
  | 0 => 0
  | n.succ => f_struct n
-/
#guard_msgs(pass trace, all) in #print sig f_struct.eq_unfold

/-- info: private theorem f_wfrec.eq_1 : ∀ (x : Nat), f_wfrec 0 x = x -/
#guard_msgs(pass trace, all) in #print sig f_wfrec.eq_1

/--
info: private theorem f_wfrec.eq_def : ∀ (x x_1 : Nat),
  f_wfrec x x_1 =
    match x, x_1 with
    | 0, acc => acc
    | n.succ, acc => f_wfrec n (acc + 1)
-/
#guard_msgs in #print sig f_wfrec.eq_def

/--
info: private theorem f_wfrec.eq_unfold : f_wfrec = fun x x_1 =>
  match x, x_1 with
  | 0, acc => acc
  | n.succ, acc => f_wfrec n (acc + 1)
-/
#guard_msgs in #print sig f_wfrec.eq_unfold

/-- info: theorem f_exp_wfrec.eq_1 : ∀ (x : Nat), f_exp_wfrec 0 x = x -/
#guard_msgs in #print sig f_exp_wfrec.eq_1

/--
info: theorem f_exp_wfrec.eq_def : ∀ (x x_1 : Nat),
  f_exp_wfrec x x_1 =
    match x, x_1 with
    | 0, acc => acc
    | n.succ, acc => f_exp_wfrec n (acc + 1)
-/
#guard_msgs in #print sig f_exp_wfrec.eq_def

/--
info: theorem f_exp_wfrec.eq_unfold : f_exp_wfrec = fun x x_1 =>
  match x, x_1 with
  | 0, acc => acc
  | n.succ, acc => f_exp_wfrec n (acc + 1)
-/
#guard_msgs in #print sig f_exp_wfrec.eq_unfold
