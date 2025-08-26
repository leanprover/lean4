module

public axiom testSorry : α

/-! Module docstring -/

/-- A definition (not exposed). -/
public def f := 1

/--
info: def f : Nat :=
1
-/
#guard_msgs in
#print f

/-- A definition (exposed) -/
@[expose] public def fexp := 1

/--
info: @[expose] def fexp : Nat :=
1
-/
#guard_msgs in
#print fexp

/-- An abbrev (auto-exposed). -/
public abbrev fabbrev := 1

/--
info: @[reducible, expose] def fabbrev : Nat :=
1
-/
#guard_msgs in
#print fabbrev

#guard_msgs(drop warning) in
/-- A theorem. -/
public theorem t : f = 1 := testSorry

/-- A private definition. -/
def fpriv := 1

/--
error: Unknown identifier `fpriv`

Note: A private declaration `fpriv` (from this module) exists but is not accessible in the current context.
-/
#guard_msgs in
public theorem tpriv : fpriv = 1 := rfl

public class X

/-- A local instance of a public class. -/
instance : X := ⟨⟩

-- Check that the theorem types are checked in exported context, where `f` is not defeq to `1`
-- (but `fexp` is)

/--
error: Type mismatch
  y
has type
  Vector Unit 1
but is expected to have type
  Vector Unit f
-/
#guard_msgs in
public theorem v (x : Vector Unit f) (y : Vector Unit 1) : x = y := testSorry

theorem v' (x : Vector Unit f) (y : Vector Unit 1) : x = y := testSorry

theorem v'' (x : Vector Unit fexp) (y : Vector Unit 1) : x = y := testSorry

-- Check that rfl theorems are complained about if they aren't rfl in the context of their type

/--
error: Not a definitional equality: the left-hand side
  f
is not definitionally equal to the right-hand side
  1

Note: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.
-/
#guard_msgs in
public theorem trfl : f = 1 := rfl
/--
error: Not a definitional equality: the left-hand side
  f
is not definitionally equal to the right-hand side
  1

Note: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.
-/
#guard_msgs in
@[defeq] public theorem trfl' : f = 1 := (rfl)

theorem trflprivate : f = 1 := rfl
def trflprivate' : f = 1 := rfl
@[defeq] def trflprivate''' : f = 1 := rfl
theorem trflprivate'''' : f = 1 := (rfl)

public theorem fexp_trfl : fexp = 1 := rfl
@[defeq] public theorem fexp_trfl' : fexp = 1 := rfl

public opaque P : Nat → Prop
public axiom hP1 : P 1

/-- error: `dsimp` made no progress -/
#guard_msgs in
example : P f := by dsimp only [t]; exact hP1
example : P f := by simp only [t]; exact hP1

/-- error: `dsimp` made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl]; exact hP1
/-- error: `dsimp` made no progress -/
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
@[defeq] public theorem not_rfl : f = 2 := testSorry

def priv := 2

/-! Private decls should not be accessible in exported contexts. -/

/--
error: Unknown identifier `priv`

Note: A private declaration `priv` (from this module) exists but is not accessible in the current context.
-/
#guard_msgs in
public abbrev h := priv


/-! Equational theorems tests. -/

public def f_struct : Nat → Nat
| 0 => 0
| n + 1 => f_struct n
termination_by structural n => n

public def f_wfrec : Nat → Nat → Nat
| 0, acc => acc
| n + 1, acc => f_wfrec n (acc + 1)
termination_by n => n

@[expose] public def f_exp_wfrec : Nat → Nat → Nat
| 0, acc => acc
| n + 1, acc => f_exp_wfrec n (acc + 1)
termination_by n => n

@[inline] protected def Test.Option.map (f : α → β) : Option α → Option β
  | some x => some (f x)
  | none   => none


/-- error: `f.eq_def` is a reserved name -/
#guard_msgs in
public def f.eq_def := 1

/-- error: `fexp.eq_def` is a reserved name -/
#guard_msgs in
public def fexp.eq_def := 1

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

/-! Private fields should force private ctors. -/

abbrev Priv := Nat

public structure StructWithPrivateField where
  private x : Priv

/--
info: structure StructWithPrivateField : Type
number of parameters: 0
fields:
  private StructWithPrivateField.x : Priv
constructor:
  private StructWithPrivateField.mk (x : Priv) : StructWithPrivateField
-/
#guard_msgs in
#print StructWithPrivateField

#check { x := 1 : StructWithPrivateField }

/-- error: invalid {...} notation, constructor for `StructWithPrivateField` is marked as private -/
#guard_msgs in
#with_exporting
#check { x := 1 : StructWithPrivateField }

#check StructWithPrivateField.x

/-- error: Unknown constant `StructWithPrivateField.x` -/
#guard_msgs in
#with_exporting
#check StructWithPrivateField.x

/-! Private constructors should be compatible with public fields. -/

public structure StructWithPrivateCtor where private mk ::
  x : Nat

/--
info: structure StructWithPrivateCtor : Type
number of parameters: 0
fields:
  StructWithPrivateCtor.x : Nat
constructor:
  private StructWithPrivateCtor.mk (x : Nat) : StructWithPrivateCtor
-/
#guard_msgs in
#print StructWithPrivateCtor

/-- error: invalid {...} notation, constructor for `StructWithPrivateCtor` is marked as private -/
#guard_msgs in
#with_exporting
#check { x := 1 : StructWithPrivateCtor }

#with_exporting
#check StructWithPrivateCtor.x

#check StructWithPrivateCtor.mk

/-- error: Unknown constant `StructWithPrivateCtor.mk` -/
#guard_msgs in
#with_exporting
#check StructWithPrivateCtor.mk

/-! Private duplicate in public section should not panic. -/

public section

private def foo : Nat := 0
/-- error: private declaration `foo` has already been declared -/
#guard_msgs in
private def foo : Nat := 0

end

/-! Check visibility of auto params. -/

public structure OptParamStruct where
  private pauto : Nat := by exact 0
  auto : Nat := by exact 0

/--
info: structure OptParamStruct : Type
number of parameters: 0
fields:
  private OptParamStruct.pauto : Nat := by
    exact 0
  OptParamStruct.auto : Nat := by
    exact 0
constructor:
  private OptParamStruct.mk (pauto : Nat := by exact 0) (auto : Nat := by exact 0) : OptParamStruct
-/
#guard_msgs in
#print OptParamStruct

section
set_option pp.oneline true
/--
info: private def OptParamStruct.pauto._autoParam : Lean.Syntax :=
Lean.Syntax.node Lean.SourceInfo.none `Lean.Parser.Tactic.tacticSeq [...]
-/
#guard_msgs in
#print OptParamStruct.pauto._autoParam
/--
info: @[expose] def OptParamStruct.auto._autoParam : Lean.Syntax :=
Lean.Syntax.node Lean.SourceInfo.none `Lean.Parser.Tactic.tacticSeq [...]
-/
#guard_msgs in
#print OptParamStruct.auto._autoParam
end
