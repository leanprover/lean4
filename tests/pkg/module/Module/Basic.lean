module

meta import Init.Dynamic
meta import Init.System.IO
public import Lean.PrettyPrinter.Delaborator.Basic
public meta import Lean.PrettyPrinter.Delaborator.Basic

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

/-- A non-exposed function type. -/
public def Fun := Nat → Nat

/-! The compiler should check it has sufficient information about types available. -/

/--
error: Compilation failed, locally inferred compilation type differs from type that would be inferred in other modules. Some of the following definitions may need to be `@[expose]`d to fix this mismatch: ⏎
  Fun ↦ 1
This is a current compiler limitation for `module`s that may be lifted in the future.
-/
#guard_msgs in
public def Fun.mk (f : Nat → Nat) : Fun := f

#guard_msgs(drop warning) in
/-- A theorem. -/
public theorem t : f = 1 := testSorry

/-- A private definition. -/
def fpriv := 1

public section
/-- Examples are always private. -/
example : fpriv = 1 := rfl

/--
error: Unknown identifier `fpriv`

Note: A private declaration `fpriv` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
/-- ...unless explicitly marked `public`. -/
public example : fpriv = 1 := rfl
end

/--
error: Unknown identifier `fpriv`

Note: A private declaration `fpriv` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
public theorem tpriv : fpriv = 1 := rfl

/-! Type inference should not be able to smuggle out private references. -/

/--
error: Unknown constant `_private.Module.Basic.0.fpriv`

Note: A private declaration `fpriv` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
public def inferredPrivRef := (rfl : fpriv = 1)

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

Note: The following definitions were not unfolded because their definition is not exposed:
  f ↦ 1
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

/-- A private definition. -/
def priv := 2

/-! Private decls should not be accessible in exported contexts. -/

/--
error: Unknown identifier `priv`

Note: A private declaration `priv` (from the current module) exists but would need to be public to access here.
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

/-- info: @[defeq] private theorem f_wfrec.eq_1 : ∀ (x : Nat), f_wfrec 0 x = x -/
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

/-- info: @[defeq] theorem f_exp_wfrec.eq_1 : ∀ (x : Nat), f_exp_wfrec 0 x = x -/
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

#check (⟨1⟩ : StructWithPrivateField)

/--
error: Invalid `⟨...⟩` notation: Constructor for `StructWithPrivateField` is marked as private
-/
#guard_msgs in
#with_exporting
#check (⟨1⟩ : StructWithPrivateField)

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
info: private meta def OptParamStruct.pauto._autoParam : Lean.Syntax :=
Lean.Syntax.node Lean.SourceInfo.none `Lean.Parser.Tactic.tacticSeq [...]
-/
#guard_msgs in
#print OptParamStruct.pauto._autoParam
/--
info: @[expose] meta def OptParamStruct.auto._autoParam : Lean.Syntax :=
Lean.Syntax.node Lean.SourceInfo.none `Lean.Parser.Tactic.tacticSeq [...]
-/
#guard_msgs in
#print OptParamStruct.auto._autoParam
end

/-! `deriving` should derive `meta` defs on `meta` structures. -/
meta structure Foo where
deriving TypeName

/--
info: private meta def instTypeNameFoo : TypeName Foo :=
inst✝
-/
#guard_msgs in
#print instTypeNameFoo

public meta def pubMeta := 1

/-! `#eval` should accept `meta` and non-`meta`. -/

meta def fmeta := 1

/-- info: 2 -/
#guard_msgs in
#eval f + fmeta

/-! Prop `instance`s should have direct access to the private scope. -/

public class PropClass : Prop where
  proof : True

theorem privTrue : True := trivial
public instance : PropClass := ⟨privTrue⟩

/-! Meta defs should only be exposed explicitly. -/

@[expose] section
public meta def msec := 1
@[expose] public meta def msecexp := 1
end

/--
info: meta def msec : Nat :=
<not imported>
-/
#guard_msgs in
#with_exporting
#print msec

/--
info: @[expose] meta def msecexp : Nat :=
1
-/
#guard_msgs in
#with_exporting
#print msecexp

attribute [simp] f_struct

/-! `[inherit_doc]` should work independently of visibility. -/

@[inherit_doc priv] public def pubInheritDoc := 1

/-! `initialize` should be run even if imported IR-only. -/

public initialize initialized : Nat ← pure 5

/-! Error message on private dot notation access. -/

public structure S

def S.s := 1

/--
error: Invalid field `s`: The environment does not contain `S.s`, so it is not possible to project the field `s` from an expression
  s
of type `S`

Note: A private declaration `S.s` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
@[expose] public def useS (s : S) := s.s

/- `meta` should trump `noncomputable`. -/

noncomputable section
/-- error: Invalid `meta` definition `m`, `S.s` not marked `meta` -/
#guard_msgs in
meta def m := S.s
end

-- setup for `Imported`
public meta def delab : Lean.PrettyPrinter.Delaborator.Delab :=
  default

public def noMetaDelab : Lean.PrettyPrinter.Delaborator.Delab :=
  default

/-- error: Cannot make suggestions for private names -/
#guard_msgs in
@[suggest_for Bar1]
def FooBar1 := 4

/-- error: Cannot make suggestions for private names -/
#guard_msgs in
@[suggest_for Bar2]
meta def FooBar2 := 4

#guard_msgs in
@[suggest_for Bar3 FooBar1 FooBar2]
public def FooBar3 := 4

/-- #11672: Check that `by` creates aux theorems with correct type in presence of opaque defs. -/

@[no_expose] public def five : Nat := 5

public class A where
  a : five = 5
  b : Nat

public instance : A where
  a := by rfl
  b := 0

-- should NOT be `five = five`, which is not a valid proof of `A.a` in the public scope
/--
info: theorem instA._proof_1 : five = 5 :=
Eq.refl five
-/
#guard_msgs in
#print instA._proof_1

/-- Setup for #11715. -/

public structure OpOperand2 where
  nextUse : Option Nat

public def func (ctx : Nat) (operand : OpOperand2) : Nat :=
  match operand.nextUse with
  | none => ctx
  | some nextPtr => ctx
