import Lean.Util.Trace

set_option linter.all true

def explicitelyUsedVariable (x : Nat) : Nat :=
  x

theorem implicitlyUsedVariable : P ∧ Q → Q := by
  intro HPQ
  have HQ : Q := by exact And.right HPQ
  assumption

axiom axiomVariable (x : Prop) : True

def unusedVariables (x : Nat) : Nat :=
  let y := 5
  3

def usedAndUnusedVariables : Nat :=
  let x : Nat :=
    let x := 5
    3
  x

def unusedWhereVariable : Nat :=
  3
where
  x := 5

def unusedWhereArgument : Nat :=
  f 2
where
  f (x : Nat) := 3

def unusedWhereFunction : Nat :=
  2
where
  f (x : Nat) := 3

def unusedFunctionArgument : Nat :=
  (fun x => 3) (x := 2)

def unusedTypedFunctionArgument : Nat :=
  (fun (x : Nat) => 3) 2

def pattern (x y : Option Nat) : Nat :=
  match x with
  | some z =>
    match y with
    | some z => 1
    | none => 0
  | none => 0

def patternLet (x : Option Nat) : Nat :=
  if let some y := x then
    0
  else
    1

def patternMatches (x : Option Nat) : Nat :=
  if x matches some y then
    0
  else
    1

def implicitVariables {α : Type} [inst : ToString α] : Nat := 4

def autoImplicitVariable [Inhabited α] := 5

def unusedArrow : (x : Nat) → Nat := fun x => x

def mutVariable (x : Nat) : Nat := Id.run <| do
  let mut y := 5
  if x == 5 then
    y := 3
  y

def mutVariableDo (list : List Nat) : Nat := Id.run <| do
  let mut sum := 0
  for elem in list do
    sum := sum + elem
  return sum

def mutVariableDo2 (list : List Nat) : Nat := Id.run <| do
  let mut sum := 0
  for _ in list do
    sum := sum.add 1
  return sum


def unusedVariablesPattern (_x : Nat) : Nat :=
  let _y := 5
  3

set_option linter.unusedVariables false in
def nolintUnusedVariables (x : Nat) : Nat :=
  let y := 5
  3

set_option linter.all false in
def nolintAll (x : Nat) : Nat :=
  let y := 5
  3

set_option linter.all false in
set_option linter.unusedVariables true in
def lintUnusedVariables (x : Nat) : Nat :=
  let y := 5
  3


set_option linter.unusedVariables.funArgs false in
def nolintFunArgs (w : Nat) : Nat :=
  let a := 5
  let f (x : Nat) := 3
  let g := fun (y : Nat) => 3
  f <| g <| h <| 2
where
  h (z : Nat) := 3

set_option linter.unusedVariables.patternVars false in
def nolintPatternVars (x : Option (Option Nat)) : Nat :=
  match x with
  | some (some y) => (fun z => 1) 2
  | _ => 0


inductive Foo (α : Type)
  | foo (x : Nat) (y : Nat)

structure Bar (α : Type) where
  bar (x : Nat) : Nat
  bar' (x : Nat) : Nat := 3

class Baz (_ : Type) where
  baz (x : Nat) : Nat
  baz' (x : Nat) : Nat :=
    let y := 5
    3

instance instBaz (α β : Type) : Baz α where
  baz (x : Nat) := 5


structure State where
  fieldA : Nat
  fieldB : Nat

abbrev M := StateT State Id

def modifyState : M Unit := do
  let s ← get
  modify fun s => { s with fieldA := s.fieldA + 1 }

def modifyState' : M Unit := do
  modify fun s => { s with fieldA := 1}

def modifyStateUnnecessaryWith : M Unit := do
  modify fun s => { s with fieldA := 1, fieldB := 2 }


def universeParam.{u} (T : Type u) (t : T) : T := t


open Lean in
initialize tc : Unit ← registerTraceClass `Baz

register_option opt : Nat := {
  defValue := 3
  descr := "test option"
}


constant foo (x : Nat) : Nat
constant foo' (x : Nat) : Nat :=
  let y := 5
  3
variable (bar)
variable (bar' : (x : Nat) → Nat)
variable {α β} [inst : ToString α]

@[specialize]
def specializeDef (x : Nat) : Nat := 3

@[implementedBy specializeDef]
def implementedByDef (x : Nat) : Nat :=
  let y := 3
  5

@[extern "test"]
def externDef (x : Nat) : Nat :=
  let y := 3
  5

@[extern "test"]
constant externConst (x : Nat) : Nat :=
  let y := 3
  5
