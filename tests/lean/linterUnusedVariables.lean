import Lean

set_option linter.missingDocs false
set_option linter.all true

def explicitlyUsedVariable (x : Nat) : Nat :=
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

def letRecVariable : Nat :=
  let rec x := 5
  3

def whereVariable : Nat :=
  3
where
  x := 5 -- x is globally available via `whereVariable.x`

def unusedWhereArgument : Nat :=
  f 2
where
  f (x : Nat) := 3

def whereFunction : Nat :=
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

set_option linter.unusedVariables.analyzeTactics true in
set_option linter.unusedVariables.patternVars false in
theorem nolintPatternVarsInduction (n : Nat) : True := by
  induction n with
  | zero => exact True.intro
  | succ m =>
    have h : True := by simp
    exact True.intro


inductive Foo (α : Type)
  | foo (x : Nat) (y : Nat)

structure Bar (α : Type) where
  bar (x : Nat) : Nat
  bar' (x : Nat) : Nat := 3

class Baz (α : Type) where
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


opaque foo (x : Nat) : Nat
opaque foo' (x : Nat) : Nat :=
  let y := 5
  3

section
variable (bar)
variable (bar' : (x : Nat) → Nat)
variable {α β} [inst : ToString α]
end

@[specialize]
def specializeDef (x : Nat) : Nat := 3

@[implemented_by specializeDef]
def implementedByDef (x : Nat) : Nat :=
  let y := 3
  5

@[extern "test"]
def externDef (x : Nat) : Nat :=
  let y := 3
  5

@[extern "test"]
opaque externConst (x : Nat) : Nat :=
  let y := 3
  5

section
variable {α : Type}

macro "useArg " name:declId arg:ident : command => `(def $name ($arg : α) : α := $arg)
useArg usedMacroVariable a

macro (name := doNotUse) "doNotUseArg " name:declId arg:ident : command =>
  `(def $name ($arg : α) : Nat := 3)
doNotUseArg unusedMacroVariable b

@[unused_variables_ignore_fn]
def ignoreDoNotUse : Lean.Linter.IgnoreFunction := fun _ stack _ => stack.matches [``doNotUse]

doNotUseArg unusedMacroVariable2 b
end

macro "ignoreArg " id:declId sig:declSig : command => `(opaque $id $sig)
ignoreArg ignoredMacroVariable (x : UInt32) : UInt32


theorem not_eq_zero_of_lt (h : b < a) : a ≠ 0 := by -- *not* unused
  cases a
  exact absurd h (Nat.not_lt_zero _)
  apply Nat.noConfusion

-- should not be reported either
example (a : Nat) : Nat := _
example (a : Nat) : Nat := sorry
example (a : sorry) : Nat := 0
example (a : Nat) : Nat := by

theorem Fin.eqq_of_val_eq {n : Nat} : ∀ {x y : Fin n}, x.val = y.val → x = y
  | ⟨_, _⟩, _, rfl => rfl

def Nat.discriminate (n : Nat) (H1 : n = 0 → α) (H2 : ∀ m, n = succ m → α) : α :=
  match n with
  | 0 => H1 rfl
  | succ m => H2 m rfl

/-! These are *not* linted against anymore as they are parameters used in the eventual body term. -/
example [ord : Ord β] (f : α → β) (x y : α) : Ordering := compare (f x) (f y)
example {α β} [ord : Ord β] (f : α → β) (x y : α) : Ordering := compare (f x) (f y)
example {h : Decidable True} (t e : α) : ite True t e = t := if_pos trivial

inductive A where
  | intro : Nat → A

def A.out : A → Nat
  | .intro n => n

/-! `h` is used indirectly via an alias introduced by `match` that is used only via the mvar ctx -/
theorem problematicAlias (n : A) (i : Nat) (h : i ≤ n.out) : i ≤ n.out :=
  match n with
  | .intro _ => by assumption

/-!
The wildcard pattern introduces a copy of `x` that should not be linted as it is in an
inaccessible annotation.
-/
example : (x = y) → y = x
  | .refl _ => .refl _

/-! We do lint parameters by default (`analyzeTactics false`) even when they have lexical uses -/

theorem lexicalTacticUse (p : α → Prop) (ha : p a) (hb : p b) : p b := by
  simp [ha, hb]

/-!
... however, `analyzeTactics true` consistently takes lexical uses for all variables into account
-/

set_option linter.unusedVariables.analyzeTactics true in
theorem lexicalTacticUse' (p : α → Prop) (ha : p a) (hb : p b) : p b := by
  simp [ha, hb]
