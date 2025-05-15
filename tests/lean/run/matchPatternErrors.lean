/-! # Errors in match patterns

This file tests various error messages in invalid match patterns.
-/

/--
error: Invalid match expression: This pattern contains metavariables:
  []
-/
#guard_msgs in
def List.len x :=
  match x with
  | [] => 0
  | _ :: xs => 1 + len xs

/--
error: Invalid pattern: Not enough arguments to 'cons'; expected 2 explicit arguments

Hint: To elide all remaining arguments, use the ellipsis notation `..`
-/
#guard_msgs in
def List.empty : List α → Bool
  | nil => true
  | cons x => false

/--
error: Invalid pattern variable: Variable name must be atomic, but 'x.y' has multiple components
-/
#guard_msgs in
def compVarName : Unit × Unit → Unit
  | (_, x.y) => x.y

/--
error: Redundant alternative: Any expression matching
  x✝¹, x✝
will match one of the preceding alternatives
-/
#guard_msgs in
def redundantMatch (T : Type) (P : Prop) :=
  match (motive := Type → Prop → Bool) T, P with
  | Nat, True => true
  | _, _ => false

def matchExplicitValid (n : Nat) :=
  match n with
  | @Nat.zero => 1
  | _ => 0

/--
error: Invalid pattern: Expected an identifier in function position, but found
  fun x => x
-/
#guard_msgs in
def matchFun : Nat → Nat
  | (fun x => x) 31 => false

/--
error: Invalid pattern: Not enough arguments to 'List.nil'; expected 1 argument

Hint: To elide all remaining arguments, use the ellipsis notation `..`
-/
#guard_msgs in
def insufficientExplicit (xs : List Nat) :=
  match xs with
  | @List.nil => True
  | _ => false

/-- error: Invalid argument names 'invalidName1' and 'invalidName2' for function 'List.cons' -/
#guard_msgs in
def invalidArgNames (xs : List Nat) :=
  match xs with
  | List.cons (invalidName1 := x) (invalidName2 := y) .. => true
  | _ => false

/-- error: Invalid pattern variable: Variable name 'xs' was already used -/
#guard_msgs in
def dupVar (xs : List Nat) : List Nat :=
  match xs with
  | List.cons xs xs => true
  | _ => false
