/-! # Errors in match patterns

This file tests various error messages that arise from missing, extra, uninferrable, or otherwise
erroneous arguments in match patterns.
-/

inductive T where
  | exp (a b c : Nat)
  | imp {a b c : Nat}
  | mix {a b : Nat} (c : Nat)

/-- error: Invalid pattern: Too many arguments to 'exp'; expected 3 explicit arguments -/
#guard_msgs in
def T.mixNamedPositional₁ : T → Unit
  | exp (b := x) y z w => ()
  | _ => ()

/-- error: Invalid pattern: Too many arguments to 'imp'; expected 0 explicit arguments -/
#guard_msgs in
def T.mixNamedPositional₂ : T → Unit
  | imp (a := x) y => ()
  | _ => ()

/--
error: Invalid pattern: Not enough arguments to 'imp'; expected 3 arguments

Hint: To ignore all remaining arguments, use the ellipsis notation `..`
-/
#guard_msgs in
def T.mixNamedPositional₃ : T → Unit
  | @imp (a := x) y => ()
  | _ => ()

/-- error: Invalid pattern: Too many arguments to 'mix'; expected 1 explicit argument -/
#guard_msgs in
def T.mixNamedPositional₄ : T → Unit
  | mix (b := x) y z => ()
  | _ => ()

def matchExplicitValid (n : Nat) :=
  match n with
  | @Nat.zero => ()
  | _ => ()

/--
error: Invalid argument names `invalidName1` and `invalidName2` for function `List.cons`

Hint: This function has the following named parameters: `α`, `head`, and `tail`
-/
#guard_msgs in
def invalidArgNames (xs : List Nat) :=
  match xs with
  | List.cons (invalidName1 := x) (invalidName2 := y) .. => true
  | _ => false

inductive T' where
  | mk (argNum1 : Nat) (otherArg : List String)

/--
error: Invalid argument names `argNo1` and `otherArgs` for function `T'.mk`

Hint: This function has the following named parameters: `argNum1` and `otherArg`. These are similar:
  • a̵r̵g̵N̵o̵1̵a̲r̲g̲N̲u̲m̲1̲
  • otherArgs̵
-/
#guard_msgs in
def argNameHints (t : T') :=
  match t with
  | T'.mk (argNo1 := k) (otherArgs := ss) => (k, ss)

/-- error: Invalid pattern variable: Variable name 'xs' was already used -/
#guard_msgs in
def dupVar (xs : List Nat) : List Nat :=
  match xs with
  | List.cons xs xs => true
  | _ => false

/--
error: Invalid pattern variable: Variable name must be atomic, but 'x.y' has multiple components
-/
#guard_msgs in
def compVarName : Unit × Unit → Unit
  | (_, x.y) => x.y

/--
error: Invalid match expression: This pattern contains metavariables:
  []
-/
#guard_msgs in
def List.len x :=
  match x with
  | [] => 0
  | _ :: xs => 1 + len xs
