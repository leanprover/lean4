/-!
# Tests of delaborator 'safe shadowing' feature
-/

set_option linter.unusedVariables false

def f (x x : Nat) :=
  match x with
  | 0          => x + 1
  | Nat.succ _ => x + 2

def f' :=
  fun (x : Nat) => id fun (x : Nat) =>
    match x with
    | 0          => x + 1
    | Nat.succ _ => x + 2

variable {α : Type}

/-- info: fun a => a : α → α -/
#guard_msgs in
#check fun (a : α) => a

/-- info: fun {α} a => a : {α : Sort u_1} → α → α -/
#guard_msgs in
#check fun {α} (a : α) => a

/-!
This would be safe shadowing, but since it's in the same `fun` it is confusing to have repeated variable names.
-/
/-- info: fun x x_1 => x_1 : Nat → Nat → Nat -/
#guard_msgs in
#check fun (x x : Nat) => x

/-!
Splitting up the `fun`, safe shadowing applies again.
-/
/-- info: fun x => id fun x => x : Nat → Nat → Nat -/
#guard_msgs in
#check fun (x : Nat) => id fun (x : Nat) => x

/-!
Same lambda, no safe shadowing.
-/
/--
info: def f : Nat → Nat → Nat :=
fun x x_1 =>
  match x_1 with
  | 0 => x_1 + 1
  | n.succ => x_1 + 2
-/
#guard_msgs in
#print f

/-!
Split up lambda, uses safe shadowing.
-/
/--
info: def f' : Nat → Nat → Nat :=
fun x =>
  id fun x =>
    match x with
    | 0 => x + 1
    | n.succ => x + 2
-/
#guard_msgs in
#print f'

/-!
The within-same-fun safe shadowing suppression does not take outer `let` into account.
-/
/--
info: let x := 1;
fun x x_1 => x_1 : Nat → Nat → Nat
-/
#guard_msgs in
#check let x := 1; fun (x x : Nat) => x

set_option pp.safeShadowing false

/-- info: fun {α_1} a => a : {α_1 : Sort u_1} → α_1 → α_1 -/
#guard_msgs in
#check fun {α} (a : α) => a

/-- info: fun x x_1 => x_1 : Nat → Nat → Nat -/
#guard_msgs in
#check fun (x x : Nat) => x

/--
info: def f : Nat → Nat → Nat :=
fun x x_1 =>
  match x_1 with
  | 0 => x_1 + 1
  | n.succ => x_1 + 2
-/
#guard_msgs in
#print f

/--
info: def f' : Nat → Nat → Nat :=
fun x =>
  id fun x_1 =>
    match x_1 with
    | 0 => x_1 + 1
    | n.succ => x_1 + 2
-/
#guard_msgs in
#print f'
