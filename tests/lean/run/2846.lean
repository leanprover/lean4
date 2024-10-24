/-!
# `delabConstWithSignature` avoids using inaccessible names
-/

/-!
Defined without named arguments, prints without named arguments.
-/
/-- info: String.append : String → String → String -/
#guard_msgs in #check String.append

/-!
The List argument is not named, it is not printed as a named argument.
-/
/-- info: List.length.{u_1} {α : Type u_1} : List α → Nat -/
#guard_msgs in #check List.length

/-!
All arguments are named, all are printed as named arguments.
-/
/-- info: Nat.pos_pow_of_pos {n : Nat} (m : Nat) (h : 0 < n) : 0 < n ^ m -/
#guard_msgs in #check Nat.pos_pow_of_pos

/-!
The hypothesis is not a named argument, so it's not printed as a named argument.
-/
def Nat.pos_pow_of_pos' {n : Nat} (m : Nat) : 0 < n → 0 < n ^ m := Nat.pos_pow_of_pos m

/-- info: Nat.pos_pow_of_pos' {n : Nat} (m : Nat) : 0 < n → 0 < n ^ m -/
#guard_msgs in #check Nat.pos_pow_of_pos'

/-!
Repetition of a named argument, only the first is printed as a named argument.
The second is made hygienic.
-/
def foo (n n : Nat) : Fin (n + 1) := 0

/-- info: foo (n : Nat) : (n✝ : Nat) → Fin (n✝ + 1) -/
#guard_msgs in #check foo

/-!
Same, but a named argument still follows, and its name is preserved.
-/

def foo' (n n : Nat) (a : Fin ((by clear n; exact n) + 1)) : Fin (n + 1) := 0

/-- info: foo' (n : Nat) : (n✝ : Nat) → (a : Fin (n + 1)) → Fin (n✝ + 1) -/
#guard_msgs in #check foo'

/-!
Named argument after inaccessible name, still stays after the colon.
But, it does not print using named pi notation since this is not a dependent type.
-/
def foo'' : String → (needle : String) → String := fun _ yo => yo

/-- info: foo'' : (a✝needle : String) → String -/
#guard_msgs in #check foo''

/-!
Named argument after inaccessible name, still stays after the colon.
Here, because it's a dependent type the named pi notation shows the name.
-/
def bar : String → (n : Nat) → Fin (n+1) := fun _ n => ⟨0, Nat.zero_lt_succ n⟩

/-- info: bar : String → (n : Nat) → Fin (n + 1) -/
#guard_msgs in #check bar

/-!
Instance argument is an inaccessible name, and we assume that it is a nameless instance,
so it goes before the colon.
-/
def bar' [LT α] (x : α) : x < x := sorry

/-- info: bar'.{u_1} {α : Type u_1} [LT α] (x : α) : x < x -/
#guard_msgs in #check bar'
