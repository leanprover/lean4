/-!
# `delabConstWithSignature` avoids using inaccessible names
-/

/-!
Defined without named arguments, prints without named arguments.
-/
#check String.append

/-!
The List argument is not named, it is not printed as a named argument.
-/
#check List.length

/-!
All arguments are named, all are printed as named arguments.
-/
#check Nat.pos_pow_of_pos

/-!
The hypothesis is not a named argument, so it's not printed as a named argument.
-/
def Nat.pos_pow_of_pos' {n : Nat} (m : Nat) : 0 < n → 0 < n ^ m := Nat.pos_pow_of_pos m

#check Nat.pos_pow_of_pos'

/-!
Repetition of a named argument, only the first is printed as a named argument.
-/
def foo (n n : Nat) : Fin (n + 1) := 0

#check foo

/-!
Repetition of a named argument, only the first is printed as a named argument.
This is checking that shadowing is represented correctly (that's not the responsibility of
`delabConstWithSignature`, but it assumes that the main delaborator will handle this correctly).
-/
def foo' (n n : Nat) (a : Fin ((by clear n; exact n) + 1)) : Fin (n + 1) := 0

#check foo'
